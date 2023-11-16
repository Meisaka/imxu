#!/usr/bin/python3
__version__ = "0.1"
__lic__ = """
Copyright (c) 2023 Meisaka Yukara

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE."""

import os
import sys
import argparse
import collections.abc
import re
import traceback
import base64
import pathlib
import socket
import socketserver
import selectors
import types
try: from secrets import randbits, token_bytes
except:
	import random
	rd = random.SystemRandom()
	def randbits(n):
		return rd.getrandbits(n)
	def token_bytes(n):
		return rd.getrandbits(n*8).to_bytes(n, 'big')
import threading
import time
import http.server
import hashlib
import struct
import zlib
try: import serial
except: serial = None

win_rsvp = re.compile('^(com[0-9]|lpt[0-9]|aux|prn)$|[/\\\\:?*"<>|]+', flags=re.I)
re_white = re.compile('[\\t ]+')
base_path = pathlib.Path('.').absolute()
imsc_config = base_path / 'imsc_config'
fs_auth = []
def read_config():
	if not imsc_config.exists(): return
	conf = imsc_config.read_text('UTF8').splitlines()
	fs_auth.clear()
	for line in conf:
		if line.startswith('#'): continue
		parts = re_white.split(line)
		if len(parts) < 1: continue
		cmd = parts[0].lower()
		if cmd == 'fsauth' and len(parts) >= 2:
			fs_auth.append(parts[1])
def write_config():
	conf = ['# ' + sys.argv[0] + ' config file']
	for a in fs_auth:
		conf.append(' '.join(('fsauth', a)))
	imsc_config.write_text(os.linesep.join(conf), 'UTF8')

def convert_path(path):
	pt = []
	for p in path.parts:
		if p == '..':
			if len(pt) > 0: pt.pop()
		elif p.startswith('..'): pass
		else: pt.append(win_rsvp.sub('r~',p))
	return pathlib.PurePosixPath('/'.join(pt))
def to_cbint(val: int, tcode=0):
	if val < 0:
		if tcode != 0: raise ValueError('negative length of type: '+str(tcode))
		tcode = 1
		val = -(val+1)
	tcode = (tcode & 7) << 5
	if val < 24: return bytes((tcode|val,))
	if val <= 255: return bytes((tcode|0x18, val))
	if val <= 65535:
		return bytes((tcode|0x19,)) + val.to_bytes(2,'big')
	if val <= 0xffffffff:
		return bytes((tcode|0x1a,)) + val.to_bytes(4,'big')
	if val <= 0xffffffffffffffff:
		return bytes((tcode|0x1b,)) + val.to_bytes(8,'big')
	raise NotImplementedError('cbint: '+str(val))

class CBMessage:
	class CBList:
		def __init__(self, msg):
			self._msg = msg
		def __enter__(self):
			self._msg._ctx += 1
			self._msg._buf.append(0x9f)
			return self._msg
		def __exit__(self, exc_type, exc_val, exc_tb):
			self._msg._buf.append(0xff)
			self._msg._ctx -= 1
			return False
	def __init__(self, buf: bytearray = bytearray()):
		self._buf = buf
		self._ctx = 0
	def get(self):
		if self._ctx > 0:
			raise AssertionError('unable to get buffer with incomplete lists')
		return self._buf
	def list(self):
		return CBMessage.CBList(self)
	def append(self, val):
		if val is True: self._buf.append(0xf5)
		elif val is False: self._buf.append(0xf4)
		elif val is None: self._buf.append(0xf7)
		elif isinstance(val, int): self._buf.extend(to_cbint(val))
		elif isinstance(val, str):
			fb = val.encode('UTF8')
			self._buf.extend(to_cbint(len(fb), 3))
			self._buf.extend(fb)
		elif isinstance(val, dict):
			self._buf.extend(to_cbint(len(val), 5))
			for k, v in val:
				self.append(k)
				self.append(v)
		elif isinstance(val, (list, tuple)):
			self._buf.extend(to_cbint(len(val), 4))
			for el in val: self.append(el)
		elif isinstance(val, collections.abc.Generator):
			with self.list():
				for el in val: self.append(el)
		else: raise ValueError('no encoding for type:'+repr(val.__class__.__qualname__))

class IMXPSession():
	__slots__ = ('ses', 'sys', 'ext_ids', 'cmd', 'dbg_status', 'dbg_len')
	def __init__(self, ses, sys, ext_ids):
		self.ses = ses
		self.sys = sys # type: IMXPService
		self.ext_ids = ext_ids
		self.cmd = IMXPSession.ex_cmd.copy()
		for ext_id in ext_ids:
			ext_fn_list = IMXPSession.extentions.get(ext_id)
			if ext_fn_list is not None:
				for ext_ent in ext_fn_list:
					self.cmd[ext_ent[0]] = ext_ent[1]
		self.dbg_status = 0
		self.dbg_len = 0

	def f_4(self, cc, param):
		extlen = str(len(self.ext_ids))
		self.ses.send(struct.pack('<H'+extlen+'H', cc|8, *self.ext_ids))
	dbg_infos = ('', 'Rx:', 'Tx:')
	def dbg_some(self, id, msg):
		if self.dbg_len > 80 or self.dbg_status != id or id == 0:
			print(
				'\n' if self.dbg_status != 0 else '',
				IMXPSession.dbg_infos[id],
				sep='', end='', flush=True)
			self.dbg_len = 0
			self.dbg_status = id
		self.dbg_len += len(msg)
		print(msg, end='' if id != 0 else '\n', flush=True)
	# serial ext
	def f_180(self, cc, param):
		res = bytearray(struct.pack('<H', cc|8))
		msg = CBMessage(res)
		msg.append(self.sys.ports)
		self.sys.last_ses = self
		print('req-serial', self.sys.ports, res)
		self.dbg_status = 0
		self.ses.send(res)
	def f_182(self, cc, param):
		data = param[1:]
		self.sys.chan_send(param[0], data)
		if data[0] == 10:
			self.dbg_some(2, '\n')
			self.dbg_status = 0
		else: self.dbg_some(2, repr(data)[12:-2])
	def chan_send(self, index, data):
		self.dbg_some(1, repr(data)[12:-2])
		res = struct.pack('<HB', 0x1820, index) + data
		self.ses.send(res)
	def f_183(self, cc, param):
		self.dbg_some(0, '{} {} {}'.format('ctl-serial', param[0], param[1]))
	# filesys ext
	def f_200(self, cc, param):
		path = param.partition(b'\0')[0].decode('UTF8')
		path = base_path.joinpath(convert_path(pathlib.PurePosixPath(path)))
		res = bytearray(struct.pack('<H', cc|8))
		with CBMessage(res).list() as msg:
			for f in path.iterdir():
				msg.append((f.is_dir(), f.stat().st_size, f.name))
		self.ses.send(res)

	ex_cmd = {
		0x4: f_4,
	}
	extentions = {
		2: [(0x200, f_200)],
		3: [(0x180, f_180), (0x182, f_182), (0x183, f_183)]
	}
	def ondata(self, data):
		cc = data[0] | (data[1] << 8)
		f = self.cmd.get(cc >> 4)
		if f is not None: f(self, cc, data[2:])
		else: print('unknown', hex(cc >> 4),repr(data[2:]))

class SerialChannel:
	def __init__(self, chan_index, port, conf):
		if conf is not None:
			b, p, d, s = conf
			if b is None: b = 9600
			if p is None: p = serial.PARITY_NONE
			if d is None: d = serial.EIGHTBITS
			if s is None: s = serial.STOPBITS_ONE
		else: b, p, d, s = 9600, serial.PARITY_NONE, serial.EIGHTBITS, serial.STOPBITS_ONE
		self.tx_buf = bytearray()
		self.rx_buf = bytearray()
		self.index = chan_index
		self.dev = serial.Serial(port=port, baudrate=b, bytesize=d, parity=p, stopbits=s)
		self.tx_event = threading.Event()
		self.rx_thread = threading.Thread(target=serial_rx, args=(self,), daemon=True)
		self.tx_thread = threading.Thread(target=serial_tx, args=(self,), daemon=True)
		self.tx_thread.start()
		self.rx_thread.start()

def serial_rx(chan: SerialChannel):
	while True:
		b = chan.dev.read()
		chan.rx_buf.extend(b)
def serial_tx(chan: SerialChannel):
	while True:
		if len(chan.tx_buf) > 0:
			c = chan.tx_buf[0:1]
			chan.tx_buf.pop(0)
			chan.dev.write(c)
		else:
			chan.tx_event.wait()
			chan.tx_event.clear()

class IMXPService:
	def __init__(self, fsconfig, comconfig):
		self.ports = comconfig
		self.filesystems = fsconfig
		self.ext_ids = [] # type: list[int]
		self.channels = [] # type: list[SerialChannel]
		self.last_ses = None # type: IMXPSession | None
		index = 0
		for com in comconfig:
			if com[0] == 'dev':
				self.channels.append(SerialChannel(index, com[1], com[2]))
			else:
				print('serial mode', com[0], 'is not yet supported', file=sys.stderr)
			index += 1
		if len(fsconfig) > 0:  self.ext_ids.append(2)
		if len(comconfig) > 0: self.ext_ids.append(3)
	def chan_send(self, chan_index, data):
		for chan in self.channels:
			if chan.index == chan_index:
				chan.tx_buf.extend(data)
				chan.tx_event.set()
	def process(self):
		if self.last_ses is not None:
			for chan in self.channels:
				if len(chan.rx_buf) > 0:
					b = bytearray()
					while len(chan.rx_buf) > 0:
						b.append(chan.rx_buf.pop(0))
					self.last_ses.chan_send(chan.index, b)
	def make_inst(self, websock, data):
		cc = data[0] | (data[1] << 8)
		if cc == 0x0020 and len(data) == 24: # handle Hello
			req = struct.unpack('<BB6sQIBB',data[2:])
			print('hello',req[0],req[1],req[2],'ext',req[5],'opt',req[6])
			websock.inst = IMXPSession(websock, self, self.ext_ids)
			websock.send(struct.pack('<HBB6sQIBB',0x20,3,0,b'EthFSC',0,randbits(32),1,0))
		else: print('unknown',repr(data))

class WebsocketException(Exception):
	pass

class WebSocketSession(socketserver.BaseRequestHandler):
	__slots__ = (
		'request', 'client_address',
		'server', 'payload', 'sendbuf'
		'decode', 'status',
		'skey', 'pkey', 'sid', 'inst',
		'is_open', '_websocket_shutdown'
		)

	def __init__(self, handler):
		self.request = handler.request
		self.request.setblocking(False)
		self.client_address = handler.client_address
		self.sys = handler.server.sys
		self.payload = bytearray()
		self.sendbuf = bytearray()
		self.decode = 0
		self.status = None
		self.auth = 0
		self.sid = token_bytes(16)
		self.is_open = True
		self.inst = None
		self._websocket_shutdown = False

	def handle(self):
		# low level stuff
		try:
			r = self.request.recv(8192)
			if len(r) < 1: return False
			self.payload += r
			l = len(self.payload)
			if len(self.payload) > 4096:
				print('#' + str(len(self.payload)) + '      ', end='\r', flush=True)
			self.WSPDecode()
			while self.decode == 0 and len(self.payload) < l:
				l = len(self.payload)
				self.WSPDecode()
		except:
			self.send(1011)
			raise
		if len(self.sendbuf) > 0: raise _MoreData()
		return True

	def handle_write(self):
		sent = self.request.send(self.sendbuf)
		if sent == len(self.sendbuf): self.sendbuf.clear()
		else: del self.sendbuf[:sent]
		if len(self.sendbuf) > 0: return True
		return None

	def finish(self):
		# I think they hung up on us
		print("ending WebSocket session")
		if self.inst is not None:
			self.inst.ses = None
		super().finish()

	def onmessage(self, data):
		# we got data! how nice :3
		try:
			if self.inst is not None:
				# not entirely my problem
				self.inst.ondata(data)
				return
			elif self.sys is not None:
				self.sys.make_inst(self, data)
		except:
			# what did you sent me?
			print('onmessage exception')
			print(traceback.format_exc())
			self.sendstatus('Rubarb Pie')
			pass

	def tick(self):
		# actually send status and reset
		if self.status is not None:
			self.send('status:' + str(self.status) + '\n')
			self.status = None

	def sendstatus(self, status):
		# set the status message
		self.status = status
		self._e_waiting = True

	def WSPDecode(self):
		# websocket protocol, look it up!
		scale = len(self.payload)
		if self.decode == 0:
			if scale < 6: return
			opcode, pll = self.payload[0], self.payload[1]
			opcode &= 15
			if pll < 128: raise WebsocketException('invalid client frame')
			pll -= 128
			dataofs = 6
			if pll == 126:
				dataofs = 8
				if scale < dataofs: return
				pll, = struct.unpack('!H',self.payload[2:4])
			elif pll == 127:
				dataofs = 14
				if scale < dataofs: return
				pll, = struct.unpack('!Q',self.payload[2:10])

			self.pll = pll
			self.opcode = opcode
			self.mask = self.payload[dataofs-4:dataofs]
			self.decode = 1
			self.payload = self.payload[dataofs:]
			scale = len(self.payload)

		if self.decode == 1 and scale >= self.pll:
			self.decode = 0
			try:
				mask = self.mask
				with memoryview(self.payload) as mem:
					for e in range(self.pll): mem[e] ^= mask[e & 3]
			except Exception: raise WebsocketException('mask error')
			if self.opcode == 1: self.onmessage(self.payload[:self.pll].decode())
			elif self.opcode == 2: self.onmessage(self.payload[:self.pll])
			elif self.opcode == 8:
				if self.pll >= 2:
					close_code = struct.unpack('!H{}s'.format(self.pll - 2), self.payload[:self.pll])
				else: close_code = 1006
				print('WebSocket close', close_code, file=sys.stderr)
				self.send(1000)
			else: print('not impl WS:', self.opcode, file=sys.stderr)
			self.payload = self.payload[self.pll:]

	def send(self, val, reqopcode = None):
		# more websocket, look it up
		if self._websocket_shutdown: return
		if val == None: return
		elif isinstance(val, int):
			opcode = 8
			if not 1000 <= val <= 1999: val = 1011
			val = struct.pack('!H', val) + b'Closing'
			self._websocket_shutdown = True
		elif isinstance(val, str):
			opcode = 1
			val = val.encode()
		else: opcode = 2
		if isinstance(reqopcode, int): opcode = reqopcode & 15
		opcode |= 128
		pll = len(val)
		if pll > 65535: pfx = struct.pack('!BBQ', opcode, 127, pll)
		elif pll > 125: pfx = struct.pack('!BBH', opcode, 126, pll)
		else: pfx = struct.pack('!BB', opcode, pll)
		self.sendbuf.extend(pfx)
		self.sendbuf.extend(val)
		sent = self.request.send(self.sendbuf)
		if sent == len(self.sendbuf): self.sendbuf.clear()
		else: del self.sendbuf[:sent]
		return sent

class _MoreData(BaseException):
	pass

class _UpgradePerform(BaseException):
	def WithObject(self, obj):
		self.upgradeto = obj
		return self

# we start off in HTTP mode, like a good websocket server
class EtheriaRequest(http.server.BaseHTTPRequestHandler):

	wbufsize = 1024
	disable_nagle_algorithm = True
	server_version = 'Etheria/' + __version__
	protocol_version = 'HTTP/1.1'

	def __init__(self, request, client_address, server):
		self.request = request
		self.client_address = client_address
		self.server = server
		self.setup()

	def try_upgrade(self):
		try:
			upto = self.headers['upgrade'].lower()
			if upto == 'websocket':
				# this could fail
				print('websocket upgrade "{}"'.format(self.headers['x-forwarded-for']))
				mh = hashlib.sha1()
				mh.update(self.headers['sec-websocket-key'].encode('ascii'))
				mh.update(b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11")
				rhs = str(base64.b64encode(mh.digest()),'ascii')
				#print('accept-key: ' + rhs)
				self.send_response_only(101, 'Switching Protocol')
				self.send_header('sec-websocket-accept', rhs)
				self.send_header('upgrade', 'websocket')
				self.send_header('connection', 'upgrade')
				self.end_headers()
				raise _UpgradePerform().WithObject(WebSocketSession(self))
		except _UpgradePerform: raise
		except:
			traceback.print_exc()
			return False
		return False

	def do_GET(self):
		#print('path: ' + self.path)
		connect_header = [x.strip() for x in self.headers['connection'].lower().split(',')]
		print(connect_header)
		if 'connection' in self.headers and 'upgrade' in connect_header:
			if not self.try_upgrade():
				self.send_error(400, "Nope") # Nope, best HTTP message
			return

		if self.path != '/':
			self.send_error(404, "Unfound") # Unfound, not "not found"
			return

		r = 'status: ok'
		er = r.encode()
		self.close_connection = False
		self.send_response(200, 'Success') # This is actually proper
		self.send_header('Content-Length',str(len(er)))
		self.send_header('Connection', 'keep-alive')
		self.end_headers()
		self.wfile.write(er)
		self.wfile.flush()
	
	def handle(self):
		self.close_connection = True
		self.handle_one_request()
		return not self.close_connection

	def finish(self):
		super().finish()
		#print("ending session")
		# still in HTTP, we don't want a ton of these

	def log_message(self, fmt, *args):
		print(fmt)
		pass

class EtheriaServer(http.server.HTTPServer):
	# this doesn't really serve files over HTTP
	# only websockets
	# although it could, if you ask it reeeeeaaallly nicely (and write file handlers)
	def __init__(self, a, r, sys=None):
		super().__init__(a,r)
		self.__is_shut_down = threading.Event()
		self.__shutdown_request = False
		self.sys = sys

	def __enter__(self):
		return self
	def __exit__(self, *args):
		self.server_close()

	def serve_forever(self, poll_timeout = None):
		self.__is_shut_down.clear()
		try:
			with socketserver._ServerSelector() as selector:
				selector.register(self, selectors.EVENT_READ)
				self.sel = selector
				while not self.__shutdown_request:
					ready = selector.select(poll_timeout)
					for key, mask in ready:
						if key.fileobj == self:
							self.begin_request()
							continue
						try:
							if mask & selectors.EVENT_READ:
								self.process_request(key.fileobj, key.data)
							if mask & selectors.EVENT_WRITE:
								self.process_write_request(key.fileobj, key.data)
						except Exception:
							self.shutdown_request(key.fileobj)
							self.handle_error(key.fileobj, key.data)
						except:
							self.shutdown_request(key.fileobj)
							raise
					self.service_actions()
		finally:
			self.__shutdown_request = False
			self.__is_shut_down.set()
	
	def begin_request(self):
		try:
			request, client_address = self.get_request()
		except OSError: return

		if self.verify_request(request, client_address):
			try:
				handle = self.RequestHandlerClass(request, client_address, self)
				handle._e_waiting = False
				self.sel.register(request, selectors.EVENT_READ, handle)
			except Exception:
				self.shutdown_request(request)
				self.handle_error(request, client_address)
			except:
				self.shutdown_request(request)
				raise
		else: self.shutdown_request(request)

	def process_write_request(self, request, handler):
		r = handler.handle_write()
		if r != True:
			self.sel.modify(request, selectors.EVENT_READ, handler)

	def process_request(self, request, handler):
		try:
			r = handler.handle()
			if r is True: return
			self.finish_request(request, handler)
		except _UpgradePerform as UR:
			handler.finish()
			r = UR.upgradeto
			r._e_waiting = False
			self.sel.modify(request, selectors.EVENT_READ, r)
		except _MoreData:
			self.sel.modify(request, selectors.EVENT_READ + selectors.EVENT_WRITE, handler)
		except: raise

	def finish_request(self, request, handler):
		handler.finish()
		handler.is_open = False
		self.shutdown_request(request)

	def shutdown_request(self, request):
		self.sel.unregister(request)
		super().shutdown_request(request)

	def service_actions(self):
		if self.sys != None:
			self.sys.process()
		for k in self.sel.get_map().values():
			if hasattr(k.data, '_e_waiting') and k.data._e_waiting:
				try: k.data.tick()
				except Exception:
					self.shutdown_request(k.fileobj)
					self.handle_error(k.fileobj, k.data)
				except:
					self.shutdown_request(k.fileobj)
					raise
				k.data._e_waiting = False

if __name__ == '__main__':
	args = argparse.ArgumentParser(
		description='Websocket bridge for CenREE',
		formatter_class=argparse.RawTextHelpFormatter)
	args.add_argument('--bind-all', action='store_true',
		help='allow connections over the network, instead of just localhost')
	fs_args = args.add_argument_group(
		'file system access',
		'''By default, file systems are read only. This feature is incomplete
and only provides access to a local directory listing.''')
	fs_args.add_argument(
		'--filesystem', action='store_true',
		help='Enable access to local file system')
	if serial is None:
		sc_msg = '''
hardware serial ports require pySerial to be installed, run
    pip install pyserial
'''
	else: sc_msg = ''
	sc_args = args.add_argument_group(
		'serial ports',
		'''Provide access to serial ports or connections with serial semantics.''' + sc_msg)
	sc_args.add_argument(
		'--serial-list', action='store_true',
		help='''Show serial devices attached to the system''')
	sc_args.add_argument(
		'--serial', action='append', nargs=1, metavar='DEV[,OPT]',
		help='''Add access to a local serial port device.
DEV must be a serial device name.
OPT overrides any port settings the client sets.
 options are [baud][parity][data bits[stop bits]]
 and must not have any space between each option.
 [baud] is number of bits per second.
 [parity] is a letter signifying the type: n,e,n,o,s,
 [data bits] is a number from 5 to 8; without parity prefix with 'd'.
 [stop bits] can be unspecified, 1, or 2.

9600n81 - a common setting.
9600e71 - the typical Centurion/ADDS setting.
d7 - always 7 data bits, but let client control baud and parity
''')
	sc_args.add_argument(
		'--tcp-connect', action='append', nargs=1, metavar='IP,PORT',
		help='''Connect to IP on PORT'''
	)
	sc_args.add_argument(
		'--tcp-listen', action='append', nargs=1, metavar='IP,PORT',
		help='''Bind to IP on PORT, and listen for a connection.'''
	)
	p_args = args.parse_args()
	print(p_args, file=sys.stderr)
	fs_config = []
	if p_args.filesystem:
		fs_config.append(base_path)
	com_serial = []
	if p_args.serial_list or p_args.serial is not None:
		if serial is None:
			print('serial library required, run "pip3 install pyserial"', file=sys.stderr)
			sys.exit(20)
		from serial.tools.list_ports import comports
		all_dev = comports()
		if p_args.serial_list:
			for dev in all_dev:
				if dev.vid is not None:
					info = '{:04x}:{:04x} {} {} {} {} {}'.format(
						dev.vid or 0, dev.pid or 0,
						dev.interface, dev.serial_number, dev.location,
						dev.manufacturer, dev.product)
				else: info = ''
				print(dev.device, dev.name, dev.description, dev.hwid, info, file=sys.stderr)
			sys.exit(0)
		if p_args.serial is not None:
			confcodes = { '': None, None: None,
				'e':serial.PARITY_EVEN, 'o':serial.PARITY_ODD,
				'm':serial.PARITY_MARK, 's':serial.PARITY_SPACE,
				'n':serial.PARITY_NONE, '.':serial.STOPBITS_ONE_POINT_FIVE,
				'1':serial.STOPBITS_ONE, '2':serial.STOPBITS_TWO,
				'5':serial.FIVEBITS, '6':serial.SIXBITS,
				'7':serial.SEVENBITS, '8':serial.EIGHTBITS,
			}
			re_conf = re.compile('^([1-9][0-9]+)?(?:([NEMOSnemos]|[Dd])(?:([5678])([12\.])?)?)?$')
			for p in p_args.serial:
				dev, sep, conf = p[0].partition(',')
				if conf != '':
					m = re_conf.fullmatch(conf)
					if m is not None:
						baud, par, dat, stop = m.groups()
						dat = confcodes[dat]
						if dat is not None and stop is None:
							stop = '1'
						conf = (int(baud), confcodes[par.lower()], dat, confcodes[stop])
					else:
						conf = None
						print('invalid config:', conf, file=sys.stderr)
						sys.exit(1)
				else:
					conf = None
				sysdev = None
				for edev in all_dev:
					if edev.name == dev or edev.device == dev:
						sysdev = edev.device
					elif os.name == 'nt':
						ldev = dev.lower()
						if ldev == edev.name.lower() or ldev == edev.device.lower():
							sysdev = edev.device
				if sysdev is None: sysdev = dev
				print('serial-device:', sysdev, 'config:', conf, file=sys.stderr)
				com_serial.append(('dev', sysdev, conf))
	if p_args.tcp_connect is not None:
		for p in p_args.tcp_connect:
			addr, _, port = p[0].partition(',')
			com_serial.append(('tcp', 'connect', addr, int(port)))
	if p_args.tcp_listen is not None:
		for p in p_args.tcp_listen:
			addr, _, port = p[0].partition(',')
			com_serial.append(('tcp', 'listen', addr, int(port)))
	if len(com_serial) > 0:
		print('configured ports:')
		for comindex in range(len(com_serial)):
			com = com_serial[comindex]
			print(comindex, com[0], com[1], com[2])
	read_config()
	try:
		addr = '127.0.0.1'
		if p_args.bind_all: addr = '0.0.0.0'
		with EtheriaServer((addr,42646),EtheriaRequest) as srv:
			srv.sys = IMXPService(fs_config, com_serial)
			print("Server started", srv.server_address[0], srv.server_port)
			srv.serve_forever(0.1)
	except KeyboardInterrupt:
		print('shutdown')
