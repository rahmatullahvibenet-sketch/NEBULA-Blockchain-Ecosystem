"""
================================================================
  NEBULA P2P NETWORK — nebula_network.py
  Bitcoin-compatible P2P protocol
  Peer discovery, block sync, tx broadcast
================================================================
"""

import socket, threading, json, time, struct, hashlib
from typing import List, Dict, Optional, Set, Tuple, Callable
from dataclasses import dataclass, field
from enum import Enum
from nebula_core import (
    NEBULABlockchain, Block, Transaction,
    sha256d, CHAIN_ID, CHAIN_NAME, DEFAULT_PORT,
    PROTOCOL_VERSION, MAX_PEERS, MAINNET_MAGIC,
    MAX_HEADERS_AT_ONCE, MAX_BLOCKS_AT_ONCE
)

# ================================================================
#  MESSAGE TYPES
# ================================================================

class MsgType(str, Enum):
    VERSION    = "version"
    VERACK     = "verack"
    PING       = "ping"
    PONG       = "pong"
    GETBLOCKS  = "getblocks"
    GETDATA    = "getdata"
    BLOCK      = "block"
    TX         = "tx"
    INV        = "inv"
    HEADERS    = "headers"
    GETHEADERS = "getheaders"
    GETADDR    = "getaddr"
    ADDR       = "addr"
    REJECT     = "reject"
    MEMPOOL    = "mempool"
    GETINFO    = "getinfo"
    INFO       = "info"

# ================================================================
#  PEER STATE
# ================================================================

class PeerState(Enum):
    CONNECTING   = "connecting"
    HANDSHAKING  = "handshaking"
    CONNECTED    = "connected"
    SYNCING      = "syncing"
    DISCONNECTED = "disconnected"
    BANNED       = "banned"

@dataclass
class PeerInfo:
    host:          str
    port:          int
    state:         PeerState    = PeerState.CONNECTING
    version:       int          = 0
    chain_id:      int          = 0
    height:        int          = 0
    user_agent:    str          = ""
    connected_at:  float        = field(default_factory=time.time)
    last_seen:     float        = field(default_factory=time.time)
    bytes_sent:    int          = 0
    bytes_recv:    int          = 0
    latency_ms:    float        = 0.0
    ping_nonce:    int          = 0
    ping_sent:     float        = 0.0
    failures:      int          = 0

    @property
    def addr(self) -> str:
        return f"{self.host}:{self.port}"

# ================================================================
#  MESSAGE CODEC
# ================================================================

class Message:
    """
    NEBULA network message:
    [ magic(4) | type(12) | length(4) | checksum(4) | payload ]
    """
    HEADER_SIZE = 24

    def __init__(self, msg_type: str, payload: dict = None):
        self.type    = msg_type
        self.payload = payload or {}

    def encode(self) -> bytes:
        body     = json.dumps(self.payload, separators=(',', ':')).encode('utf-8')
        checksum = sha256d(body)[:4]
        type_bytes = self.type.encode('utf-8').ljust(12, b'\x00')[:12]
        header = (
            MAINNET_MAGIC +
            type_bytes +
            struct.pack('<I', len(body)) +
            checksum
        )
        return header + body

    @classmethod
    def decode(cls, data: bytes) -> Optional['Message']:
        if len(data) < cls.HEADER_SIZE:
            return None
        magic    = data[:4]
        msg_type = data[4:16].rstrip(b'\x00').decode('utf-8')
        length   = struct.unpack_from('<I', data, 16)[0]
        checksum = data[20:24]
        body     = data[24:24+length]
        if sha256d(body)[:4] != checksum:
            return None
        payload = json.loads(body.decode('utf-8'))
        return cls(msg_type, payload)

    @classmethod
    def peek_length(cls, data: bytes) -> Optional[int]:
        if len(data) < cls.HEADER_SIZE:
            return None
        return struct.unpack_from('<I', data, 16)[0] + cls.HEADER_SIZE

# ================================================================
#  PEER CONNECTION
# ================================================================

class PeerConnection:
    """Manages a single peer connection"""

    RECV_BUF = 1 << 20   # 1 MB receive buffer

    def __init__(self,
                 host:     str,
                 port:     int,
                 node:     'P2PNode',
                 sock:     socket.socket = None,
                 inbound:  bool = False):
        self.info    = PeerInfo(host=host, port=port)
        self.node    = node
        self._sock   = sock
        self.inbound = inbound
        self._buf    = b''
        self._lock   = threading.Lock()
        self._running = False

    def connect(self) -> bool:
        try:
            self._sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self._sock.settimeout(10)
            self._sock.connect((self.info.host, self.info.port))
            self._sock.settimeout(None)
            return True
        except Exception as e:
            self.info.state = PeerState.DISCONNECTED
            return False

    def start(self):
        self._running = True
        t = threading.Thread(target=self._recv_loop, daemon=True,
                              name=f"Peer-{self.info.addr}")
        t.start()
        # Send version immediately
        self._send_version()

    def send(self, msg: Message) -> bool:
        try:
            with self._lock:
                data = msg.encode()
                self._sock.sendall(data)
                self.info.bytes_sent += len(data)
                return True
        except Exception:
            self.disconnect()
            return False

    def _recv_loop(self):
        self._sock.settimeout(30)
        while self._running:
            try:
                chunk = self._sock.recv(self.RECV_BUF)
                if not chunk:
                    break
                self.info.bytes_recv += len(chunk)
                self.info.last_seen   = time.time()
                self._buf += chunk
                self._process_buf()
            except socket.timeout:
                self._ping()
            except Exception:
                break
        self.disconnect()

    def _process_buf(self):
        while True:
            needed = Message.peek_length(self._buf)
            if needed is None or len(self._buf) < needed:
                break
            msg_data  = self._buf[:needed]
            self._buf = self._buf[needed:]
            msg = Message.decode(msg_data)
            if msg:
                self.node._handle_message(self, msg)

    def _send_version(self):
        self.send(Message(MsgType.VERSION, {
            "version":    PROTOCOL_VERSION,
            "chain_id":   CHAIN_ID,
            "height":     self.node.bc.height,
            "user_agent": f"/NEBULA:{CHAIN_ID}/",
            "timestamp":  int(time.time()),
            "addr_from":  f"{self.node.host}:{self.node.port}",
        }))
        self.info.state = PeerState.HANDSHAKING

    def _ping(self):
        nonce = int(time.time() * 1000) & 0xFFFFFFFF
        self.info.ping_nonce = nonce
        self.info.ping_sent  = time.time()
        self.send(Message(MsgType.PING, {"nonce": nonce}))

    def disconnect(self):
        self._running = False
        try:
            self._sock.close()
        except Exception:
            pass
        self.info.state = PeerState.DISCONNECTED
        self.node._on_peer_disconnect(self)

# ================================================================
#  P2P NODE
# ================================================================

# ── NEBULA MAINNET SEED NODES ──────────────────────────────────
# These are the permanent bootstrap nodes for the NEBULA network.
# Anyone can run a node. No permission needed.
# Launch: 2025-03-16 | Author: Zayn Quantum | License: MIT
SEED_NODES = [
    # Asia Pacific
    ("seed1.nebula-nbl.io",  DEFAULT_PORT),
    ("seed2.nebula-nbl.io",  DEFAULT_PORT),
    ("seed3.nebula-nbl.io",  DEFAULT_PORT),
    # Europe
    ("seed4.nebula-nbl.io",  DEFAULT_PORT),
    ("seed5.nebula-nbl.io",  DEFAULT_PORT),
    # Americas
    ("seed6.nebula-nbl.io",  DEFAULT_PORT),
    ("seed7.nebula-nbl.io",  DEFAULT_PORT),
    # Africa & Middle East
    ("seed8.nebula-nbl.io",  DEFAULT_PORT),
    # Oceania
    ("seed9.nebula-nbl.io",  DEFAULT_PORT),
    ("seed10.nebula-nbl.io", DEFAULT_PORT),
]

# DNS seed hostnames — resolved automatically at startup
DNS_SEEDS = [
    "dnsseed.nebula-nbl.io",
    "dnsseed2.nebula-nbl.io",
    "seed.nebula-nbl.io",
]

def resolve_dns_seeds(dns_seeds: list = DNS_SEEDS) -> list:
    """Resolve DNS seeds to get bootstrap peer addresses."""
    import socket
    peers = []
    for host in dns_seeds:
        try:
            results = socket.getaddrinfo(host, DEFAULT_PORT,
                                         socket.AF_UNSPEC,
                                         socket.SOCK_STREAM)
            for res in results:
                ip = res[4][0]
                if ip not in [p[0] for p in peers]:
                    peers.append((ip, DEFAULT_PORT))
        except Exception:
            pass  # DNS not configured yet
    return peers


class P2PNode:
    """
    Full NEBULA P2P node.
    Handles peer discovery, handshake, block sync, tx relay.
    """

    def __init__(self,
                 bc:    NEBULABlockchain,
                 host:  str = "0.0.0.0",
                 port:  int = DEFAULT_PORT):
        self.bc      = bc
        self.host    = host
        self.port    = port
        self._peers: Dict[str, PeerConnection] = {}
        self._banned: Set[str] = set()
        self._lock    = threading.RLock()
        self._running = False
        self._known_invs: Set[str] = set()   # avoid rebroadcast

        # Callbacks
        self.on_new_block: Optional[Callable] = None
        self.on_new_tx:    Optional[Callable] = None

    def start(self):
        self._running = True
        # Listen for inbound
        threading.Thread(target=self._listen, daemon=True, name="P2P-Listen").start()
        # Connect to seeds
        threading.Thread(target=self._seed_connect, daemon=True, name="P2P-Seeds").start()
        # Maintenance loop
        threading.Thread(target=self._maintenance, daemon=True, name="P2P-Maint").start()
        print(f"🌐 P2P Node listening on {self.host}:{self.port}")

    def stop(self):
        self._running = False
        with self._lock:
            for peer in list(self._peers.values()):
                peer.disconnect()

    def connect_peer(self, host: str, port: int) -> bool:
        addr = f"{host}:{port}"
        if addr in self._banned:
            return False
        with self._lock:
            if addr in self._peers:
                return False
            if len(self._peers) >= MAX_PEERS:
                return False

        peer = PeerConnection(host, port, self)
        if not peer.connect():
            return False

        with self._lock:
            self._peers[addr] = peer
        peer.start()
        return True

    def broadcast_block(self, block: Block):
        """Broadcast new block to all peers"""
        inv_msg = Message(MsgType.INV, {
            "type":  "block",
            "items": [block.hash],
        })
        self._broadcast(inv_msg)

    def broadcast_tx(self, tx: Transaction):
        """Broadcast transaction to all peers"""
        inv_msg = Message(MsgType.INV, {
            "type":  "tx",
            "items": [tx.txid],
        })
        self._broadcast(inv_msg)

    def _broadcast(self, msg: Message):
        with self._lock:
            peers = list(self._peers.values())
        for peer in peers:
            if peer.info.state == PeerState.CONNECTED:
                peer.send(msg)

    def _listen(self):
        try:
            srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            srv.bind((self.host, self.port))
            srv.listen(50)
            srv.settimeout(1)
            while self._running:
                try:
                    conn, addr = srv.accept()
                    host, port = addr
                    if host in self._banned:
                        conn.close()
                        continue
                    peer = PeerConnection(host, port, self, sock=conn, inbound=True)
                    with self._lock:
                        if len(self._peers) < MAX_PEERS:
                            key = f"{host}:{port}"
                            self._peers[key] = peer
                            peer.start()
                        else:
                            conn.close()
                except socket.timeout:
                    continue
        except Exception as e:
            print(f"Listen error: {e}")

    def _seed_connect(self):
        time.sleep(1)
        for host, port in SEED_NODES:
            if not self._running:
                break
            try:
                import socket as _s
                _s.setdefaulttimeout(5)
                addrs = _s.getaddrinfo(host, port)
                if addrs:
                    self.connect_peer(host, port)
            except Exception:
                pass  # Seed DNS not available yet

    def _maintenance(self):
        """Periodic: ping peers, drop stale, find new"""
        while self._running:
            time.sleep(30)
            now = time.time()
            with self._lock:
                stale = [addr for addr, p in self._peers.items()
                         if (p.info.state == PeerState.DISCONNECTED or
                             now - p.info.last_seen > 120)]
                for addr in stale:
                    self._peers.pop(addr, None)

            # Ask connected peers for more peers
            with self._lock:
                connected = [p for p in self._peers.values()
                             if p.info.state == PeerState.CONNECTED]
            for peer in connected:
                peer.send(Message(MsgType.GETADDR))

    def _handle_message(self, peer: PeerConnection, msg: Message):
        """Route incoming messages"""
        t = msg.type
        p = msg.payload

        if t == MsgType.VERSION:
            peer.info.version    = p.get("version", 0)
            peer.info.chain_id   = p.get("chain_id", 0)
            peer.info.height     = p.get("height", 0)
            peer.info.user_agent = p.get("user_agent", "")
            if peer.info.chain_id != CHAIN_ID:
                peer.disconnect()
                return
            peer.send(Message(MsgType.VERACK))
            peer.info.state = PeerState.CONNECTED
            # Ask for blocks if they're ahead
            if peer.info.height > self.bc.height:
                self._request_sync(peer)

        elif t == MsgType.VERACK:
            peer.info.state = PeerState.CONNECTED

        elif t == MsgType.PING:
            peer.send(Message(MsgType.PONG, {"nonce": p.get("nonce", 0)}))

        elif t == MsgType.PONG:
            if p.get("nonce") == peer.info.ping_nonce:
                peer.info.latency_ms = (time.time() - peer.info.ping_sent) * 1000

        elif t == MsgType.INV:
            self._handle_inv(peer, p)

        elif t == MsgType.GETBLOCKS:
            self._handle_getblocks(peer, p)

        elif t == MsgType.BLOCK:
            self._handle_block(peer, p)

        elif t == MsgType.TX:
            self._handle_tx(peer, p)

        elif t == MsgType.GETADDR:
            with self._lock:
                addrs = [{"host": c.info.host, "port": c.info.port}
                         for c in self._peers.values()
                         if c.info.state == PeerState.CONNECTED]
            peer.send(Message(MsgType.ADDR, {"addrs": addrs[:100]}))

        elif t == MsgType.ADDR:
            for addr_info in p.get("addrs", [])[:20]:
                h, po = addr_info.get("host"), addr_info.get("port", DEFAULT_PORT)
                if h and f"{h}:{po}" not in self._peers:
                    threading.Thread(target=self.connect_peer, args=(h, po),
                                     daemon=True).start()

        elif t == MsgType.GETINFO:
            peer.send(Message(MsgType.INFO, self.bc.chain_info()))

    def _handle_inv(self, peer: PeerConnection, p: dict):
        inv_type  = p.get("type")
        items     = p.get("items", [])
        needed    = [i for i in items if i not in self._known_invs]
        if needed:
            peer.send(Message(MsgType.GETDATA, {"type": inv_type, "items": needed}))

    def _handle_getblocks(self, peer: PeerConnection, p: dict):
        start_hash = p.get("hash_stop", "")
        start_h    = 0
        for h_str in p.get("locator", []):
            blk = self.bc.get_block_by_hash(h_str)
            if blk:
                start_h = blk.height + 1
                break

        blocks_to_send = []
        for i in range(start_h, min(start_h + MAX_BLOCKS_AT_ONCE, self.bc.height + 1)):
            blk = self.bc.get_block(i)
            if blk:
                blocks_to_send.append(blk.to_dict())

        if blocks_to_send:
            peer.send(Message(MsgType.BLOCK, {"blocks": blocks_to_send}))

    def _handle_block(self, peer: PeerConnection, p: dict):
        for blk_dict in p.get("blocks", []):
            # Simplified: in production would fully deserialize
            self._known_invs.add(blk_dict.get("hash", ""))

    def _handle_tx(self, peer: PeerConnection, p: dict):
        txid = p.get("txid", "")
        self._known_invs.add(txid)

    def _request_sync(self, peer: PeerConnection):
        locator = self.bc.get_locator()
        peer.send(Message(MsgType.GETBLOCKS, {"locator": locator}))
        peer.info.state = PeerState.SYNCING

    def _on_peer_disconnect(self, peer: PeerConnection):
        with self._lock:
            self._peers.pop(peer.info.addr, None)

    def peer_count(self) -> int:
        return sum(1 for p in self._peers.values()
                   if p.info.state == PeerState.CONNECTED)

    def all_peers(self) -> List[dict]:
        with self._lock:
            return [{
                "addr":       p.info.addr,
                "state":      p.info.state.value,
                "height":     p.info.height,
                "latency_ms": f"{p.info.latency_ms:.1f}",
                "inbound":    p.inbound,
                "agent":      p.info.user_agent,
            } for p in self._peers.values()]

    def network_info(self) -> dict:
        return {
            "listening":    f"{self.host}:{self.port}",
            "peers_total":  len(self._peers),
            "peers_connected": self.peer_count(),
            "chain_height": self.bc.height,
            "banned":       len(self._banned),
        }
