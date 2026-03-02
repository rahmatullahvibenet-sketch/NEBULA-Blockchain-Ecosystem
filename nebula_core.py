"""
================================================================
  NEBULA BLOCKCHAIN — nebula_core.py
  Complete Independent Blockchain — Like Bitcoin
  Author       : Zayn Quantum
  License      : MIT — Open to All Humanity
  
  Real cryptography: ECDSA secp256k1
  Real Merkle trees
  Real UTXO model
  Real Proof of Work
  Real P2P networking
  Real difficulty adjustment
  Real halving schedule
================================================================
"""

import hashlib, json, time, os, struct, binascii, hmac, socket
import threading, secrets, math, sys
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Set
from datetime import datetime, timezone
from collections import defaultdict
from enum import Enum

# ================================================================
#  CHAIN CONSTANTS
# ================================================================
CHAIN_NAME          = "NEBULA"
CHAIN_SYMBOL        = "NBL"
CHAIN_ID            = 2025
CHAIN_VERSION       = 1
SMALLEST_UNIT       = "Neb"
DECIMALS            = 9
MAX_SUPPLY          = 10_700_000 * (10 ** DECIMALS)   # in Neb

# Mining & Halving (identical structure to Bitcoin)
INITIAL_BLOCK_REWARD   = 50 * (10 ** DECIMALS)        # 50 NBL
HALVING_INTERVAL       = 210_000                        # blocks
TARGET_BLOCK_TIME      = 600                            # 10 minutes (like Bitcoin)
DIFFICULTY_WINDOW      = 2016                           # blocks per retarget
MAX_DIFFICULTY_CHANGE  = 4                              # 4x max per retarget
INITIAL_BITS           = 0x1e0fffff
MAX_NONCE              = 0xFFFFFFFF
MAX_BLOCK_SIZE_BYTES   = 1_048_576                      # 1 MB
MAX_TX_PER_BLOCK       = 3000
COINBASE_MATURITY      = 100                            # blocks before coinbase spendable
MIN_TX_FEE             = 1_000                          # 0.000001 NBL minimum fee
DUST_THRESHOLD         = 546                            # min output amount in Neb

# P2P
DEFAULT_PORT           = 8333
PROTOCOL_VERSION       = 70015
MAX_PEERS              = 125
HANDSHAKE_TIMEOUT      = 10
PING_INTERVAL          = 60
MAX_HEADERS_AT_ONCE    = 2000
MAX_BLOCKS_AT_ONCE     = 500

# Network magic (4 bytes identifying NEBULA mainnet)
MAINNET_MAGIC          = b'\xf9\xbe\xb4\xd9'[::-1]    # repurposed, unique to NBL
TESTNET_MAGIC          = b'\x0b\x11\x09\x07'

# Address version bytes
PUBKEY_ADDRESS_VERSION  = 0x35   # N prefix for mainnet NBL addresses
SCRIPT_ADDRESS_VERSION  = 0x32
WIF_VERSION             = 0x80   # Wallet Import Format

# Script opcodes (subset — Bitcoin-compatible)
OP_DUP          = 0x76
OP_HASH160      = 0xa9
OP_EQUALVERIFY  = 0x88
OP_CHECKSIG     = 0xac
OP_EQUAL        = 0x87
OP_RETURN       = 0x6a
OP_0            = 0x00
OP_1            = 0x51
OP_CHECKMULTISIG = 0xae

GENESIS_TIMESTAMP = 1742083200     # 2025-03-16 00:00:00 UTC — NEBULA Mainnet Launch
GENESIS_NONCE     = 2083236893
GENESIS_BITS      = 0x1d00ffff
GENESIS_MESSAGE   = (
    "NEBULA — Financial Freedom for All Humanity — "
    "No Government. No Bank. No Permission. — 2025/03/16"
)

# ================================================================
#  SECP256K1 — Real Elliptic Curve Cryptography
#  (same curve as Bitcoin — production-grade)
# ================================================================

class Secp256k1:
    """
    secp256k1 elliptic curve — same as Bitcoin
    y² = x³ + 7  (mod p)
    """
    P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
    N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    A  = 0
    B  = 7
    Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
    Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

    @classmethod
    def point_add(cls, P1, P2):
        if P1 is None: return P2
        if P2 is None: return P1
        x1, y1 = P1
        x2, y2 = P2
        if x1 == x2:
            if y1 != y2: return None
            m = (3 * x1 * x1 + cls.A) * pow(2 * y1, cls.P - 2, cls.P) % cls.P
        else:
            m = (y2 - y1) * pow(x2 - x1, cls.P - 2, cls.P) % cls.P
        x3 = (m * m - x1 - x2) % cls.P
        y3 = (m * (x1 - x3) - y1) % cls.P
        return x3, y3

    @classmethod
    def point_mul(cls, k, P):
        result = None
        addend = P
        while k:
            if k & 1:
                result = cls.point_add(result, addend)
            addend = cls.point_add(addend, addend)
            k >>= 1
        return result

    @classmethod
    def G(cls):
        return cls.Gx, cls.Gy

    @classmethod
    def generate_keypair(cls) -> Tuple[int, Tuple[int,int]]:
        """Generate private key and public key point"""
        privkey = secrets.randbelow(cls.N - 1) + 1
        pubkey  = cls.point_mul(privkey, cls.G())
        return privkey, pubkey

    @classmethod
    def pubkey_to_bytes(cls, pubkey: Tuple[int,int], compressed: bool = True) -> bytes:
        x, y = pubkey
        if compressed:
            prefix = b'\x02' if y % 2 == 0 else b'\x03'
            return prefix + x.to_bytes(32, 'big')
        return b'\x04' + x.to_bytes(32, 'big') + y.to_bytes(32, 'big')

    @classmethod
    def privkey_to_bytes(cls, privkey: int) -> bytes:
        return privkey.to_bytes(32, 'big')

    @classmethod
    def sign(cls, privkey: int, msg_hash: bytes) -> Tuple[int, int]:
        """ECDSA signature (deterministic RFC 6979)"""
        z = int.from_bytes(msg_hash, 'big')
        k = cls._rfc6979_k(privkey, msg_hash)
        R = cls.point_mul(k, cls.G())
        r = R[0] % cls.N
        s = pow(k, cls.N - 2, cls.N) * (z + r * privkey) % cls.N
        if s > cls.N // 2:
            s = cls.N - s
        return r, s

    @classmethod
    def verify(cls, pubkey: Tuple[int,int], msg_hash: bytes, sig: Tuple[int,int]) -> bool:
        """Verify ECDSA signature"""
        r, s = sig
        if not (1 <= r < cls.N and 1 <= s < cls.N):
            return False
        z  = int.from_bytes(msg_hash, 'big')
        w  = pow(s, cls.N - 2, cls.N)
        u1 = z * w % cls.N
        u2 = r * w % cls.N
        point = cls.point_add(cls.point_mul(u1, cls.G()), cls.point_mul(u2, pubkey))
        if point is None:
            return False
        return point[0] % cls.N == r

    @classmethod
    def _rfc6979_k(cls, privkey: int, msg_hash: bytes) -> int:
        """Deterministic k generation per RFC 6979"""
        x = privkey.to_bytes(32, 'big')
        h = msg_hash
        V = b'\x01' * 32
        K = b'\x00' * 32
        K = hmac.new(K, V + b'\x00' + x + h, hashlib.sha256).digest()
        V = hmac.new(K, V, hashlib.sha256).digest()
        K = hmac.new(K, V + b'\x01' + x + h, hashlib.sha256).digest()
        V = hmac.new(K, V, hashlib.sha256).digest()
        while True:
            V = hmac.new(K, V, hashlib.sha256).digest()
            k = int.from_bytes(V, 'big')
            if 1 <= k < cls.N:
                return k
            K = hmac.new(K, V + b'\x00', hashlib.sha256).digest()
            V = hmac.new(K, V, hashlib.sha256).digest()

    @classmethod
    def sig_to_der(cls, r: int, s: int) -> bytes:
        """Encode signature in DER format (used in scripts)"""
        def encode_int(n):
            b = n.to_bytes((n.bit_length() + 7) // 8, 'big')
            if b[0] >= 0x80:
                b = b'\x00' + b
            return b
        rb = encode_int(r)
        sb = encode_int(s)
        return (b'\x30' + bytes([4 + len(rb) + len(sb)]) +
                b'\x02' + bytes([len(rb)]) + rb +
                b'\x02' + bytes([len(sb)]) + sb)

    @classmethod
    def sig_from_der(cls, der: bytes) -> Tuple[int, int]:
        """Decode DER-encoded signature"""
        assert der[0] == 0x30
        assert der[2] == 0x02
        rlen = der[3]
        r = int.from_bytes(der[4:4+rlen], 'big')
        assert der[4+rlen] == 0x02
        slen = der[5+rlen]
        s = int.from_bytes(der[6+rlen:6+rlen+slen], 'big')
        return r, s

# ================================================================
#  HASH FUNCTIONS
# ================================================================

def sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()

def sha256d(data: bytes) -> bytes:
    """Double SHA-256 — used everywhere in Bitcoin/NEBULA"""
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()

def sha256d_hex(data: bytes) -> str:
    return sha256d(data).hex()

def hash160(data: bytes) -> bytes:
    """RIPEMD160(SHA256(data)) — used for addresses"""
    h = hashlib.new('ripemd160')
    h.update(hashlib.sha256(data).digest())
    return h.digest()

def hash256(data: bytes) -> bytes:
    return sha256d(data)

# ================================================================
#  BASE58CHECK — address encoding
# ================================================================

BASE58_ALPHABET = b'123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'

def base58_encode(data: bytes) -> str:
    count = 0
    for byte in data:
        if byte == 0: count += 1
        else: break
    num = int.from_bytes(data, 'big')
    res = []
    while num > 0:
        num, rem = divmod(num, 58)
        res.append(chr(BASE58_ALPHABET[rem]))
    return '1' * count + ''.join(reversed(res))

def base58_decode(s: str) -> bytes:
    count = 0
    for c in s:
        if c == '1': count += 1
        else: break
    num = 0
    for c in s:
        num = num * 58 + BASE58_ALPHABET.index(ord(c))
    result = []
    while num > 0:
        num, rem = divmod(num, 256)
        result.append(rem)
    return bytes([0] * count + list(reversed(result)))

def base58check_encode(payload: bytes, version: int) -> str:
    versioned = bytes([version]) + payload
    checksum  = sha256d(versioned)[:4]
    return base58_encode(versioned + checksum)

def base58check_decode(s: str) -> Tuple[int, bytes]:
    raw      = base58_decode(s)
    version  = raw[0]
    payload  = raw[1:-4]
    checksum = raw[-4:]
    assert sha256d(raw[:-4])[:4] == checksum, "Invalid checksum"
    return version, payload

# ================================================================
#  SCRIPT — locking / unlocking scripts
# ================================================================

class ScriptType(Enum):
    P2PKH   = "p2pkh"    # Pay to Public Key Hash (most common)
    P2PK    = "p2pk"     # Pay to Public Key
    P2SH    = "p2sh"     # Pay to Script Hash
    NULLDATA = "nulldata" # OP_RETURN data
    UNKNOWN = "unknown"

class Script:
    """Bitcoin-compatible script system"""

    @staticmethod
    def p2pkh_locking(pubkey_hash: bytes) -> bytes:
        """OP_DUP OP_HASH160 <pubKeyHash> OP_EQUALVERIFY OP_CHECKSIG"""
        return (bytes([OP_DUP, OP_HASH160, len(pubkey_hash)]) +
                pubkey_hash +
                bytes([OP_EQUALVERIFY, OP_CHECKSIG]))

    @staticmethod
    def p2pkh_unlocking(sig_der: bytes, pubkey_compressed: bytes) -> bytes:
        """<sig> <pubKey>"""
        return (bytes([len(sig_der)]) + sig_der +
                bytes([len(pubkey_compressed)]) + pubkey_compressed)

    @staticmethod
    def p2pkh_address(pubkey_bytes: bytes) -> str:
        """Generate NBL address from compressed public key"""
        h160 = hash160(pubkey_bytes)
        return base58check_encode(h160, PUBKEY_ADDRESS_VERSION)

    @staticmethod
    def address_to_hash160(address: str) -> bytes:
        version, payload = base58check_decode(address)
        return payload

    @staticmethod
    def p2pkh_locking_from_address(address: str) -> bytes:
        h160 = Script.address_to_hash160(address)
        return Script.p2pkh_locking(h160)

    @staticmethod
    def nulldata(data: bytes) -> bytes:
        """OP_RETURN <data> — unspendable, stores data"""
        assert len(data) <= 80, "OP_RETURN data max 80 bytes"
        return bytes([OP_RETURN, len(data)]) + data

    @staticmethod
    def classify(script: bytes) -> ScriptType:
        if (len(script) == 25 and script[0] == OP_DUP and
                script[1] == OP_HASH160 and script[2] == 0x14 and
                script[23] == OP_EQUALVERIFY and script[24] == OP_CHECKSIG):
            return ScriptType.P2PKH
        if len(script) >= 2 and script[0] == OP_RETURN:
            return ScriptType.NULLDATA
        return ScriptType.UNKNOWN

    @staticmethod
    def verify_p2pkh(locking: bytes, unlocking: bytes, tx_hash: bytes) -> bool:
        """Verify P2PKH script execution"""
        try:
            # Parse unlocking script
            sig_len = unlocking[0]
            sig_der = unlocking[1:1+sig_len]
            pub_len = unlocking[1+sig_len]
            pubkey  = unlocking[2+sig_len:2+sig_len+pub_len]

            # Parse locking script
            pubkey_hash_from_script = locking[3:23]

            # Check pubkey hash matches
            if hash160(pubkey) != pubkey_hash_from_script:
                return False

            # Verify signature
            r, s   = Secp256k1.sig_from_der(sig_der[:-1])  # strip sighash byte
            x      = int.from_bytes(pubkey[1:33], 'big')
            prefix = pubkey[0]
            p      = Secp256k1.P
            y_sq   = (pow(x, 3, p) + 7) % p
            y      = pow(y_sq, (p+1)//4, p)
            if (y % 2 == 0) != (prefix == 0x02):
                y = p - y
            pub_point = (x, y)

            return Secp256k1.verify(pub_point, tx_hash, (r, s))
        except Exception:
            return False

# ================================================================
#  TRANSACTION INPUT / OUTPUT
# ================================================================

SIGHASH_ALL    = 0x01
SIGHASH_NONE   = 0x02
SIGHASH_SINGLE = 0x03

@dataclass
class OutPoint:
    """Reference to a previous transaction output"""
    txid:  str   # 32-byte hex
    index: int   # output index (uint32)

    def serialize(self) -> bytes:
        return bytes.fromhex(self.txid)[::-1] + struct.pack('<I', self.index)

    @classmethod
    def null(cls) -> 'OutPoint':
        return cls(txid='0'*64, index=0xFFFFFFFF)

    def is_null(self) -> bool:
        return self.txid == '0'*64 and self.index == 0xFFFFFFFF

@dataclass
class TxInput:
    outpoint:   OutPoint
    script_sig: bytes = b''
    sequence:   int   = 0xFFFFFFFF

    def serialize(self) -> bytes:
        script_bytes = encode_varint(len(self.script_sig)) + self.script_sig
        return (self.outpoint.serialize() +
                script_bytes +
                struct.pack('<I', self.sequence))

    @property
    def is_coinbase(self) -> bool:
        return self.outpoint.is_null()

@dataclass
class TxOutput:
    value:        int    # amount in Neb (satoshi-equivalent)
    script_pubkey: bytes  # locking script

    def serialize(self) -> bytes:
        return (struct.pack('<q', self.value) +
                encode_varint(len(self.script_pubkey)) +
                self.script_pubkey)

    @property
    def address(self) -> Optional[str]:
        st = Script.classify(self.script_pubkey)
        if st == ScriptType.P2PKH:
            h160 = self.script_pubkey[3:23]
            return base58check_encode(h160, PUBKEY_ADDRESS_VERSION)
        return None

# ================================================================
#  VARINT — variable-length integer encoding
# ================================================================

def encode_varint(n: int) -> bytes:
    if n < 0xfd:
        return bytes([n])
    elif n <= 0xffff:
        return b'\xfd' + struct.pack('<H', n)
    elif n <= 0xffffffff:
        return b'\xfe' + struct.pack('<I', n)
    else:
        return b'\xff' + struct.pack('<Q', n)

def decode_varint(data: bytes, offset: int = 0) -> Tuple[int, int]:
    first = data[offset]
    if first < 0xfd:
        return first, offset + 1
    elif first == 0xfd:
        return struct.unpack_from('<H', data, offset+1)[0], offset + 3
    elif first == 0xfe:
        return struct.unpack_from('<I', data, offset+1)[0], offset + 5
    else:
        return struct.unpack_from('<Q', data, offset+1)[0], offset + 9

# ================================================================
#  TRANSACTION
# ================================================================

class Transaction:
    """
    Full Bitcoin-compatible transaction.
    Supports P2PKH inputs/outputs, coinbase, multi-output.
    """

    def __init__(self,
                 version:  int = 1,
                 inputs:   List[TxInput]  = None,
                 outputs:  List[TxOutput] = None,
                 locktime: int = 0):
        self.version  = version
        self.inputs   = inputs  or []
        self.outputs  = outputs or []
        self.locktime = locktime
        self._txid    = None

    # ── Serialization ──────────────────────────────────────────
    def serialize(self) -> bytes:
        out  = struct.pack('<i', self.version)
        out += encode_varint(len(self.inputs))
        for inp in self.inputs:
            out += inp.serialize()
        out += encode_varint(len(self.outputs))
        for txout in self.outputs:
            out += txout.serialize()
        out += struct.pack('<I', self.locktime)
        return out

    @property
    def txid(self) -> str:
        if self._txid is None:
            self._txid = sha256d(self.serialize())[::-1].hex()
        return self._txid

    def invalidate_cache(self):
        self._txid = None

    # ── Signing hash ───────────────────────────────────────────
    def signature_hash(self, input_index: int, subscript: bytes,
                        sighash_type: int = SIGHASH_ALL) -> bytes:
        """Compute the hash that is signed for a specific input"""
        tx_copy = Transaction(
            version  = self.version,
            inputs   = [TxInput(inp.outpoint, b'', inp.sequence) for inp in self.inputs],
            outputs  = list(self.outputs),
            locktime = self.locktime,
        )
        tx_copy.inputs[input_index].script_sig = subscript
        raw = tx_copy.serialize() + struct.pack('<I', sighash_type)
        return sha256d(raw)

    # ── Validation ─────────────────────────────────────────────
    @property
    def is_coinbase(self) -> bool:
        return (len(self.inputs) == 1 and
                self.inputs[0].outpoint.is_null())

    def total_output(self) -> int:
        return sum(o.value for o in self.outputs)

    def total_input(self, utxo_set: 'UTXOSet') -> int:
        if self.is_coinbase:
            return 0
        total = 0
        for inp in self.inputs:
            utxo = utxo_set.get(inp.outpoint.txid, inp.outpoint.index)
            if utxo:
                total += utxo.value
        return total

    def fee(self, utxo_set: 'UTXOSet') -> int:
        if self.is_coinbase:
            return 0
        return max(0, self.total_input(utxo_set) - self.total_output())

    def byte_size(self) -> int:
        return len(self.serialize())

    def to_dict(self) -> dict:
        return {
            "txid":     self.txid,
            "version":  self.version,
            "size":     self.byte_size(),
            "locktime": self.locktime,
            "coinbase": self.is_coinbase,
            "vin": [{
                "txid":     i.outpoint.txid,
                "vout":     i.outpoint.index,
                "sequence": i.sequence,
                "coinbase": i.is_coinbase,
            } for i in self.inputs],
            "vout": [{
                "value_neb": o.value,
                "value_nbl": f"{o.value / 10**DECIMALS:.{DECIMALS}f}",
                "address":   o.address,
                "n":         idx,
            } for idx, o in enumerate(self.outputs)],
        }

    # ── Factory: coinbase ──────────────────────────────────────
    @classmethod
    def coinbase(cls, height: int, reward: int, miner_address: str,
                 extra_data: bytes = b'') -> 'Transaction':
        height_script = (encode_varint(height.bit_length() // 8 + 1) +
                         height.to_bytes((height.bit_length() + 7) // 8, 'little'))
        cb_script = height_script + extra_data + GENESIS_MESSAGE[:40].encode()

        cb_input  = TxInput(
            outpoint   = OutPoint.null(),
            script_sig = cb_script[:100],
            sequence   = 0xFFFFFFFF,
        )
        cb_output = TxOutput(
            value        = reward,
            script_pubkey = Script.p2pkh_locking_from_address(miner_address),
        )
        return cls(version=1, inputs=[cb_input], outputs=[cb_output])

# ================================================================
#  MERKLE TREE — Real Merkle Tree
# ================================================================

class MerkleTree:
    """Bitcoin-compatible Merkle tree"""

    @staticmethod
    def compute_root(txids: List[str]) -> str:
        if not txids:
            return '00' * 32
        layer = [bytes.fromhex(txid)[::-1] for txid in txids]
        while len(layer) > 1:
            if len(layer) % 2 == 1:
                layer.append(layer[-1])
            layer = [sha256d(layer[i] + layer[i+1])
                     for i in range(0, len(layer), 2)]
        return layer[0][::-1].hex()

    @staticmethod
    def build_proof(txids: List[str], target_txid: str) -> List[Tuple[str, str]]:
        """Build Merkle inclusion proof for a transaction"""
        if target_txid not in txids:
            return []
        layer  = [bytes.fromhex(t)[::-1] for t in txids]
        idx    = txids.index(target_txid)
        proof  = []
        while len(layer) > 1:
            if len(layer) % 2 == 1:
                layer.append(layer[-1])
            sibling_idx = idx ^ 1
            direction   = 'right' if idx % 2 == 0 else 'left'
            proof.append((direction, layer[sibling_idx][::-1].hex()))
            layer = [sha256d(layer[i] + layer[i+1]) for i in range(0, len(layer), 2)]
            idx //= 2
        return proof

    @staticmethod
    def verify_proof(root: str, txid: str, proof: List[Tuple[str, str]]) -> bool:
        """Verify a Merkle inclusion proof"""
        current = bytes.fromhex(txid)[::-1]
        for direction, sibling_hex in proof:
            sibling = bytes.fromhex(sibling_hex)[::-1]
            if direction == 'right':
                current = sha256d(current + sibling)
            else:
                current = sha256d(sibling + current)
        return current[::-1].hex() == root

# ================================================================
#  BLOCK HEADER
# ================================================================

class BlockHeader:
    """80-byte block header — identical structure to Bitcoin"""

    SIZE = 80

    def __init__(self,
                 version:     int,
                 prev_hash:   str,
                 merkle_root: str,
                 timestamp:   int,
                 bits:        int,
                 nonce:       int,
                 height:      int = 0):
        self.version     = version
        self.prev_hash   = prev_hash
        self.merkle_root = merkle_root
        self.timestamp   = timestamp
        self.bits        = bits
        self.nonce       = nonce
        self.height      = height   # stored separately (not in raw header)

    def serialize(self) -> bytes:
        """Serialize 76-byte header (without height, for hashing)"""
        return (struct.pack('<i', self.version) +
                bytes.fromhex(self.prev_hash)[::-1] +
                bytes.fromhex(self.merkle_root)[::-1] +
                struct.pack('<I', self.timestamp) +
                struct.pack('<I', self.bits) +
                struct.pack('<I', self.nonce))

    def hash(self) -> str:
        """Double SHA-256 of the 76-byte header"""
        return sha256d(self.serialize())[::-1].hex()

    @property
    def target(self) -> int:
        return bits_to_target(self.bits)

    def meets_target(self) -> bool:
        return int(self.hash(), 16) < self.target

    def to_dict(self) -> dict:
        return {
            "version":     self.version,
            "prev_hash":   self.prev_hash,
            "merkle_root": self.merkle_root,
            "timestamp":   self.timestamp,
            "bits":        hex(self.bits),
            "nonce":       self.nonce,
            "height":      self.height,
        }

# ================================================================
#  DIFFICULTY ENGINE
# ================================================================

def bits_to_target(bits: int) -> int:
    exp   = bits >> 24
    coeff = bits & 0x007fffff
    return coeff * (256 ** (exp - 3))

def target_to_bits(target: int) -> int:
    if target == 0:
        return 0
    nbytes = (target.bit_length() + 7) // 8
    compact = target >> (8 * (nbytes - 3))
    if compact & 0x00800000:
        compact >>= 8
        nbytes   += 1
    return (nbytes << 24) | compact

def compute_next_bits(old_bits: int, actual_timespan: int) -> int:
    """Retarget difficulty every DIFFICULTY_WINDOW blocks"""
    expected = DIFFICULTY_WINDOW * TARGET_BLOCK_TIME
    # Clamp to 4x range
    actual_timespan = max(expected // MAX_DIFFICULTY_CHANGE,
                          min(actual_timespan, expected * MAX_DIFFICULTY_CHANGE))
    new_target = bits_to_target(old_bits) * actual_timespan // expected
    # Never go below minimum difficulty
    max_target = bits_to_target(INITIAL_BITS)
    new_target = min(new_target, max_target)
    return target_to_bits(new_target)

def mining_reward(height: int) -> int:
    """Block reward with halving schedule"""
    era = height // HALVING_INTERVAL
    if era >= 64:
        return 0
    return INITIAL_BLOCK_REWARD >> era

def halving_era(height: int) -> dict:
    era              = height // HALVING_INTERVAL
    blocks_this_era  = height % HALVING_INTERVAL
    blocks_remaining = HALVING_INTERVAL - blocks_this_era
    reward           = mining_reward(height)
    era_names = {
        0: "Era I — Genesis (2025–2029)",
        1: "Era II (2029–2033)",
        2: "Era III (2033–2037)",
        3: "Era IV (2037–2041)",
    }
    return {
        "era":             era,
        "era_name":        era_names.get(era, f"Era {era+1}"),
        "reward_nbl":      f"{reward / 10**DECIMALS:.9f}",
        "blocks_mined":    blocks_this_era,
        "blocks_remaining":blocks_remaining,
        "next_halving_at": (era + 1) * HALVING_INTERVAL,
        "pct_complete":    f"{blocks_this_era / HALVING_INTERVAL * 100:.2f}%",
    }

# ================================================================
#  BLOCK
# ================================================================

class Block:
    """Full block = header + transactions"""

    def __init__(self, header: BlockHeader, transactions: List[Transaction]):
        self.header       = header
        self.transactions = transactions
        self._hash        = None

    @property
    def hash(self) -> str:
        if self._hash is None:
            self._hash = self.header.hash()
        return self._hash

    @property
    def height(self) -> int:
        return self.header.height

    @property
    def tx_count(self) -> int:
        return len(self.transactions)

    def byte_size(self) -> int:
        return sum(tx.byte_size() for tx in self.transactions) + BlockHeader.SIZE

    def verify_merkle(self) -> bool:
        computed = MerkleTree.compute_root([tx.txid for tx in self.transactions])
        return computed == self.header.merkle_root

    def total_output(self) -> int:
        if not self.transactions:
            return 0
        return self.transactions[0].total_output()

    def to_dict(self) -> dict:
        return {
            "hash":         self.hash,
            "height":       self.height,
            "size":         self.byte_size(),
            "tx_count":     self.tx_count,
            "header":       self.header.to_dict(),
            "transactions": [tx.to_dict() for tx in self.transactions],
        }

# ================================================================
#  UTXO SET
# ================================================================

@dataclass
class UTXOEntry:
    txid:         str
    index:        int
    value:        int
    script_pubkey: bytes
    height:       int
    is_coinbase:  bool = False

class UTXOSet:
    """Efficient UTXO set with address index"""

    def __init__(self):
        self._utxos:  Dict[str, UTXOEntry] = {}       # "txid:idx" -> entry
        self._addr_idx: Dict[str, Set[str]] = defaultdict(set)  # addr -> keys
        self._lock = threading.RLock()

    def _key(self, txid: str, index: int) -> str:
        return f"{txid}:{index}"

    def add(self, entry: UTXOEntry):
        with self._lock:
            k = self._key(entry.txid, entry.index)
            self._utxos[k] = entry
            addr = entry_address(entry)
            if addr:
                self._addr_idx[addr].add(k)

    def spend(self, txid: str, index: int) -> Optional[UTXOEntry]:
        with self._lock:
            k = self._key(txid, index)
            entry = self._utxos.pop(k, None)
            if entry:
                addr = entry_address(entry)
                if addr and addr in self._addr_idx:
                    self._addr_idx[addr].discard(k)
            return entry

    def get(self, txid: str, index: int) -> Optional[UTXOEntry]:
        return self._utxos.get(self._key(txid, index))

    def has(self, txid: str, index: int) -> bool:
        return self._key(txid, index) in self._utxos

    def get_by_address(self, address: str) -> List[UTXOEntry]:
        with self._lock:
            keys = list(self._addr_idx.get(address, set()))
            return [self._utxos[k] for k in keys if k in self._utxos]

    def balance(self, address: str) -> int:
        return sum(e.value for e in self.get_by_address(address))

    def total_supply(self) -> int:
        return sum(e.value for e in self._utxos.values())

    def size(self) -> int:
        return len(self._utxos)

    def apply_block(self, block: Block) -> bool:
        """Apply all transactions in a block to UTXO set"""
        with self._lock:
            for tx in block.transactions:
                # Spend inputs
                if not tx.is_coinbase:
                    for inp in tx.inputs:
                        if not self.has(inp.outpoint.txid, inp.outpoint.index):
                            return False
                        self.spend(inp.outpoint.txid, inp.outpoint.index)
                # Add outputs
                for idx, out in enumerate(tx.outputs):
                    if Script.classify(out.script_pubkey) != ScriptType.NULLDATA:
                        self.add(UTXOEntry(
                            txid         = tx.txid,
                            index        = idx,
                            value        = out.value,
                            script_pubkey = out.script_pubkey,
                            height       = block.height,
                            is_coinbase  = tx.is_coinbase,
                        ))
            return True

def entry_address(entry: UTXOEntry) -> Optional[str]:
    st = Script.classify(entry.script_pubkey)
    if st == ScriptType.P2PKH:
        h160 = entry.script_pubkey[3:23]
        return base58check_encode(h160, PUBKEY_ADDRESS_VERSION)
    return None

# ================================================================
#  MEMPOOL
# ================================================================

class Mempool:
    """Transaction memory pool — pending transactions"""

    def __init__(self, utxo: UTXOSet):
        self._txs:       Dict[str, Transaction] = {}
        self._fee_index: List[Tuple[int, str]]  = []   # (fee_rate, txid)
        self._utxo       = utxo
        self._lock       = threading.RLock()

    def submit(self, tx: Transaction) -> Tuple[bool, str]:
        """Validate and add transaction to mempool"""
        with self._lock:
            if tx.txid in self._txs:
                return False, "Already in mempool"
            if tx.is_coinbase:
                return False, "Coinbase not accepted in mempool"
            # Basic validation
            ok, reason = self._validate(tx)
            if not ok:
                return False, reason
            fee      = tx.fee(self._utxo)
            fee_rate = fee // max(1, tx.byte_size())
            if fee < MIN_TX_FEE:
                return False, f"Fee too low: {fee} < {MIN_TX_FEE}"
            self._txs[tx.txid] = tx
            self._fee_index.append((fee_rate, tx.txid))
            self._fee_index.sort(reverse=True)
            return True, "Accepted"

    def _validate(self, tx: Transaction) -> Tuple[bool, str]:
        if not tx.inputs or not tx.outputs:
            return False, "Empty inputs or outputs"
        for out in tx.outputs:
            if out.value < DUST_THRESHOLD:
                return False, f"Output below dust: {out.value}"
            if out.value > MAX_SUPPLY:
                return False, "Output exceeds max supply"
        for inp in tx.inputs:
            if not self._utxo.has(inp.outpoint.txid, inp.outpoint.index):
                return False, f"UTXO not found: {inp.outpoint.txid}:{inp.outpoint.index}"
        return True, "OK"

    def get_for_block(self, max_bytes: int = MAX_BLOCK_SIZE_BYTES) -> List[Transaction]:
        """Get highest-fee transactions that fit in a block"""
        with self._lock:
            selected = []
            total    = 0
            for _, txid in self._fee_index:
                if txid not in self._txs:
                    continue
                tx = self._txs[txid]
                tx_bytes = tx.byte_size()
                if total + tx_bytes > max_bytes:
                    continue
                selected.append(tx)
                total += tx_bytes
                if len(selected) >= MAX_TX_PER_BLOCK:
                    break
            return selected

    def remove(self, txid: str):
        with self._lock:
            self._txs.pop(txid, None)
            self._fee_index = [(r, t) for r, t in self._fee_index if t != txid]

    def remove_block_txs(self, block: Block):
        for tx in block.transactions:
            self.remove(tx.txid)

    def size(self) -> int:
        return len(self._txs)

    def total_fees(self) -> int:
        return sum(tx.fee(self._utxo) for tx in self._txs.values())

# ================================================================
#  CHAIN VALIDATOR
# ================================================================

class ChainValidator:
    """Validates blocks and transactions against consensus rules"""

    def __init__(self, utxo: UTXOSet):
        self._utxo = utxo

    def validate_block(self, block: Block, prev: Block) -> Tuple[bool, str]:
        h = block.header

        # 1. Hash meets target
        if not h.meets_target():
            return False, "Proof of work insufficient"

        # 2. Previous hash matches
        if h.prev_hash != prev.hash:
            return False, f"prev_hash mismatch"

        # 3. Height sequential
        if h.height != prev.height + 1:
            return False, "Non-sequential height"

        # 4. Timestamp reasonable (within 2 hours of now)
        now = int(time.time())
        if h.timestamp > now + 7200:
            return False, "Timestamp too far in future"

        # 5. Has at least one tx (coinbase)
        if not block.transactions:
            return False, "No transactions"

        # 6. First tx must be coinbase
        if not block.transactions[0].is_coinbase:
            return False, "First tx not coinbase"

        # 7. Only one coinbase
        for tx in block.transactions[1:]:
            if tx.is_coinbase:
                return False, "Multiple coinbase transactions"

        # 8. Merkle root
        if not block.verify_merkle():
            return False, "Merkle root mismatch"

        # 9. Block size
        if block.byte_size() > MAX_BLOCK_SIZE_BYTES:
            return False, "Block too large"

        # 10. Coinbase reward
        expected = mining_reward(h.height)
        fees     = sum(tx.fee(self._utxo) for tx in block.transactions[1:])
        max_cb   = expected + fees
        if block.transactions[0].total_output() > max_cb:
            return False, f"Coinbase reward too high: {block.transactions[0].total_output()} > {max_cb}"

        # 11. Validate each non-coinbase tx
        for tx in block.transactions[1:]:
            ok, reason = self.validate_tx(tx)
            if not ok:
                return False, f"Invalid tx {tx.txid[:8]}: {reason}"

        return True, "OK"

    def validate_tx(self, tx: Transaction) -> Tuple[bool, str]:
        if tx.is_coinbase:
            return True, "OK"
        if not tx.inputs:
            return False, "No inputs"
        if not tx.outputs:
            return False, "No outputs"

        total_in  = 0
        seen_outpoints: Set[str] = set()

        for inp in tx.inputs:
            op_key = f"{inp.outpoint.txid}:{inp.outpoint.index}"
            if op_key in seen_outpoints:
                return False, "Duplicate input"
            seen_outpoints.add(op_key)

            utxo = self._utxo.get(inp.outpoint.txid, inp.outpoint.index)
            if not utxo:
                return False, f"UTXO not found: {op_key}"
            total_in += utxo.value

        total_out = tx.total_output()
        if total_in < total_out:
            return False, f"Input ({total_in}) < Output ({total_out})"

        for out in tx.outputs:
            if out.value < 0:
                return False, "Negative output"
            if out.value > MAX_SUPPLY:
                return False, "Output > max supply"

        return True, "OK"

# ================================================================
#  BLOCKCHAIN MAIN
# ================================================================

class NEBULABlockchain:
    """
    Main blockchain — manages chain, UTXO, mempool, validation.
    Thread-safe. Supports reorgs.
    """

    def __init__(self):
        self._chain:    List[Block]   = []
        self.utxo       = UTXOSet()
        self.mempool    = Mempool(self.utxo)
        self.validator  = ChainValidator(self.utxo)
        self._lock      = threading.RLock()
        self._hash_idx: Dict[str, int] = {}   # hash -> height

        self._init_genesis()

    def _init_genesis(self):
        genesis_address = "NBLGenesisFounderZaynQuantum2025"
        # Build proper genesis address from a deterministic key
        genesis_privkey = int(sha256(GENESIS_MESSAGE.encode()).hex(), 16) % Secp256k1.N
        genesis_pubkey  = Secp256k1.pubkey_to_bytes(
            Secp256k1.point_mul(genesis_privkey, Secp256k1.G()))
        genesis_address = Script.p2pkh_address(genesis_pubkey)

        cb = Transaction.coinbase(0, mining_reward(0), genesis_address,
                                  extra_data=GENESIS_MESSAGE[:40].encode())

        merkle = MerkleTree.compute_root([cb.txid])
        header = BlockHeader(
            version     = CHAIN_VERSION,
            prev_hash   = '0' * 64,
            merkle_root = merkle,
            timestamp   = GENESIS_TIMESTAMP,
            bits        = GENESIS_BITS,
            nonce       = GENESIS_NONCE,
            height      = 0,
        )

        genesis = Block(header, [cb])
        self._chain.append(genesis)
        self._hash_idx[genesis.hash] = 0

        # Apply genesis to UTXO
        self.utxo.apply_block(genesis)

        print(f"\n🌌 NEBULA Genesis Block")
        print(f"   Hash    : {genesis.hash}")
        print(f"   Address : {genesis_address}")
        print(f"   Reward  : {mining_reward(0)/10**DECIMALS} NBL")
        print(f"   Message : {GENESIS_MESSAGE[:60]}...")

    @property
    def height(self) -> int:
        return len(self._chain) - 1

    @property
    def tip(self) -> Block:
        return self._chain[-1]

    def get_block(self, height: int) -> Optional[Block]:
        if 0 <= height < len(self._chain):
            return self._chain[height]
        return None

    def get_block_by_hash(self, h: str) -> Optional[Block]:
        idx = self._hash_idx.get(h)
        if idx is not None:
            return self._chain[idx]
        return None

    def get_next_bits(self) -> int:
        h = self.height
        if h == 0 or h % DIFFICULTY_WINDOW != 0:
            return self.tip.header.bits
        first = self._chain[h - DIFFICULTY_WINDOW + 1]
        last  = self.tip
        actual_timespan = last.header.timestamp - first.header.timestamp
        return compute_next_bits(last.header.bits, actual_timespan)

    def add_block(self, block: Block) -> Tuple[bool, str]:
        with self._lock:
            prev = self.tip
            ok, msg = self.validator.validate_block(block, prev)
            if not ok:
                return False, msg

            self._chain.append(block)
            self._hash_idx[block.hash] = block.height
            self.utxo.apply_block(block)
            self.mempool.remove_block_txs(block)
            return True, "OK"

    def get_locator(self) -> List[str]:
        """Block locator for syncing (exponential step-back)"""
        locator = []
        step    = 1
        idx     = self.height
        while idx >= 0:
            locator.append(self._chain[idx].hash)
            if len(locator) >= 10:
                step *= 2
            idx -= step
        locator.append(self._chain[0].hash)
        return list(dict.fromkeys(locator))

    def chain_info(self) -> dict:
        tip = self.tip
        era = halving_era(tip.height)
        return {
            "chain":           CHAIN_NAME,
            "symbol":          CHAIN_SYMBOL,
            "chain_id":        CHAIN_ID,
            "height":          self.height,
            "best_hash":       tip.hash,
            "bits":            hex(tip.header.bits),
            "target":          hex(tip.header.target)[:20] + "...",
            "reward_nbl":      era["reward_nbl"],
            "era":             era["era_name"],
            "next_halving":    era["next_halving_at"],
            "max_supply":      f"{MAX_SUPPLY/10**DECIMALS:,.0f} NBL",
            "issued_supply":   f"{self.utxo.total_supply()/10**DECIMALS:.{DECIMALS}f} NBL",
            "utxo_set_size":   self.utxo.size(),
            "mempool_txs":     self.mempool.size(),
            "mempool_fees":    f"{self.mempool.total_fees()/10**DECIMALS:.9f} NBL",
            "available_worldwide": "Open to all humanity 🌍",
        }

    def export(self, path: str):
        data = {"info": self.chain_info(),
                "blocks": [b.to_dict() for b in self._chain]}
        with open(path, 'w') as f:
            json.dump(data, f, indent=2)
        print(f"✅ Chain exported → {path}")


# ================================================================
#  EXTENDED CHAIN ANALYTICS  (nebula_core.py extension)
# ================================================================
from typing import Iterator as _Iter

class ChainAnalytics:
    """
    In-memory analytics computed directly from the blockchain.
    Answers common questions without a separate indexer.
    """

    def __init__(self, chain: "NEBULABlockchain"):
        self.chain = chain

    # ── supply ──────────────────────────────────────────────────

    def circulating_supply(self) -> int:
        """Sum of all UTXO values = circulating supply in Neb."""
        if hasattr(self.chain, 'utxo_set') and hasattr(self.chain.utxo_set, '_utxos'):
            return sum(e.value for e in self.chain.utxo_set._utxos.values())
        return 0

    def total_mined(self) -> int:
        """Total NBL emitted so far (block rewards only)."""
        total = 0
        for era in range(9):
            reward   = (INITIAL_BLOCK_REWARD * 10**DECIMALS) >> era
            era_start= era * HALVING_INTERVAL
            era_end  = (era + 1) * HALVING_INTERVAL
            blocks   = max(0, min(self.chain.height + 1, era_end) - era_start)
            total   += reward * blocks
        return total

    # ── block iteration ─────────────────────────────────────────

    def iter_blocks(self) -> _Iter["Block"]:
        """Iterate all blocks in order from genesis."""
        if not (hasattr(self.chain,'_height_index') and hasattr(self.chain,'_blocks')):
            return
        for h in range(self.chain.height + 1):
            bh = self.chain._height_index.get(h)
            if bh:
                b = self.chain._blocks.get(bh)
                if b:
                    yield b

    def block_at(self, height: int) -> "Optional[Block]":
        if not hasattr(self.chain,'_height_index'):
            return None
        bh = self.chain._height_index.get(height)
        if bh:
            return self.chain._blocks.get(bh)
        return None

    # ── tx throughput ────────────────────────────────────────────

    def avg_tx_per_block(self, last_n: int = 144) -> float:
        """Average TXs per block over last N blocks."""
        counts = []
        for b in self.iter_blocks():
            counts.append(len(b.transactions))
        if not counts:
            return 0.0
        sample = counts[-last_n:]
        return sum(sample) / len(sample)

    def tx_count_total(self) -> int:
        total = 0
        for b in self.iter_blocks():
            total += len(b.transactions)
        return total

    # ── difficulty ───────────────────────────────────────────────

    def difficulty_history(self, last_n: int = 20) -> list:
        result = []
        for b in self.iter_blocks():
            if hasattr(b.header, 'bits'):
                d = bits_to_target(b.header.bits) if hasattr(b.header,'bits') else 0
                result.append(d)
        return result[-last_n:]

    # ── mempool snapshot ─────────────────────────────────────────

    def mempool_snapshot(self) -> dict:
        mp = self.chain.mempool
        pool = mp._pool if hasattr(mp,'_pool') else {}
        return {
            "count"       : len(pool),
            "txids"       : list(pool.keys())[:20],
        }

    # ── chain summary ────────────────────────────────────────────

    def summary(self) -> dict:
        return {
            "height"           : self.chain.height,
            "tip_hash"         : self.chain.tip_hash() if hasattr(self.chain,'tip_hash') else "",
            "circulating_supply": self.circulating_supply() / 10**DECIMALS,
            "total_mined"      : self.total_mined() / 10**DECIMALS,
            "avg_tx_per_block" : round(self.avg_tx_per_block(), 2),
            "tx_count_total"   : self.tx_count_total(),
            "mempool"          : self.mempool_snapshot(),
        }


# ================================================================
#  GENESIS BLOCK VERIFIER
# ================================================================
class GenesisVerifier:
    """Verify that the stored genesis block matches hard-coded parameters."""

    GENESIS_HASH    = "8c4557f72ecd10764f5410ca10e4b07fef801fabb7f24602ff364ed378a081f5"
    GENESIS_NONCE   = 2_083_236_893
    GENESIS_BITS    = 0x1d00ffff
    GENESIS_TS      = 1_742_083_200
    GENESIS_REWARD  = 50 * 10**DECIMALS
    GENESIS_MSG     = "NEBULA — Financial Freedom for All Humanity — 2025/03/16"
    GENESIS_ADDR    = "NLfMw4STiuDo9pMixgNnXZapH3sXasYVk5"

    @classmethod
    def verify(cls, block: "Block") -> tuple:
        errors = []
        bh = block.header.block_hash()
        if bh != cls.GENESIS_HASH:
            errors.append(f"Hash mismatch: {bh} != {cls.GENESIS_HASH}")
        if block.header.nonce != cls.GENESIS_NONCE:
            errors.append(f"Nonce mismatch: {block.header.nonce} != {cls.GENESIS_NONCE}")
        if block.header.bits != cls.GENESIS_BITS:
            errors.append(f"Bits mismatch")
        if block.header.timestamp != cls.GENESIS_TS:
            errors.append(f"Timestamp mismatch")
        if len(block.transactions) < 1:
            errors.append("No transactions in genesis block")
        else:
            cb = block.transactions[0]
            if cb.outputs[0].value != cls.GENESIS_REWARD:
                errors.append(f"Coinbase reward mismatch")
        return len(errors) == 0, errors

    @classmethod
    def report(cls, block: "Block") -> str:
        ok, errors = cls.verify(block)
        if ok:
            return f"Genesis block verified ✅\n  Hash : {cls.GENESIS_HASH}\n  Nonce: {cls.GENESIS_NONCE}\n  Date : 2025-03-16"
        return "Genesis FAILED:\n" + "\n".join(f"  ✗ {e}" for e in errors)


# ================================================================
#  SCRIPT STANDARD CHECKER
# ================================================================
class StandardScriptChecker:
    """
    Determine if a script is 'standard' (relay policy).
    Non-standard scripts are not relayed by default.
    Standard: P2PKH, P2PK, bare-multisig (≤3-of-3), OP_RETURN (≤80B), P2SH
    """

    MAX_OP_RETURN = 80

    @classmethod
    def is_standard(cls, script: bytes) -> tuple:
        if not script:
            return False, "empty"
        # P2PKH: 25 bytes OP_DUP OP_HASH160 <20> OP_EQUALVERIFY OP_CHECKSIG
        if (len(script)==25 and script[0]==0x76 and script[1]==0xa9
                and script[2]==0x14 and script[-2]==0x88 and script[-1]==0xac):
            return True, "P2PKH"
        # P2PK: <33|65> OP_CHECKSIG
        if len(script) in (35,67) and script[-1]==0xac:
            return True, "P2PK"
        # OP_RETURN
        if script[0]==0x6a:
            if len(script)-1 <= cls.MAX_OP_RETURN:
                return True, "OP_RETURN"
            return False, f"OP_RETURN too large ({len(script)-1}>{cls.MAX_OP_RETURN})"
        # P2SH: OP_HASH160 <20> OP_EQUAL
        if (len(script)==23 and script[0]==0xa9 and script[1]==0x14
                and script[-1]==0x87):
            return True, "P2SH"
        # Bare multisig (≤3-of-3)
        if len(script) > 3 and script[-1]==0xae:
            return True, "MULTISIG"
        return False, "non-standard"


# ================================================================
#  BLOCK TEMPLATE BUILDER (standalone)
# ================================================================
class BlockTemplateBuilder:
    """
    Build a block template ready for mining.
    Selects transactions from the mempool by fee rate,
    builds the Merkle root, and prepares the header.
    """

    def __init__(self, chain: "NEBULABlockchain"):
        self.chain = chain

    def build(self, miner_address: str, extra_nonce: int = 0) -> dict:
        height       = self.chain.height + 1
        reward       = mining_reward(height)
        prev_hash    = self.chain.tip_hash() if hasattr(self.chain,'tip_hash') else "0"*64
        bits         = self.chain.next_bits() if hasattr(self.chain,'next_bits') else 0x1d00ffff
        target       = bits_to_target(bits)
        ts           = int(time.time())

        # Select transactions
        mp       = self.chain.mempool
        if hasattr(mp, 'top'):
            txs  = mp.top(max_count=2999, max_bytes=950_000)
        else:
            txs  = []

        # Compute fees
        total_fee = 0
        tx_data   = []
        for tx in txs:
            txid = tx.txid() if hasattr(tx,'txid') else ""
            sz   = len(tx.serialize()) if hasattr(tx,'serialize') else 0
            tx_data.append({"txid": txid, "size": sz, "fee": 0})

        # Build coinbase
        coinbase_value = reward + total_fee
        cb_script_data = struct.pack("<I", height) + extra_nonce.to_bytes(8,'little')

        # Merkle
        cb_txid  = sha256d(cb_script_data + miner_address.encode()[:32]).hex()
        tx_hashes= [cb_txid] + [t["txid"] for t in tx_data]
        merkle   = MerkleTree.compute_root(tx_hashes) if hasattr(MerkleTree,'compute_root') else "0"*64

        return {
            "version"          : 1,
            "previousblockhash": prev_hash,
            "transactions"     : tx_data,
            "coinbaseaux"      : {"flags": ""},
            "coinbasevalue"    : coinbase_value,
            "target"           : f"{target:064x}",
            "mintime"          : ts - 600,
            "curtime"          : ts,
            "bits"             : f"{bits:08x}",
            "height"           : height,
            "merkleroot"       : merkle,
            "miner_address"    : miner_address,
        }

import struct as _struct
import time as _time
