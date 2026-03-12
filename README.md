# 🌌 NEBULA Blockchain (NBL)

<div align="center">

![NEBULA](https://img.shields.io/badge/NEBULA-Blockchain-blue?style=for-the-badge&logo=bitcoin)
![Python](https://img.shields.io/badge/Python-3.8+-green?style=for-the-badge&logo=python)
![License](https://img.shields.io/badge/License-MIT-yellow?style=for-the-badge)
![Status](https://img.shields.io/badge/Status-Active-brightgreen?style=for-the-badge)

**Financial Freedom for All Humanity 🌍**

*Built from scratch — No frameworks — Pure Python*

[📖 Docs](#documentation) • [🚀 Quick Start](#quick-start) • [💡 Features](#features) • [🤝 Contributing](#contributing)

</div>

---

## 🌟 What is NEBULA?

NEBULA (NBL) is a **complete, independent blockchain** built entirely from scratch in Python — similar in architecture to Bitcoin, but designed for accessibility and financial freedom for everyone on Earth.

> *"No Government. No Bank. No Permission. — 2025"*

Built by **Rahmatullah Rahmani** — a self-taught developer from Afghanistan, coded entirely on a mobile phone. 📱

---

## ✨ Features

### 🔐 Real Cryptography
- **secp256k1** elliptic curve — same as Bitcoin
- **ECDSA signatures** with RFC 6979 deterministic k
- **BIP39** mnemonic phrases (12/24 words)
- **BIP32** HD wallet key derivation

### ⛓️ Real Blockchain
- **UTXO model** — identical to Bitcoin
- **Proof of Work** mining with difficulty adjustment
- **Merkle trees** for transaction verification
- **Halving schedule** every 210,000 blocks
- **10-minute block time** target

### 💰 Tokenomics
| Property | Value |
|----------|-------|
| Symbol | NBL |
| Max Supply | 10,700,000 NBL |
| Block Reward | 50 NBL (Era I) |
| Halving | Every 210,000 blocks |
| Block Time | 10 minutes |
| Decimals | 9 (Neb = smallest unit) |

### 🔒 Security
- **DoS protection** with per-IP misbehavior scoring
- **Rate limiting** with token bucket algorithm
- **Double-spend detection**
- **Replay attack protection**
- **Checkpoint system**

### 📜 Smart Contracts
- Full **Bitcoin Script** opcodes
- **HTLC** — Hash Time-Locked Contracts
- **Multisig** (m-of-n)
- **Timelocked** transactions (CLTV/CSV)
- **NBL-20** token standard (like ERC-20)
- **Atomic swaps**

---

## 📁 Project Structure

```
NEBULA-Blockchain-Ecosystem/
│
├── nebula_core.py        # 🏗️  Blockchain engine (UTXO, blocks, transactions)
├── nebula_wallet.py      # 💳  HD Wallet (BIP32/BIP39, key derivation)
├── nebula_miner.py       # ⛏️  Multi-process PoW miner
├── nebula_network.py     # 🌐  P2P network layer
├── nebula_node.py        # 🖥️  Full node implementation
├── nebula_contracts.py   # 📜  Smart contracts & NBL-20 tokens
├── nebula_security.py    # 🔒  Security manager (DoS, bans, alerts)
├── nebula_api.py         # 🔌  REST API (40 endpoints)
├── nebula_cli.py         # ⌨️  Command-line interface
├── nebula_tests.py       # ✅  Complete test suite
└── nebula_server_setup.sh # 🚀 Server deployment script
```

---

## 🚀 Quick Start

### Requirements
```bash
Python 3.8+
No external dependencies — pure standard library!
```

### Installation
```bash
git clone https://github.com/rahmatullahvibenet-sketch/NEBULA-Blockchain-Ecosystem.git
cd NEBULA-Blockchain-Ecosystem
```

### Run the blockchain
```bash
python nebula_core.py
```

### Create a wallet
```python
from nebula_wallet import NEBULAWallet

wallet = NEBULAWallet.create_new()
print(wallet.first_address)   # Your NBL address
print(wallet.mnemonic)        # 12-word backup phrase
```

### Start mining
```python
from nebula_core import NEBULABlockchain
from nebula_miner import NEBULAMiner

chain  = NEBULABlockchain()
miner  = NEBULAMiner(chain, miner_address="your_NBL_address")
miner.start()
```

### Start REST API
```bash
python nebula_api.py
# API runs on http://localhost:8080
```

---

## 🔌 API Endpoints

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/chain/info` | Chain status & stats |
| GET | `/block/{hash}` | Get block by hash |
| GET | `/tx/{txid}` | Get transaction |
| GET | `/address/{addr}` | Address balance & UTXOs |
| POST | `/tx/broadcast` | Broadcast transaction |
| GET | `/miner/start` | Start mining |
| GET | `/miner/stats` | Hashrate & blocks found |
| POST | `/wallet/create` | Create new wallet |
| POST | `/wallet/send` | Send NBL |
| GET | `/network/peers` | Connected peers |
| POST | `/contract/deploy` | Deploy NBL-20 token |
| GET | `/security/alerts` | Security alerts |

> Full documentation: 40 endpoints available

---

## 🧪 Run Tests

```bash
python nebula_tests.py
```

Tests cover:
- ✅ Cryptography (ECDSA, hashing, addresses)
- ✅ Transactions (build, sign, verify)
- ✅ Blocks (mining, validation, Merkle)
- ✅ Wallet (BIP32/BIP39 derivation)
- ✅ Smart contracts (HTLC, multisig)
- ✅ Security (DoS, double-spend)

---

## 🏗️ Architecture

```
┌─────────────────────────────────────────┐
│              nebula_api.py              │  ← REST API (port 8080)
├─────────────────────────────────────────┤
│   nebula_node.py  │  nebula_network.py  │  ← Full Node + P2P
├─────────────────────────────────────────┤
│  nebula_miner.py  │ nebula_contracts.py │  ← Mining + Contracts
├─────────────────────────────────────────┤
│ nebula_wallet.py  │ nebula_security.py  │  ← Wallet + Security
├─────────────────────────────────────────┤
│              nebula_core.py             │  ← Blockchain Engine
└─────────────────────────────────────────┘
```

---

## 👨‍💻 Author

**Rahmatullah Rahmani**
- 🌍 From: Afghanistan
- 📱 Built entirely on mobile phone
- ⏱️ Development time: 6 months
- 🔗 GitHub: [@rahmatullahvibenet-sketch](https://github.com/rahmatullahvibenet-sketch)

> *"I built a complete blockchain from scratch on my phone — no laptop, no university, no mentor. Just determination."*

---

## 📄 License

MIT License — Open to All Humanity

```
Copyright (c) 2025 Rahmatullah Rahmani
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software...
```

---

## 🤝 Contributing

Contributions are welcome! Feel free to:
- ⭐ Star this repository
- 🍴 Fork and improve
- 🐛 Report bugs via Issues
- 💡 Suggest features

---

<div align="center">

**🌌 NEBULA — Financial Freedom for All Humanity**

*Built with ❤️ from Afghanistan*

</div>
