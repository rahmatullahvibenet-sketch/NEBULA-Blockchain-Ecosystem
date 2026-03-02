#!/bin/bash
# ================================================================
#  NEBULA BLOCKCHAIN — Complete Server Setup
#  Author  : Zayn Quantum
#  License : MIT
#  OS      : Ubuntu 22.04 / 24.04 LTS
#
#  HOW TO USE:
#    1. Upload all nebula_*.py files to your server
#    2. Run: chmod +x nebula_server_setup.sh
#    3. Run: sudo ./nebula_server_setup.sh
# ================================================================

set -e

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
GOLD='\033[0;33m'
NC='\033[0m'

ok()   { echo -e "${GREEN}[OK]  $1${NC}"; }
err()  { echo -e "${RED}[ERR] $1${NC}"; exit 1; }
info() { echo -e "${BLUE}[...] $1${NC}"; }
warn() { echo -e "${YELLOW}[!!!] $1${NC}"; }
step() { echo -e "\n${GOLD}=== STEP $1 ===${NC}"; }

echo -e "${GOLD}"
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║                                                              ║"
echo "║   NEBULA BLOCKCHAIN — SERVER DEPLOYMENT                     ║"
echo "║   Author  : Zayn Quantum                                     ║"
echo "║   License : MIT — Open to All Humanity                      ║"
echo "║   For All Humanity — Worldwide                              ║"
echo "║                                                              ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo -e "${NC}"

# ================================================================
step "1 — Check Root"
# ================================================================
if [ "$EUID" -ne 0 ]; then
    err "Please run as root: sudo ./nebula_server_setup.sh"
fi
ok "Running as root"

# ================================================================
step "2 — Check NEBULA Files"
# ================================================================
NEBULA_FILES=(
    "nebula_core.py"
    "nebula_wallet.py"
    "nebula_miner.py"
    "nebula_network.py"
    "nebula_node.py"
    "nebula_contracts.py"
    "nebula_security.py"
    "nebula_cli.py"
    "nebula_tests.py"
)

MISSING=0
for f in "${NEBULA_FILES[@]}"; do
    if [ ! -f "$f" ]; then
        warn "Missing: $f"
        MISSING=$((MISSING + 1))
    else
        ok "Found: $f"
    fi
done

if [ $MISSING -gt 0 ]; then
    err "Missing $MISSING files. Run this script from the NEBULA folder."
fi

# ================================================================
step "3 — System Update"
# ================================================================
info "Updating system packages..."
apt-get update -qq
apt-get upgrade -y -qq
ok "System updated"

# ================================================================
step "4 — Install Dependencies"
# ================================================================
info "Installing required packages..."
apt-get install -y -qq \
    python3 python3-pip python3-venv \
    git curl wget \
    screen tmux \
    ufw fail2ban \
    htop net-tools \
    openssl ca-certificates \
    logrotate
ok "All dependencies installed"

# Check Python version
PYTHON_VER=$(python3 --version 2>&1 | cut -d' ' -f2)
ok "Python version: $PYTHON_VER"

# ================================================================
step "5 — Create NEBULA System User"
# ================================================================
if ! id "nebula" &>/dev/null; then
    useradd -m -s /bin/bash -c "NEBULA Blockchain Node" nebula
    ok "User 'nebula' created"
else
    ok "User 'nebula' already exists"
fi

# ================================================================
step "6 — Create Directory Structure"
# ================================================================
mkdir -p /opt/nebula/{blockchain,wallet,logs,backup,config,data}

chown -R nebula:nebula /opt/nebula
chmod -R 750 /opt/nebula
chmod 700 /opt/nebula/config

ok "Directories created:"
echo "    /opt/nebula/blockchain  — code"
echo "    /opt/nebula/data        — chain data"
echo "    /opt/nebula/wallet      — wallet files"
echo "    /opt/nebula/logs        — log files"
echo "    /opt/nebula/backup      — backups"
echo "    /opt/nebula/config      — config & keys"

# ================================================================
step "7 — Python Virtual Environment"
# ================================================================
info "Creating Python virtual environment..."
sudo -u nebula python3 -m venv /opt/nebula/venv
sudo -u nebula /opt/nebula/venv/bin/pip install --upgrade pip -q
ok "Python venv ready at /opt/nebula/venv"

# ================================================================
step "8 — Install NEBULA Blockchain Files"
# ================================================================
info "Copying NEBULA files..."
cp "${NEBULA_FILES[@]}" /opt/nebula/blockchain/
chown -R nebula:nebula /opt/nebula/blockchain/
chmod 640 /opt/nebula/blockchain/*.py
ok "All ${#NEBULA_FILES[@]} NEBULA files installed"

# ================================================================
step "9 — Run Test Suite"
# ================================================================
info "Running 42 blockchain tests..."
cd /opt/nebula/blockchain
TEST_RESULT=$(sudo -u nebula /opt/nebula/venv/bin/python3 nebula_tests.py 2>&1 | tail -4)
echo "$TEST_RESULT"

if echo "$TEST_RESULT" | grep -q "ALL PASSED"; then
    ok "All 42 tests passed!"
else
    warn "Some tests failed — check output above"
fi
cd -

# ================================================================
step "10 — Firewall (UFW)"
# ================================================================
info "Configuring firewall rules..."
ufw --force reset > /dev/null 2>&1
ufw default deny incoming
ufw default allow outgoing
ufw allow 22/tcp          comment "SSH"
ufw allow 8333/tcp        comment "NEBULA P2P"
ufw allow 8334/tcp        comment "NEBULA RPC"
ufw --force enable > /dev/null 2>&1
ok "Firewall enabled"
echo ""
ufw status numbered
echo ""

# ================================================================
step "11 — Fail2Ban (Brute Force Protection)"
# ================================================================
info "Configuring Fail2Ban..."
cat > /etc/fail2ban/jail.local << 'F2B'
[DEFAULT]
bantime  = 3600
findtime = 600
maxretry = 5

[sshd]
enabled = true
port    = ssh
logpath = %(sshd_log)s
backend = %(sshd_backend)s
F2B

systemctl enable fail2ban > /dev/null 2>&1
systemctl restart fail2ban
ok "Fail2Ban enabled — SSH brute force protection active"

# ================================================================
step "12 — Create Miner Wallet"
# ================================================================
info "Creating NEBULA wallet for mining rewards..."
echo ""
warn "Your 12-word mnemonic will appear below."
warn "WRITE IT DOWN ON PAPER. KEEP IT OFFLINE. NEVER SHARE IT."
echo ""

sudo -u nebula /opt/nebula/venv/bin/python3 - << 'WALLETPY'
import sys
sys.path.insert(0, '/opt/nebula/blockchain')
from nebula_wallet import NEBULAWallet
import os, stat

w = NEBULAWallet.create_new()

print()
print("=" * 56)
print("  YOUR NEBULA WALLET")
print("=" * 56)
print(f"  Address  : {w.first_address}")
print()
print("  12-WORD MNEMONIC (WRITE THIS DOWN — NEVER SHARE):")
print(f"  {w.mnemonic}")
print("=" * 56)
print()

# Save address (public - ok to store)
with open('/opt/nebula/config/miner_address.txt', 'w') as f:
    f.write(w.first_address)

# Save backup (private - owner only)
backup_path = '/opt/nebula/config/wallet_backup.txt'
with open(backup_path, 'w') as f:
    f.write(f"NEBULA WALLET BACKUP\n")
    f.write(f"Author  : Zayn Quantum\n")
    f.write(f"Created : {__import__('datetime').datetime.now().isoformat()}\n")
    f.write(f"\nAddress  : {w.first_address}\n")
    f.write(f"Mnemonic : {w.mnemonic}\n")
    f.write(f"\nWARNING: Keep this file PRIVATE. Never share your mnemonic.\n")

os.chmod(backup_path, stat.S_IRUSR | stat.S_IWUSR)  # 600 — owner only
print("  Address saved : /opt/nebula/config/miner_address.txt")
print("  Backup saved  : /opt/nebula/config/wallet_backup.txt")
WALLETPY

ok "Wallet created"
MINER_ADDR=$(cat /opt/nebula/config/miner_address.txt 2>/dev/null || echo "UNKNOWN")
ok "Miner address: $MINER_ADDR"

# ================================================================
step "13 — Systemd Services"
# ================================================================
info "Creating nebula.service (full node)..."
cat > /etc/systemd/system/nebula.service << SERVICE
[Unit]
Description=NEBULA Blockchain Full Node — Zayn Quantum
Documentation=https://github.com/zaynquantum/nebula
After=network-online.target
Wants=network-online.target

[Service]
Type=simple
User=nebula
Group=nebula
WorkingDirectory=/opt/nebula/blockchain
ExecStart=/opt/nebula/venv/bin/python3 nebula_cli.py node --datadir /opt/nebula/data --port 8333
ExecStop=/bin/kill -s SIGTERM \$MAINPID
Restart=always
RestartSec=15
TimeoutStopSec=30
StandardOutput=append:/opt/nebula/logs/nebula.log
StandardError=append:/opt/nebula/logs/nebula.log
LimitNOFILE=65536
LimitNPROC=4096
Environment=PYTHONUNBUFFERED=1
Environment=PYTHONDONTWRITEBYTECODE=1
KillMode=mixed
PrivateTmp=true
NoNewPrivileges=true

[Install]
WantedBy=multi-user.target
SERVICE

info "Creating nebula-miner.service..."
cat > /etc/systemd/system/nebula-miner.service << MINER
[Unit]
Description=NEBULA Blockchain Miner — Zayn Quantum
After=network-online.target nebula.service
Wants=network-online.target

[Service]
Type=simple
User=nebula
Group=nebula
WorkingDirectory=/opt/nebula/blockchain
ExecStart=/opt/nebula/venv/bin/python3 nebula_cli.py mine --address $MINER_ADDR --datadir /opt/nebula/data
Restart=always
RestartSec=30
StandardOutput=append:/opt/nebula/logs/nebula-miner.log
StandardError=append:/opt/nebula/logs/nebula-miner.log
Environment=PYTHONUNBUFFERED=1
LimitNOFILE=65536
NoNewPrivileges=true

[Install]
WantedBy=multi-user.target
MINER

systemctl daemon-reload
systemctl enable nebula
systemctl enable nebula-miner
ok "Services created and enabled:"
echo "    nebula.service        — full node (auto-starts on boot)"
echo "    nebula-miner.service  — miner    (auto-starts on boot)"

# ================================================================
step "14 — Log Rotation"
# ================================================================
cat > /etc/logrotate.d/nebula << 'LOGROT'
/opt/nebula/logs/*.log {
    daily
    rotate 30
    compress
    delaycompress
    missingok
    notifempty
    copytruncate
    su nebula nebula
}
LOGROT
ok "Log rotation: daily, keep 30 days"

# ================================================================
step "15 — Auto Backup"
# ================================================================
cat > /opt/nebula/backup/backup.sh << 'BACKUP'
#!/bin/bash
# NEBULA Auto-Backup — runs every 6 hours via cron
BACKUP_DIR="/opt/nebula/backup"
DATA_DIR="/opt/nebula/data"
DATE=$(date +%Y%m%d_%H%M%S)

if [ -f "$DATA_DIR/chain.json" ]; then
    cp "$DATA_DIR/chain.json" "$BACKUP_DIR/chain_$DATE.json"
    # Keep only last 28 backups (7 days x 4 per day)
    ls -t "$BACKUP_DIR"/chain_*.json 2>/dev/null | tail -n +29 | xargs -r rm
    echo "[$(date)] Backup: chain_$DATE.json"
fi
BACKUP

chmod +x /opt/nebula/backup/backup.sh
chown nebula:nebula /opt/nebula/backup/backup.sh

# Add to cron
(crontab -u nebula -l 2>/dev/null; echo "0 */6 * * * /opt/nebula/backup/backup.sh >> /opt/nebula/logs/backup.log 2>&1") | crontab -u nebula -
ok "Auto-backup: every 6 hours, keeps 7 days"

# ================================================================
step "16 — System Optimization"
# ================================================================
info "Optimizing system for blockchain node..."

# Increase file descriptor limits
cat >> /etc/security/limits.conf << 'LIMITS'
nebula soft nofile 65536
nebula hard nofile 65536
nebula soft nproc  4096
nebula hard nproc  4096
LIMITS

# Network optimization
cat >> /etc/sysctl.conf << 'SYSCTL'
# NEBULA Blockchain Optimization
net.core.somaxconn = 1024
net.ipv4.tcp_max_syn_backlog = 1024
net.core.netdev_max_backlog = 5000
SYSCTL

sysctl -p > /dev/null 2>&1
ok "System optimized for P2P networking"

# ================================================================
step "17 — Health Check Script"
# ================================================================
cat > /opt/nebula/nebula_health.sh << 'HEALTH'
#!/bin/bash
# NEBULA Health Check
echo "=== NEBULA Node Health ==="
echo "Node service : $(systemctl is-active nebula)"
echo "Miner service: $(systemctl is-active nebula-miner)"
echo "Disk usage   : $(du -sh /opt/nebula/data 2>/dev/null | cut -f1 || echo 'N/A')"
echo "Log size     : $(du -sh /opt/nebula/logs 2>/dev/null | cut -f1 || echo 'N/A')"
echo "Last backup  : $(ls -t /opt/nebula/backup/chain_*.json 2>/dev/null | head -1 | xargs basename 2>/dev/null || echo 'none')"
echo "Uptime       : $(uptime -p)"
echo "Memory       : $(free -h | grep Mem | awk '{print $3"/"$2}')"
echo "CPU          : $(nproc) cores"
HEALTH

chmod +x /opt/nebula/nebula_health.sh
chown nebula:nebula /opt/nebula/nebula_health.sh
ok "Health check script created: /opt/nebula/nebula_health.sh"

# ================================================================
#  FINAL SUMMARY
# ================================================================
echo ""
echo -e "${GOLD}"
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║                                                              ║"
echo "║   SETUP COMPLETE — NEBULA IS READY!                         ║"
echo "║   Author : Zayn Quantum                                      ║"
echo "║                                                              ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo -e "${NC}"

echo -e "${GREEN}START COMMANDS:${NC}"
echo "  sudo systemctl start nebula              # Start full node"
echo "  sudo systemctl start nebula-miner        # Start mining"
echo ""
echo -e "${GREEN}MONITOR COMMANDS:${NC}"
echo "  sudo systemctl status nebula             # Node status"
echo "  sudo journalctl -u nebula -f             # Live logs"
echo "  tail -f /opt/nebula/logs/nebula.log      # Log file"
echo "  /opt/nebula/nebula_health.sh             # Health check"
echo ""
echo -e "${GREEN}INTERACTIVE MODE:${NC}"
echo "  cd /opt/nebula/blockchain"
echo "  sudo -u nebula /opt/nebula/venv/bin/python3 nebula_cli.py repl"
echo ""
echo -e "${GREEN}CHECK BALANCE:${NC}"
echo "  cd /opt/nebula/blockchain"
echo "  sudo -u nebula /opt/nebula/venv/bin/python3 nebula_cli.py balance"
echo ""
echo -e "${YELLOW}YOUR MINER ADDRESS:${NC}"
echo "  $(cat /opt/nebula/config/miner_address.txt 2>/dev/null || echo 'check /opt/nebula/config/')"
echo ""
echo -e "${RED}KEEP SAFE — YOUR MNEMONIC BACKUP:${NC}"
echo "  sudo cat /opt/nebula/config/wallet_backup.txt"
echo ""
echo -e "${GOLD}NEBULA Blockchain — Zayn Quantum — For All Humanity 🌍${NC}"
echo ""

