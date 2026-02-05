# 🐺 Wolf VPN

![Project Banner](https://img.shields.io/badge/Status-prod)
[![License: CC0-1.0](https://img.shields.io/badge/License-CC0--1.0-lightgrey.svg)](http://creativecommons.org/publicdomain/zero/1.0/)
[![Go Version](https://img.shields.io/badge/Go-1.18%2B-00ADD8?logo=go&logoColor=white)](https://golang.org/doc/devel/release.html)
[![Platform](https://img.shields.io/badge/Platform-Linux%20%7C%20macOS-blue)](#requirements)

A lightweight, secure VPN tunnel implementation written in pure Go. **Wolf VPN** provides a simple way to create a Layer 3 (IP) tunnel between a server and a client without the overhead of massive configuration files.



---

## ✨ Features

- [x] **Zero Dependencies:** Built exclusively with the Go standard library.
- [x] **Lightweight:** Minimal memory footprint and binary size.
- [x] **Dual Role:** Same binary acts as both Server and Client.
- [x] **Cross-Platform:** Full support for Linux and macOS (TUN/TAP).

---

## 🛠 Installation

### System Requirements

| Requirement | Minimum Version | Note |
| :--- | :--- | :--- |
| **Go Compiler** | 1.18+ | Required for building from source |
| **OS** | Linux / macOS | Requires TUN/TAP driver support |
| **Privileges** | Root / Sudo | Needed to manage network interfaces |

### Quick Start Build

```bash
# 1. Clone the repo
git clone https://github.com/Mycoearthdome/wolf.git

# 2. Navigate to project
cd wolf

# 3. Build the binary
go build -o wolf

# 4. Verify installation
./wolf -h
```

⚙️ Usage Configuration

[!IMPORTANT] Because Wolf VPN creates and manages virtual network interfaces, you must run the application with administrative privileges (sudo).

🏗️ Server Mode

Host a VPN endpoint to accept incoming client connections.
```Bash
sudo ./wolf -l 9000 -server
```
🏎️ Client Mode

Connect to your remote Wolf VPN server.
```Bash
sudo ./wolf -l 9000 -t <SERVER_PUBLIC_IP>:9000
```
📂 Project Roadmap

    [x] Basic TUN interface management

    [x] TCP handshake and packet forwarding

    [x] Support for UDP transport

    [x] End-to-end encryption

    [x] Dynamic IP address assignment (DHCP-like)

📌 Usage Example

To simulate a local tunnel for testing:

Terminal A (Server):
```Bash
sudo ./wolf -l 9000 -server
```

Terminal B (Client):
```Bash
sudo ./wolf -l 9000 -ip [external server ip]:9000
```

Explore the Dashboard:

once launched, type in your favorite internet browser:
```Bash
localhost:8080
```

To see the world map of your VPN on the dashbord connections:

USE KEYBOARD KEY " H "

📝 License

This project is licensed under the CC0 1.0 Universal (CC0 1.0) Public Domain Dedication.

You can copy, modify, distribute, and perform the work, even for commercial purposes, all without asking permission.

Built with ❤️ by Mycoearthdome.
