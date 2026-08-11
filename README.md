# 🔍 Easy Fix DeadCode Auditor (EFDC)

[![Last commit](https://img.shields.io/github/last-commit/robertoabbruzzese/easyfix-deadcode)](https://github.com/robertoabbruzzese/easyfix-deadcode/commits/main)
[![Repo size](https://img.shields.io/github/repo-size/robertoabbruzzese/easyfix-deadcode)](https://github.com/robertoabbruzzese/easyfix-deadcode)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Language](https://img.shields.io/badge/Language-Python-3776AB)](https://www.python.org/)
![Version](https://img.shields.io/badge/version-v0.5-brightgreen)

<!-- Visitor counter (free) – replace the link with yours -->
![Visits](https://komarev.com/ghpvc/?username=robertoabbruzzese&repo=easyfix-deadcode&color=lightgrey)

**EFDC** is a multi‑language static analysis tool that automatically identifies **dead code** (functions, classes, methods, CSS selectors, HTML tags) within software projects.

The goal is to help developers and teams keep codebases clean, reduce technical debt, and facilitate refactoring.

---

## ✨ Key features

- Support for **12+ languages**: Python, JavaScript, TypeScript, HTML, CSS, Rust, Go, Java, PHP, Ruby, C/C++.
- **Dual parsing engine**: tree‑sitter (precise) with a regex fallback (robust).
- Import resolution (TypeScript aliases, `package.json`, `pyproject.toml`, `Cargo.toml`).
- Call graph and **BFS** from entry points to determine reachability.
- Detailed **JSON report** with a confidence level for each symbol.
- **Safe quarantine**: comments out suspicious code with a unique marker, allowing restoration via `efdc restore <id>`.
- **Strict Go mode** to avoid false positives in projects using dependency injection.

---

## 🧰 System requirements

| Component              | Minimum version        |
|------------------------|------------------------|
| Python                 | 3.8 or higher          |
| tree‑sitter core       | ≥ 0.21                 |
| tree‑sitter‑language‑pack | ≥ 0.5               |
| Operating system       | Linux, macOS, Windows  |

All Python dependencies are listed in the `requirements.txt` file (if you don't have it, you can install them manually with `pip install tree-sitter tree-sitter-language-pack`).

---

## 🚀 Installation and first use

1. **Clone the repository** (or download the files):
   ```bash
   git clone https://github.com/robertoabbruzzese/easyfix-deadcode.git
   cd easyfix-deadcode
   ```
2. Install the dependencies (recommended in a virtual environment):
   ```bash
   pip install tree-sitter tree-sitter-language-pack
   ```
3. Make the script executable (optional, on Linux/macOS):
   ```bash
   chmod +x efdc.py
   ```
4. Run an analysis on your project:
   ```bash
   python efdc.py audit ./my-project --min-confidence 80
   ```
5. View the report in the `deadcode_report.json` file generated in the current folder.

For all commands (`audit`, `apply`, `restore`), consult the full guide (attached file).

---

## 🖼️ Screenshots
<img width="1842" height="1026" alt="Immagine" src="https://github.com/user-attachments/assets/bdee1a9c-5b0b-4646-b6b8-8ddf2ff88f91" />
<img width="1842" height="1026" alt="Immagine2" src="https://github.com/user-attachments/assets/91faf6e3-2c07-4b03-951e-ab1a096479c8" />
<img width="1842" height="1026" alt="Immagine3" src="https://github.com/user-attachments/assets/3061fc52-ffd5-4e6e-a4bd-95569af9ff22" />


---

## 🤖 How it was made
This project was entirely developed in a browser, with the assistance of an artificial intelligence (language model) that helped with writing the code, documentation, and architectural design.
The goal was to demonstrate that a professional tool can be created even without a traditional development environment, by harnessing the potential of generative AI.

---

## 📄 License
This software is distributed under the Apache 2.0 License. See the `LICENSE` file for details.

---

## 👤 Author
Roberto Abbruzzese
[LinkedIn [(replace with your profile)](https://www.linkedin.com/in/roberto-abbruzzese-aa3b343b6/)
](https://www.linkedin.com/in/roberto-abbruzzese-aa3b343b6/)
---

## 🤝 Contributions
Contributions are welcome! Read the `CONTRIBUTING.md` file to learn how to report bugs or suggest improvements.
