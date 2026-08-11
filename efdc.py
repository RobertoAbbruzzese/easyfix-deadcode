#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright 2026 (da definire)
#
# Concesso in licenza in base alla Licenza Apache, Versione 2.0 (la "Licenza");
# è vietato utilizzare questo file se non in conformità con la Licenza.
# È possibile ottenere una copia della Licenza all'indirizzo
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Salvo diversamente previsto dalla legge applicabile o concordato per iscritto,
# il software distribuito in base alla Licenza è fornito "COSÌ COM'È",
# SENZA GARANZIE O CONDIZIONI DI ALCUN TIPO, né esplicite né implicite.
# Vedere la Licenza per la lingua specifica che regola permessi e limitazioni
# ai sensi della Licenza.

# Easy Fix DeadCode Auditor - Rilevamento automatico di codice morto multi‑linguaggio.
# Versione: v0.5
# Descrizione: analizza progetti Python, JavaScript, TypeScript, HTML, CSS e altri
#              per individuare funzioni, classi, metodi non più richiamati.
#              Supporta tree‑sitter come parser principale e fallback a espressioni regolari.

__version__ = "v0.5"

import os
import sys
import re
import json
import hashlib
import uuid
import shutil
import datetime
import argparse
import logging
import logging.handlers
import tempfile
import platform
import ast
import time
import difflib
import fnmatch
import threading
import subprocess
import traceback
from concurrent.futures import ProcessPoolExecutor, as_completed
from collections import deque, defaultdict
from pathlib import Path

# =============================================================================
# Funzioni di utilità per la compatibilità con tree‑sitter
# =============================================================================

def _get_node_children_safe(node):
    """Restituisce i figli del nodo tree‑sitter in modo sicuro per diverse versioni."""
    if not hasattr(node, 'children'):
        if hasattr(node, 'named_children'):
            named = node.named_children
            if callable(named):
                named = named()
            if hasattr(named, '__iter__') and not isinstance(named, list):
                named = list(named)
            return named
        if hasattr(node, 'child_count'):
            risultato = []
            for i in range(node.child_count):
                if hasattr(node, 'child'):
                    figlio = node.child(i)
                    if figlio is not None:
                        risultato.append(figlio)
            return risultato
        return []
    figli = node.children
    if callable(figli):
        figli = figli()
    if hasattr(figli, '__iter__') and not isinstance(figli, list):
        figli = list(figli)
    return figli

def _get_node_type_safe(node, language=None, cursor=None):
    """Ottiene il tipo di un nodo tree‑sitter, con fallback per API più vecchie."""
    if hasattr(node, 'type'):
        tipo_nodo = node.type
        if callable(tipo_nodo):
            tipo_nodo = tipo_nodo()
        if tipo_nodo is not None and str(tipo_nodo) not in ('', 'None'):
            return str(tipo_nodo)
    if language is not None and hasattr(node, 'kind_id'):
        try:
            kind_id = node.kind_id
            if callable(kind_id):
                kind_id = kind_id()
            nome = language.node_kind_for_id(kind_id)
            if nome:
                return nome
        except Exception:
            pass
    if hasattr(node, 'kind_id'):
        return f"node_{node.kind_id}"
    if hasattr(node, 'grammar_name'):
        grammatica = node.grammar_name
        if callable(grammatica):
            grammatica = grammatica()
        return str(grammatica) if grammatica is not None else "unknown"
    return "unknown"

def _get_node_text_safe(node, raw_bytes):
    """Restituisce sempre una stringa, gestendo sia bytes che str."""
    if raw_bytes is not None and not isinstance(raw_bytes, (bytes, bytearray, str)):
        print(f"[LOG _get_node_text_safe] ATTENZIONE: raw_bytes tipo inaspettato: {type(raw_bytes).__name__}")
    if hasattr(node, 'text'):
        testo = node.text
        if callable(testo):
            testo = testo()
        if testo is not None:
            if isinstance(testo, bytes):
                return testo.decode('utf-8', errors='replace')
            return str(testo)
    if raw_bytes is not None and hasattr(node, 'start_byte') and hasattr(node, 'end_byte'):
        inizio = node.start_byte
        fine = node.end_byte
        if callable(inizio):
            inizio = inizio()
        if callable(fine):
            fine = fine()
        if not isinstance(raw_bytes, (bytes, bytearray)):
            if isinstance(raw_bytes, str):
                raw_bytes = raw_bytes.encode('utf-8')
            else:
                try:
                    raw_bytes = bytes(raw_bytes)
                except Exception:
                    return ''
        try:
            if isinstance(raw_bytes, bytes):
                return raw_bytes[inizio:fine].decode('utf-8', errors='replace')
            elif isinstance(raw_bytes, bytearray):
                return bytes(raw_bytes[inizio:fine]).decode('utf-8', errors='replace')
            else:
                return ''
        except Exception:
            return ''
    return ''

def _get_node_start_byte_safe(node):
    if hasattr(node, 'start_byte'):
        val = node.start_byte
        if callable(val):
            val = val()
        return val
    return 0

def _get_node_end_byte_safe(node):
    if hasattr(node, 'end_byte'):
        val = node.end_byte
        if callable(val):
            val = val()
        return val
    return 0

def _get_node_child_by_field_name_safe(node, field_name):
    if node is None:
        return None
    if not hasattr(node, 'child_by_field_name'):
        return None
    try:
        child = node.child_by_field_name(field_name)
        if callable(child):
            return None
        return child
    except Exception:
        return None

def _parse_version(ver_str):
    parti = re.split(r'[.\-+]', ver_str)
    numeriche = []
    for p in parti:
        try:
            numeriche.append(int(p))
        except ValueError:
            break
    while len(numeriche) < 2:
        numeriche.append(0)
    return tuple(numeriche)

# =============================================================================
# Adattatore tree‑sitter cross‑versione – gestione di bytes e TreeCursor
# =============================================================================

def _crea_cursore(nodo):
    """Restituisce un TreeCursor compatibile con tree‑sitter ≥0.21 e versioni precedenti."""
    if nodo is None:
        return None
    if hasattr(nodo, 'walk'):
        return nodo.walk()
    try:
        from tree_sitter import TreeCursor
        return TreeCursor(nodo)
    except (ImportError, TypeError):
        return None

def _parse_sorgente(parser, sorgente_bytes):
    """
    Chiama parser.parse() usando bytes, come richiesto da tree‑sitter ≥0.22.
    Restituisce (albero, radice) oppure (None, None) in caso di errore.
    """
    if not isinstance(sorgente_bytes, (bytes, bytearray)):
        print(f"[LOG _parse_sorgente] ATTENZIONE: sorgente_bytes non è bytes/bytearray, è {type(sorgente_bytes).__name__}. Converto.")
        if isinstance(sorgente_bytes, str):
            sorgente_bytes = sorgente_bytes.encode('utf-8')
        else:
            try:
                sorgente_bytes = bytes(sorgente_bytes)
            except Exception as e:
                print(f"[LOG _parse_sorgente] Impossibile convertire: {e}")
                return None, None
    else:
        print(f"[LOG _parse_sorgente] sorgente_bytes è {type(sorgente_bytes).__name__}, lunghezza {len(sorgente_bytes)}")

    try:
        albero = parser.parse(sorgente_bytes)
    except Exception as e:
        print(f"[LOG _parse_sorgente] parser.parse ha sollevato eccezione: {e}")
        return None, None

    if albero is None:
        print("[LOG _parse_sorgente] parser.parse ha restituito None")
        return None, None

    try:
        nodo_radice = albero.root_node
    except AttributeError:
        print("[LOG _parse_sorgente] albero non ha root_node")
        return None, None

    print("[LOG _parse_sorgente] parsing completato con successo")
    return albero, nodo_radice

# =============================================================================
# Caricamento delle grammatiche tree‑sitter e verifica compatibilità
# =============================================================================
try:
    import tree_sitter_language_pack as tree_sitter_languages
except ImportError:
    print("[ERRORE] tree-sitter-language-pack non è installato. "
          "Installa con: pip install tree-sitter-language-pack>=1.0.0,<2.0.0")
    sys.exit(2)

from tree_sitter import Language, Parser, TreeCursor

def _verifica_compatibilita_dipendenze():
    try:
        from importlib.metadata import version as get_version
        versione_ts_core = get_version('tree-sitter')
        versione_ts_pack = get_version('tree-sitter-language-pack')
        print(f"[LOG] tree-sitter core versione: {versione_ts_core}")
        print(f"[LOG] tree-sitter-language-pack versione: {versione_ts_pack}")
    except Exception as e:
        print(f"[LOG] Impossibile ottenere versioni: {e}")
        return
    tupla_core = _parse_version(versione_ts_core)
    tupla_pack = _parse_version(versione_ts_pack)
    avvisi = []
    if tupla_core < (0, 21):
        avvisi.append(f"tree-sitter {versione_ts_core} obsoleto. È richiesta versione >=0.21. "
                      "TreeCursor non può essere istanziato direttamente; usare node.walk().")
    elif not ((0, 21) <= tupla_core < (0, 28)):
        avvisi.append(f"Versione tree‑sitter {versione_ts_core} non testata (intervallo consigliato: 0.21–0.27).")
    if not ((0, 5) <= tupla_pack < (2, 0)):
        avvisi.append(f"Versione tree‑sitter‑language‑pack {versione_ts_pack} non testata (intervallo consigliato: 0.5–1.x).")
    if avvisi:
        print("[AVVISO] Compatibilità dipendenze:")
        for a in avvisi:
            print("   ", a)
        print("   Lo script tenterà comunque di funzionare, ma potrebbero verificarsi errori di parsing.\n")

_verifica_compatibilita_dipendenze()

PARSER_TREE_SITTER = {}
MAPPA_LINGUAGGI_TS = {
    'python': 'python',
    'javascript': 'javascript',
    'typescript': 'typescript',
    'tsx': 'tsx',
    'rust': 'rust',
    'go': 'go',
    'ruby': 'ruby',
    'java': 'java',
    'php': 'php',
    'c_cpp': 'c',
    'html': 'html',
    'css': 'css',
}
_avvisi_caricamento_ts = []
for chiave_lingua, nome_lingua_ts in MAPPA_LINGUAGGI_TS.items():
    try:
        lingua_ts = tree_sitter_languages.get_language(nome_lingua_ts)
        parser_ts = tree_sitter_languages.get_parser(nome_lingua_ts)
        PARSER_TREE_SITTER[chiave_lingua] = (lingua_ts, parser_ts)
        print(f"[OK] Caricato parser per {nome_lingua_ts}")
    except Exception as e:
        import traceback
        print(f"[ERRORE] Parser per {nome_lingua_ts}:")
        traceback.print_exc()
        _avvisi_caricamento_ts.append(f"[AVVISO] Parser tree‑sitter non disponibile per {nome_lingua_ts}: {e}")

if not PARSER_TREE_SITTER:
    print("[ERRORE] Nessun parser tree‑sitter caricato. Impossibile proseguire.")
    sys.exit(2)

# =============================================================================
# Impostazioni globali
# =============================================================================

DIRECTORY_IGNORATE = {
    '.git', 'node_modules', 'venv', '__pycache__', '.idea', '.vscode',
    'dist', 'build', 'vendor', 'target', '.env', 'bower_components',
    '__deadcode_quarantine__'
}

NOMI_GENERICI = {
    'run', 'main', 'init', 'handle', 'start', 'stop', 'test', 'setup',
    'teardown', 'index', 'app', 'config', 'default', 'update', 'delete', 'create'
}

# Nuovo: pattern di funzioni che in Go (e potenzialmente altri linguaggi) sono
# tipicamente usate per registrare dipendenze senza eseguirne i metodi.
# Quando la modalità strict per Go è attiva, le chiamate interne a queste
# funzioni non vengono propagate ulteriormente.
GO_REGISTRATION_PATTERNS = {'Register', 'Add', 'Provide', 'HandleFunc', 'Handle', 'Use', 'Init'}

PATTERN_CHIAMATE_DINAMICHE = [
    'getattr', 'setattr', 'eval', 'exec', '__getattribute__',
    'call_user_func', 'Reflection', 'invoke', 'send', '__call', 'apply', 'bind'
]

MARCATORI_DEPRECATI = [
    r'DEPRECATED', r'TODO:\s*remove', r'FIXME:\s*delete',
    r'@deprecated', r'REMOVE_ME', r'OBSOLETE'
]

PATTERN_FILE_ESCLUSI = [
    '*.pb.py', '*_grpc.py', '*.min.js', '*.min.css', '*.pb.go', '*.pb.cc', '*.pb.h',
    '*.log', '*.lock', '*.ini', 'desktop.ini', 'thumbs.db'
]

LISTA_NERA_PAROLE_CHIAVE = {
    'False', 'None', 'True', 'and', 'as', 'assert', 'async', 'await', 'break',
    'class', 'continue', 'def', 'del', 'elif', 'else', 'except', 'finally',
    'for', 'from', 'global', 'if', 'import', 'in', 'is', 'lambda', 'nonlocal',
    'not', 'or', 'pass', 'raise', 'return', 'try', 'while', 'with', 'yield',
    'break', 'case', 'catch', 'class', 'const', 'continue', 'debugger', 'default',
    'delete', 'do', 'else', 'export', 'extends', 'finally', 'for', 'function',
    'if', 'import', 'in', 'instanceof', 'let', 'new', 'return', 'super',
    'switch', 'this', 'throw', 'try', 'typeof', 'var', 'void', 'while', 'with',
    'yield', 'enum', 'implements', 'interface', 'package', 'private', 'protected',
    'public', 'static',
    'auto', 'break', 'case', 'char', 'const', 'continue', 'default', 'do',
    'double', 'else', 'enum', 'extern', 'float', 'for', 'goto', 'if', 'int',
    'long', 'register', 'return', 'short', 'signed', 'sizeof', 'static',
    'struct', 'switch', 'typedef', 'union', 'unsigned', 'void', 'volatile',
    'while',
    'abstract', 'assert', 'boolean', 'break', 'byte', 'case', 'catch', 'char',
    'class', 'const', 'continue', 'default', 'do', 'double', 'else', 'enum',
    'extends', 'final', 'finally', 'float', 'for', 'goto', 'if', 'implements',
    'import', 'instanceof', 'int', 'interface', 'long', 'native', 'new',
    'package', 'private', 'protected', 'public', 'return', 'short', 'static',
    'strictfp', 'super', 'switch', 'synchronized', 'this', 'throw', 'throws',
    'transient', 'try', 'void', 'volatile', 'while',
    'BEGIN', 'END', 'alias', 'and', 'begin', 'break', 'case', 'class', 'def',
    'defined?', 'do', 'else', 'elsif', 'end', 'ensure', 'false', 'for', 'if',
    'in', 'module', 'next', 'nil', 'not', 'or', 'redo', 'rescue', 'retry',
    'return', 'self', 'super', 'then', 'true', 'undef', 'unless', 'until',
    'when', 'while', 'yield',
    '__halt_compiler', 'abstract', 'and', 'array', 'as', 'break', 'callable',
    'case', 'catch', 'class', 'clone', 'const', 'continue', 'declare', 'default',
    'die', 'do', 'echo', 'else', 'elseif', 'empty', 'enddeclare', 'endfor',
    'endforeach', 'endif', 'endswitch', 'endwhile', 'eval', 'exit', 'extends',
    'final', 'finally', 'for', 'foreach', 'function', 'global', 'goto', 'if',
    'implements', 'include', 'instanceof', 'insteadof', 'interface', 'isset',
    'list', 'namespace', 'new', 'or', 'print', 'private', 'protected', 'public',
    'require', 'return', 'static', 'switch', 'throw', 'trait', 'try', 'unset',
    'use', 'var', 'while', 'xor', 'yield',
    'break', 'case', 'chan', 'const', 'continue', 'default', 'defer', 'else',
    'fallthrough', 'for', 'func', 'go', 'goto', 'if', 'import', 'interface',
    'map', 'package', 'range', 'return', 'select', 'struct', 'switch', 'type',
    'var',
    'as', 'break', 'const', 'continue', 'crate', 'else', 'enum', 'extern',
    'false', 'fn', 'for', 'if', 'impl', 'in', 'let', 'loop', 'match', 'mod',
    'move', 'mut', 'pub', 'ref', 'return', 'self', 'Self', 'static', 'struct',
    'super', 'trait', 'true', 'type', 'unsafe', 'use', 'where', 'while',
}
NOMI_CORTI_CONSENTITI = {'fs', 'os', 'io', 'db', 'id'}

REGISTRO_CALLBACK = {
    'python': [
        r'@app\.route\(', r'@app\.get\(', r'@app\.post\(', r'@app\.put\(', r'@app\.delete\(', r'@app\.patch\(',
        r'@router\.get\(', r'@router\.post\(', r'@router\.put\(', r'@router\.delete\(', r'@router\.patch\(',
        r'APIRouter\(\)\.add_api_route\(', r'\.add_api_route\(', r'@pytest\.fixture', r'@pytest\.mark\.',
        r'@mock\.patch\(', r'@hypothesis\.given\(', r'@unittest\.mock\.patch\(', r'@celery\.task', r'@task\(',
        r'register\(', r'\.on\(', r'\.add_handler\(', r'set_\w+\(', r'register_\w+\(', r'\.subscribe\(',
        r'\.on_event\(', r'@app\.on_event\(', r'@router\.on_event\(', r'@event_handler\(', r'@app\.\w+\(', r'@router\.\w+\(',
        r'@event\.listens_for\(', r'@csrf_exempt', r'@login_required', r'@permission_required', r'@bp\.route\(',
        r'@before_request', r'@after_request', r'@orm\.reconstructor', r'@app\.websocket\(', r'@app\.middleware\(',
        r'@app\.exception_handler\(', r'@click\.command', r'@click\.group', r'parser\.add_command\(', r'@app\.command',
        r'@click\.argument\(', r'@click\.option\(', r'\.connect\(', r'\.add_listener\(', r'\.emit\(', r'@receiver\(',
        r'@django\.dispatch\.receiver\(', r'signals\.\w+\.connect\(', r'add_event_listener\(', r'\.add_event_listener\(',
    ],
    'javascript': [
        r'app\.get\(', r'app\.post\(', r'app\.put\(', r'app\.delete\(', r'router\.get\(', r'router\.post\(',
        r'\.use\(', r'\.on\(', r'\.addEventListener\(', r'describe\(', r'it\(', r'test\(', r'beforeEach\(', r'afterEach\(',
        r'\.subscribe\(', r'set\w+\(', r'register\w+\(', r'\.on\w+\(', r'useEffect\(', r'useState\(', r'useCallback\(',
        r'useMemo\(', r'useRef\(', r'useContext\(', r'useReducer\(', r'setTimeout\(', r'setInterval\(', r'\.then\(',
        r'\.catch\(', r'\.finally\(', r'process\.on\(', r'new Promise\(', r'promisify\(', r'\.emit\(', r'\.addEventListener\(',
    ],
    'typescript': [
        r'app\.get\(', r'app\.post\(', r'app\.put\(', r'app\.delete\(', r'router\.get\(', r'router\.post\(',
        r'\.use\(', r'\.on\(', r'\.addEventListener\(', r'describe\(', r'it\(', r'test\(', r'beforeEach\(', r'afterEach\(',
        r'\.subscribe\(', r'set\w+\(', r'register\w+\(', r'\.on\w+\(', r'@Component', r'@Injectable', r'@NgModule',
        r'@Controller', r'@Module', r'@Controller\(', r'@Get\(', r'@Post\(', r'@Put\(', r'@Delete\(', r'@Patch\(',
        r'@Options\(', r'@Head\(', r'@All\(', r'@HttpCode\(', r'@Redirect\(', r'@Header\(', r'@UseGuards\(',
        r'@UseInterceptors\(', r'@UsePipes\(', r'@UseFilters\(', r'@Inject\(', r'@Injectable\(', r'@Catch\(',
        r'@Module\(', r'@Global\(', r'@Param\(', r'@Body\(', r'@Query\(', r'@Req\(', r'@Res\(', r'@Entity\(',
        r'@Column\(', r'@PrimaryGeneratedColumn\(', r'@ManyToOne\(', r'@OneToMany\(', r'@JoinColumn\(',
        r'setTimeout\(', r'setInterval\(', r'\.then\(', r'\.catch\(', r'\.finally\(', r'process\.on\(', r'new Promise\(',
        r'promisify\(', r'\.emit\(',
    ],
    'rust': [
        r'#\[test\]', r'#\[tokio::test\]', r'#\[actix_rt::test\]', r'#\[actix_web::test\]', r'#\[cfg\(test\)\]',
    ],
    'go': [
        r'func Test\w+\(', r'func Benchmark\w+\(', r'\.Handle\(', r'\.HandleFunc\(',
    ],
    'java': [
        r'@Test', r'@Before', r'@After', r'@EventListener', r'@Subscribe', r'\.addListener\(', r'\.register\w+\(',
        r'set\w+Listener\(', r'@Bean', r'@Autowired', r'@Component', r'@Service', r'@Repository', r'@Controller',
        r'@RequestMapping', r'@GetMapping', r'@PostMapping', r'@PutMapping', r'@Scheduled', r'@Async',
    ],
    'php': [
        r'->on\(', r'->addListener\(', r'->subscribe\(', r'@Route\(', r'function test\w+\(', r'function setUp\(',
        r'#\[Route\(', r'#\[EventListener\(', r'#\[AsCommand\(', r'Route::(get|post|put|delete|patch)\(',
    ],
    'ruby': [
        r'\.on\(', r'\.subscribe\(', r'get\s+[\'"]/[^"\']+[\'"]\s+do', r'post\s+[\'"]/[^"\']+[\'"]\s+do',
        r'describe\s+[\'"]', r'before_action\s+:', r'skip_before_action\s+:', r'after_action\s+:', r'rescue_from\s+:',
        r'helper_method\s+:', r'validates\s+:', r'belongs_to\s+:', r'has_many\s+:',
    ],
    'c_cpp': [
        r'QObject::connect\(', r'\.connect\(', r'signal\w+\(', r'\.on\w+\(', r'addEventListener\(',
    ],
}

PATTERN_FILE_TEST = [
    'test_*.py', '*_test.py', 'test_*.js', '*.test.js', '*.spec.js',
    '*_test.go', 'test_*.rs', '*_test.rs', 'test_*.rb', '*_spec.rb',
    'Test*.java', '*Test.java', '*.test.ts', '*.spec.ts', 'test_*.ts',
    '*_test.cpp', 'test_*.cpp', '*Test.php', 'test_*.php',
    '*/migrations/*.py', '*/migrations/*.js', '*/migrations/*.ts',
    '*/scripts/*.py', '*/scripts/*.sh', '*/scripts/*.js',
    '*/templates/*.html', '*/templates/*.jinja', '*/templates/*.j2',
    '*/fixtures/*.json', '*/fixtures/*.yaml', '*/fixtures/*.py',
    '*/build/*.js', '*/dist/*.js',
    '*.spec.js', '*.test.jsx', '*.test.tsx',
]

_MODULI_STDLIB_PRINCIPALI = set(sys.stdlib_module_names)
_MODULI_STDLIB_PRINCIPALI.update({
    'importlib', 'concurrent', 'asyncio', 'xml', 'html', 'http', 'urllib',
    'wsgiref', 'json', 'unittest', 'logging', 'collections', 'distutils',
    'ctypes', 'curses', 'dbm', 'decimal', 'email', 'encodings', 'formatter',
    'fractions', 'ftplib', 'functools', 'getpass', 'gettext', 'glob',
    'hashlib', 'heapq', 'hmac', 'imaplib', 'inspect', 'io', 'ipaddress',
    'itertools', 'json', 'keyword', 'lib2to3', 'linecache', 'locale',
    'lzma', 'mailbox', 'mailcap', 'marshal', 'math', 'mimetypes',
    'mmap', 'multiprocessing', 'netrc', 'nntplib', 'numbers', 'operator',
    'optparse', 'os', 'ossaudiodev', 'pathlib', 'pdb', 'pickle',
    'pickletools', 'pipes', 'pkgutil', 'platform', 'plistlib', 'poplib',
    'posix', 'pprint', 'profile', 'pstats', 'pty', 'pwd', 'py_compile',
    'pyclbr', 'pydoc', 'queue', 'quopri', 'random', 're', 'readline',
    'reprlib', 'resource', 'rlcompleter', 'runpy', 'sched', 'secrets',
    'select', 'selectors', 'shelve', 'shlex', 'shutil', 'signal',
    'site', 'smtpd', 'smtplib', 'sndhdr', 'socket', 'socketserver',
    'spwd', 'sqlite3', 'ssl', 'stat', 'statistics', 'string', 'stringprep',
    'struct', 'subprocess', 'sunau', 'symtable', 'sys', 'sysconfig',
    'syslog', 'tabnanny', 'tarfile', 'telnetlib', 'tempfile', 'termios',
    'test', 'textwrap', 'threading', 'time', 'timeit', 'tkinter', 'token',
    'tokenize', 'trace', 'traceback', 'tracemalloc', 'tty', 'turtle',
    'turtledemo', 'types', 'typing', 'unicodedata', 'unittest', 'urllib',
    'uu', 'uuid', 'venv', 'warnings', 'wave', 'weakref', 'webbrowser',
    'winreg', 'winsound', 'wsgiref', 'xdrlib', 'xml', 'xmlrpc', 'zipapp',
    'zipfile', 'zipimport', 'zlib',
})

REGISTRO_LINGUAGGI = {
    'python': {
        'ext': ['.py'],
        'tipo_blocco': 'indent',
        'sintassi_commento': ('#', ''),
        'commento_linea': '#',
        'commento_blocco': None,
        'pattern_pulizia': ['#'],
        'accuratezza': 95,
    },
    'javascript': {
        'ext': ['.js', '.jsx', '.mjs', '.cjs'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('//', ''),
        'commento_linea': '//',
        'commento_blocco': ('/*', '*/'),
        'pattern_pulizia': ['//', '/*'],
        'accuratezza': 90,
    },
    'typescript': {
        'ext': ['.ts', '.tsx', '.d.ts'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('//', ''),
        'commento_linea': '//',
        'commento_blocco': ('/*', '*/'),
        'pattern_pulizia': ['//', '/*'],
        'accuratezza': 90,
    },
    'php': {
        'ext': ['.php'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('//', ''),
        'commento_linea': '//',
        'commento_blocco': ('/*', '*/'),
        'pattern_pulizia': ['//', '/*', '#'],
        'accuratezza': 85,
    },
    'java': {
        'ext': ['.java'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('//', ''),
        'commento_linea': '//',
        'commento_blocco': ('/*', '*/'),
        'pattern_pulizia': ['//', '/*'],
        'accuratezza': 85,
    },
    'c_cpp': {
        'ext': ['.c', '.cpp', '.h', '.hpp', '.cc'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('//', ''),
        'commento_linea': '//',
        'commento_blocco': ('/*', '*/'),
        'pattern_pulizia': ['//', '/*'],
        'accuratezza': 85,
    },
    'rust': {
        'ext': ['.rs'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('//', ''),
        'commento_linea': '//',
        'commento_blocco': ('/*', '*/'),
        'pattern_pulizia': ['//', '/*'],
        'accuratezza': 85,
    },
    'go': {
        'ext': ['.go'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('//', ''),
        'commento_linea': '//',
        'commento_blocco': ('/*', '*/'),
        'pattern_pulizia': ['//', '/*'],
        'accuratezza': 85,
    },
    'ruby': {
        'ext': ['.rb'],
        'tipo_blocco': 'end',
        'sintassi_commento': ('#', ''),
        'commento_linea': '#',
        'commento_blocco': ('=begin', '=end'),
        'pattern_pulizia': ['#', '=begin'],
        'accuratezza': 85,
    },
    'html': {
        'ext': ['.html', '.htm'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('<!--', '-->'),
        'commento_linea': None,
        'commento_blocco': ('<!--', '-->'),
        'pattern_pulizia': ['<!--'],
        'accuratezza': 85,
    },
    'css': {
        'ext': ['.css', '.scss', '.less'],
        'tipo_blocco': 'brace',
        'sintassi_commento': ('/*', '*/'),
        'commento_linea': None,
        'commento_blocco': ('/*', '*/'),
        'pattern_pulizia': ['/*'],
        'accuratezza': 70,
    }
}

# =============================================================================
# Pre‑elaborazione del testo (pulizia commenti e stringhe per il grep)
# =============================================================================

def _dimensione_file(percorso):
    try:
        return os.path.getsize(percorso)
    except OSError:
        return 0

def pulisci_per_grep(contenuto_o_percorso, estensione, linguaggio=None):
    if isinstance(contenuto_o_percorso, str) and os.path.isfile(contenuto_o_percorso):
        percorso_file = contenuto_o_percorso
        blocchi = []
        with open(percorso_file, 'r', encoding='utf-8', errors='replace') as fh:
            for blocco in iter(lambda: fh.read(65536), ''):
                blocchi.append(_pulisci_blocco(blocco, estensione, linguaggio))
        return ''.join(blocchi)
    return _pulisci_blocco(contenuto_o_percorso, estensione, linguaggio)

def _pulisci_blocco(contenuto, estensione, linguaggio=None):
    if linguaggio is None:
        linguaggio = next((l for l, d in REGISTRO_LINGUAGGI.items() if estensione in d['ext']), None)
    if linguaggio is None:
        return contenuto
    info = REGISTRO_LINGUAGGI[linguaggio]
    caratteri = list(contenuto)
    n = len(caratteri)
    i = 0
    commento_linea = info.get('commento_linea')
    commento_blocco = info.get('commento_blocco')
    while i < n:
        if caratteri[i] == '\\' and i + 1 < n and caratteri[i+1] == '\n':
            i += 2
            continue
        if commento_blocco and i + len(commento_blocco[0]) <= n and \
           ''.join(caratteri[i:i+len(commento_blocco[0])]) == commento_blocco[0]:
            marcatore_inizio = commento_blocco[0]
            marcatore_fine = commento_blocco[1]
            for j in range(i, i+len(marcatore_inizio)):
                caratteri[j] = ' '
            i += len(marcatore_inizio)
            while i < n:
                if i + len(marcatore_fine) <= n and ''.join(caratteri[i:i+len(marcatore_fine)]) == marcatore_fine:
                    for j in range(i, i+len(marcatore_fine)):
                        caratteri[j] = ' '
                    i += len(marcatore_fine)
                    break
                if caratteri[i] != '\n':
                    caratteri[i] = ' '
                i += 1
            continue
        if commento_linea and i + len(commento_linea) <= n and \
           ''.join(caratteri[i:i+len(commento_linea)]) == commento_linea:
            while i < n and caratteri[i] != '\n':
                caratteri[i] = ' '
                i += 1
            continue
        if caratteri[i] in ('"', "'") or (caratteri[i] == '`' and linguaggio in ('javascript', 'typescript')):
            virgolette = caratteri[i]
            caratteri[i] = ' '
            i += 1
            while i < n:
                if caratteri[i] == '\\':
                    caratteri[i] = ' '
                    if i + 1 < n:
                        caratteri[i+1] = ' '
                    i += 2
                    continue
                if virgolette == '`' and i + 1 < n and caratteri[i] == '$' and caratteri[i+1] == '{':
                    caratteri[i], caratteri[i+1] = ' ', ' '
                    i += 2
                    profondita_graffe = 1
                    while i < n and profondita_graffe > 0:
                        if caratteri[i] == '{':
                            profondita_graffe += 1
                        elif caratteri[i] == '}':
                            profondita_graffe -= 1
                        if profondita_graffe > 0:
                            caratteri[i] = ' '
                        i += 1
                    continue
                if caratteri[i] == virgolette:
                    caratteri[i] = ' '
                    i += 1
                    break
                if caratteri[i] != '\n':
                    caratteri[i] = ' '
                i += 1
            continue
        i += 1
    return ''.join(caratteri)

def _rimuovi_commenti_per_regex(contenuto, linguaggio):
    """Rimuove i commenti dal codice prima di applicare le espressioni regolari."""
    info = REGISTRO_LINGUAGGI.get(linguaggio)
    if not info:
        return contenuto
    caratteri = list(contenuto)
    n = len(caratteri)
    i = 0
    commento_linea = info.get('commento_linea')
    commento_blocco = info.get('commento_blocco')
    while i < n:
        if caratteri[i] == '\\' and i + 1 < n and caratteri[i+1] == '\n':
            i += 2
            continue
        if commento_blocco and i + len(commento_blocco[0]) <= n and \
           ''.join(caratteri[i:i+len(commento_blocco[0])]) == commento_blocco[0]:
            marcatore_inizio = commento_blocco[0]
            marcatore_fine = commento_blocco[1]
            for j in range(i, i+len(marcatore_inizio)):
                caratteri[j] = ' '
            i += len(marcatore_inizio)
            while i < n:
                if i + len(marcatore_fine) <= n and ''.join(caratteri[i:i+len(marcatore_fine)]) == marcatore_fine:
                    for j in range(i, i+len(marcatore_fine)):
                        caratteri[j] = ' '
                    i += len(marcatore_fine)
                    break
                if caratteri[i] != '\n':
                    caratteri[i] = ' '
                i += 1
            continue
        if commento_linea and i + len(commento_linea) <= n and \
           ''.join(caratteri[i:i+len(commento_linea)]) == commento_linea:
            while i < n and caratteri[i] != '\n':
                caratteri[i] = ' '
                i += 1
            continue
        i += 1
    return ''.join(caratteri)

def _analizza_file_singolo_lavoratore(percorso):
    """Funzione eseguita nei processi paralleli per leggere un file."""
    estensione = os.path.splitext(percorso)[1]
    linguaggio = next((l for l, d in REGISTRO_LINGUAGGI.items() if estensione in d['ext']), None)
    if linguaggio is None:
        return None
    try:
        with open(percorso, 'rb') as f:
            byte_grezzi = f.read()
        testo = None
        for codifica in ('utf-8', 'utf-16', 'latin-1'):
            try:
                testo = byte_grezzi.decode(codifica)
                if testo is not None:
                    break
            except (UnicodeDecodeError, UnicodeError):
                continue
        if testo is None:
            return None
        byte_utf8 = testo.encode('utf-8')
    except Exception:
        return None
    return percorso, byte_utf8, testo, linguaggio

# =============================================================================
# Cache per i risultati dell'analisi AST (evita di rianalizzare file invariati)
# =============================================================================

class CacheAST:
    def __init__(self):
        self._cache = {}

    def ottieni(self, percorso, hash_corrente):
        voce = self._cache.get(percorso)
        if voce and voce['hash'] == hash_corrente and voce['versione'] == __version__:
            return voce['simboli'], voce.get('mappa_import', {}), voce.get('chiamate_membro', [])
        return None, None, None

    def imposta(self, percorso, hash_file, simboli, mappa_import=None, chiamate_membro=None):
        self._cache[percorso] = {
            'hash': hash_file,
            'versione': __version__,
            'simboli': simboli,
            'mappa_import': mappa_import if mappa_import else {},
            'chiamate_membro': chiamate_membro if chiamate_membro else []
        }

    def invalida(self, percorso):
        self._cache.pop(percorso, None)

    def distruggi(self):
        self._cache.clear()

    def chiudi(self):
        self.distruggi()

# =============================================================================
# Classe principale: DeadCodeAuditor
# =============================================================================

class DeadCodeAuditor:
    def __init__(self, directory_radice, confidenza_minima=70, forza_regex=False,
                 includi_solo_test=False, go_strict=None):
        self.directory_radice = self._normalizza_percorso(directory_radice)
        self.confidenza_minima = confidenza_minima
        self.forza_regex = forza_regex
        self.includi_solo_test = includi_solo_test
        # La modalità strict per Go può essere forzata (True/False) o decisa automaticamente
        self._go_strict_override = go_strict  # None = auto
        self.go_strict = go_strict if go_strict is not None else False  # sarà impostato dopo discovery
        self.directory_quarantena = os.path.join(self.directory_radice, '__deadcode_quarantine__')
        self.percorso_manifest = os.path.join(self.directory_quarantena, 'manifest.json')

        self._fallback_utilizzato = False
        self._diario_manifest = []

        os.makedirs(self.directory_quarantena, exist_ok=True)

        self.logger = logging.getLogger("EFDC")
        self.logger.setLevel(logging.INFO)
        self.logger.handlers.clear()
        gestore_console = logging.StreamHandler(sys.stdout)
        gestore_console.setFormatter(logging.Formatter('[%(levelname)s] %(message)s'))
        self.logger.addHandler(gestore_console)
        self._debug_handler_file = None

        self.lista_nera_personalizzata = set()
        self.nomi_generici_personalizzati = set()

        self.lista_bianca = set()
        self.pattern_lista_bianca = []
        self.regex_lista_bianca = []

        self.punti_ingresso_espliciti = set()
        file_auto_ep = os.path.join(self.directory_radice, '.efdc_entrypoints')
        if self._file_esiste_sicuro(file_auto_ep):
            self._carica_punti_ingresso(file_auto_ep)

        self.registro_callback = REGISTRO_CALLBACK.copy()

        self.mappa_import_statici = {}

        self.simboli_esaminati = set()
        self.moduli_approvati = set()

        self._hash_file = {}

        self.tutti_i_file = set()
        self.punti_ingresso = set()
        self.simboli = {}
        self.mappa_import = defaultdict(dict)
        self.mappa_import_strutturata = defaultdict(dict)
        self.chiamate_file = defaultdict(set)
        self.chiamate_membro_file = defaultdict(set)
        self.simboli_raggiungibili = set()  # ora conterrà solo sid univoci
        self.moduli_orfani = set()
        self.simboli_deprecati = {}
        self.avvisi = []
        self.import_incerti = []
        self.import_non_risolti = []
        self.falsi_positivi = []

        self._cache_testo = {}
        self._cache_pulizia = {}
        self._indice_grep = defaultdict(list)
        self._byte_a_linea = {}

        self.cache_ast = CacheAST()

        self.tempi = {}

        self.alias_tsconfig = {}
        self._carica_tsconfig()
        self._carica_pyproject_toml()
        self._carica_package_json()
        self._carica_cargo_toml()

        self.file_non_analizzabili = set()
        self._percorso_log_non_analizzabili = os.path.join(self.directory_quarantena, '.file_non_analizzabili.log')

        self._carica_diario_manifest()

        self.metodi_classe = defaultdict(set)
        self.mappa_override_metodi = defaultdict(set)
        self.emettitori_eventi = defaultdict(set)
        self.ascoltatori_eventi = defaultdict(set)
        self.esportazioni_barrel = defaultdict(dict)
        self.simboli_incerti = set()
        self._barrel_risolti = {}

        self._linee_ignorate = defaultdict(set)

        self._simboli_ts_estratti = 0
        self._file_ts_elaborati = 0
        self._tipi_ts_dumpati = False

        self._registro_eventi_python = defaultdict(set)

        self._tipi_nodo_dinamici = {}
        for chiave_lingua, (lingua_ts, _) in PARSER_TREE_SITTER.items():
            try:
                tipi = set()
                for i in range(lingua_ts.node_kind_count):
                    nome = lingua_ts.node_kind_for_id(i)
                    if nome:
                        tipi.add(nome)
                self._tipi_nodo_dinamici[chiave_lingua] = tipi
            except AttributeError:
                pass

        self._EXPECTED_TYPES_FALLBACK = {
            'python': {'function_definition', 'class_definition'},
            'javascript': {'function_declaration', 'class_declaration', 'method_definition',
                           'variable_declarator', 'arrow_function', 'function_expression',
                           'import_statement', 'lexical_declaration', 'variable_declaration',
                           'member_expression', 'call_expression', 'arguments',
                           'identifier', 'property_identifier'},
            'typescript': {
                'function_declaration', 'generator_function_declaration',
                'class_declaration',
                'method_definition',
                'public_field_definition', 'private_field_definition',
                'protected_field_definition', 'interface_declaration',
                'type_alias_declaration', 'enum_declaration', 'enum_member',
                'namespace_declaration', 'ambient_declaration', 'external_module_declaration',
                'lexical_declaration', 'variable_declaration', 'variable_declarator',
                'arrow_function', 'function_expression', 'export_statement',
                'default_export_statement', 'member_expression', 'call_expression',
                'arguments', 'identifier', 'property_identifier', 'type_identifier',
                'type_parameters', 'decorator', 'asserts_annotation',
                'type_predicate_annotation', 'module_declaration'
            },
            'rust': {'function_item', 'struct_item', 'enum_item', 'trait_item'},
            'go': {'function_declaration', 'type_declaration'},
            'ruby': {'method', 'class', 'module', 'singleton_method'},
            'java': {'method_declaration', 'class_declaration', 'interface_declaration',
                     'enum_declaration', 'annotation_type_declaration'},
            'php': {'function_definition', 'class_declaration', 'method_declaration',
                    'interface_declaration', 'trait_declaration', 'enum_declaration'},
            'c_cpp': {'function_definition', 'class_specifier', 'struct_specifier',
                      'enum_specifier', 'union_specifier', 'namespace_definition', 'template_declaration'},
            'css': {'rule_set', 'keyframe_block_list', 'media_statement', 'import_statement', 'namespace_statement'},
            'html': {'element', 'script_element', 'style_element', 'doctype'}
        }

        self._valida_tipi_nodo()
        self._debug_mode = False
        self._dump_counter = 0
        self._debug_log_path = None

    def _valida_tipi_nodo(self):
        """Confronta i tipi di nodo attesi con quelli realmente forniti dalla grammatica."""
        for chiave_lingua, (lingua_ts, parser_ts) in PARSER_TREE_SITTER.items():
            tipi_attesi = self._tipi_nodo_dinamici.get(chiave_lingua) or self._EXPECTED_TYPES_FALLBACK.get(chiave_lingua, set())
            if not tipi_attesi:
                continue
            tipi_esistenti = set()
            try:
                for i in range(lingua_ts.node_kind_count):
                    tipo = lingua_ts.node_kind_for_id(i)
                    if tipo:
                        tipi_esistenti.add(tipo)
            except AttributeError:
                self.logger.debug(f"Impossibile validare tipi di nodo per {chiave_lingua}: API non disponibile")
                continue
            mancanti = tipi_attesi - tipi_esistenti
            if mancanti:
                self.logger.warning(
                    f"Grammatica {chiave_lingua}: tipi di nodo mancanti o rinominati: {', '.join(sorted(mancanti))}. "
                    "L'analisi potrebbe essere incompleta. Aggiorna tree‑sitter o la lista."
                )
                if self._debug_mode:
                    self._log_debug_error('WARNING', f"Tipi mancanti per {chiave_lingua}", extra={
                        'language': chiave_lingua,
                        'missing': sorted(mancanti)
                    })
            else:
                self.logger.debug(f"Validazione tipi di nodo per {chiave_lingua} completata con successo.")

    def _log_debug_error(self, level, message, extra=None, exc_info=False):
        if not self._debug_mode or not self._debug_handler_file:
            log_func = getattr(self.logger, level.lower(), self.logger.error)
            log_func(message)
            return
        record = {
            'timestamp': datetime.datetime.utcnow().isoformat() + 'Z',
            'level': level.upper(),
            'phase': extra.get('phase', 'general') if extra else 'general',
            'file': extra.get('file', '') if extra else '',
            'language': extra.get('language', '') if extra else '',
            'error_type': extra.get('error_type', '') if extra else '',
            'message': message,
            'traceback': traceback.format_exc() if exc_info else '',
        }
        try:
            with open(self._debug_log_path, 'a', encoding='utf-8') as f:
                f.write(json.dumps(record, ensure_ascii=False) + '\n')
        except Exception:
            print(f"[DEBUG LOG FALLITO] {record}", file=sys.stderr)

    def _setup_debug_log_file(self):
        self._debug_log_path = os.path.join(self.directory_quarantena, 'debug_errors.jsonl')
        try:
            pass
        except Exception as e:
            self.logger.error(f"Impossibile creare file debug: {e}. Logging solo su console.")
            self._debug_mode = False
            return
        original_hook = sys.excepthook
        def debug_excepthook(exc_type, exc_value, tb):
            error_msg = f"Unhandled exception: {exc_type.__name__}: {exc_value}"
            self._log_debug_error('ERROR', error_msg, exc_info=True, extra={
                'phase': 'global',
                'error_type': exc_type.__name__,
                'file': ''
            })
            original_hook(exc_type, exc_value, tb)
        sys.excepthook = debug_excepthook

    def set_debug_mode(self, enable=True):
        self._debug_mode = enable
        if enable:
            self.logger.setLevel(logging.DEBUG)
            for handler in self.logger.handlers:
                handler.setLevel(logging.DEBUG)
            self._setup_debug_log_file()
            self.logger.debug("Debug mode attivato – errori salvati in %s", self._debug_log_path)
        else:
            self.logger.setLevel(logging.INFO)
            for handler in self.logger.handlers:
                handler.setLevel(logging.INFO)

    # -------------------------------------------------------------------------
    # Strumenti di diagnostica avanzata (dump dell'albero e report)
    # -------------------------------------------------------------------------
    def _dump_tree_to_string(self, node, byte_grezzi, indent=0, max_depth=50):
        if node is None or indent > max_depth:
            return ""
        tipo = _get_node_type_safe(node)
        is_missing = node.is_missing if hasattr(node, 'is_missing') else False

        if byte_grezzi is not None and not isinstance(byte_grezzi, (bytes, bytearray, str)):
            print(f"[LOG _dump_tree_to_string] ATTENZIONE: byte_grezzi tipo inaspettato: {type(byte_grezzi).__name__}")
            if isinstance(byte_grezzi, str):
                byte_grezzi = byte_grezzi.encode('utf-8')
            else:
                try:
                    byte_grezzi = bytes(byte_grezzi)
                except Exception:
                    byte_grezzi = b''

        testo_raw = _get_node_text_safe(node, byte_grezzi)
        if isinstance(testo_raw, bytes):
            testo = testo_raw.decode('utf-8', errors='replace')
        else:
            testo = str(testo_raw) if testo_raw is not None else ''
        testo = testo[:40].replace('\n', '\\n')
        missing_marker = " [MISSING]" if is_missing else ""
        lines = ["  " * indent + f"{tipo}{missing_marker}  '{testo}'"]
        for child in _get_node_children_safe(node):
            lines.extend(self._dump_tree_to_string(child, byte_grezzi, indent+1, max_depth).splitlines())
        return "\n".join(lines)

    def _dump_tree_to_file(self, node, byte_grezzi, filepath):
        dump = self._dump_tree_to_string(node, byte_grezzi)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(dump)
        return filepath

    def _diagnostica_estrazione(self, percorso, nodo_radice, byte_grezzi, linguaggio):
        """Crea un report dettagliato quando un file non produce simboli."""
        if nodo_radice is None:
            self.logger.warning(f"[DIAG] Nodo radice nullo per {percorso} – impossibile estrarre simboli.")
            dump_file = os.path.join(self.directory_quarantena, f"debug_null_root_{uuid.uuid4().hex}.txt")
            try:
                with open(dump_file, 'w', encoding='utf-8') as f:
                    f.write(f"File: {percorso}\nLinguaggio: {linguaggio}\nNodo radice: None\n")
                self.logger.warning(f"[DIAG] Report diagnostico (radice nulla) salvato in {dump_file}")
            except Exception:
                pass
            return

        tipi_incontrati = defaultdict(int)
        def raccogli_tipi(node):
            if node is None:
                return
            tipi_incontrati[_get_node_type_safe(node)] += 1
            for child in _get_node_children_safe(node):
                raccogli_tipi(child)
        raccogli_tipi(nodo_radice)

        self.logger.warning(f"[DIAG] NESSUN SIMBOLO estratto per {percorso}")
        self.logger.warning(f"[DIAG] {len(tipi_incontrati)} tipi di nodo incontrati")
        top = sorted(tipi_incontrati.items(), key=lambda x: -x[1])[:20]
        for tipo, count in top:
            self.logger.warning(f"  {tipo}: {count}")

        suggeriti = []
        for t in tipi_incontrati:
            if any(k in t for k in ('function', 'class', 'interface', 'enum', 'type', 'namespace',
                                    'module', 'declaration', 'definition', 'item', 'specifier',
                                    'method', 'struct', 'variable')):
                suggeriti.append(t)
        if suggeriti:
            self.logger.warning(f"[DIAG] Possibili tipi definitori: {', '.join(suggeriti)}")
            self.logger.warning("[DIAG] Aggiorna def_patterns con questi tipi se mancano.")

        dump_file = os.path.join(self.directory_quarantena, f"debug_tree_{uuid.uuid4().hex}.txt")
        self._dump_tree_to_file(nodo_radice, byte_grezzi, dump_file)
        self.logger.warning(f"[DIAG] Dump albero salvato in {dump_file}")

        report = {
            "file": percorso,
            "linguaggio": linguaggio,
            "timestamp": datetime.datetime.utcnow().isoformat(),
            "tipi_incontrati": dict(tipi_incontrati),
            "suggeriti": suggeriti,
            "dump_file": dump_file
        }
        json_file = os.path.join(self.directory_quarantena, f"diagnostic_{uuid.uuid4().hex}.json")
        with open(json_file, 'w') as f:
            json.dump(report, f, indent=2)
        self.logger.warning(f"[DIAG] Report diagnostico salvato in {json_file}")
        if self._debug_mode:
            self._log_debug_error('WARNING', f"Nessun simbolo estratto per {percorso}", extra={
                'phase': 'estrazione',
                'file': percorso,
                'language': linguaggio,
                'error_type': 'zero_symbols'
            })

    def _verifica_grammatica(self, lingua_ts, linguaggio):
        if not self._debug_mode:
            return
        tipi_disponibili = set()
        try:
            for i in range(lingua_ts.node_kind_count):
                nome = lingua_ts.node_kind_for_id(i)
                if nome:
                    tipi_disponibili.add(nome)
        except Exception:
            return
        self.logger.debug(f"Grammatica {linguaggio}: {len(tipi_disponibili)} tipi disponibili.")
        attesi = self._EXPECTED_TYPES_FALLBACK.get(linguaggio, set())
        mancanti = attesi - tipi_disponibili
        if mancanti:
            self.logger.warning(f"[GRAMMATICA] Tipi attesi mancanti per {linguaggio}: {', '.join(sorted(mancanti))}")

    # -------------------------------------------------------------------------
    # Gestione del manifest (diario delle operazioni di quarantena)
    # -------------------------------------------------------------------------
    def _carica_diario_manifest(self):
        if os.path.isfile(self.percorso_manifest):
            try:
                with open(self.percorso_manifest, 'r') as f:
                    self._diario_manifest = json.load(f)
            except Exception:
                self._diario_manifest = []
        else:
            self._diario_manifest = []

    def _salva_manifest(self):
        try:
            with tempfile.NamedTemporaryFile(mode='w', dir=self.directory_quarantena,
                                             delete=False, suffix='.json', encoding='utf-8') as tf:
                json.dump(self._diario_manifest, tf, indent=2)
                temp_name = tf.name
            os.replace(temp_name, self.percorso_manifest)
        except Exception as e:
            self.logger.error(f"Salvataggio manifest fallito: {e}")

    def _ripristina_da_manifest(self):
        if not self._diario_manifest:
            return
        in_sospeso = [voce for voce in self._diario_manifest if voce.get('stato') == 'pending']
        if not in_sospeso:
            return
        self.logger.info(f"Ripristino di {len(in_sospeso)} operazioni pending dal manifest...")
        for voce in in_sospeso:
            if voce['tipo'] == 'sostituzione_backup' and os.path.isfile(voce['backup']):
                try:
                    os.replace(voce['backup'], voce['destinazione'])
                    self.logger.info(f"Ripristinato {voce['destinazione']} da backup")
                except Exception as e:
                    self.logger.warning(f"Impossibile ripristinare {voce['destinazione']}: {e}")
            self._diario_manifest.remove(voce)
        self._salva_manifest()

    def _replace_with_retry(self, origine, destinazione, tentativi=3, ritardo=0.1):
        import time as time_module
        for tentativo in range(tentativi):
            try:
                os.replace(origine, destinazione)
                return
            except PermissionError:
                if tentativo == tentativi - 1:
                    raise
                time_module.sleep(ritardo * (2 ** tentativo))

    def _sostituzione_sicura(self, origine, destinazione):
        try:
            origine_sicura = self._percorso_sicuro(origine)
            destinazione_sicura = self._percorso_sicuro(destinazione)
            percorso_backup = None
            if os.path.isfile(destinazione_sicura):
                nome_backup = f"{uuid.uuid4().hex}_{os.path.basename(destinazione_sicura)}"
                dir_backup = os.path.join(self.directory_quarantena, 'backup_sostituzioni')
                os.makedirs(dir_backup, exist_ok=True)
                percorso_backup = os.path.join(dir_backup, nome_backup)
                shutil.copy2(destinazione_sicura, percorso_backup)
                voce_diario = {
                    'id': str(uuid.uuid4()),
                    'tipo': 'sostituzione_backup',
                    'destinazione': destinazione_sicura,
                    'backup': percorso_backup,
                    'stato': 'pending'
                }
                self._diario_manifest.append(voce_diario)
                self._salva_manifest()
            self._replace_with_retry(origine_sicura, destinazione_sicura)
            if percorso_backup:
                try:
                    os.remove(percorso_backup)
                except OSError:
                    pass
                self._diario_manifest = [e for e in self._diario_manifest
                                         if e.get('destinazione') != destinazione_sicura or e.get('stato') != 'pending']
                self._salva_manifest()
        except (OSError, ValueError) as e:
            self.logger.critical(f"[ERRORE I/O] sostituzione fallita: {origine} -> {destinazione}: {e}")
            sys.exit(3)

    # -------------------------------------------------------------------------
    # Protezione dei percorsi (anti path traversal)
    # -------------------------------------------------------------------------
    @staticmethod
    def _normalizza_percorso(p):
        try:
            if p.startswith('\\\\') or p.startswith('//'):
                parti = p.replace('/', '\\').split('\\')
                if len(parti) >= 4 and parti[0] == '' and parti[1] == '':
                    prefisso_unc = f"\\\\{parti[2]}\\{parti[3]}"
                    resto = '\\'.join(parti[4:])
                    if resto:
                        resto_normalizzato = os.path.normpath(resto)
                        return os.path.normcase(f"{prefisso_unc}\\{resto_normalizzato}")
                    return os.path.normcase(prefisso_unc)
            normalizzato = os.path.realpath(os.path.abspath(p))
        except OSError:
            return p
        if platform.system() == 'Windows':
            normalizzato = os.path.normcase(normalizzato)
        return normalizzato

    def _percorso_sicuro(self, percorso, fallimento_soft=False):
        try:
            percorso_reale = self._normalizza_percorso(percorso)
            radice_reale = self.directory_radice
        except OSError as e:
            self.logger.error(f"[SICUREZZA] Errore nella risoluzione del percorso: {percorso} - {e}")
            if fallimento_soft:
                return None
            raise ValueError(f"Percorso non risolvibile: {percorso}")
        try:
            comune = os.path.commonpath([percorso_reale, radice_reale])
        except ValueError:
            if "'" in percorso or ";" in percorso:
                self.logger.debug(f"[SICUREZZA] Percorso sospetto (artefatto): {percorso} -> {percorso_reale}")
                if fallimento_soft:
                    return None
                raise ValueError(f"Tentativo di Path Traversal: {percorso}")
            self.logger.error(f"[SICUREZZA] Path Traversal rilevato: {percorso} -> {percorso_reale}")
            if fallimento_soft:
                return None
            raise ValueError(f"Tentativo di Path Traversal: {percorso}")
        if comune != radice_reale and not percorso_reale.startswith(radice_reale + os.sep) and percorso_reale != radice_reale:
            self.logger.error(f"[SICUREZZA] Percorso fuori dalla root: {percorso_reale}")
            if fallimento_soft:
                return None
            raise ValueError(f"Accesso negato al percorso: {percorso}")
        return percorso_reale

    def _apertura_sicura(self, percorso, modalita='r', codifica='utf-8'):
        percorso_sicuro = self._percorso_sicuro(percorso)
        if 'b' in modalita:
            return open(percorso_sicuro, modalita)
        else:
            return open(percorso_sicuro, modalita, encoding=codifica)

    def _spostamento_sicuro(self, origine, destinazione):
        try:
            origine_sicura = self._percorso_sicuro(origine)
            destinazione_sicura = self._percorso_sicuro(destinazione)
            shutil.move(origine_sicura, destinazione_sicura)
        except (OSError, ValueError) as e:
            self.logger.critical(f"[ERRORE I/O] spostamento fallito: {origine} -> {destinazione}: {e}")
            sys.exit(3)

    def _listadir_sicura(self, percorso):
        percorso_sicuro = self._percorso_sicuro(percorso)
        return os.listdir(percorso_sicuro)

    def _file_esiste_sicuro(self, percorso):
        try:
            percorso_sicuro = self._percorso_sicuro(percorso, fallimento_soft=True)
        except ValueError:
            return False
        if percorso_sicuro is None:
            return False
        return os.path.isfile(percorso_sicuro)

    def _directory_esiste_sicura(self, percorso):
        try:
            percorso_sicuro = self._percorso_sicuro(percorso, fallimento_soft=True)
        except ValueError:
            return False
        if percorso_sicuro is None:
            return False
        return os.path.isdir(percorso_sicuro)

    def _pulisci_stringa_import(self, import_grezzo):
        pulito = import_grezzo.strip().strip("'\"")
        pulito = re.sub(r"['\";]+", '', pulito)
        return pulito

    # -------------------------------------------------------------------------
    # Lettura dei file e riconoscimento di file binari / di test
    # -------------------------------------------------------------------------
    def _leggi_sorgente_str(self, percorso):
        try:
            with self._apertura_sicura(percorso, 'rb') as f:
                byte_grezzi = f.read()
        except Exception:
            return None

        if byte_grezzi.startswith(b'\xef\xbb\xbf'):
            try:
                return byte_grezzi.decode('utf-8-sig')
            except Exception:
                pass
        elif byte_grezzi.startswith(b'\xff\xfe') or byte_grezzi.startswith(b'\xfe\xff'):
            for codifica in ('utf-16', 'utf-16-le', 'utf-16-be'):
                try:
                    return byte_grezzi.decode(codifica)
                except Exception:
                    continue
        else:
            try:
                return byte_grezzi.decode('utf-8')
            except UnicodeDecodeError:
                pass
        for codifica in ('latin-1', 'cp1252'):
            try:
                return byte_grezzi.decode(codifica)
            except Exception:
                continue
        return None

    def _e_analizzabile(self, percorso, campione_contenuto=None):
        try:
            if campione_contenuto is None:
                with self._apertura_sicura(percorso, 'rb') as f:
                    campione = f.read(8192)
            else:
                campione = campione_contenuto[:8192]
            if not campione:
                return False
            non_stampabili = sum(1 for b in campione if b > 127 or (b < 32 and b not in (9, 10, 13)))
            rapporto = non_stampabili / len(campione)
            return rapporto <= 0.1
        except Exception:
            return False

    def _e_file_di_testo(self, percorso):
        percorso_sicuro = self._percorso_sicuro(percorso, fallimento_soft=True)
        if percorso_sicuro is None:
            return ""
        if percorso_sicuro in self._cache_testo:
            return self._cache_testo[percorso_sicuro]
        if not self._e_analizzabile(percorso_sicuro):
            self.logger.debug(f"File binario saltato: {percorso_sicuro}")
            self._cache_testo[percorso_sicuro] = ""
            return ""
        sorgente_str = self._leggi_sorgente_str(percorso_sicuro)
        self._cache_testo[percorso_sicuro] = sorgente_str if sorgente_str else ""
        return self._cache_testo[percorso_sicuro]

    def _ottieni_byte_grezzi(self, percorso):
        sorgente = self._e_file_di_testo(percorso)
        if sorgente is None or sorgente == "":
            return None
        return sorgente.encode('utf-8')

    def _costruisci_mappa_byte_a_linea(self, percorso, byte_grezzi):
        if isinstance(byte_grezzi, str):
            byte_grezzi = byte_grezzi.encode('utf-8')
        mappatura = [0] * (len(byte_grezzi) + 1)
        linea = 0
        for i, b in enumerate(byte_grezzi):
            mappatura[i] = linea
            if b == ord('\n'):
                linea += 1
        mappatura[-1] = linea
        self._byte_a_linea[percorso] = mappatura
        return mappatura

    def _offset_byte_a_linea(self, percorso, offset_byte, byte_grezzi=None):
        if percorso not in self._byte_a_linea:
            if byte_grezzi is not None:
                self._costruisci_mappa_byte_a_linea(percorso, byte_grezzi)
            else:
                return 0
        mappatura = self._byte_a_linea[percorso]
        if offset_byte >= len(mappatura):
            return mappatura[-1] if mappatura else 0
        return mappatura[offset_byte]

    # -------------------------------------------------------------------------
    # Risoluzione dei percorsi di import (inclusi alias tsconfig)
    # -------------------------------------------------------------------------
    def _risolvi_percorso(self, file_corrente, stringa_import, linguaggio, livello=0):
        stringa_import = self._pulisci_stringa_import(stringa_import)
        if stringa_import.startswith('/') or stringa_import.startswith('\\'):
            self.import_non_risolti.append((file_corrente, stringa_import, linguaggio))
            return None

        dir_corrente = os.path.dirname(file_corrente)
        if livello > 0 and linguaggio == 'python':
            for _ in range(livello):
                dir_corrente = os.path.dirname(dir_corrente)

        if linguaggio in ('typescript', 'javascript') and self.alias_tsconfig:
            for alias, (url_base, percorsi_mappati) in self.alias_tsconfig.items():
                if '*' in alias:
                    if fnmatch.fnmatch(stringa_import, alias):
                        prefisso = alias.split('*')[0]
                        suffisso = stringa_import[len(prefisso):]
                        for mappato in percorsi_mappati:
                            pattern_risolto = mappato.replace('*', suffisso)
                            candidato_base = os.path.normpath(os.path.join(self.directory_radice, url_base, pattern_risolto))
                            estensioni = REGISTRO_LINGUAGGI[linguaggio]['ext']
                            for est in estensioni:
                                completo = candidato_base + est
                                if os.path.isfile(completo):
                                    return self._normalizza_percorso(completo)
                            if os.path.isdir(candidato_base):
                                for est in estensioni:
                                    file_indice = os.path.join(candidato_base, 'index' + est)
                                    if os.path.isfile(file_indice):
                                        return self._normalizza_percorso(file_indice)
                else:
                    if stringa_import == alias or stringa_import.startswith(alias + '/'):
                        for mappato in percorsi_mappati:
                            dir_base = os.path.join(self.directory_radice, url_base)
                            import_candidato = os.path.join(dir_base, stringa_import.replace(alias, mappato, 1))
                            estensioni = REGISTRO_LINGUAGGI[linguaggio]['ext']
                            for est in estensioni:
                                completo = import_candidato + est
                                if os.path.isfile(completo):
                                    return self._normalizza_percorso(completo)
                            if os.path.isdir(import_candidato):
                                for est in estensioni:
                                    file_indice = os.path.join(import_candidato, 'index' + est)
                                    if os.path.isfile(file_indice):
                                        return self._normalizza_percorso(file_indice)

        if linguaggio == 'python':
            primo_livello = stringa_import.split('.')[0]
            if primo_livello in _MODULI_STDLIB_PRINCIPALI or stringa_import in sys.stdlib_module_names:
                return None

        if linguaggio in ('javascript', 'typescript'):
            if not stringa_import.startswith('./') and not stringa_import.startswith('../') \
               and '/' not in stringa_import and '\\' not in stringa_import:
                self.import_non_risolti.append((file_corrente, stringa_import, linguaggio))
                return None

        if stringa_import.startswith('./') or stringa_import.startswith('../'):
            dir_corrente = os.path.normpath(os.path.join(dir_corrente, stringa_import))
            import_pulito = dir_corrente
        else:
            import_pulito = stringa_import.replace('.', '/').replace('\\', '/')

        estensioni = REGISTRO_LINGUAGGI[linguaggio]['ext']
        candidati = []
        for est in estensioni:
            candidati.append(os.path.normpath(os.path.join(dir_corrente, import_pulito + est)))
        candidati.append(os.path.normpath(os.path.join(dir_corrente, import_pulito)))
        for est in estensioni:
            candidati.append(os.path.normpath(os.path.join(self.directory_radice, import_pulito + est)))
        candidati.append(os.path.normpath(os.path.join(self.directory_radice, import_pulito)))

        for p in candidati:
            p_sicuro = self._percorso_sicuro(p, fallimento_soft=True)
            if p_sicuro is None:
                continue
            if os.path.isfile(p_sicuro):
                return p_sicuro
            if os.path.isdir(p_sicuro):
                if linguaggio == 'python':
                    file_init = os.path.join(p_sicuro, '__init__.py')
                    if os.path.isfile(file_init):
                        return self._normalizza_percorso(file_init)
                elif linguaggio in ('javascript', 'typescript'):
                    for est in estensioni:
                        file_indice = os.path.join(p_sicuro, 'index' + est)
                        if os.path.isfile(file_indice):
                            return self._normalizza_percorso(file_indice)
                if os.path.isfile(os.path.join(p_sicuro, 'package.json')):
                    try:
                        with self._apertura_sicura(os.path.join(p_sicuro, 'package.json'), 'r', 'utf-8') as f:
                            pkg = json.load(f)
                        file_principale = pkg.get('main', 'index.js')
                        percorso_principale = os.path.join(p_sicuro, file_principale)
                        if os.path.isfile(percorso_principale):
                            return self._normalizza_percorso(percorso_principale)
                    except:
                        pass
        self.import_non_risolti.append((file_corrente, stringa_import, linguaggio))
        return None

    def _carica_tsconfig(self):
        percorso_tsconfig = os.path.join(self.directory_radice, 'tsconfig.json')
        if not self._file_esiste_sicuro(percorso_tsconfig):
            return
        try:
            with self._apertura_sicura(percorso_tsconfig, 'r', 'utf-8') as f:
                tsconfig = json.load(f)
            opzioni_compilatore = tsconfig.get('compilerOptions', {})
            url_base = opzioni_compilatore.get('baseUrl', '.')
            percorsi = opzioni_compilatore.get('paths', {})
            for alias, pattern in percorsi.items():
                self.alias_tsconfig[alias] = (url_base, pattern)
        except Exception as e:
            self.logger.debug(f"Impossibile caricare tsconfig.json: {e}")

    def _carica_pyproject_toml(self):
        percorso_toml = os.path.join(self.directory_radice, 'pyproject.toml')
        if not self._file_esiste_sicuro(percorso_toml):
            return
        try:
            if sys.version_info >= (3, 11):
                import tomllib
            else:
                try:
                    import tomli as tomllib
                except ImportError:
                    self.logger.debug("tomli non installato, impossibile leggere pyproject.toml")
                    return
            with self._apertura_sicura(percorso_toml, 'rb') as f:
                dati = tomllib.load(f)
            progetto = dati.get('project', {})
            nome_pacchetto = progetto.get('name')
            if nome_pacchetto:
                dir_sorgenti = [self.directory_radice]
                strumento = dati.get('tool', {})
                setuptools = strumento.get('setuptools', {})
                pacchetti = setuptools.get('packages', [])
                if pacchetti:
                    dir_sorgenti = [os.path.join(self.directory_radice, p) for p in pacchetti]
                self.mappa_import_statici[nome_pacchetto] = dir_sorgenti
        except Exception as e:
            self.logger.debug(f"pyproject.toml non processato: {e}")

    def _carica_package_json(self):
        percorso_pkg = os.path.join(self.directory_radice, 'package.json')
        if not self._file_esiste_sicuro(percorso_pkg):
            return
        try:
            with self._apertura_sicura(percorso_pkg, 'r', 'utf-8') as f:
                pkg = json.load(f)
            file_principale = pkg.get('main')
            if file_principale:
                percorso_principale = self._normalizza_percorso(os.path.join(self.directory_radice, file_principale))
                if os.path.isfile(percorso_principale):
                    self.punti_ingresso.add(percorso_principale)
            campo_bin = pkg.get('bin', {})
            if isinstance(campo_bin, dict):
                for cmd, file_bin in campo_bin.items():
                    percorso_bin = self._normalizza_percorso(os.path.join(self.directory_radice, file_bin))
                    if os.path.isfile(percorso_bin):
                        self.punti_ingresso.add(percorso_bin)
            workspace = pkg.get('workspaces', [])
            if workspace:
                for ws in workspace:
                    percorso_ws = os.path.join(self.directory_radice, ws)
                    if os.path.isdir(percorso_ws):
                        for sotto in os.listdir(percorso_ws):
                            sotto_completo = os.path.join(percorso_ws, sotto)
                            if os.path.isdir(sotto_completo):
                                sotto_pkg = os.path.join(sotto_completo, 'package.json')
                                if os.path.isfile(sotto_pkg):
                                    try:
                                        with self._apertura_sicura(sotto_pkg, 'r', 'utf-8') as sf:
                                            dati_sotto = json.load(sf)
                                        principale_sotto = dati_sotto.get('main', 'index.js')
                                        percorso_principale_sotto = os.path.join(sotto_completo, principale_sotto)
                                        if os.path.isfile(percorso_principale_sotto):
                                            self.punti_ingresso.add(self._normalizza_percorso(percorso_principale_sotto))
                                    except:
                                        pass
        except Exception:
            pass

    def _carica_cargo_toml(self):
        percorso_cargo = os.path.join(self.directory_radice, 'Cargo.toml')
        if not self._file_esiste_sicuro(percorso_cargo):
            return
        try:
            with self._apertura_sicura(percorso_cargo, 'r', 'utf-8') as f:
                contenuto = f.read()
            match_nome = re.search(r'^\s*name\s*=\s*"([^"]+)"', contenuto, re.MULTILINE)
            if match_nome:
                main_rs = os.path.join(self.directory_radice, 'src', 'main.rs')
                if os.path.isfile(main_rs):
                    self.punti_ingresso.add(self._normalizza_percorso(main_rs))
                lib_rs = os.path.join(self.directory_radice, 'src', 'lib.rs')
                if os.path.isfile(lib_rs):
                    self.punti_ingresso.add(self._normalizza_percorso(lib_rs))
            for match_bin in re.finditer(r'\[\[bin\]\]\s*name\s*=\s*"([^"]+)"\s*path\s*=\s*"([^"]+)"', contenuto, re.DOTALL):
                percorso_bin = os.path.join(self.directory_radice, match_bin.group(2))
                if os.path.isfile(percorso_bin):
                    self.punti_ingresso.add(self._normalizza_percorso(percorso_bin))
        except Exception:
            pass

    # -------------------------------------------------------------------------
    # Punti di ingresso (espliciti, package.json, euristica automatica)
    # -------------------------------------------------------------------------
    def _carica_punti_ingresso(self, percorso_file):
        if not os.path.isfile(percorso_file):
            return
        try:
            with self._apertura_sicura(percorso_file, 'r', 'utf-8') as f:
                for linea in f:
                    linea = linea.strip()
                    if linea and not linea.startswith('#'):
                        percorso_completo = self._normalizza_percorso(os.path.join(self.directory_radice, linea))
                        if os.path.isfile(percorso_completo):
                            self.punti_ingresso_espliciti.add(percorso_completo)
                        else:
                            self.logger.warning(f"Punto di ingresso nel file {percorso_file} non trovato: {percorso_completo}")
        except Exception as e:
            self.logger.warning(f"Impossibile leggere {percorso_file}: {e}")

    def _scopri_ambiente(self):
        """Fase 1: individua i file del progetto e i punti di ingresso."""
        self.logger.info("Fase 1: Ricerca dei file principali...")
        go_presente = False  # tracciamo se ci sono file Go

        if self.punti_ingresso_espliciti:
            self.punti_ingresso = self.punti_ingresso_espliciti.copy()
            self.logger.info(f"Punti di ingresso espliciti: {len(self.punti_ingresso)} file.")
            for radice, dirs, files in os.walk(self.directory_radice):
                dirs[:] = [d for d in dirs if d not in DIRECTORY_IGNORATE and d not in self.lista_nera_personalizzata]
                for file in files:
                    percorso = os.path.join(radice, file)
                    percorso_sicuro = self._percorso_sicuro(percorso, fallimento_soft=True)
                    if percorso_sicuro is None:
                        continue
                    estensione = os.path.splitext(file)[1]
                    if any(estensione in d['ext'] for d in REGISTRO_LINGUAGGI.values()):
                        if self._file_escluso(percorso_sicuro):
                            continue
                        if percorso_sicuro in self.file_non_analizzabili:
                            continue
                        contenuto = self._e_file_di_testo(percorso_sicuro)
                        if contenuto:
                            self.tutti_i_file.add(percorso_sicuro)
                            if estensione == '.go':
                                go_presente = True
            if self._go_strict_override is None:
                self.go_strict = go_presente
            return

        conteggio_file = 0
        for radice, dirs, files in os.walk(self.directory_radice):
            dirs[:] = [d for d in dirs if d not in DIRECTORY_IGNORATE and d not in self.lista_nera_personalizzata]
            for file in files:
                percorso = os.path.join(radice, file)
                percorso_sicuro = self._percorso_sicuro(percorso, fallimento_soft=True)
                if percorso_sicuro is None:
                    continue
                if self._file_escluso(percorso_sicuro):
                    continue
                if percorso_sicuro in self.file_non_analizzabili:
                    continue
                estensione = os.path.splitext(file)[1]
                linguaggio = next((l for l, d in REGISTRO_LINGUAGGI.items() if estensione in d['ext']), None)
                if not linguaggio:
                    continue
                contenuto = self._e_file_di_testo(percorso_sicuro)
                if not contenuto:
                    continue
                self.tutti_i_file.add(percorso_sicuro)
                conteggio_file += 1
                if estensione == '.go':
                    go_presente = True

                e_ingresso = False
                if re.search(r'^(main|index|app|server)\.', file, re.IGNORECASE):
                    e_ingresso = True
                if file == '__main__.py':
                    e_ingresso = True
                prima_linea = contenuto.splitlines()[0] if contenuto else ''
                if prima_linea.startswith('#!') and ('node' in prima_linea or 'python' in prima_linea or 'ruby' in prima_linea):
                    e_ingresso = True
                pulito = pulisci_per_grep(contenuto, estensione, linguaggio)
                if linguaggio == 'python':
                    if 'if __name__ == "__main__":' in contenuto:
                        e_ingresso = True
                    if any(x in pulito for x in ['@app.route', '@app.get', '@app.post', '@router.', '@app.put', '@app.delete']):
                        e_ingresso = True
                    if 'urlpatterns' in pulito and 'django.urls' in contenuto:
                        e_ingresso = True
                    if 'setup(' in contenuto and 'console_scripts' in contenuto:
                        e_ingresso = True
                elif linguaggio in ['javascript', 'typescript']:
                    if re.search(r'ReactDOM\.render|React\.createRoot|createRoot\(', pulito):
                        e_ingresso = True
                    if 'createApp(' in pulito:
                        e_ingresso = True
                    if 'bootstrapApplication(' in pulito:
                        e_ingresso = True
                elif linguaggio == 'rust':
                    if 'fn main()' in contenuto:
                        e_ingresso = True
                elif linguaggio == 'go':
                    if 'package main' in contenuto:
                        e_ingresso = True
                elif linguaggio == 'php':
                    if 'index.php' in file.lower():
                        e_ingresso = True

                if e_ingresso and self._e_file_di_test(percorso_sicuro):
                    e_ingresso = False
                    self.logger.debug(f"File di test escluso dai punti di ingresso: {percorso_sicuro}")

                if e_ingresso:
                    self.punti_ingresso.add(percorso_sicuro)

        # Imposta automaticamente go_strict se ci sono file .go e non c'è override
        if self._go_strict_override is None:
            self.go_strict = go_presente
            if go_presente:
                self.logger.info("Progetto Go rilevato: attivata modalità strict (--go-strict implicito). "
                                 "Usare --no-go-strict per disabilitarla.")

        if not self.punti_ingresso:
            self.logger.warning("Nessun punto di ingresso automatico trovato. Cerco nella root e in src/...")
            dir_candidate = [self.directory_radice, os.path.join(self.directory_radice, 'src')]
            candidati_trovati = set()
            for cdir in dir_candidate:
                if os.path.isdir(cdir):
                    for f in os.listdir(cdir):
                        fpath = os.path.join(cdir, f)
                        fpath_sicuro = self._percorso_sicuro(fpath, fallimento_soft=True)
                        if fpath_sicuro is None:
                            continue
                        if os.path.isfile(fpath_sicuro) and fpath_sicuro in self.tutti_i_file:
                            contenuto = self._e_file_di_testo(fpath_sicuro)
                            if contenuto:
                                if '__all__' in contenuto or 'export ' in contenuto or 'module.exports' in contenuto:
                                    candidati_trovati.add(fpath_sicuro)
                            if fpath_sicuro.endswith('.py'):
                                try:
                                    albero = ast.parse(contenuto)
                                    for nodo in ast.walk(albero):
                                        if isinstance(nodo, (ast.FunctionDef, ast.ClassDef)):
                                            candidati_trovati.add(fpath_sicuro)
                                            break
                                except:
                                    if re.search(r'(?:def |class )', contenuto):
                                        candidati_trovati.add(fpath_sicuro)
            if candidati_trovati:
                self.punti_ingresso = candidati_trovati
                self.logger.info(f"Trovati {len(candidati_trovati)} possibili punti di ingresso nella root/src.")
            else:
                file_radice = [f for f in self.tutti_i_file if os.path.dirname(f) == self.directory_radice][:10]
                if file_radice:
                    self.punti_ingresso = set(file_radice)
                    self.logger.warning(f"Nessun punto di ingresso identificabile. Provo con i primi {len(file_radice)} file nella root.")
                else:
                    self.logger.error("Impossibile identificare punti di ingresso. Usa un file .efdc_entrypoints per specificarli manualmente.")
                    self.punti_ingresso = set()

    def _file_escluso(self, percorso):
        nome_file = os.path.basename(percorso)
        for pattern in PATTERN_FILE_ESCLUSI:
            if fnmatch.fnmatch(nome_file, pattern):
                return True
        return False

    def _e_file_di_test(self, percorso_file):
        nome_file = os.path.basename(percorso_file)
        percorso_rel = os.path.normpath(os.path.relpath(percorso_file, self.directory_radice))
        for pattern in PATTERN_FILE_TEST:
            pattern_norm = pattern.replace('\\', '/')
            if '/' in pattern_norm or '\\' in pattern_norm:
                if fnmatch.fnmatch(percorso_rel, pattern_norm) or \
                   fnmatch.fnmatch(percorso_rel.replace(os.sep, '/'), pattern_norm):
                    return True
            elif fnmatch.fnmatch(nome_file, pattern):
                return True
        parti = percorso_rel.replace(os.sep, '/').split('/')
        if any(p.lower() in ('test', 'tests') for p in parti):
            return True
        return False

    # -------------------------------------------------------------------------
    # Direttive di ignoramento (es. # noqa, deadcode: ignore)
    # -------------------------------------------------------------------------
    def _scansiona_direttive_ignora(self, percorso, contenuto):
        linee = contenuto.splitlines()
        for i, linea in enumerate(linee):
            if (re.search(r'#\s*noqa', linea) or
                re.search(r'deadcode:\s*ignore', linea) or
                re.search(r'\bnodangle\b', linea, re.IGNORECASE) or
                re.search(r'#\[allow\(dead_code\)\]', linea)):
                self._linee_ignorate[percorso].add(i)

    def _linea_ignorata(self, percorso, num_linea):
        return num_linea in self._linee_ignorate.get(percorso, set())

    # -------------------------------------------------------------------------
    # Analisi degli import con regex (per tutti i linguaggi)
    # -------------------------------------------------------------------------
    def _analizza_import(self, percorso, testo_pulito, linguaggio):
        linee = testo_pulito.splitlines()
        if linguaggio in ['javascript', 'typescript']:
            for linea in linee:
                req = re.search(r'(?:const|let|var)\s+(\w+)\s*=\s*require\s*\(\s*[\'"]([^\'"]+)[\'"]\s*\)', linea)
                if req:
                    percorso_import = req.group(2)
                    destinazione = self._risolvi_percorso(percorso, percorso_import, linguaggio)
                    if destinazione:
                        self.mappa_import[percorso][req.group(1)] = (destinazione, "*")
                es = re.search(r'import\s+(.*?)\s+from\s+[\'"]([^\'"]+)[\'"]', linea)
                if es:
                    percorso_import = es.group(2)
                    destinazione = self._risolvi_percorso(percorso, percorso_import, linguaggio)
                    if destinazione:
                        spec = es.group(1).strip()
                        if '*' in spec:
                            m = re.match(r'\*\s+as\s+(\w+)', spec)
                            if m:
                                self.mappa_import[percorso][m.group(1)] = (destinazione, "*")
                        elif '{' in spec:
                            for parte_nome in spec.replace('{', '').replace('}', '').split(','):
                                m = re.match(r'^\s*(\w+)(?:\s+as\s+(\w+))?\s*$', parte_nome)
                                if m:
                                    locale = m.group(2) or m.group(1)
                                    self.mappa_import[percorso][locale] = (destinazione, m.group(1))
                        else:
                            self.mappa_import[percorso][spec] = (destinazione, "default")
            dynamic_imports = re.findall(r'import\s*\(\s*[\'"]([^\'"]+)[\'"]\s*\)', testo_pulito)
            for percorso_import in dynamic_imports:
                dest = self._risolvi_percorso(percorso, percorso_import, linguaggio)
                if dest:
                    self.mappa_import[percorso][percorso_import.split('/')[-1]] = (dest, "*")
                else:
                    self.import_incerti.append((percorso, f"import({percorso_import})"))
        elif linguaggio == 'rust':
            for linea in linee:
                match_use = re.search(r'use\s+([\w:]+)(?:::\*|::\{([^}]+)\}|::(\w+))?;', linea)
                if match_use:
                    base_percorso = match_use.group(1)
                    destinazione = self._risolvi_percorso(percorso, base_percorso, linguaggio)
                    if destinazione:
                        if match_use.group(2):
                            for sotto in match_use.group(2).split(','):
                                self.mappa_import[percorso][sotto.strip()] = (destinazione, sotto.strip())
                        elif match_use.group(3):
                            self.mappa_import[percorso][match_use.group(3)] = (destinazione, match_use.group(3))
                        else:
                            self.mappa_import[percorso][base_percorso.split('::')[-1]] = (destinazione, "*")
        elif linguaggio == 'go':
            import_match = re.findall(r'import\s+\((.*?)\)|import\s+"([^"]+)"', testo_pulito, re.DOTALL)
            for blocco, singolo in import_match:
                if blocco:
                    for m in re.finditer(r'["\']([^"\']+)["\']', blocco):
                        destinazione = self._risolvi_percorso(percorso, m.group(1), linguaggio)
                        if destinazione:
                            self.mappa_import[percorso][m.group(1).split('/')[-1]] = (destinazione, "*")
                elif singolo:
                    destinazione = self._risolvi_percorso(percorso, singolo, linguaggio)
                    if destinazione:
                        self.mappa_import[percorso][singolo.split('/')[-1]] = (destinazione, "*")
        elif linguaggio == 'php':
            for linea in linee:
                ns = re.search(r'use\s+([\w\\]+)(?:\s+as\s+(\w+))?;', linea)
                if ns:
                    destinazione = self._risolvi_percorso(percorso, ns.group(1), linguaggio)
                    if destinazione:
                        alias = ns.group(2) or ns.group(1).split('\\')[-1]
                        self.mappa_import[percorso][alias] = (destinazione, ns.group(1))
                req = re.search(r'(?:require(?:_once)?|include(?:_once)?)\s*[\'"]([^\'"]+)[\'"]', linea)
                if req:
                    destinazione = self._risolvi_percorso(percorso, req.group(1), linguaggio)
                    if destinazione:
                        self.mappa_import[percorso][req.group(1).split('/')[-1]] = (destinazione, "*")
        elif linguaggio == 'java':
            for linea in linee:
                imp = re.search(r'import\s+([\w.]+)(?:\.\*)?;', linea)
                if imp:
                    destinazione = self._risolvi_percorso(percorso, imp.group(1), linguaggio)
                    if destinazione:
                        parti = imp.group(1).split('.')
                        if '*' in imp.group(0):
                            self.mappa_import[percorso][parti[-1]] = (destinazione, "*")
                        else:
                            self.mappa_import[percorso][parti[-1]] = (destinazione, parti[-1])
        elif linguaggio == 'ruby':
            for linea in linee:
                req = re.search(r'require\s+[\'"]([^\'"]+)[\'"]', linea)
                if req:
                    destinazione = self._risolvi_percorso(percorso, req.group(1), linguaggio)
                    if destinazione:
                        self.mappa_import[percorso][req.group(1).split('/')[-1]] = (destinazione, "*")
                req_rel = re.search(r'require_relative\s+[\'"]([^\'"]+)[\'"]', linea)
                if req_rel:
                    destinazione = self._risolvi_percorso(percorso, req_rel.group(1), linguaggio)
                    if destinazione:
                        self.mappa_import[percorso][req_rel.group(1).split('/')[-1]] = (destinazione, "*")
                match_autoload = re.search(r'autoload\s+:(\w+),\s*[\'"]([^\'"]+)[\'"]', linea)
                if match_autoload:
                    nome_costante = match_autoload.group(1)
                    percorso_import = match_autoload.group(2)
                    destinazione = self._risolvi_percorso(percorso, percorso_import, linguaggio)
                    if destinazione:
                        self.mappa_import[percorso][nome_costante.lower()] = (destinazione, nome_costante)
        elif linguaggio == 'c_cpp':
            for linea in linee:
                inc = re.search(r'#include\s+[<"]([^>"]+)[>"]', linea)
                if inc:
                    destinazione = self._risolvi_percorso(percorso, inc.group(1), linguaggio)
                    if destinazione:
                        self.mappa_import[percorso][inc.group(1).split('/')[-1]] = (destinazione, "*")
        elif linguaggio == 'html':
            for match in re.finditer(r'<script\s+[^>]*src=["\']([^"\']+)["\']', testo_pulito, re.IGNORECASE):
                percorso_import = match.group(1)
                dest = self._risolvi_percorso(percorso, percorso_import, 'javascript')
                if dest:
                    self.mappa_import[percorso][os.path.basename(percorso_import)] = (dest, "*")
                else:
                    self.import_non_risolti.append((percorso, percorso_import, 'html'))
            for match in re.finditer(r'<link\s+[^>]*href=["\']([^"\']+)["\']', testo_pulito, re.IGNORECASE):
                percorso_import = match.group(1)
                if percorso_import.endswith('.css') or 'stylesheet' in match.group(0).lower():
                    dest = self._risolvi_percorso(percorso, percorso_import, 'css')
                    if dest:
                        self.mappa_import[percorso][os.path.basename(percorso_import)] = (dest, "*")
                    else:
                        self.import_non_risolti.append((percorso, percorso_import, 'html'))
        elif linguaggio == 'css':
            for match in re.finditer(r'@import\s+(?:url\(\s*["\']?|["\'])([^"\')\s]+)', testo_pulito, re.IGNORECASE):
                percorso_import = match.group(1).strip('"\'')
                dest = self._risolvi_percorso(percorso, percorso_import, 'css')
                if dest:
                    self.mappa_import[percorso][os.path.basename(percorso_import)] = (dest, "*")
                else:
                    self.import_non_risolti.append((percorso, percorso_import, 'css'))

    def _risolvi_import_dinamici(self, percorso, contenuto):
        """Analizza gli import dinamici di Python (importlib, __import__, getattr)."""
        try:
            albero = ast.parse(contenuto)
        except SyntaxError:
            return
        costanti = {}
        for nodo in ast.iter_child_nodes(albero):
            if isinstance(nodo, ast.Assign):
                for destinazione in nodo.targets:
                    if isinstance(destinazione, ast.Name):
                        val = None
                        if isinstance(nodo.value, ast.Constant) and isinstance(nodo.value.value, str):
                            val = nodo.value.value
                        elif isinstance(nodo.value, ast.JoinedStr):
                            parti = []
                            for parte in nodo.value.values:
                                if isinstance(parte, ast.Constant):
                                    parti.append(parte.value)
                                else:
                                    parti = None
                                    break
                            if parti is not None:
                                val = ''.join(parti)
                        if val:
                            costanti[destinazione.id] = val
        for nodo in ast.walk(albero):
            if isinstance(nodo, ast.Call):
                if isinstance(nodo.func, ast.Attribute) and isinstance(nodo.func.value, ast.Name):
                    if nodo.func.value.id == 'importlib' and nodo.func.attr == 'import_module':
                        if nodo.args:
                            arg = nodo.args[0]
                            nome_modulo = self._valuta_costante(arg, costanti)
                            if nome_modulo:
                                self._aggiungi_import_dinamico(percorso, nome_modulo)
                            else:
                                self.import_incerti.append((percorso, f"importlib.import_module({ast.dump(arg)})"))
                elif isinstance(nodo.func, ast.Name) and nodo.func.id == '__import__':
                    if nodo.args:
                        arg = nodo.args[0]
                        nome_modulo = self._valuta_costante(arg, costanti)
                        if nome_modulo:
                            self._aggiungi_import_dinamico(percorso, nome_modulo)
                        else:
                            self.import_incerti.append((percorso, f"__import__({ast.dump(arg)})"))
                elif isinstance(nodo.func, ast.Name) and nodo.func.id in ('getattr', '__getattr__'):
                    if len(nodo.args) >= 2:
                        if isinstance(nodo.args[0], ast.Name):
                            alias = nodo.args[0].id
                            nome_funzione = self._valuta_costante(nodo.args[1], costanti)
                            if nome_funzione:
                                if alias in self.mappa_import.get(percorso, {}):
                                    file_dest, _ = self.mappa_import[percorso][alias]
                                    self.chiamate_file[percorso].add(nome_funzione)
                                    self.chiamate_membro_file[percorso].add((alias, nome_funzione))
                                else:
                                    self.chiamate_file[percorso].add(nome_funzione)
                elif isinstance(nodo.func, ast.Attribute) and isinstance(nodo.func.value, ast.Name):
                    if nodo.func.attr == '__getattr__':
                        if nodo.args:
                            nome_arg = self._valuta_costante(nodo.args[0], costanti)
                            if nome_arg:
                                self.chiamate_file[percorso].add(nome_arg)
        for linea in contenuto.splitlines():
            match = re.search(r'#\s*zta-import:\s*([\w.]+)', linea)
            if match:
                self._aggiungi_import_dinamico(percorso, match.group(1))

    def _valuta_costante(self, nodo, costanti):
        """Cerca di risalire al valore di una costante nota a tempo di analisi."""
        if isinstance(nodo, ast.Constant) and isinstance(nodo.value, str):
            return nodo.value
        if isinstance(nodo, ast.Name) and nodo.id in costanti:
            return costanti[nodo.id]
        if isinstance(nodo, ast.JoinedStr):
            parti = []
            for parte in nodo.values:
                if isinstance(parte, ast.Constant):
                    parti.append(parte.value)
                elif isinstance(parte, ast.FormattedValue):
                    val = self._valuta_costante(parte.value, costanti)
                    if val is None:
                        return None
                    parti.append(val)
                else:
                    return None
            return ''.join(parti)
        if isinstance(nodo, ast.BinOp) and isinstance(nodo.op, ast.Add):
            sinistro = self._valuta_costante(nodo.left, costanti)
            destro = self._valuta_costante(nodo.right, costanti)
            if sinistro is not None and destro is not None:
                return sinistro + destro
        if isinstance(nodo, ast.Subscript):
            if isinstance(nodo.value, ast.Attribute):
                if isinstance(nodo.value.value, ast.Name) and nodo.value.value.id == 'os':
                    if nodo.value.attr == 'environ':
                        if isinstance(nodo.slice, ast.Constant) and isinstance(nodo.slice.value, str):
                            val_amb = os.environ.get(nodo.slice.value)
                            if val_amb:
                                return val_amb
        if isinstance(nodo, ast.Call):
            if isinstance(nodo.func, ast.Attribute):
                if isinstance(nodo.func.value, ast.Name) and nodo.func.value.id == 'os':
                    if nodo.func.attr == 'getenv' and nodo.args:
                        chiave = self._valuta_costante(nodo.args[0], costanti)
                        if chiave:
                            val_amb = os.environ.get(chiave)
                            if val_amb:
                                return val_amb
            if isinstance(nodo.func, ast.Name) and nodo.func.id == 'getattr':
                if len(nodo.args) >= 2:
                    nome_attr = self._valuta_costante(nodo.args[1], costanti)
                    if nome_attr:
                        return nome_attr
        return None

    def _aggiungi_import_dinamico(self, percorso, nome_modulo):
        if nome_modulo in self.mappa_import_statici:
            for percorso_mappato in self.mappa_import_statici[nome_modulo]:
                percorso_completo = self._normalizza_percorso(os.path.join(self.directory_radice, percorso_mappato))
                if os.path.isfile(percorso_completo):
                    self.mappa_import[percorso][nome_modulo.split('.')[-1]] = (percorso_completo, "*")
                    self.logger.info(f"Import dinamico risolto (mappa): {nome_modulo} -> {percorso_completo}")
                    return
        destinazione = self._risolvi_percorso(percorso, nome_modulo, 'python')
        if destinazione:
            self.mappa_import[percorso][nome_modulo.split('.')[-1]] = (destinazione, "*")
            self.logger.info(f"Import dinamico risolto (percorso): {nome_modulo} -> {destinazione}")
        else:
            self.import_incerti.append((percorso, nome_modulo))
            self.logger.warning(f"Import dinamico non risolto: {nome_modulo} in {percorso}")

    # =========================================================================
    # Parsing Python con AST nativo
    # =========================================================================

    def _analizza_python_con_ast(self, percorso, sorgente_str, byte_grezzi):
        """Estrae simboli e chiamate da un file Python usando il modulo ast."""
        try:
            albero = ast.parse(sorgente_str)
        except SyntaxError as e:
            self.logger.error(f"SyntaxError in {percorso}: {e}")
            if self._debug_mode:
                self._log_debug_error('ERROR', f"Python parse error in {percorso}", extra={
                    'phase': 'parsing',
                    'file': percorso,
                    'language': 'python',
                    'error_type': 'SyntaxError'
                }, exc_info=True)
            return False

        linee = sorgente_str.splitlines(keepends=True)
        offset_byte = [0]
        for linea in linee:
            offset_byte.append(offset_byte[-1] + len(linea.encode('utf-8')))

        try:
            for nodo in ast.walk(albero):
                if isinstance(nodo, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    num_linea = nodo.lineno - 1
                    col_offset = nodo.col_offset
                    if num_linea < len(offset_byte):
                        inizio_byte = offset_byte[num_linea] + col_offset
                        fine_byte = inizio_byte
                        if hasattr(nodo, 'end_lineno') and nodo.end_lineno is not None:
                            fine_linea = nodo.end_lineno - 1
                            fine_col = nodo.end_col_offset if hasattr(nodo, 'end_col_offset') else 0
                            if fine_linea < len(offset_byte):
                                fine_byte = offset_byte[fine_linea] + fine_col
                        else:
                            fine_byte = inizio_byte + len(nodo.name.encode('utf-8'))
                        self._aggiungi_simbolo(percorso, byte_grezzi, inizio_byte, nodo.name, 'python', fine_byte=fine_byte)
                elif isinstance(nodo, ast.Call) and isinstance(nodo.func, ast.Name):
                    self.chiamate_file[percorso].add(nodo.func.id)
                elif isinstance(nodo, ast.Import):
                    for alias in nodo.names:
                        destinazione = self._risolvi_percorso(percorso, alias.name, 'python')
                        if destinazione:
                            if os.path.isdir(destinazione):
                                try:
                                    for file_py in [f for f in os.listdir(destinazione) if f.endswith('.py')]:
                                        py_completo = self._normalizza_percorso(os.path.join(destinazione, file_py))
                                        self.mappa_import[percorso][alias.asname or alias.name.split('.')[-1]] = (py_completo, "*")
                                except Exception:
                                    pass
                            else:
                                self.mappa_import[percorso][alias.asname or alias.name.split('.')[-1]] = (destinazione, "*")
                elif isinstance(nodo, ast.ImportFrom) and nodo.module:
                    destinazione = self._risolvi_percorso(percorso, nodo.module, 'python', livello=nodo.level)
                    if destinazione:
                        if os.path.isdir(destinazione):
                            try:
                                for file_py in [f for f in os.listdir(destinazione) if f.endswith('.py')]:
                                    py_completo = self._normalizza_percorso(os.path.join(destinazione, file_py))
                                    for alias in nodo.names:
                                        self.mappa_import[percorso][alias.asname or alias.name] = (py_completo, alias.name)
                            except Exception:
                                pass
                        else:
                            for alias in nodo.names:
                                self.mappa_import[percorso][alias.asname or alias.name] = (destinazione, alias.name)
        except Exception as e:
            self.logger.error(f"Errore durante estrazione simboli Python da {percorso}: {e}")
            if self._debug_mode:
                self._log_debug_error('ERROR', f"Python extraction error in {percorso}", extra={
                    'phase': 'estrazione',
                    'file': percorso,
                    'language': 'python',
                    'error_type': type(e).__name__
                }, exc_info=True)
            return False

        self._rileva_eventi_python(percorso, albero, sorgente_str, offset_byte)
        return True

    def _rileva_eventi_python(self, percorso, albero, sorgente_str, offset_byte):
        """Registra chiamate .connect(), .emit() e decorator di route per Python."""
        for nodo in ast.walk(albero):
            if isinstance(nodo, ast.Call):
                if isinstance(nodo.func, ast.Attribute):
                    if nodo.func.attr == 'connect' and nodo.args:
                        for arg in nodo.args:
                            if isinstance(arg, ast.Name):
                                self._registro_eventi_python[percorso].add(('connect', arg.id))
                            elif isinstance(arg, ast.Attribute) and isinstance(arg.value, ast.Name):
                                self._registro_eventi_python[percorso].add(('connect', f"{arg.value.id}.{arg.attr}"))
                    if nodo.func.attr == 'emit':
                        if isinstance(nodo.func.value, ast.Name):
                            nome_segnale = nodo.func.value.id
                            self._registro_eventi_python[percorso].add(('emit', nome_segnale))
                if isinstance(nodo.func, ast.Attribute) and nodo.func.attr == 'send':
                    if isinstance(nodo.func.value, ast.Name):
                        self._registro_eventi_python[percorso].add(('send', nodo.func.value.id))
            if isinstance(nodo, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for decoratore in nodo.decorator_list:
                    if isinstance(decoratore, ast.Call):
                        if isinstance(decoratore.func, ast.Attribute):
                            if decoratore.func.attr in ('route', 'get', 'post', 'put', 'delete', 'patch'):
                                self._registro_eventi_python[percorso].add(('decorator_route', nodo.name))
                        elif isinstance(decoratore.func, ast.Name):
                            if decoratore.func.id in ('receiver', 'connect'):
                                self._registro_eventi_python[percorso].add(('decorator_signal', nodo.name))

    # -------------------------------------------------------------------------
    # Estrazione simboli con tree‑sitter
    # -------------------------------------------------------------------------
    def _estrai_simboli_treesitter(self, percorso, byte_grezzi, nodo_radice, linguaggio, lingua_ts=None):
        print(f"[LOG _estrai_simboli_treesitter] percorso={percorso}, tipo byte_grezzi={type(byte_grezzi).__name__}, lunghezza={len(byte_grezzi) if byte_grezzi is not None else 'None'}")
        if byte_grezzi is not None and not isinstance(byte_grezzi, (bytes, bytearray)):
            print(f"[LOG _estrai_simboli_treesitter] ATTENZIONE: byte_grezzi non è bytes/bytearray, è {type(byte_grezzi).__name__}. Converto.")
            if isinstance(byte_grezzi, str):
                byte_grezzi = byte_grezzi.encode('utf-8')
            else:
                try:
                    byte_grezzi = bytes(byte_grezzi)
                except Exception as e:
                    self.logger.error(f"Impossibile convertire byte_grezzi a bytes: {e}")
                    return 0

        if nodo_radice is None:
            self.logger.warning(f"Impossibile estrarre simboli da {percorso}: nodo radice nullo")
            return 0

        if isinstance(byte_grezzi, str):
            byte_utf8 = byte_grezzi.encode('utf-8')
        else:
            byte_utf8 = byte_grezzi

        self._costruisci_mappa_byte_a_linea(percorso, byte_utf8)

        def_patterns = [
            'function', 'method', 'class', 'interface', 'enum', 'type_alias',
            'namespace', 'module', 'declaration', 'definition', 'item',
            'specifier', 'struct', 'variable_declarator', 'variable_declaration',
            'lexical_declaration', 'signature', 'property', 'property_declaration',
            'method_signature', 'index_signature', 'call_signature'
        ]
        non_def = {
            'call_expression', 'member_expression', 'binary_expression', 'unary_expression',
            'parenthesized_expression', 'assignment_expression', 'arrow_function',
            'function_expression', 'class_expression', 'new_expression',
            'this_expression', 'super_expression', 'array', 'object', 'regex',
            'string', 'template_string', 'number', 'true', 'false', 'null', 'undefined',
            'expression_statement', 'if_statement', 'for_statement', 'while_statement',
            'do_statement', 'switch_statement', 'case_clause', 'default_clause',
            'return_statement', 'break_statement', 'continue_statement', 'throw_statement',
            'try_statement', 'catch_clause', 'finally_clause', 'labeled_statement',
            'import_statement', 'export_statement', 'default_export_statement',
            'comment', 'block_comment', 'line_comment', 'html_comment',
            'ERROR', 'MISSING'
        }

        simboli_trovati = 0
        cursor = _crea_cursore(nodo_radice)
        if cursor is None:
            self.logger.warning(f"Impossibile creare TreeCursor per {percorso}")
            return 0

        if self._debug_mode:
            self.logger.debug(f"[DIAG] Dump albero per {percorso}:")
            dump_str = self._dump_tree_to_string(nodo_radice, byte_utf8, max_depth=30)
            lines = dump_str.splitlines()
            for i, line in enumerate(lines[:50]):
                self.logger.debug(line)
            if len(lines) > 50:
                self.logger.debug(f"... e altri {len(lines)-50} nodi")
            self._verifica_grammatica(lingua_ts, linguaggio)

        def attraversa(c):
            nonlocal simboli_trovati
            if c.node is None:
                return
            nodo = c.node

            if hasattr(nodo, 'is_missing') and nodo.is_missing:
                if self._debug_mode:
                    self.logger.debug(f"[TS] Saltato nodo MISSING: {_get_node_type_safe(nodo, lingua_ts)}")
                return

            tipo = _get_node_type_safe(nodo, lingua_ts)

            if self._debug_mode:
                self.logger.debug(f"[TS] Nodo: {tipo}")

            is_def = any(p in tipo.lower() for p in def_patterns) and tipo not in non_def

            if is_def:
                nome_node = _get_node_child_by_field_name_safe(nodo, 'name')
                if nome_node is None:
                    for child in _get_node_children_safe(nodo):
                        ct = _get_node_type_safe(child, lingua_ts)
                        if ct in ('identifier', 'property_identifier', 'type_identifier'):
                            nome_node = child
                            break
                if nome_node is not None:
                    if hasattr(nome_node, 'is_missing') and nome_node.is_missing:
                        return
                    nome_grezzo = _get_node_text_safe(nome_node, byte_utf8)
                    if nome_grezzo:
                        nome_simbolo, troncato = self._normalizza_nome_simbolo(nome_grezzo)
                        if nome_simbolo:
                            inizio_byte = _get_node_start_byte_safe(nodo)
                            fine_byte = _get_node_end_byte_safe(nodo)
                            self._aggiungi_simbolo(percorso, byte_utf8, inizio_byte, nome_simbolo,
                                                   linguaggio, troncato, fine_byte=fine_byte)
                            simboli_trovati += 1
                            if self._debug_mode:
                                self.logger.debug(f"[TS] Estratto: {nome_simbolo} ({tipo})")

            if c.goto_first_child():
                while True:
                    attraversa(c)
                    if not c.goto_next_sibling():
                        break
                c.goto_parent()

        try:
            attraversa(cursor)
        except Exception as e:
            self.logger.error(f"[ERRORE ESTRAZIONE] {percorso}: {e}")
            self.logger.error(traceback.format_exc())
            if self._debug_mode:
                self._log_debug_error('ERROR', f"Tree-sitter extraction error in {percorso}", extra={
                    'phase': 'estrazione',
                    'file': percorso,
                    'language': linguaggio,
                    'error_type': type(e).__name__
                }, exc_info=True)
                self.logger.error("[DIAG] Dump albero al momento dell'errore:")
                dump_str = self._dump_tree_to_string(nodo_radice, byte_utf8, max_depth=20)
                self.logger.error(dump_str)
                dump_file = os.path.join(self.directory_quarantena, f"debug_error_{uuid.uuid4().hex}.txt")
                self._dump_tree_to_file(nodo_radice, byte_utf8, dump_file)
                self.logger.error(f"[DIAG] Dump salvato in {dump_file}")
            raise

        if simboli_trovati == 0 and not self.forza_regex:
            error_count = 0
            def count_errors(node):
                nonlocal error_count
                if node is None:
                    return
                if hasattr(node, 'type') and node.type in ('ERROR', 'MISSING'):
                    error_count += 1
                for child in _get_node_children_safe(node):
                    count_errors(child)
            count_errors(nodo_radice)
            if simboli_trovati == 0 or error_count > 0:
                self.logger.debug(f"Trovati {error_count} nodi ERROR/MISSING in {percorso}, attivo fallback.")
                self._fallback_utilizzato = True
                try:
                    self._analizza_con_regex(percorso, byte_utf8.decode('utf-8'), linguaggio)
                except Exception as regex_err:
                    self.logger.error(f"Fallback regex fallito per {percorso}: {regex_err}")
                    if self._debug_mode:
                        self._log_debug_error('ERROR', f"Regex fallback error in {percorso}", extra={
                            'phase': 'fallback',
                            'file': percorso,
                            'language': linguaggio,
                            'error_type': type(regex_err).__name__
                        }, exc_info=True)
            else:
                self._diagnostica_estrazione(percorso, nodo_radice, byte_utf8, linguaggio)
                self.logger.warning(f"Nessun simbolo in {percorso} ma albero valido. Vedi diagnostica sopra.")

        if linguaggio == 'typescript':
            self._file_ts_elaborati += 1
            self._simboli_ts_estratti += simboli_trovati

        return simboli_trovati

    # -------------------------------------------------------------------------
    # Estrazione chiamate con tree‑sitter
    # -------------------------------------------------------------------------
    def _estrai_chiamate_treesitter(self, percorso, byte_grezzi, nodo_radice, lingua_ts=None):
        if nodo_radice is None:
            return
        cursor = _crea_cursore(nodo_radice)
        if cursor is None:
            return
        def attraversa(c):
            if c.node is None:
                return
            tipo = _get_node_type_safe(c.node, lingua_ts)
            if tipo in ('call_expression', 'call'):
                for child in _get_node_children_safe(c.node):
                    ct = _get_node_type_safe(child, lingua_ts)
                    if ct == 'identifier':
                        nome = _get_node_text_safe(child, byte_grezzi)
                        if nome:
                            self.chiamate_file[percorso].add(nome)
                    elif ct in ('member_expression', 'attribute'):
                        obj = None
                        prop = None
                        for sub in _get_node_children_safe(child):
                            st = _get_node_type_safe(sub, lingua_ts)
                            if st in ('identifier', 'property_identifier', 'name'):
                                if obj is None:
                                    obj = _get_node_text_safe(sub, byte_grezzi)
                                else:
                                    prop = _get_node_text_safe(sub, byte_grezzi)
                        if obj and prop:
                            self.chiamate_membro_file[percorso].add((obj, prop))
            if c.goto_first_child():
                while True:
                    attraversa(c)
                    if not c.goto_next_sibling():
                        break
                c.goto_parent()
        attraversa(cursor)

    # -------------------------------------------------------------------------
    # Costruzione mappa import via tree‑sitter (per JS/TS)
    # -------------------------------------------------------------------------
    def _costruisci_mappa_import_treesitter(self, percorso, byte_grezzi, nodo_radice, linguaggio, lingua_ts=None):
        if linguaggio not in ('javascript', 'typescript'):
            return
        if nodo_radice is None:
            return
        cursor = _crea_cursore(nodo_radice)
        if cursor is None:
            return
        def attraversa(c):
            if c.node is None:
                return
            tipo = _get_node_type_safe(c.node, lingua_ts)
            if tipo == 'import_statement':
                import_path = None
                import_name = None
                for child in _get_node_children_safe(c.node):
                    ct = _get_node_type_safe(child, lingua_ts)
                    if ct == 'string':
                        import_path = _get_node_text_safe(child, byte_grezzi)
                    elif ct == 'import_clause':
                        for sub in _get_node_children_safe(child):
                            st = _get_node_type_safe(sub, lingua_ts)
                            if st == 'identifier':
                                import_name = _get_node_text_safe(sub, byte_grezzi)
                            elif st == 'namespace_import':
                                for ns in _get_node_children_safe(sub):
                                    if _get_node_type_safe(ns, lingua_ts) == 'identifier':
                                        import_name = _get_node_text_safe(ns, byte_grezzi)
                                        break
                            elif st == 'named_imports':
                                for spec in _get_node_children_safe(sub):
                                    if _get_node_type_safe(spec, lingua_ts) == 'import_specifier':
                                        for id_node in _get_node_children_safe(spec):
                                            if _get_node_type_safe(id_node, lingua_ts) in ('identifier', 'property_identifier'):
                                                import_name = _get_node_text_safe(id_node, byte_grezzi)
                                                break
                                        if import_name:
                                            break
                if import_name and import_path:
                    path_clean = import_path.strip('"\' ')
                    destinazione = self._risolvi_percorso(percorso, path_clean, linguaggio)
                    if destinazione:
                        self.mappa_import[percorso][import_name] = (destinazione, "*")
            if c.goto_first_child():
                while True:
                    attraversa(c)
                    if not c.goto_next_sibling():
                        break
                c.goto_parent()
        attraversa(cursor)

    # -------------------------------------------------------------------------
    # Parsing HTML con tree‑sitter e JavaScript inline
    # -------------------------------------------------------------------------
    def _analizza_html_con_treesitter(self, percorso, sorgente_str, byte_grezzi, nodo_radice):
        if nodo_radice is None:
            return
        lingua_ts, parser = PARSER_TREE_SITTER['html']
        cursor = _crea_cursore(nodo_radice)
        if cursor is None:
            return
        def attraversa(c):
            if c.node is None:
                return
            tipo = _get_node_type_safe(c.node, lingua_ts)
            if tipo in ('element', 'script_element', 'style_element'):
                for child in _get_node_children_safe(c.node):
                    if _get_node_type_safe(child, lingua_ts) == 'tag_name':
                        nome = _get_node_text_safe(child, byte_grezzi)
                        if nome:
                            start = _get_node_start_byte_safe(child)
                            if not self._linea_ignorata(percorso, self._offset_byte_a_linea(percorso, start, byte_grezzi)):
                                self._aggiungi_simbolo(percorso, byte_grezzi, start, nome, 'html')
            if c.goto_first_child():
                while True:
                    attraversa(c)
                    if not c.goto_next_sibling():
                        break
                c.goto_parent()
        attraversa(cursor)
        self._estrai_simboli_da_script_tag(percorso, byte_grezzi, nodo_radice, lingua_ts)

    # -------------------------------------------------------------------------
    # Estrazione di simboli da <script> inline
    # -------------------------------------------------------------------------
    def _estrai_simboli_da_script_tag(self, percorso, byte_grezzi, nodo_radice, lingua_ts_html):
        if nodo_radice is None:
            return 0

        voce_js = PARSER_TREE_SITTER.get('javascript')
        if voce_js is None:
            self.logger.debug("Parser JavaScript non disponibile, impossibile analizzare script tag")
            return 0

        _, parser_js = voce_js
        lingua_js = PARSER_TREE_SITTER['javascript'][0]
        simboli_trovati = 0

        cursor = _crea_cursore(nodo_radice)
        if cursor is None:
            return 0

        def attraversa(c):
            nonlocal simboli_trovati
            if c.node is None:
                return

            tipo = _get_node_type_safe(c.node, lingua_ts_html)

            if tipo == 'script_element':
                for child in _get_node_children_safe(c.node):
                    if _get_node_type_safe(child, lingua_ts_html) == 'raw_text':
                        js_code = _get_node_text_safe(child, byte_grezzi)
                        if js_code and js_code.strip():
                            try:
                                if isinstance(js_code, str):
                                    js_bytes = js_code.encode('utf-8')
                                else:
                                    js_bytes = js_code

                                js_albero, js_radice = _parse_sorgente(parser_js, js_bytes)
                                if js_radice is not None:
                                    self._estrai_simboli_treesitter(
                                        percorso, js_bytes, js_radice,
                                        'javascript', lingua_js
                                    )
                                    self._estrai_chiamate_treesitter(
                                        percorso, js_bytes, js_radice, lingua_js
                                    )
                                    simboli_trovati += 1
                            except Exception as e:
                                self.logger.debug(f"Errore parsing JS in script tag di {percorso}: {e}")

            if c.goto_first_child():
                while True:
                    attraversa(c)
                    if not c.goto_next_sibling():
                        break
                c.goto_parent()

        attraversa(cursor)
        return simboli_trovati

    # -------------------------------------------------------------------------
    # Orchestratore tree‑sitter (chiama tutti i sotto‑parser)
    # -------------------------------------------------------------------------
    def _analizza_con_treesitter(self, percorso, sorgente_str, byte_sorgente, linguaggio):
        print(f"[LOG _analizza_con_treesitter] percorso={percorso}, tipo byte_sorgente={type(byte_sorgente).__name__}, lunghezza={len(byte_sorgente) if byte_sorgente is not None else 'None'}")

        estensione = os.path.splitext(percorso)[1].lower()
        chiave_ts = linguaggio if estensione != '.tsx' else 'tsx'
        voce_parser = PARSER_TREE_SITTER.get(chiave_ts) or PARSER_TREE_SITTER.get(linguaggio)
        if voce_parser is None:
            raise KeyError(f"Parser non disponibile per {linguaggio}/{chiave_ts}")
        lingua_ts, parser = voce_parser

        try:
            albero, nodo_radice = _parse_sorgente(parser, byte_sorgente)
        except Exception as e:
            self.logger.error(f"[ERRORE PARSING] {percorso}: {e}")
            self.logger.error(traceback.format_exc())
            if self._debug_mode:
                self._log_debug_error('ERROR', f"Tree-sitter parse error in {percorso}", extra={
                    'phase': 'parsing',
                    'file': percorso,
                    'language': linguaggio,
                    'error_type': type(e).__name__
                }, exc_info=True)
                dump_file = os.path.join(self.directory_quarantena, f"debug_parse_error_{uuid.uuid4().hex}.txt")
                try:
                    with open(dump_file, 'w', encoding='utf-8') as df:
                        df.write(sorgente_str)
                    self.logger.error(f"[DIAG] Sorgente salvato in {dump_file}")
                except:
                    pass
            return False

        if albero is None or nodo_radice is None:
            self.logger.warning(f"[PARSING] Albero nullo per {percorso}. Attivo fallback regex.")
            self._fallback_utilizzato = True
            try:
                self._analizza_con_regex(percorso, sorgente_str, linguaggio)
            except Exception as e:
                self.logger.error(f"Fallback regex fallito per {percorso}: {e}")
                if self._debug_mode:
                    self._log_debug_error('ERROR', f"Regex fallback for null tree in {percorso}", extra={
                        'phase': 'fallback',
                        'file': percorso,
                        'language': linguaggio,
                        'error_type': type(e).__name__
                    }, exc_info=True)
                return False
            return True

        try:
            self._estrai_simboli_treesitter(percorso, byte_sorgente, nodo_radice, linguaggio, lingua_ts)
            self._estrai_chiamate_treesitter(percorso, byte_sorgente, nodo_radice, lingua_ts)
            self._costruisci_mappa_import_treesitter(percorso, byte_sorgente, nodo_radice, linguaggio, lingua_ts)
        except Exception as e:
            self.logger.error(f"[ERRORE DURANTE ESTRAZIONE] {percorso}: {e}")
            self.logger.error(traceback.format_exc())
            if self._debug_mode:
                self._log_debug_error('ERROR', f"Tree-sitter extraction failed for {percorso}", extra={
                    'phase': 'estrazione',
                    'file': percorso,
                    'language': linguaggio,
                    'error_type': type(e).__name__
                }, exc_info=True)
                self.logger.error("[DIAG] Dump dell'albero al momento dell'errore:")
                dump_str = self._dump_tree_to_string(nodo_radice, byte_sorgente, max_depth=20)
                self.logger.error(dump_str)
                dump_file = os.path.join(self.directory_quarantena, f"debug_crash_{uuid.uuid4().hex}.txt")
                self._dump_tree_to_file(nodo_radice, byte_sorgente, dump_file)
                self.logger.error(f"[DIAG] Dump salvato in {dump_file}")
            raise

        if linguaggio == 'html':
            self._analizza_html_con_treesitter(percorso, sorgente_str, byte_sorgente, nodo_radice)

        return True

    # -------------------------------------------------------------------------
    # Fallback a espressioni regolari (con pattern arricchiti per HTML)
    # -------------------------------------------------------------------------
    def _analizza_con_regex(self, percorso, contenuto, linguaggio):
        try:
            contenuto_pulito = _rimuovi_commenti_per_regex(contenuto, linguaggio)
            byte_grezzi = contenuto.encode('utf-8')
            self._costruisci_mappa_byte_a_linea(percorso, byte_grezzi)
            pattern_definizioni = {
                'python': [
                    r'^\s*(?:async\s+)?def\s+([^\W\d_]\w*)\s*\(',
                    r'^\s*class\s+([^\W\d_]\w*)\s*[:\(]',
                ],
                'javascript': [
                    r'function\s+([^\W\d_]\w*)\s*\(',
                    r'class\s+([^\W\d_]\w*)',
                    r'(?:const|let|var)\s+([^\W\d_]\w*)\s*=\s*(?:function|\()',
                    r'(?:const|let|var)\s+([^\W\d_]\w*)\s*=\s*\([^)]*\)\s*=>',
                ],
                'typescript': [
                    r'function\s+([^\W\d_]\w*)\s*\(',
                    r'class\s+([^\W\d_]\w*)',
                    r'interface\s+([^\W\d_]\w*)',
                    r'type\s+([^\W\d_]\w*)\s*=',
                    r'enum\s+([^\W\d_]\w*)',
                    r'(?:const|let|var)\s+([^\W\d_]\w*)\s*=\s*(?:function|\()',
                    r'(?:const|let|var)\s+([^\W\d_]\w*)\s*=\s*\([^)]*\)\s*=>',
                    r'export\s+const\s+([^\W\d_]\w*)\s*=\s*\([^)]*\)\s*=>',
                    r'export\s+function\s+([^\W\d_]\w*)\s*\(',
                    r'export\s+class\s+([^\W\d_]\w*)',
                    r'export\s+interface\s+([^\W\d_]\w*)',
                    r'export\s+type\s+([^\W\d_]\w*)\s*=',
                    r'export\s+enum\s+([^\W\d_]\w*)',
                    r'export\s+default\s+function\s+([^\W\d_]\w*)\s*\(',
                    r'export\s+default\s+class\s+([^\W\d_]\w*)',
                    r'export\s+default\s+([^\W\d_]\w*)',
                ],
                'java': [
                    r'(?:public|private|protected|static)?\s+\w+\s+([^\W\d_]\w*)\s*\(',
                    r'class\s+([^\W\d_]\w*)',
                    r'interface\s+([^\W\d_]\w*)',
                    r'enum\s+([^\W\d_]\w*)',
                ],
                'php': [
                    r'function\s+([^\W\d_]\w*)\s*\(',
                    r'class\s+([^\W\d_]\w*)',
                    r'interface\s+([^\W\d_]\w*)',
                    r'trait\s+([^\W\d_]\w*)',
                    r'(\$\w+)\s*=\s*function\s*\(',
                ],
                'ruby': [
                    r'def\s+([^\W\d_]\w*)',
                    r'class\s+([^\W\d_]\w*)',
                    r'module\s+([^\W\d_]\w*)',
                    r'def\s+self\.([^\W\d_]\w*)',
                    r'attr_accessor\s+:([^\W\d_]\w*)',
                    r'attr_reader\s+:([^\W\d_]\w*)',
                    r'attr_writer\s+:([^\W\d_]\w*)',
                ],
                'go': [
                    r'func\s+([^\W\d_]\w*)\s*\(',
                    r'type\s+([^\W\d_]\w*)\s+struct',
                    r'type\s+([^\W\d_]\w*)\s+interface',
                ],
                'rust': [
                    r'fn\s+([^\W\d_]\w*)',
                    r'struct\s+([^\W\d_]\w*)',
                    r'enum\s+([^\W\d_]\w*)',
                    r'trait\s+([^\W\d_]\w*)',
                    r'impl\s+\w+\s+for\s+([^\W\d_]\w*)',
                ],
                'c_cpp': [
                    r'\w+\s+([^\W\d_]\w*)\s*\([^)]*\)\s*\{',
                    r'class\s+([^\W\d_]\w*)',
                    r'struct\s+([^\W\d_]\w*)',
                    r'enum\s+([^\W\d_]\w*)',
                    r'namespace\s+([^\W\d_]\w*)',
                ],
                'html': [
                    r'<script[^>]*>\s*function\s+([^\W\d_]\w*)',
                    r'<script[^>]*>\s*(?:const|let|var)\s+([^\W\d_]\w*)\s*=\s*function',
                    r'<script[^>]*>\s*(?:const|let|var)\s+([^\W\d_]\w*)\s*=\s*\(',
                    r'<script[^>]*>\s*class\s+([^\W\d_]\w*)',
                    r'<script[^>]*>\s*(?:export\s+)?(?:async\s+)?function\s+([^\W\d_]\w*)\s*\(',
                    r'<script[^>]*>\s*(?:export\s+)?(?:const|let|var)\s+([^\W\d_]\w*)\s*=\s*(?:async\s*)?\([^)]*\)\s*=>',
                    r'<script[^>]*>\s*(?:export\s+)?(?:const|let|var)\s+([^\W\d_]\w*)\s*:\s*[^=]+\s*=',
                    r'<script[^>]*>\s*(?:export\s+)?interface\s+([^\W\d_]\w*)',
                    r'<script[^>]*>\s*(?:export\s+)?type\s+([^\W\d_]\w*)\s*=',
                    r'<script[^>]*>\s*(?:export\s+)?enum\s+([^\W\d_]\w*)',
                    r'<script[^>]*>\s*([^\W\d_]\w*)\s*:\s*function\s*\(',
                    r'<script[^>]*>\s*([^\W\d_]\w*)\s*\([^)]*\)\s*{',
                    r'<script[^>]*>\s*([^\W\d_]\w*)\s*=\s*\([^)]*\)\s*=>',
                ],
                'css': [
                    r'\.([a-zA-Z_][\w-]*)\s*\{',
                    r'#([a-zA-Z_][\w-]*)\s*\{',
                    r'@keyframes\s+([a-zA-Z_][\w-]*)',
                    r'@mixin\s+([a-zA-Z_][\w-]*)',
                ],
            }

            pattern = pattern_definizioni.get(linguaggio, [])
            for p in pattern:
                for match in re.finditer(p, contenuto_pulito, re.MULTILINE | re.DOTALL | re.UNICODE):
                    nome_simbolo = match.group(1).strip()
                    if not nome_simbolo:
                        continue
                    nome_pulito, troncato = self._normalizza_nome_simbolo(nome_simbolo)
                    if not nome_pulito:
                        continue
                    pos_byte = len(contenuto[:match.start()].encode('utf-8'))
                    fine_byte_stimata = pos_byte + len(match.group(0).encode('utf-8'))
                    self._aggiungi_simbolo(percorso, byte_grezzi, pos_byte, nome_pulito, linguaggio, troncato, fine_byte=fine_byte_stimata, fallback=True)

            chiamate_regex = re.findall(r'\b([^\W\d_]\w*)\s*\(', contenuto_pulito, re.UNICODE)
            for c in chiamate_regex:
                nome, _ = self._normalizza_nome_simbolo(c)
                if nome:
                    self.chiamate_file[percorso].add(nome)

            if linguaggio == 'ruby':
                for linea in contenuto_pulito.splitlines():
                    if re.match(r'^\s*(def|class|module|attr_|private|protected|public)\b', linea):
                        continue
                    for token in re.findall(r'\b([^\W\d_]\w*)\b', linea, re.UNICODE):
                        nome, _ = self._normalizza_nome_simbolo(token)
                        if nome:
                            self.chiamate_file[percorso].add(nome)

            if linguaggio == 'html':
                for m in re.finditer(r'<script[^>]+src=["\']([^"\']+)["\']', contenuto):
                    percorso_import = m.group(1)
                    destinazione = self._risolvi_percorso(percorso, percorso_import, 'javascript')
                    if destinazione:
                        self.mappa_import[percorso][percorso_import.split('/')[-1]] = (destinazione, "*")
        except Exception as e:
            self.logger.error(f"Errore nel fallback regex per {percorso}: {e}")
            if self._debug_mode:
                self._log_debug_error('ERROR', f"Regex fallback crash in {percorso}", extra={
                    'phase': 'fallback',
                    'file': percorso,
                    'language': linguaggio,
                    'error_type': type(e).__name__
                }, exc_info=True)

    # -------------------------------------------------------------------------
    # Normalizzazione e aggiunta di un simbolo alla lista
    # -------------------------------------------------------------------------
    def _normalizza_nome_simbolo(self, nome_grezzo):
        nome = ' '.join(nome_grezzo.split())
        match = re.search(r'([^\W\d_][\w-]*)', nome, re.UNICODE)
        if match:
            pulito = match.group(0)
            if pulito in LISTA_NERA_PAROLE_CHIAVE:
                return '', False
            if len(pulito) < 3 and pulito not in NOMI_CORTI_CONSENTITI:
                return '', False
            troncato = False
            if match.end() < len(nome) and not nome[match.end():].isspace():
                troncato = True
            return pulito, troncato
        return '', False

    def _aggiungi_simbolo(self, percorso, byte_grezzi_o_sorgente, inizio_byte, nome_simbolo, linguaggio,
                          troncato=False, fine_byte=None, euristico=False, fallback=False):
        if isinstance(byte_grezzi_o_sorgente, str):
            byte_grezzi = byte_grezzi_o_sorgente.encode('utf-8')
        else:
            byte_grezzi = byte_grezzi_o_sorgente
        self._costruisci_mappa_byte_a_linea(percorso, byte_grezzi)
        sid = f"{percorso}:{inizio_byte}:{nome_simbolo}"
        # Non usiamo più sid_raggiungibile per evitare duplicati
        num_linea = self._offset_byte_a_linea(percorso, inizio_byte, byte_grezzi)
        if self._linea_ignorata(percorso, num_linea):
            return
        self._hash_file[percorso] = self._hash_file.get(percorso, hashlib.sha256(byte_grezzi).hexdigest())
        if fine_byte is None:
            fine_byte = inizio_byte + len(nome_simbolo.encode('utf-8'))
        self.simboli[sid] = {
            'file': percorso,
            'inizio_byte': inizio_byte,
            'fine_byte': fine_byte,
            'linea': num_linea,
            'nome': nome_simbolo,
            'stato': 'unreachable',
            'linguaggio': linguaggio,
            'lista_bianca': nome_simbolo in self.lista_bianca,
            'troncato': troncato,
            'solo_test': False,
            'percorso_chiamate': [],
            'incerto': euristico,
            'aumento_confidenza': 0,
            'fallback': fallback,
        }

    def _marca_callback_raggiungibile(self, percorso_file, nome_simbolo, linguaggio):
        # ora il match è solo per sid (unico)
        for sid, d in self.simboli.items():
            if d['file'] == percorso_file and d['nome'] == nome_simbolo:
                d['stato'] = 'reachable'
                self.simboli_raggiungibili.add(sid)
                self.logger.debug(f"Callback marcato raggiungibile: {nome_simbolo} in {percorso_file}")
                return
        self.logger.debug(f"Callback ignorato (simbolo non trovato): {nome_simbolo} in {percorso_file}")

    # -------------------------------------------------------------------------
    # Risoluzione simboli da file barrel (es. index.ts che riesporta)
    # -------------------------------------------------------------------------
    def _risolvi_simbolo_barrel(self, percorso_file, nome_simbolo):
        risultati = []
        try:
            contenuto = self._e_file_di_testo(percorso_file)
            if not contenuto:
                return risultati

            pattern = r'export\s*\{\s*([^}]+)\s*\}\s*from\s*[\'"]([^\'"]+)[\'"]'
            for match in re.finditer(pattern, contenuto):
                esportati = match.group(1).strip()
                percorso_rel = match.group(2)
                target_path = self._risolvi_percorso(percorso_file, percorso_rel, 'typescript')
                if not target_path:
                    continue
                for item in esportati.split(','):
                    item = item.strip()
                    if ' as ' in item:
                        orig, alias = item.split(' as ')
                        orig = orig.strip()
                        alias = alias.strip()
                        if alias == nome_simbolo:
                            for sid, d in self.simboli.items():
                                if d['file'] == target_path and d['nome'] == orig:
                                    risultati.append((target_path, orig))
                                    break
                    else:
                        if item == nome_simbolo:
                            for sid, d in self.simboli.items():
                                if d['file'] == target_path and d['nome'] == item:
                                    risultati.append((target_path, item))
                                    break

            pattern_default = r'export\s*\{\s*default\s*as\s*(\w+)\s*\}\s*from\s*[\'"]([^\'"]+)[\'"]'
            for match in re.finditer(pattern_default, contenuto):
                alias = match.group(1)
                percorso_rel = match.group(2)
                if alias == nome_simbolo:
                    target_path = self._risolvi_percorso(percorso_file, percorso_rel, 'typescript')
                    if target_path:
                        for sid, d in self.simboli.items():
                            if d['file'] == target_path and d['nome'] == alias:
                                risultati.append((target_path, alias))
                                break

            pattern_star = r'export\s*\*\s*from\s*[\'"]([^\'"]+)[\'"]'
            for match in re.finditer(pattern_star, contenuto):
                percorso_rel = match.group(1)
                target_path = self._risolvi_percorso(percorso_file, percorso_rel, 'typescript')
                if target_path:
                    for sid, d in self.simboli.items():
                        if d['file'] == target_path and d['nome'] == nome_simbolo:
                            risultati.append((target_path, nome_simbolo))
                            break

        except Exception as e:
            self.logger.debug(f"Errore in _risolvi_simbolo_barrel per {percorso_file}: {e}")

        return risultati

    # -------------------------------------------------------------------------
    # Costruzione del grafo delle chiamate e analisi principale
    # -------------------------------------------------------------------------
    def _costruisci_grafo_chiamate_e_analizza(self):
        self.logger.info("Fase 2: Analisi del codice...")
        conteggio_cache = 0
        file_da_analizzare = []
        for percorso in self.tutti_i_file:
            contenuto = self._e_file_di_testo(percorso)
            if not contenuto:
                continue
            self._scansiona_direttive_ignora(percorso, contenuto)
            byte_grezzi = self._ottieni_byte_grezzi(percorso)
            if byte_grezzi is None:
                continue
            hash_corrente = hashlib.sha256(byte_grezzi).hexdigest()
            self._hash_file[percorso] = hash_corrente
            simboli_cache, mappa_import_cache, chiamate_membro_cache = self.cache_ast.ottieni(percorso, hash_corrente)
            if simboli_cache is not None:
                for sim in simboli_cache:
                    self.simboli[sim['sid']] = sim
                if mappa_import_cache:
                    for alias, (dest, orig) in mappa_import_cache.items():
                        self.mappa_import[percorso][alias] = (dest, orig)
                if chiamate_membro_cache:
                    for coppia in chiamate_membro_cache:
                        self.chiamate_membro_file[percorso].add(tuple(coppia))
                conteggio_cache += 1
            else:
                file_da_analizzare.append(percorso)
        if conteggio_cache:
            self.logger.info(f"Caricati {conteggio_cache} file dalla cache AST.")

        usa_parallelo = not (len(file_da_analizzare) <= 10 or platform.system() == 'Windows')
        if usa_parallelo:
            self.logger.info(f"Parallelizzazione analisi su {len(file_da_analizzare)} file...")
            with ProcessPoolExecutor() as esecutore:
                futures = {esecutore.submit(_analizza_file_singolo_lavoratore, p): p for p in file_da_analizzare}
                for futuro in as_completed(futures):
                    percorso_originale = futures[futuro]
                    try:
                        risultato = futuro.result()
                        if risultato:
                            p, byte_grezzi, testo, ling = risultato
                            self._analizza_file_singolo_lavoratore_callback(p, byte_grezzi, testo, ling)
                    except Exception as e:
                        self.logger.error(f"Analisi fallita per {percorso_originale} (worker): {e}")
                        self.file_non_analizzabili.add(percorso_originale)
                        if self._debug_mode:
                            self._log_debug_error('ERROR', f"Worker exception for {percorso_originale}", extra={
                                'phase': 'parsing',
                                'file': percorso_originale,
                                'language': 'unknown',
                                'error_type': type(e).__name__
                            }, exc_info=True)
        else:
            for percorso in file_da_analizzare:
                estensione = os.path.splitext(percorso)[1]
                linguaggio = next((l for l, d in REGISTRO_LINGUAGGI.items() if estensione in d['ext']), None)
                if linguaggio is None:
                    continue
                testo = self._e_file_di_testo(percorso)
                if not testo:
                    continue
                byte_grezzi = self._ottieni_byte_grezzi(percorso)
                try:
                    self._analizza_file_singolo_lavoratore_callback(percorso, byte_grezzi, testo, linguaggio)
                except Exception as e:
                    self.logger.error(f"Analisi fallita per {percorso}: {e}")
                    self.file_non_analizzabili.add(percorso)
                    if self._debug_mode:
                        self._log_debug_error('ERROR', f"Analysis exception for {percorso}", extra={
                            'phase': 'parsing',
                            'file': percorso,
                            'language': linguaggio,
                            'error_type': type(e).__name__
                        }, exc_info=True)

    def _analizza_file_singolo_lavoratore_callback(self, percorso, byte_grezzi, testo, linguaggio):
        sorgente_str = testo

        if linguaggio == 'python':
            success = self._analizza_python_con_ast(percorso, sorgente_str, byte_grezzi)
            if not success:
                return
            self._risolvi_import_dinamici(percorso, sorgente_str)
        else:
            analizzato = False
            if not self.forza_regex and linguaggio in PARSER_TREE_SITTER and not REGISTRO_LINGUAGGI.get(linguaggio, {}).get('regex_only'):
                try:
                    self._analizza_con_treesitter(percorso, sorgente_str, byte_grezzi, linguaggio)
                    analizzato = True
                except Exception as e:
                    self.logger.debug(f"Tree-sitter fallito per {percorso}: {e}")
                    if self._debug_mode:
                        self._log_debug_error('WARNING', f"Tree-sitter fallback needed for {percorso}", extra={
                            'phase': 'parsing',
                            'file': percorso,
                            'language': linguaggio,
                            'error_type': type(e).__name__
                        }, exc_info=True)

            if analizzato:
                conteggio_simboli = sum(1 for d in self.simboli.values() if d['file'] == percorso)
                if conteggio_simboli == 0 and sorgente_str.strip():
                    if linguaggio == 'typescript' and '.d.ts' in percorso:
                        self.logger.debug(f"File .d.ts senza simboli di definizione: {percorso}")
                        return
                    if not self._debug_mode:
                        self.logger.warning(
                            f"Nessun simbolo estratto da tree-sitter per {os.path.basename(percorso)}. "
                            f"Usa --debug per diagnostica dettagliata."
                        )
                    self.logger.warning(f"Forzo fallback regex per {percorso} (zero simboli)")
                    self._fallback_utilizzato = True
                    try:
                        self._analizza_con_regex(percorso, sorgente_str, linguaggio)
                    except Exception as regex_err:
                        self.logger.error(f"Fallback regex fallito per {percorso}: {regex_err}")
                        if self._debug_mode:
                            self._log_debug_error('ERROR', f"Regex fallback forced for {percorso}", extra={
                                'phase': 'fallback',
                                'file': percorso,
                                'language': linguaggio,
                                'error_type': type(regex_err).__name__
                            }, exc_info=True)
                        self.file_non_analizzabili.add(percorso)
                        return

            if not analizzato:
                self._fallback_utilizzato = True
                self.logger.warning(
                    f"Fallback regex attivato per {os.path.basename(percorso)} (linguaggio {linguaggio}). "
                    "L'accuratezza dell'analisi potrebbe essere ridotta."
                )
                try:
                    self._analizza_con_regex(percorso, sorgente_str, linguaggio)
                except Exception as e:
                    self.logger.error(f"Fallback regex fallito per {percorso}: {e}")
                    if self._debug_mode:
                        self._log_debug_error('ERROR', f"Regex fallback failure for {percorso}", extra={
                            'phase': 'fallback',
                            'file': percorso,
                            'language': linguaggio,
                            'error_type': type(e).__name__
                        }, exc_info=True)
                    self.file_non_analizzabili.add(percorso)
                    return

            for m in re.finditer(r'\b([^\W\d_]\w*)\s*(?:\.|::|->)\s*([^\W\d_]\w*)\s*(?:\(|;|\b)', sorgente_str, re.UNICODE):
                self.chiamate_membro_file[percorso].add((m.group(1), m.group(2)))

            estensione = os.path.splitext(percorso)[1]
            testo_pulito = pulisci_per_grep(sorgente_str, estensione, linguaggio)
            try:
                self._analizza_import(percorso, testo_pulito, linguaggio)
            except Exception as e:
                self.logger.error(f"Analisi import fallita per {percorso}: {e}")
                if self._debug_mode:
                    self._log_debug_error('ERROR', f"Import analysis failed for {percorso}", extra={
                        'phase': 'parsing',
                        'file': percorso,
                        'language': linguaggio,
                        'error_type': type(e).__name__
                    }, exc_info=True)

            pattern_callback = self.registro_callback.get(linguaggio, [])
            if self._fallback_utilizzato or not (linguaggio in PARSER_TREE_SITTER) or linguaggio == 'python':
                for pattern in pattern_callback:
                    for match in re.finditer(pattern, sorgente_str):
                        dopo = sorgente_str[match.end():].lstrip()
                        m_def = re.search(r'(?:def|class|function|func|fn|async\s+def|const\s+\w+\s*=\s*\(|let\s+\w+\s*=\s*\()\s+([^\W\d_]\w*)', dopo)
                        if m_def:
                            self._marca_callback_raggiungibile(percorso, m_def.group(1), linguaggio)
                        else:
                            self.punti_ingresso.add(percorso)

            if linguaggio == 'python' and percorso in self._registro_eventi_python:
                for tipo_evento, nome in self._registro_eventi_python[percorso]:
                    if tipo_evento in ('connect', 'send', 'decorator_route', 'decorator_signal'):
                        self._marca_callback_raggiungibile(percorso, nome, linguaggio)

        simboli_cache = []
        for sid, d in self.simboli.items():
            if d['file'] == percorso:
                simboli_cache.append(dict(d, sid=sid))
        self.cache_ast.imposta(percorso, self._hash_file.get(percorso, ''), simboli_cache,
                               mappa_import=dict(self.mappa_import.get(percorso, {})),
                               chiamate_membro=list(self.chiamate_membro_file.get(percorso, [])))

        self._costruisci_indice_grep_per_file(percorso, sorgente_str)

    def _costruisci_indice_grep_per_file(self, percorso, contenuto):
        parole = set(re.findall(r'\b[^\W\d_]\w*\b', contenuto, re.UNICODE))
        for parola in parole:
            if percorso not in self._indice_grep[parola]:
                self._indice_grep[parola].append(percorso)

    # -------------------------------------------------------------------------
    # Calcolo della raggiungibilità (BFS a partire dai punti di ingresso)
    # -------------------------------------------------------------------------

    # Nuovo helper per determinare se una funzione è di sola registrazione
    def _is_registration_function(self, nome_simbolo):
        """Restituisce True se il nome della funzione corrisponde a un pattern di registrazione noto."""
        if not nome_simbolo or nome_simbolo == '__entry__':
            return False
        for pattern in GO_REGISTRATION_PATTERNS:
            if nome_simbolo.startswith(pattern):
                return True
        return False

    def _marca_raggiungibilita(self):
        self.logger.info("Fase 3: Calcolo della raggiungibilità...")
        coda = deque()
        for ep in self.punti_ingresso:
            ha_simbolo = False
            for sid, d in self.simboli.items():
                if d['file'] == ep:
                    d['stato'] = 'reachable'
                    d['percorso_chiamate'] = [(ep, d['nome'])]
                    self.simboli_raggiungibili.add(sid)
                    coda.append((ep, d['nome'], [(ep, d['nome'])]))
                    ha_simbolo = True
            if not ha_simbolo:
                coda.append((ep, '__entry__', [(ep, '__entry__')]))

        coppie_visitate = set()
        while coda:
            percorso_file, nome_simbolo, percorso_chiamate = coda.popleft()
            coppia = (percorso_file, nome_simbolo)
            if coppia in coppie_visitate:
                continue
            coppie_visitate.add(coppia)

            # Se strict Go è attivo e il simbolo è una funzione di registrazione, non propagare
            if self.go_strict and self._is_registration_function(nome_simbolo):
                self.logger.debug(f"Strict mode: salto propagazione da registrazione {nome_simbolo} in {percorso_file}")
                continue

            self._propaga_chiamate(percorso_file, nome_simbolo, percorso_chiamate, coda)
            if nome_simbolo != '__entry__':
                self._propaga_eventi(percorso_file, nome_simbolo, percorso_chiamate, coda)
                self._propaga_eventi_python(percorso_file, nome_simbolo, percorso_chiamate, coda)

        self._propaga_ereditarieta(coda)

    def _propaga_chiamate(self, percorso_file, nome_simbolo, percorso_chiamate, coda):
        for nome_chiamato in self.chiamate_file.get(percorso_file, set()):
            self._risolvi_e_accoda(percorso_file, nome_chiamato, None, percorso_chiamate, coda)
        for (base, metodo) in self.chiamate_membro_file.get(percorso_file, set()):
            self._risolvi_e_accoda(percorso_file, metodo, base, percorso_chiamate, coda)

    def _risolvi_e_accoda(self, file_chiamante, nome_metodo, alias_base, percorso_chiamate, coda):
        file_destinazione = None
        if alias_base:
            if alias_base in self.mappa_import.get(file_chiamante, {}):
                file_destinazione, _ = self.mappa_import[file_chiamante][alias_base]
            elif alias_base in self.mappa_import_strutturata.get(file_chiamante, {}):
                file_destinazione, _ = self.mappa_import_strutturata[file_chiamante][alias_base]
            if file_destinazione:
                trovato = False
                for sid, d in self.simboli.items():
                    if d['file'] == file_destinazione and d['nome'] == nome_metodo and not d['lista_bianca']:
                        if d['stato'] != 'reachable':
                            d['stato'] = 'reachable'
                            d['percorso_chiamate'] = percorso_chiamate + [(file_destinazione, nome_metodo)]
                            self.simboli_raggiungibili.add(sid)
                            coda.append((file_destinazione, nome_metodo, d['percorso_chiamate']))
                        trovato = True
                if not trovato:
                    risolto = self._risolvi_simbolo_barrel(file_destinazione, nome_metodo)
                    if risolto:
                        for file_ris, nome_ris in risolto:
                            self._marca_simbolo_in_file(file_ris, nome_ris, percorso_chiamate, coda)
            else:
                self._marca_simbolo_globale(file_chiamante, nome_metodo, percorso_chiamate, coda)
        else:
            self._marca_simbolo_in_file(file_chiamante, nome_metodo, percorso_chiamate, coda)
            if nome_metodo in self.mappa_import.get(file_chiamante, {}):
                file_destinazione, originale = self.mappa_import[file_chiamante][nome_metodo]
                self._marca_simbolo_in_file(file_destinazione, originale, percorso_chiamate, coda)
            elif nome_metodo in self.mappa_import_strutturata.get(file_chiamante, {}):
                file_destinazione, originale = self.mappa_import_strutturata[file_chiamante][nome_metodo]
                self._marca_simbolo_in_file(file_destinazione, originale, percorso_chiamate, coda)
            if '*' in self.mappa_import.get(file_chiamante, {}):
                file_destinazione, _ = self.mappa_import[file_chiamante]['*']
                self._marca_simbolo_in_file(file_destinazione, nome_metodo, percorso_chiamate, coda)

    def _marca_simbolo_in_file(self, percorso_file, nome_simbolo, percorso_chiamate, coda):
        for sid, d in self.simboli.items():
            if d['file'] == percorso_file and d['nome'] == nome_simbolo and not d['lista_bianca'] and d['stato'] != 'reachable':
                d['stato'] = 'reachable'
                d['percorso_chiamate'] = percorso_chiamate + [(percorso_file, nome_simbolo)]
                self.simboli_raggiungibili.add(sid)
                coda.append((percorso_file, nome_simbolo, d['percorso_chiamate']))
                return True
        return False

    # Modificato: se go_strict attivo, non fare match globali per nome
    def _marca_simbolo_globale(self, file_chiamante, nome_simbolo, percorso_chiamate, coda):
        if self.go_strict:
            self.logger.debug(f"Strict mode: _marca_simbolo_globale disabilitata per {nome_simbolo}")
            return
        for sid, d in self.simboli.items():
            if d['nome'] == nome_simbolo and d['stato'] != 'reachable' and not d['lista_bianca']:
                d['stato'] = 'reachable'
                d['percorso_chiamate'] = percorso_chiamate + [(d['file'], nome_simbolo)]
                self.simboli_raggiungibili.add(sid)
                coda.append((d['file'], nome_simbolo, d['percorso_chiamate']))
                break

    def _propaga_eventi(self, percorso_file, nome_simbolo, percorso_chiamate, coda):
        for nome_evento, ascoltatori in self.ascoltatori_eventi.items():
            contenuto = self._e_file_di_testo(percorso_file)
            if contenuto and re.search(rf'\.emit\(\s*[\'"]{re.escape(nome_evento)}[\'"]\s*\)', contenuto):
                for file_ascoltatore, nome_ascoltatore in ascoltatori:
                    self._marca_simbolo_in_file(file_ascoltatore, nome_ascoltatore, percorso_chiamate, coda)
                    self.logger.debug(f"Evento '{nome_evento}' propagato: {nome_ascoltatore} in {file_ascoltatore}")

    def _propaga_eventi_python(self, percorso_file, nome_simbolo, percorso_chiamate, coda):
        for file_evento, eventi in self._registro_eventi_python.items():
            for tipo_evento, nome_evento in eventi:
                if tipo_evento == 'connect' and nome_evento == nome_simbolo:
                    self._marca_simbolo_in_file(file_evento, nome_simbolo, percorso_chiamate, coda)
                elif tipo_evento == 'emit' and nome_evento == nome_simbolo:
                    for file_conn, eventi_conn in self._registro_eventi_python.items():
                        for t_conn, n_conn in eventi_conn:
                            if t_conn == 'connect' and n_conn != nome_simbolo:
                                self._marca_callback_raggiungibile(file_conn, n_conn, 'python')

    def _propaga_ereditarieta(self, coda):
        cambiato = True
        while cambiato:
            cambiato = False
            for sid_classe, metodi in self.metodi_classe.items():
                sim_classe = self.simboli.get(sid_classe)
                if sim_classe and sim_classe['stato'] == 'reachable':
                    for sid_metodo in metodi:
                        sim_metodo = self.simboli.get(sid_metodo)
                        if sim_metodo and sim_metodo['stato'] != 'reachable':
                            sim_metodo['stato'] = 'reachable'
                            self.simboli_raggiungibili.add(sid_metodo)
                            coda.append((sim_metodo['file'], sim_metodo['nome'], sim_metodo.get('percorso_chiamate', [])))
                            cambiato = True
                    for sid_metodo in metodi:
                        sim_metodo = self.simboli.get(sid_metodo)
                        if sim_metodo and sim_metodo['stato'] == 'reachable':
                            nome_metodo = sim_metodo['nome']
                            for altra_classe_sid in self.mappa_override_metodi.get(nome_metodo, set()):
                                if altra_classe_sid != sid_classe:
                                    for altro_sid_metodo in self.metodi_classe.get(altra_classe_sid, set()):
                                        altro_sim = self.simboli.get(altro_sid_metodo)
                                        if altro_sim and altro_sim['nome'] == nome_metodo and altro_sim['stato'] != 'reachable':
                                            altro_sim['stato'] = 'reachable'
                                            self.simboli_raggiungibili.add(altro_sid_metodo)
                                            coda.append((altro_sim['file'], altro_sim['nome'], altro_sim.get('percorso_chiamate', [])))
                                            cambiato = True

    # -------------------------------------------------------------------------
    # Validazione ibrida e grep paranoico
    # -------------------------------------------------------------------------
    def _validazione_ibrida(self):
        self.logger.info("Fase 4b: Validazione ibrida (grafo + grep) ottimizzata...")
        candidati = [sid for sid, d in self.simboli.items() if d['stato'] == 'unreachable']
        for sid in candidati:
            d = self.simboli[sid]
            conf = self._calcola_confidenza(d['nome'], d['stato'], d['linguaggio'], d.get('troncato', False), d.get('fallback', False))
            if conf < 80:
                continue
            nome_simbolo = d['nome']
            if d['linguaggio'] == 'css':
                if self._risolvi_uso_selettore_css(nome_simbolo, d['file']):
                    d['stato'] = 'potentially_alive (hybrid)'
                    self.logger.debug(f"Validazione ibrida CSS: {nome_simbolo} trovato in JS/HTML, marcato potentially_alive")
                    continue
            if nome_simbolo in NOMI_GENERICI or nome_simbolo in self.nomi_generici_personalizzati:
                if self._grep_contestuale(nome_simbolo, d['file']):
                    d['stato'] = 'potentially_alive (contextual)'
                    d['aumento_confidenza'] = 20
                    self.logger.debug(f"Grep contestuale: {nome_simbolo} probabilmente vivo per contesto")
                    continue
            file_candidati = self._indice_grep.get(nome_simbolo, [])
            trovato_vivo = False
            for fpath in file_candidati:
                if fpath == d['file']:
                    continue
                contenuto = self._e_file_di_testo(fpath)
                if not contenuto:
                    continue
                if re.search(r'\b' + re.escape(nome_simbolo) + r'\b', contenuto):
                    if not self._e_file_di_test(fpath):
                        d['stato'] = 'potentially_alive (hybrid)'
                        self.logger.debug(f"Validazione ibrida: {nome_simbolo} trovato in {fpath}, marcato potentially_alive")
                        trovato_vivo = True
                        break
            if not trovato_vivo:
                d['confermato_ibrido'] = True
                self.logger.debug(f"Validazione ibrida: {nome_simbolo} confermato morto")

    def _grep_contestuale(self, nome_simbolo, file_origine):
        for ep in self.punti_ingresso:
            contenuto = self._e_file_di_testo(ep)
            if not contenuto:
                continue
            linee = contenuto.splitlines()
            for i, linea in enumerate(linee):
                if re.search(r'\b' + re.escape(nome_simbolo) + r'\b', linea):
                    finestra_contesto = linee[max(0,i-2):i+3]
                    testo_contesto = '\n'.join(finestra_contesto)
                    if re.search(r'if\s+__name__|@click\.|parser\.add_command|def\s+main|app\.run|flask\s+run|uvicorn|gunicorn|start\s*\(', testo_contesto):
                        return True
                    if re.search(r'command|cli|argparse|console_scripts|entry_points', testo_contesto, re.IGNORECASE):
                        return True
        return False

    def _risolvi_uso_selettore_css(self, selettore, file_origine):
        pulito = re.sub(r'^[.#]', '', selettore)
        for fpath in self.tutti_i_file:
            if fpath == file_origine:
                continue
            estensione = os.path.splitext(fpath)[1]
            if estensione not in {'.js', '.jsx', '.ts', '.tsx', '.html', '.htm'}:
                continue
            contenuto = self._e_file_di_testo(fpath)
            if not contenuto:
                continue
            if re.search(rf'(?:className|classList|getElementById|querySelector|querySelectorAll|$\(|\'|\")\s*[\'\"](?:.*?{re.escape(pulito)}.*?)[\'\"]', contenuto):
                return True
        return False

    def _grep_paranoico(self):
        self.logger.info("Fase 4: Verifica incrociata testuale...")
        candidati = [sid for sid, d in self.simboli.items() if d['stato'] == 'unreachable']
        for sid in candidati:
            d = self.simboli[sid]
            nome_simbolo = d['nome']
            file_origine = d['file']
            file_candidati = self._indice_grep.get(nome_simbolo, [])
            if not file_candidati:
                continue
            trovato_solo_in_test = True
            trovato_ovunque = False
            for percorso_dest in file_candidati:
                if percorso_dest == file_origine:
                    continue
                contenuto = self._e_file_di_testo(percorso_dest)
                if not contenuto:
                    continue
                estensione = os.path.splitext(percorso_dest)[1]
                linguaggio = next((l for l, d in REGISTRO_LINGUAGGI.items() if estensione in d['ext']), None)
                testo_pulito = pulisci_per_grep(contenuto, estensione, linguaggio)
                if re.search(rf'\b{re.escape(nome_simbolo)}\b', testo_pulito):
                    trovato_ovunque = True
                    if any(dyn in testo_pulito for dyn in PATTERN_CHIAMATE_DINAMICHE):
                        d['stato'] = 'potentially_alive (dynamic)'
                        trovato_solo_in_test = False
                    elif nome_simbolo in NOMI_GENERICI or nome_simbolo in self.nomi_generici_personalizzati:
                        if not self._e_file_di_test(percorso_dest):
                            d['stato'] = 'potentially_alive (textual)'
                            trovato_solo_in_test = False
                    else:
                        if not self._e_file_di_test(percorso_dest):
                            d['stato'] = 'potentially_alive (textual)'
                            trovato_solo_in_test = False
            if trovato_ovunque and trovato_solo_in_test:
                d['stato'] = 'potentially_alive (test_only)'
                d['solo_test'] = True

    def _calcola_confidenza(self, nome, stato, linguaggio, troncato=False, fallback=False):
        accuratezza = REGISTRO_LINGUAGGI.get(linguaggio, {}).get('accuratezza', 50)
        if stato == 'unreachable':
            base = 100 if linguaggio == 'python' else 80
        elif 'test_only' in stato:
            base = 60
        elif 'dynamic' in stato:
            base = 30
        elif 'textual' in stato:
            base = 50
        elif 'hybrid' in stato:
            base = 40
        else:
            base = 0
        if len(nome) < 4 and nome not in NOMI_CORTI_CONSENTITI:
            base -= 30
        if troncato:
            base -= 20
        if fallback:
            base -= 10
        return max(0, min(base, accuratezza))

    # -------------------------------------------------------------------------
    # Generazione del report JSON (corretta: conta solo sid univoci)
    # -------------------------------------------------------------------------
    def _genera_report(self):
        hasher = hashlib.sha256()
        for f in sorted(list(self.tutti_i_file)):
            h = self._hash_file.get(f, '')
            if h:
                hasher.update(h.encode('utf-8'))
        id_sessione = str(uuid.uuid4())
        # Ora contiamo solo i sid univoci presenti in simboli_raggiungibili
        num_raggiungibili = len(self.simboli_raggiungibili)
        report = {
            "versione_strumento": __version__,
            "id_sessione": id_sessione,
            "checksum": hasher.hexdigest(),
            "versione_python": sys.version,
            "piattaforma": platform.platform(),
            "timestamp_utc": datetime.datetime.utcnow().isoformat() + "Z",
            "totale_file": len(self.tutti_i_file),
            "simboli_raggiungibili": num_raggiungibili,
            "non_raggiungibili": [],
            "moduli_orfani": [],
            "avvisi": self.avvisi,
            "risoluzioni_fallite": [],
            "import_dinamici_incerti": self.import_incerti,
            "falsi_positivi_segnalati": self.falsi_positivi,
            "file_non_analizzabili": sorted(list(self.file_non_analizzabili)),
            "riepilogo": {"per_linguaggio": {}, "per_confidenza": {"alta": 0, "media": 0, "bassa": 0}},
            "tempi": self.tempi,
            "ambiente": {
                "tree_sitter_abilitato": True,
                "modalita_parser": "tree-sitter" if not self._fallback_utilizzato else "fallback-regex",
                "fallback_verificato": self._fallback_utilizzato,
                "validazione_ibrida": True,
                "fallback_regex_disponibile": True,
                "go_strict": self.go_strict,
            }
        }
        if self._debug_mode and self._debug_log_path:
            report["debug_log"] = self._debug_log_path

        file_vivi = set(d['file'] for d in self.simboli.values() if d['stato'] == 'reachable')
        file_vivi.update(self.punti_ingresso)
        self.moduli_orfani = self.tutti_i_file - file_vivi
        cambiato = True
        while cambiato:
            cambiato = False
            for candidato in list(self.moduli_orfani):
                importatori = [f for f in self.tutti_i_file if any(tf == candidato for tf, _ in
                              list(self.mappa_import.get(f, {}).values()) +
                              list(self.mappa_import_strutturata.get(f, {}).values()))]
                if importatori and any(imp not in self.moduli_orfani for imp in importatori):
                    self.moduli_orfani.remove(candidato)
                    cambiato = True

        for sid, d in self.simboli.items():
            conf = self._calcola_confidenza(d['nome'], d['stato'], d['linguaggio'], d.get('troncato', False), d.get('fallback', False))
            if conf > self.confidenza_minima and d['stato'] != 'reachable' and not d['lista_bianca']:
                if self._corrisponde_lista_bianca(d['file']):
                    continue
                if self._e_file_di_test(d['file']):
                    continue
                if not self.includi_solo_test and d.get('solo_test', False):
                    continue
                linea = d.get('linea', self._offset_byte_a_linea(d['file'], d['inizio_byte']))
                voce = {
                    "simbolo": d['nome'],
                    "file": d['file'],
                    "linea": linea,
                    "inizio_byte": d['inizio_byte'],
                    "confidenza": conf,
                    "stato": d['stato'],
                    "troncato": d.get('troncato', False),
                    "solo_test": d.get('solo_test', False),
                    "percorso_chiamate": d.get('percorso_chiamate', []),
                    "incerto": d.get('incerto', False),
                    "suggerimento": "Verifica manuale se il simbolo è realmente inutilizzato." if d.get('incerto') else "",
                }
                report['non_raggiungibili'].append(voce)
                ling = d['linguaggio']
                report['riepilogo']['per_linguaggio'][ling] = report['riepilogo']['per_linguaggio'].get(ling, 0) + 1
                if conf >= 80:
                    report['riepilogo']['per_confidenza']['alta'] += 1
                elif conf >= 60:
                    report['riepilogo']['per_confidenza']['media'] += 1
                else:
                    report['riepilogo']['per_confidenza']['bassa'] += 1

        percorso_report = os.path.join(os.getcwd(), 'deadcode_report.json')
        with open(percorso_report, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=4)
        self.logger.info(f"Report principale salvato in {percorso_report}")
        return len(report['non_raggiungibili']) + len(report['moduli_orfani'])

    def _corrisponde_lista_bianca(self, percorso_file):
        for pattern in self.pattern_lista_bianca:
            if fnmatch.fnmatch(percorso_file, pattern):
                return True
            try:
                if Path(percorso_file).match(pattern):
                    return True
            except Exception:
                pass
        for regex in self.regex_lista_bianca:
            if regex.search(percorso_file):
                return True
        return False

    # -------------------------------------------------------------------------
    # Quarantena e applicazione delle marcature (invariata)
    # -------------------------------------------------------------------------
    def applica_quarantena(self, id_obiettivo=None, applica_tutti=False):
        os.makedirs(self.directory_quarantena, exist_ok=True)
        if id_obiettivo:
            sid = id_obiettivo
            if sid not in self.simboli:
                self.logger.warning(f"ID simbolo non trovato: {sid}")
                return
            d = self.simboli[sid]
            if d['stato'] == 'reachable' or d['lista_bianca']:
                self.logger.info(f"Il simbolo {d['nome']} non è codice morto, salto.")
                return
            percorso_file = d['file']
            contenuto_originale = self._e_file_di_testo(percorso_file)
            byte_contenuto = contenuto_originale.encode('utf-8')
            linee = contenuto_originale.splitlines(keepends=True)
            inizio_byte = d['inizio_byte']
            fine_byte = d.get('fine_byte', inizio_byte)
            if fine_byte <= inizio_byte:
                fine_byte = len(byte_contenuto)
            linea_inizio = self._offset_byte_a_linea(percorso_file, inizio_byte, byte_contenuto)
            linea_fine = self._offset_byte_a_linea(percorso_file, fine_byte, byte_contenuto)
            commento_linea = REGISTRO_LINGUAGGI[d['linguaggio']]['commento_linea']
            for indice_linea in range(linea_inizio, min(linea_fine + 1, len(linee))):
                stripped = linee[indice_linea].lstrip()
                if not stripped.startswith(commento_linea):
                    linee[indice_linea] = f"{commento_linea} {linee[indice_linea].rstrip()}\n"
            stringa_id = str(uuid.uuid4())
            id_breve = stringa_id[:8]
            confidenza = self._calcola_confidenza(d['nome'], d['stato'], d['linguaggio'], d.get('troncato', False), d.get('fallback', False))
            testo_originale = "".join(linee[linea_inizio:linea_fine+1])
            percorso_patch = os.path.join(self.directory_quarantena, f"{stringa_id}.patch")
            with open(percorso_patch, 'w', encoding='utf-8') as pf:
                pf.write(testo_originale)
            nome_sicuro = re.sub(r'[^\w\-]', '_', d['nome'])
            marcatore = (
                f"{commento_linea if commento_linea else '// '}"
                f"AI_DEADCODE_DAVERIFICARE: Se questo codice è vivo, ripristinalo (rimuovi il commento). "
                f"Se è morto, segnalo (es 1 di 3) alla terza volta che viene segnalato può essere rimosso. "
                f"(QUESTO RIFERIMENTO è PRETTAMENTE PER L UTENTE ID ripristino: {id_breve} -> efdc restore {id_breve}).\n"
            )
            linee.insert(linea_inizio, marcatore)
            self._diario_manifest.append({
                "id": stringa_id,
                "tipo": "simbolo",
                "percorso_originale": percorso_file,
                "percorso_patch": percorso_patch,
                "marcatore": marcatore.strip(),
                "checksum_originale": self._hash_file.get(percorso_file, ''),
                "intervallo_linee": [linea_inizio, linea_fine + 1],
                "stato": "completed"
            })
            with tempfile.NamedTemporaryFile(mode='w', dir=os.path.dirname(percorso_file),
                                            delete=False, suffix='.tmp', encoding='utf-8') as tf:
                tf.writelines(linee)
                temp_name = tf.name
            self._sostituzione_sicura(temp_name, percorso_file)
            self._salva_manifest()
            self.logger.info(f"Simbolo {d['nome']} neutralizzato.")
        else:
            simboli_per_file = defaultdict(list)
            for sid, d in self.simboli.items():
                if d['stato'] == 'reachable' or d['lista_bianca'] or \
                   self._calcola_confidenza(d['nome'], d['stato'], d['linguaggio'], d.get('troncato', False), d.get('fallback', False)) <= self.confidenza_minima:
                    continue
                if self._e_file_di_test(d['file']):
                    continue
                simboli_per_file[d['file']].append(d)

            for percorso_file, simboli in simboli_per_file.items():
                if not os.path.exists(percorso_file):
                    continue
                contenuto_originale = self._e_file_di_testo(percorso_file)
                byte_contenuto = contenuto_originale.encode('utf-8')
                linee = contenuto_originale.splitlines(keepends=True)
                simboli.sort(key=lambda x: x['inizio_byte'], reverse=True)
                for sim in simboli:
                    inizio_byte = sim['inizio_byte']
                    fine_byte = sim.get('fine_byte', inizio_byte)
                    if fine_byte <= inizio_byte:
                        fine_byte = len(byte_contenuto)
                    linea_inizio = self._offset_byte_a_linea(percorso_file, inizio_byte, byte_contenuto)
                    linea_fine = self._offset_byte_a_linea(percorso_file, fine_byte, byte_contenuto)
                    commento_linea = REGISTRO_LINGUAGGI[sim['linguaggio']]['commento_linea']
                    for indice_linea in range(linea_inizio, min(linea_fine + 1, len(linee))):
                        stripped = linee[indice_linea].lstrip()
                        if not stripped.startswith(commento_linea):
                            linee[indice_linea] = f"{commento_linea} {linee[indice_linea].rstrip()}\n"
                    stringa_id = str(uuid.uuid4())
                    id_breve = stringa_id[:8]
                    confidenza = self._calcola_confidenza(sim['nome'], sim['stato'], sim['linguaggio'], sim.get('troncato', False), sim.get('fallback', False))
                    testo_originale = "".join(linee[linea_inizio:linea_fine+1])
                    percorso_patch = os.path.join(self.directory_quarantena, f"{stringa_id}.patch")
                    with open(percorso_patch, 'w', encoding='utf-8') as pf:
                        pf.write(testo_originale)
                    nome_sicuro = re.sub(r'[^\w\-]', '_', sim['nome'])
                    marcatore = (
                        f"{commento_linea if commento_linea else '// '}"
                        f"AI_DEADCODE_DAVERIFICARE: Se questo codice è vivo, ripristinalo (rimuovi il commento). "
                        f"Se è morto, segnalo (es 1 di 3) alla terza volta che viene segnalato può essere rimosso. "
                        f"(QUESTO RIFERIMENTO è PRETTAMENTE PER L UTENTE ID ripristino: {id_breve} -> efdc restore {id_breve}).\n"
                    )
                    linee.insert(linea_inizio, marcatore)
                    self._diario_manifest.append({
                        "id": stringa_id,
                        "tipo": "simbolo",
                        "percorso_originale": percorso_file,
                        "percorso_patch": percorso_patch,
                        "marcatore": marcatore.strip(),
                        "checksum_originale": self._hash_file.get(percorso_file, ''),
                        "intervallo_linee": [linea_inizio, linea_fine + 1],
                        "stato": "completed"
                    })
                    self._salva_manifest()
                with tempfile.NamedTemporaryFile(mode='w', dir=os.path.dirname(percorso_file),
                                                delete=False, suffix='.tmp', encoding='utf-8') as tf:
                    tf.writelines(linee)
                    temp_name = tf.name
                self._sostituzione_sicura(temp_name, percorso_file)
            self._salva_manifest()

    def _metti_in_quarantena_modulo(self, percorso_modulo):
        qid = str(uuid.uuid4())
        nome_dest = f"{qid}_{os.path.basename(percorso_modulo)}"
        percorso_dest = os.path.join(self.directory_quarantena, nome_dest)
        self._spostamento_sicuro(percorso_modulo, percorso_dest)
        self._diario_manifest.append({
            "id": qid,
            "tipo": "modulo",
            "percorso_originale": percorso_modulo,
            "percorso_quarantena": percorso_dest,
            "stato": "completed"
        })
        self._salva_manifest()

    # -------------------------------------------------------------------------
    # Ripristino elementi marcati (basato sul manifest)
    # -------------------------------------------------------------------------
    def ripristina_elemento(self, id_obiettivo):
        if not os.path.exists(self.percorso_manifest):
            self.logger.error("Nessun manifest trovato. Impossibile ripristinare.")
            return
        with open(self.percorso_manifest, 'r') as f:
            manifest = json.load(f)
        elemento = next((i for i in manifest if i['id'] == id_obiettivo or i['id'].startswith(id_obiettivo)), None)
        if not elemento:
            self.logger.warning(f"ID {id_obiettivo} non trovato nel manifest.")
            return
        if elemento['tipo'] == 'modulo':
            if os.path.exists(elemento['percorso_quarantena']):
                self._spostamento_sicuro(elemento['percorso_quarantena'], elemento['percorso_originale'])
                self.logger.info(f"Modulo ripristinato: {elemento['percorso_originale']}")
            else:
                self.logger.warning("File di quarantena mancante.")
        elif elemento['tipo'] == 'simbolo':
            if not os.path.exists(elemento['percorso_originale']):
                self.logger.warning("File originale non trovato.")
                return
            contenuto_corrente = self._e_file_di_testo(elemento['percorso_originale'])
            checksum_corrente = hashlib.sha256(contenuto_corrente.encode('utf-8')).hexdigest()
            linee = contenuto_corrente.splitlines(keepends=True)
            marcatore = elemento['marcatore']
            indice_marcatore = next((i for i, l in enumerate(linee) if marcatore in l), -1)
            if indice_marcatore == -1:
                self.logger.warning("Marcatore non trovato. Forse già ripristinato?")
                return
            with open(elemento['percorso_patch'], 'r', encoding='utf-8') as pf:
                linee_originali = pf.readlines()
            inizio_blocco = indice_marcatore + 1
            fine_blocco = inizio_blocco
            for k in range(inizio_blocco, len(linee)):
                if linee[k].lstrip().startswith(('#', '//', '/*', '<!--')) or \
                   any(parola_marcatore in linee[k] for parola_marcatore in ['AI_DEADCODE_REVIEW', 'AI_DEADCODE_DAVERIFICARE']):
                    fine_blocco = k
                else:
                    break
            if checksum_corrente == elemento.get('checksum_originale', ''):
                nuove_linee = linee[:indice_marcatore] + list(linee_originali) + linee[fine_blocco + 1:]
            else:
                diff = list(difflib.unified_diff(
                    linee_originali,
                    linee[inizio_blocco:fine_blocco + 1],
                    fromfile='originale',
                    tofile='corrente'
                ))
                if diff:
                    self.logger.warning("Il blocco è stato modificato. Applico merge conservativo (rimozione commenti).")
                    non_commentate = []
                    for linea in linee[inizio_blocco:fine_blocco + 1]:
                        stripped = linea.lstrip()
                        for prefisso in ['# ', '#', '// ', '//', '/* ', '/*']:
                            if stripped.startswith(prefisso):
                                linea = linea.replace(prefisso, '', 1).lstrip()
                                break
                        non_commentate.append(linea)
                    nuove_linee = linee[:indice_marcatore] + non_commentate + linee[fine_blocco + 1:]
                else:
                    nuove_linee = linee[:indice_marcatore] + list(linee_originali) + linee[fine_blocco + 1:]
            with tempfile.NamedTemporaryFile(mode='w', dir=os.path.dirname(elemento['percorso_originale']),
                                            delete=False, suffix='.tmp', encoding='utf-8') as tf:
                tf.writelines(nuove_linee)
                temp_name = tf.name
            self._sostituzione_sicura(temp_name, elemento['percorso_originale'])
            self.logger.info(f"Simbolo ripristinato correttamente.")
        nuovo_manifest = [i for i in manifest if i['id'] != id_obiettivo and not i['id'].startswith(id_obiettivo)]
        with open(self.percorso_manifest, 'w') as f:
            json.dump(nuovo_manifest, f, indent=2)

    # -------------------------------------------------------------------------
    # Pulizia risorse temporanee
    # -------------------------------------------------------------------------
    def _pulisci_risorse_temporanee(self):
        self.cache_ast.distruggi()

    # -------------------------------------------------------------------------
    # Esecuzione completa dell'audit
    # -------------------------------------------------------------------------
    def esegui_audit(self):
        self._ripristina_da_manifest()
        try:
            self._percorso_sicuro(self.directory_radice)
        except ValueError as e:
            self.logger.error(f"[ACCESSO VIETATO] {e}")
            sys.exit(3)

        tempo_inizio = time.time()
        try:
            t0 = time.time()
            try:
                self._scopri_ambiente()
            except Exception as e:
                self.logger.error(f"Errore fatale in discovery: {e}")
                if self._debug_mode:
                    self._log_debug_error('ERROR', "Discovery phase failed", extra={'phase': 'discovery'}, exc_info=True)
                raise
            self.tempi['discovery'] = time.time() - t0

            t0 = time.time()
            try:
                self._costruisci_grafo_chiamate_e_analizza()
            except Exception as e:
                self.logger.error(f"Errore fatale in parsing: {e}")
                if self._debug_mode:
                    self._log_debug_error('ERROR', "Parsing phase failed", extra={'phase': 'parsing'}, exc_info=True)
                raise
            self.tempi['parsing'] = time.time() - t0

            t0 = time.time()
            try:
                self._marca_raggiungibilita()
            except Exception as e:
                self.logger.error(f"Errore fatale in reachability: {e}")
                if self._debug_mode:
                    self._log_debug_error('ERROR', "Reachability phase failed", extra={'phase': 'raggiungibilita'}, exc_info=True)
                raise
            self.tempi['raggiungibilita'] = time.time() - t0

            t0 = time.time()
            try:
                self._grep_paranoico()
            except Exception as e:
                self.logger.error(f"Errore fatale in grep paranoico: {e}")
                if self._debug_mode:
                    self._log_debug_error('ERROR', "Paranoid grep phase failed", extra={'phase': 'grep'}, exc_info=True)
                raise
            self.tempi['grep_paranoico'] = time.time() - t0

            t0 = time.time()
            try:
                self._validazione_ibrida()
            except Exception as e:
                self.logger.error(f"Errore fatale in validazione ibrida: {e}")
                if self._debug_mode:
                    self._log_debug_error('ERROR', "Hybrid validation phase failed", extra={'phase': 'validazione'}, exc_info=True)
                raise
            self.tempi['validazione_ibrida'] = time.time() - t0

            conteggio_morti = self._genera_report()
            tempo_totale = time.time() - tempo_inizio
            self.logger.info(f"Analisi completata in {tempo_totale:.2f} secondi.")
            print(f"\n[RIEPILOGO] File analizzati: {len(self.tutti_i_file)}")
            print(f"Simboli totali: {len(self.simboli)}")
            print(f"Simboli raggiungibili: {len(self.simboli_raggiungibili)}")
            print(f"Codice morto trovato (simboli+orfani): {conteggio_morti}")
            if self.go_strict:
                print("[INFO] Modalità Go strict attiva: propagazione limitata per funzioni di registrazione.")
            if self._file_ts_elaborati > 0:
                print(f"[DIAG TS] File TypeScript processati: {self._file_ts_elaborati}, simboli estratti: {self._simboli_ts_estratti}")
        finally:
            self._pulisci_risorse_temporanee()
            for gestore in self.logger.handlers[:]:
                gestore.close()
                self.logger.removeHandler(gestore)

    # -------------------------------------------------------------------------
    # Test automatico (verifica funzionamento di base) – invariato
    # -------------------------------------------------------------------------
    @staticmethod
    def autotest():
        print(f"[AUTOTEST] Easy Fix DeadCode Auditor v{__version__} - Verifica funzionamento")
        dir_temp = tempfile.mkdtemp()
        auditor = None
        try:
            main_py = os.path.join(dir_temp, "main.py")
            helper_py = os.path.join(dir_temp, "helper.py")
            with open(main_py, "w") as f:
                f.write("from helper import viva\nviva()\n")
            with open(helper_py, "w") as f:
                f.write("def viva():\n    pass\ndef morta():\n    pass\n")

            ts_main = os.path.join(dir_temp, "main.ts")
            ts_helper = os.path.join(dir_temp, "helper.ts")
            with open(ts_main, "w") as f:
                f.write("import { viva } from './helper';\n viva();\n")
            with open(ts_helper, "w") as f:
                f.write("export function viva(): void {}\n export function morta(): void {}\n")

            html_file = os.path.join(dir_temp, "index.html")
            with open(html_file, "w") as f:
                f.write("<html><head><title>Test</title></head><body><script>function hello(){}</script></body></html>")

            auditor = DeadCodeAuditor(dir_temp)
            main_py = auditor._normalizza_percorso(main_py)
            helper_py = auditor._normalizza_percorso(helper_py)
            ts_main = auditor._normalizza_percorso(ts_main)
            ts_helper = auditor._normalizza_percorso(ts_helper)
            html_file = auditor._normalizza_percorso(html_file)

            auditor.punti_ingresso.add(main_py)
            auditor.punti_ingresso.add(ts_main)
            auditor.forza_regex = False

            auditor._scopri_ambiente()
            auditor._costruisci_grafo_chiamate_e_analizza()
            auditor._marca_raggiungibilita()
            auditor._grep_paranoico()
            auditor._validazione_ibrida()

            viva_raggiungibile = any(d['stato'] == 'reachable' for sid, d in auditor.simboli.items() if 'viva' in d['nome'] and d['file'] == helper_py)
            morta_raggiungibile = any(d['stato'] == 'reachable' for sid, d in auditor.simboli.items() if 'morta' in d['nome'] and d['file'] == helper_py)
            assert viva_raggiungibile, "viva non è raggiungibile (Python)"
            assert not morta_raggiungibile, "morta è raggiungibile (falso positivo Python)"

            ts_viva_raggiungibile = any(d['stato'] == 'reachable' for sid, d in auditor.simboli.items() if 'viva' in d['nome'] and d['file'] == ts_helper)
            ts_morta_raggiungibile = any(d['stato'] == 'reachable' for sid, d in auditor.simboli.items() if 'morta' in d['nome'] and d['file'] == ts_helper)
            assert ts_viva_raggiungibile, "viva non è raggiungibile (TypeScript)"
            assert not ts_morta_raggiungibile, "morta è raggiungibile (falso positivo TypeScript)"

            html_simboli = [d for sid, d in auditor.simboli.items() if d['linguaggio'] == 'html']
            assert len(html_simboli) >= 1, "Nessun simbolo estratto da HTML"

            print("[AUTOTEST] SUPERATO!")
            return True
        except Exception as e:
            print(f"[AUTOTEST FALLITO] {e}")
            import traceback
            traceback.print_exc()
            return False
        finally:
            if auditor is not None:
                auditor._pulisci_risorse_temporanee()
            shutil.rmtree(dir_temp, ignore_errors=True)

# =============================================================================
# Interfaccia a riga di comando (aggiornata con opzioni go-strict)
# =============================================================================

def main():
    if len(sys.argv) < 2:
        print("Utilizzo: efdc <comando> [opzioni]")
        print("Comandi disponibili: audit, apply, restore")
        print("Eseguire 'efdc audit --help' per le opzioni di audit.")
        sys.exit(1)

    cmd = sys.argv[1].lower()

    if cmd == 'restore':
        parser = argparse.ArgumentParser(prog='efdc restore')
        parser.add_argument('percorso', nargs='?', default='.', help='Cartella del progetto (contiene __deadcode_quarantine__)')
        parser.add_argument('id', help='ID dell\'elemento da ripristinare')
        args = parser.parse_args(sys.argv[2:])
        auditor = DeadCodeAuditor(args.percorso)
        auditor.ripristina_elemento(args.id)
        return

    elif cmd == 'apply':
        parser = argparse.ArgumentParser(prog='efdc apply')
        parser.add_argument('percorso', nargs='?', default='.', help='Cartella del progetto analizzato')
        parser.add_argument('--id', help='ID specifico del simbolo da neutralizzare')
        parser.add_argument('--all', action='store_true', help='Applica tutte le neutralizzazioni dal report')
        args = parser.parse_args(sys.argv[2:])
        auditor = DeadCodeAuditor(args.percorso)
        auditor.esegui_audit()
        auditor.applica_quarantena(id_obiettivo=args.id, applica_tutti=args.all)
        return

    elif cmd == 'audit':
        parser = argparse.ArgumentParser(prog='efdc audit', description=f"Easy Fix DeadCode Auditor v{__version__}")
        parser.add_argument("percorso", nargs="?", default=".", help="Cartella del progetto da analizzare")
        parser.add_argument("--min-confidence", type=int, default=70, help="Soglia minima di confidenza (0-100, default 70)")
        parser.add_argument("--force-regex", action="store_true", help="Forza il parsing via regex invece di tree-sitter")
        parser.add_argument("--autotest", action="store_true", help="Esegue il test automatico e termina")
        parser.add_argument("--debug", action="store_true", help="Abilita debug avanzato (dump albero, diagnostica, log errori persistente)")
        parser.add_argument("--go-strict", dest="go_strict", action="store_true", default=None,
                            help="Forza la modalità strict per Go (evita la propagazione da funzioni di registrazione)")
        parser.add_argument("--no-go-strict", dest="go_strict", action="store_false", default=None,
                            help="Disabilita la modalità strict per Go (comportamento originale)")
        args = parser.parse_args(sys.argv[2:])

        if args.autotest:
            sys.exit(0 if DeadCodeAuditor.autotest() else 2)

        auditor = DeadCodeAuditor(
            directory_radice=args.percorso,
            confidenza_minima=args.min_confidence,
            forza_regex=args.force_regex,
            go_strict=args.go_strict  # None = auto
        )
        if args.debug:
            auditor.set_debug_mode(True)
        auditor.esegui_audit()
    else:
        print(f"Comando sconosciuto: {cmd}")
        print("Utilizzo: efdc audit|apply|restore ...")
        sys.exit(1)

if __name__ == "__main__":
    main()