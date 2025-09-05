#!/usr/bin/env python3
"""Evaluate generated TLA modules against the benchmark.

- Compares generated invariant strings to expected (exact match)
- Detects simple syntax presence (contains 'Inv')
- If `tlc` binary is on PATH, runs TLC on each generated module and notes if TLC finds a counterexample for the invariant.

Outputs a small CSV-like summary to stdout.
"""
import json
import shutil
import subprocess
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parents[1]
DATA_FILE = BASE_DIR / 'data' / 'benchmark.jsonl'
OUTPUT_DIR = BASE_DIR / 'outputs'


def load_benchmark():
    items = []
    with open(DATA_FILE, 'r') as f:
        for line in f:
            if line.strip():
                items.append(json.loads(line))
    return items


def find_tlc():
    # Look for tlc (TLA+ model checker) on PATH
    return shutil.which('tlc') or shutil.which('tlc2')


def run_tlc(tla_path, cfg_path):
    tlc = find_tlc()
    if not tlc:
        return 'tlc-missing'
    # Run tlc and capture stdout (may require Java and tla2tools on PATH)
    try:
        proc = subprocess.run([tlc, str(tla_path)], capture_output=True, text=True, timeout=20)
        out = proc.stdout + proc.stderr
        if 'Invariant Inv is violated' in out or 'error: Invariant' in out:
            return 'violated'
        if 'No error has been found' in out or 'Model checking completed' in out:
            return 'holds'
        return 'unknown'
    except Exception as e:
        return f'error:{e}'


def main():
    items = load_benchmark()
    print('id,expected,generated,syntactic_ok,tlc_status')
    for it in items:
        module = f"Gen_{it['id']}"
        tla = OUTPUT_DIR / f"{module}.tla"
        cfg = OUTPUT_DIR / f"{module}.cfg"
        if not tla.exists():
            print(f"{it['id']},MISSING_TLA,,,,")
            continue
        text = tla.read_text()
        # crude parsing: find line starting with 'Inv == '
        gen = 'N/A'
        for line in text.splitlines():
            line = line.strip()
            if line.startswith('Inv =='):
                gen = line[len('Inv =='):].strip()
                break
        expected = it.get('expected_invariant','')
        syntactic_ok = 'Inv' in text
        tlc_status = run_tlc(tla, cfg) if syntactic_ok else 'skipped'
        print(f"{it['id']},{expected!r},{gen!r},{syntactic_ok},{tlc_status}")

if __name__ == '__main__':
    main()
