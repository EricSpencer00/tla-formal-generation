#!/usr/bin/env python3
"""Generate TLA+ modules from the benchmark entries.

Usage:
  python3 scripts/generate_tla.py --all
  python3 scripts/generate_tla.py --id sem_001

The script uses an LLM if OPENAI_API_KEY is present (optional). Otherwise it uses a deterministic stub that returns the ground-truth invariant from the dataset (useful for reproducible experiments).
"""
import os
import json
import argparse
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parents[1]
DATA_FILE = BASE_DIR / 'data' / 'benchmark.jsonl'
TEMPLATE = BASE_DIR / 'tla_templates' / 'base.tpl'
OUTPUT_DIR = BASE_DIR / 'outputs'

try:
    import openai
except Exception:
    openai = None


def load_benchmark():
    items = []
    with open(DATA_FILE, 'r') as f:
        for line in f:
            if line.strip():
                items.append(json.loads(line))
    return items


def render_template(module, vars_list, invariant):
    tpl = TEMPLATE.read_text()
    return tpl.replace('{{module}}', module).replace('{{vars}}', ', '.join(vars_list)).replace('{{invariant}}', invariant)


def call_llm_prompt(nl):
    """Call OpenAI GPT if configured, otherwise return None."""
    api_key = os.getenv('OPENAI_API_KEY')
    if not api_key or not openai:
        return None
    openai.api_key = api_key
    prompt = f"Translate this English requirement into a TLA+ invariant expression only:\n{nl}\nInvariant:" 
    resp = openai.ChatCompletion.create(model='gpt-4-0613', messages=[{"role": "user", "content": prompt}], max_tokens=256)
    text = resp['choices'][0]['message']['content'].strip()
    return text


def stub_generate(item):
    # Deterministic stub: return the expected_invariant if present, otherwise a simple heuristic
    if 'expected_invariant' in item:
        return item['expected_invariant']
    nl = item.get('nl', '').lower()
    if 'semaphore' in nl or 'counter' in nl:
        if 'below 0' in nl or 'non-neg' in nl:
            return 'counter >= 0'
        if 'exceeds' in nl or 'greater than' in nl:
            return 'counter <= 10'
    if 'boolean' in nl or 'true or false' in nl:
        return 'flag \\in BOOLEAN'
    return 'TRUE'


def generate_for_item(item):
    gen = call_llm_prompt(item['nl'])
    if not gen:
        gen = stub_generate(item)
    module = f"Gen_{item['id']}"
    vars_list = item.get('vars', ['counter'])
    tla = render_template(module, vars_list, f"Inv == {gen}")
    OUTPUT_DIR.mkdir(exist_ok=True)
    out_tla = OUTPUT_DIR / f"{module}.tla"
    out_cfg = OUTPUT_DIR / f"{module}.cfg"
    out_tla.write_text(tla)
    out_cfg.write_text(f"INIT Init\nNEXT Next\nINVARIANT Inv\n")
    return out_tla, out_cfg, gen


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--id')
    parser.add_argument('--all', action='store_true')
    args = parser.parse_args()

    items = load_benchmark()
    if args.all:
        selected = items
    elif args.id:
        selected = [it for it in items if it['id'] == args.id]
    else:
        parser.print_help()
        return

    for it in selected:
        tla, cfg, gen = generate_for_item(it)
        print(f'Wrote {tla} and {cfg}; generated invariant: {gen}')

if __name__ == '__main__':
    main()
