def test_benchmark_exists():
    import json
    from pathlib import Path
    p = Path(__file__).resolve().parents[1] / 'data' / 'benchmark.jsonl'
    lines = [l for l in p.read_text().splitlines() if l.strip()]
    assert len(lines) >= 1
