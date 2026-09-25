#!/usr/bin/env python3
"""Streaming test for lean-geospatial-prover.

Generates a JSONL input at run time (nothing is stored in the repository),
feeds it to the prover in one process and checks:

- the prover exits with 0;
- there is one answer per non-blank input line, in input order (by id);
- each request gets the expected answer, malformed lines give an error,
  and the lines after them are still answered.

A small stack makes a stack that grows per line fail quickly, so CI can use
a few thousand lines instead of hundreds of thousands:

    python3 scripts/prover_stream_test.py --lines 20000 --stack-kb 256   # CI
    python3 scripts/prover_stream_test.py --lines 720000                 # stress
"""
import argparse
import json
import os
import resource
import subprocess
import sys
import tempfile

REQUESTS = [
    ('{"id":"r%d","facts":[{"a":"A","relation":"NTPP","b":"B"},'
     '{"a":"B","relation":"NTPP","b":"C"}],"query":{"a":"A","b":"C"}}',
     {"status": "entailed", "relation": "NTPP"}),
    ('{"id":"m%d","matrix":"FF2F11212","claim":"touches"}',
     {"status": "entailed", "claim": "touches"}),
    ('{"id":"c%d","facts":[{"a":"A","relation":"DC","b":"B"},'
     '{"a":"A","relation":"EQ","b":"B"}],"query":{"a":"A","b":"B"}}',
     {"status": "contradictory"}),
]


def generate(path, n):
    """Write n lines; return the expected answer for each non-blank line."""
    expected = []
    with open(path, "w", encoding="utf-8") as f:
        for i in range(n):
            if i % 5000 == 2500:
                f.write('{"id":"broken%d",\n' % i)
                expected.append({"id": None, "status": "error"})
            elif i % 7000 == 1:
                f.write("\n")
            else:
                line, answer = REQUESTS[i % len(REQUESTS)]
                f.write(line.replace("%d", str(i)) + "\n")
                expected.append(dict(answer, id=line.split('"')[3].replace("%d", str(i))))
    return expected


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lines", type=int, default=720000)
    ap.add_argument("--stack-kb", type=int, default=None,
                    help="stack limit for the prover process, in KB")
    ap.add_argument("--binary", default=".lake/build/bin/lean-geospatial-prover")
    a = ap.parse_args()

    def limit_stack():
        if a.stack_kb is not None:
            kb = a.stack_kb * 1024
            resource.setrlimit(resource.RLIMIT_STACK, (kb, kb))

    with tempfile.TemporaryDirectory() as d:
        inp = os.path.join(d, "in.jsonl")
        expected = generate(inp, a.lines)
        with open(inp, "rb") as fin:
            proc = subprocess.run([a.binary], stdin=fin, capture_output=True,
                                  preexec_fn=limit_stack)
    out = proc.stdout.decode("utf-8").splitlines()

    problems = []
    if proc.returncode != 0:
        problems.append(f"exit code {proc.returncode}: {proc.stderr.decode()[-200:]}")
    if len(out) != len(expected):
        problems.append(f"{len(out)} answers for {len(expected)} non-blank lines")
    for k, (line, exp) in enumerate(zip(out, expected)):
        got = json.loads(line)
        if any(got.get(key) != value for key, value in exp.items()):
            problems.append(f"answer {k}: expected {exp}, got {got}")
            break

    print(f"lines={a.lines} non-blank={len(expected)} answers={len(out)} "
          f"exit={proc.returncode} stack_kb={a.stack_kb}")
    if problems:
        for p in problems:
            print("FAIL:", p)
        sys.exit(1)
    print("ok")


if __name__ == "__main__":
    main()
