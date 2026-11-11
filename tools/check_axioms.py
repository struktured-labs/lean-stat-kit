#!/usr/bin/env python3
"""Fail-closed axiom audit. Usage: check_axioms.py AUDIT_OUTPUT EXPECTED_COUNT
Every report must list only propext / Classical.choice / Quot.sound (or none), and the number of
reports must equal EXPECTED_COUNT. Anything else (sorryAx, a custom axiom, Lean.ofReduceBool,
Lean.trustCompiler, an error line) fails."""
import re, sys
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
text = open(sys.argv[1], encoding="utf-8").read()
expected = int(sys.argv[2])
flat = re.sub(r"\s*\n\s+", " ", text)  # join wrapped continuation lines
ok = bad = 0; used = set()
for line in flat.splitlines():
    line = line.strip()
    if not line: continue
    m = re.match(r"^'([^']+)' depends on axioms: \[(.*)\]$", line)
    if m:
        ax = {a.strip() for a in m.group(2).split(",") if a.strip()}
        used |= ax
        if ax <= ALLOWED: ok += 1
        else: bad += 1; print(f"AXIOM FAIL: {m.group(1)} uses {sorted(ax - ALLOWED)}")
        continue
    if re.match(r"^'([^']+)' does not depend on any axioms$", line): ok += 1; continue
    bad += 1; print(f"AXIOM FAIL: unexpected output line: {line[:200]}")
print(f"axiom audit: {ok} clean reports, {bad} failures, expected {expected}; axioms used: {sorted(used)}")
if bad or ok != expected: print("axiom audit: FAIL"); sys.exit(1)
print("axiom audit: PASS"); sys.exit(0)
