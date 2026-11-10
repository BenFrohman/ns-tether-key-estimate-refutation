#!/usr/bin/env bash
# Copyright 2026 Benjamin Stanley Frohman. Licensed under the Apache License, Version 2.0.
#
# One-command verification:
#   ./verify.sh              Lean build + axiom check + exact symbolic + interval (Arb) certificate
#   ./verify.sh --numerics   also runs the pseudo-spectral simulation (SUPPORTING ONLY, not part of any proof)
#
# Needs: elan (Lean toolchain manager), git, curl, python3 (>= 3.10) with venv.
# Set PYTHON=/path/to/python to use an existing interpreter that already has scripts/requirements.txt.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NUMERICS=0
for a in "$@"; do
  case "$a" in
    --numerics) NUMERICS=1 ;;
    *) echo "unknown option: $a" >&2; exit 2 ;;
  esac
done
OUT="$ROOT/out"; mkdir -p "$OUT"
step() { printf '\n==== %s ====\n' "$*"; }

step "1/4 Lean: fetch Mathlib cache and build (Lean 4.22.0, Mathlib v4.22.0)"
cd "$ROOT/lean"
lake exe cache get
lake build 2>&1 | tee "$OUT/lake_build.log"
if grep -qiE "declaration uses 'sorry'|^error" "$OUT/lake_build.log"; then
  echo "FAIL: build reported sorry or errors" >&2; exit 1
fi

step "2/4 Lean: forbidden-token scan and #print axioms"
echo "Occurrences of sorry/admit/axiom/native_decide/implemented_by/unsafe (expected: one comment line only):"
grep -nwE 'sorry|admit|axiom|native_decide|implemented_by|unsafe' FrohmanianTetherDraftAudit.lean KeyEstimateRefutation.lean || true
lake env lean PrintAxioms.lean 2>&1 | tee "$OUT/axioms.log"
NDECL=$(grep -c "depends on axioms" "$OUT/axioms.log" || true)
AXSET=$(tr -d '\n' < "$OUT/axioms.log" | grep -o 'axioms: \[[^]]*\]' | sed 's/axioms: \[//; s/\]//' | tr ',' '\n' | tr -d ' ' | sort -u | paste -sd, -)
echo "declarations checked: $NDECL ; union of axioms used: [$AXSET]"
if [ "$NDECL" -ne 50 ] || [ "$AXSET" != "Classical.choice,Quot.sound,propext" ]; then
  echo "FAIL: expected 50 declarations using only [propext, Classical.choice, Quot.sound]" >&2; exit 1
fi
echo "OK: all 50 declarations use only Lean's standard axioms (no sorryAx)."

step "3/4 Python environment"
if [ -z "${PYTHON:-}" ]; then
  if [ ! -x "$ROOT/.venv/bin/python" ]; then
    python3 -m venv "$ROOT/.venv"
    "$ROOT/.venv/bin/pip" install -q -r "$ROOT/scripts/requirements.txt"
  fi
  PYTHON="$ROOT/.venv/bin/python"
fi
"$PYTHON" -c "import flint, sympy, numpy; print('python-flint', flint.__version__, '| sympy', sympy.__version__, '| numpy', numpy.__version__)"

step "4/4 Exact symbolic checks (sympy) and rigorous interval certificate (python-flint / Arb)"
cd "$OUT"
"$PYTHON" "$ROOT/scripts/v1_trig_example.py" | tee v1_trig_example.log
grep -q "div U = 0" v1_trig_example.log
grep -q "d/dt |omega(0,t)| at t=0 = 6\*A\*(A - nu)" v1_trig_example.log
"$PYTHON" "$ROOT/scripts/v2_symbolic.py" | tee v2_symbolic.log
grep -q "div u1 (coefficient of beta) = 0" v2_symbolic.log
grep -q "Laplacian omega1(0) = \[0, 0, -120\]" v2_symbolic.log
"$PYTHON" "$ROOT/scripts/v2_maxcert.py" | tee v2_maxcert.log
grep -q "^CERTIFIED: max |omega1|^2 = 144" v2_maxcert.log
echo "OK: V1 exact identities and V2 symbolic values reproduced; Arb maximum certificate passed."

if [ "$NUMERICS" -eq 1 ]; then
  step "OPTIONAL numerics (SUPPORTING ONLY - not part of any proof)"
  "$PYTHON" "$ROOT/scripts/ns_check.py" | tee ns_check.log
fi

printf '\nALL CHECKS PASSED. Logs in %s\n' "$OUT"
