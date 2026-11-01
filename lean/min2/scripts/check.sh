#!/bin/bash
# Full check of this release, from empty. Run with Lean 4.33.1 from elan. The last line is CHECK PASSED or CHECK FAILED,
# and the exit status is 0 only for CHECK PASSED. Usage: scripts/check.sh [log]
set -u -o pipefail
cd "$(dirname "$0")/.."
export PATH=$HOME/.elan/bin:$PATH
L=${1:-logs/check.log}
mkdir -p logs "$(dirname "$L")"
fail=0
bad() { echo "FAILED: $1"; fail=1; }
(
date
rm -rf .lake
echo "--- build"
nice -n 5 lake build > logs/build.log 2>&1; rc=$?
grep -E "error|Build completed|build failed" logs/build.log
echo "build rc=$rc"; [ $rc -eq 0 ] || bad build
echo "--- audit"
lake env lean Audit.lean > logs/audit.log 2>&1; rc=$?
cut -c1-300 logs/audit.log
echo "audit rc=$rc"; [ $rc -eq 0 ] || bad audit
n=$(grep -c "depends on axioms" logs/audit.log)
[ "$n" -eq 10 ] || bad "axiom lines: $n, expected 10"
grep "depends on axioms" logs/audit.log | grep -vE "axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" && bad "axioms"
grep -qE "error|sorry" logs/audit.log && bad "error or sorry in audit"
echo "--- leanchecker"
MODS=$(find LeanJudge TBeta -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | sort | tr '\n' ' ')
echo "$MODS"
nice -n 5 lake env leanchecker $MODS; rc=$?
echo "leanchecker rc=$rc"; [ $rc -eq 0 ] || bad leanchecker
echo "--- statement files"
sha256sum LeanJudge/Defs.lean LeanJudge/Final.lean
echo "05bab60acdca29b92f004fc8830b7c3fa99ab50da80c53416250929e2f01c223  LeanJudge/Defs.lean" | sha256sum -c || bad Defs
echo "2d3a3b984c2794a4ddb5a0d637463cbfe396c8076e8cae23060f556e84d6be10  LeanJudge/Final.lean" | sha256sum -c || bad Final
echo "--- sorry"
if grep -rnw sorry LeanJudge TBeta; then bad sorry; else echo "no sorry"; fi
echo "--- names in the table (existence only)"
lake env lean scripts/table_names.lean > logs/table.log 2>&1; rc=$?
cut -c1-300 logs/table.log
[ $rc -eq 0 ] || bad table
grep -q "missing: \[\]" logs/table.log || bad "table names"
echo "--- used lines"
lake env lean scripts/DepGraph.lean > logs/dep.log 2>&1; rc=$?
cut -c1-200 logs/dep.log
[ $rc -eq 0 ] || bad walk
python3 scripts/dep_sum.py || bad dep_sum
echo "--- physical lines"
find LeanJudge TBeta -name '*.lean' | sort | xargs wc -l
if [ $fail -eq 0 ]; then echo "CHECK PASSED"; else echo "CHECK FAILED"; fi
exit $fail
) > "$L" 2>&1
rc=$?
cat "$L"
exit $rc
