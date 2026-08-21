#!/usr/bin/env bash
# Run the gadget search on every predicate that the two standard criteria leave
# unresolved at arity 6 and 7.  For a predicate bracketed Omega(n^l)..O(n^u), a
# gadget improves on l exactly when k/s > l, and Proposition 5.1 caps
# k <= s*min(r,u).  Phase 1 is s=2, phase 2 is s=3.  Rows with k > KMAX are
# skipped as infeasible.
#
#   bash tests/unresolved_sweep.sh          # both phases
#   PHASE=2 bash tests/unresolved_sweep.sh  # s=2 only
set -u
cd "$(dirname "$0")/.."
mkdir -p results
LOG=results/unresolved_sweep.log
TIMEOUT=${TIMEOUT:-600}
KMAX=${KMAX:-12}
PAR=${PAR:-8}

# r:W:l:u  -- the 36 predicates with l < u at arity 6 and 7
PREDS="6:0,2,3:2:3 6:1,2,4:2:3 6:1,3,4:2:3 6:0,1,3,4:2:3 6:0,2,3,4:3:4
6:0,2,3,5:2:3 6:0,2,3,6:2:3 7:0,1,3:2:3 7:0,2,3:2:3 7:1,2,4:2:3 7:0,3,4:2:3
7:1,3,4:2:3 7:0,1,3,4:2:4 7:0,2,3,4:3:4 7:2,3,5:2:3 7:0,2,3,5:2:3
7:1,2,3,5:3:4 7:1,2,4,5:2:3 7:1,3,4,5:3:4 7:0,1,3,4,5:3:4 7:0,2,3,4,5:4:5
7:0,1,3,6:2:3 7:0,2,3,6:2:3 7:1,2,3,6:3:4 7:0,1,4,6:2:3 7:0,3,4,6:2:3
7:1,3,4,6:2:3 7:0,1,3,4,6:3:4 7:1,2,3,4,6:4:5 7:0,2,5,6:2:3 7:0,3,5,6:2:3
7:1,2,3,5,6:3:4 7:0,2,3,7:2:3 7:0,2,3,4,7:3:4 7:0,1,4,5,7:2:3 7:0,1,3,6,7:2:3"

one() {                                  # one <r> <W> <l> <u> <s> <k>
  local r=$1 W=$2 l=$3 u=$4 s=$5 k=$6 out res
  out=$(timeout "$TIMEOUT" python src/sat/wsat_t.py --r "$r" --W "$W" --k "$k" --s "$s" 2>&1)
  if [ $? -ne 0 ]; then res="UNDECIDED(${TIMEOUT}s)"
  else res=$(echo "$out" | grep -oE 'RESULT (SAT|UNSAT)' | head -1); fi
  printf 'r=%s W={%s} l=%s u=%s  s=%s k=%-2s exp=%s/%s  %s\n' \
         "$r" "$W" "$l" "$u" "$s" "$k" "$k" "$s" "$res"
}
export -f one; export TIMEOUT

emit() {                                 # emit <s>
  local s=$1 spec r rest W l u kmax k
  for spec in $PREDS; do
    r=${spec%%:*}; rest=${spec#*:}
    W=${rest%%:*}; rest=${rest#*:}
    l=${rest%%:*}; u=${rest#*:}
    kmax=$(( s * ( r < u ? r : u ) )); [ "$kmax" -gt "$KMAX" ] && kmax=$KMAX
    k=$(( l * s + 1 ))
    while [ "$k" -le "$kmax" ]; do echo "$r $W $l $u $s $k"; k=$(( k + 1 )); done
  done
}

: > "$LOG"
for s in 2 3; do
  [ "${PHASE:-0}" = "2" ] && [ "$s" = "3" ] && continue
  echo "### width s=$s" | tee -a "$LOG"
  emit "$s" | xargs -P "$PAR" -n 6 bash -c 'one "$@"' _ | tee -a "$LOG"
done
echo "=== unresolved sweep complete ===" | tee -a "$LOG"
