#!/usr/bin/env bash
# Regenerate every gadget-existence result reported in the paper.
#
#   bash tests/barriers.sh            # decided cases only (minutes)
#   FULL=1 bash tests/barriers.sh     # also attempt the undecided cells
#
# Each line records predicate, (s,t,k), the certified exponent (t+1)/s, and the
# decision.  t = k-1 is the complete source; t < k-1 is an intersection-bounded
# source.
set -u
cd "$(dirname "$0")/.."
mkdir -p results
LOG=results/barriers.log
TIMEOUT=${TIMEOUT:-600}
: > "$LOG"

run() {                      # run <name> <s> <t> <k> <predicate-args...>
  local name=$1 s=$2 t=$3 k=$4; shift 4
  local out rc
  out=$(timeout "$TIMEOUT" python src/sat/wsat_t.py "$@" --k "$k" --s "$s" --t "$t" 2>&1)
  rc=$?
  if [ $rc -ne 0 ]; then
    printf '%-10s s=%s t=%-2s k=%-2s exp=%s/%s  UNDECIDED (timeout %ss)\n' \
           "$name" "$s" "$t" "$k" "$((t+1))" "$s" "$TIMEOUT" | tee -a "$LOG"
  else
    printf '%-10s s=%s t=%-2s k=%-2s exp=%s/%s  %s\n' "$name" "$s" "$t" "$k" \
           "$((t+1))" "$s" "$(echo "$out" | grep -oE 'RESULT (SAT|UNSAT)' | head -1)" \
           | tee -a "$LOG"
  fi
}

echo "### control: the class contains the construction of [BGP26] for R_317" | tee -a "$LOG"
run R317 1 1 3 --r 4 --R 0x1797
run R317 1 1 4 --r 4 --R 0x1797
run R317 2 4 5 --r 4 --R 0x1797
run R317 2 5 6 --r 4 --R 0x1797
run R299 1 1 3 --r 4 --R 0x19ee
run R299 2 4 5 --r 4 --R 0x19ee
run R299 2 5 6 --r 4 --R 0x19ee

echo "### complete source (t = k-1): R_{0,1,3,4}, arity 7" | tee -a "$LOG"
for k in 5 6 7 8; do run R0134 2 $((k-1)) "$k" --r 7 --W 0,1,3,4; done

echo "### barriers: no gadget in the class certifies exponent > 2" | tee -a "$LOG"
for P in "R181|--r 4 --R 0xE917" "R023|--r 5 --W 0,2,3" "R124|--r 5 --W 1,2,4"; do
  n=${P%%|*}; a=${P#*|}
  for k in 5 6;  do run "$n" 2 $((k-1)) "$k" $a; done      # complete, s=2
  for k in 7 8 9; do run "$n" 3 $((k-1)) "$k" $a; done     # complete, s=3
  for k in 9 10 11 12; do run "$n" 4 $((k-1)) "$k" $a; done # complete, s=4
  for st in "1 2" "2 4" "2 5" "3 6" "3 7" "3 8"; do        # intersection-bounded
    set -- $st
    run "$n" "$1" "$2" $(($2+1)) $a
    run "$n" "$1" "$2" $(($2+2)) $a
  done
done

if [ "${FULL:-0}" = "1" ]; then
  echo "### undecided cells (expect timeouts)" | tee -a "$LOG"
  for k in 8 9;      do run R0134 3 $((k-1)) "$k" --r 7 --W 0,1,3,4; done
  for k in 10 11 12; do run R0134 3 $((k-1)) "$k" --r 7 --W 0,1,3,4; done
  for k in 11 12 13; do run R0134 4 $((k-1)) "$k" --r 7 --W 0,1,3,4; done
fi

echo "written to $LOG"
