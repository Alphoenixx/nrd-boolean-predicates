#!/usr/bin/env bash
# Regression battery.  Every expected number below was produced independently by
# at least two distinct implementations (see docs/RESULTS.md).
set -u
B=bin/wsearch
fail=0

chk() { # chk <label> <expected> <args...>
  local label=$1 exp=$2; shift 2
  local out got
  out=$($B "$@" 2>/dev/null | grep '^DONE')
  got=$(sed -n 's/.*found=\([0-9]*\).*/\1/p' <<<"$out")
  if [[ "$got" == "$exp" ]]; then
    printf '  ok   %-42s %s\n' "$label" "$got"
  else
    printf '  FAIL %-42s got=%s want=%s\n' "$label" "$got" "$exp"; fail=1
  fi
}

chkorb() { # chkorb <label> <expected-orbits> <expected-total> <args...>
  local label=$1 eo=$2 et=$3; shift 3
  local out o t
  out=$($B "$@" 2>/dev/null | grep '^DONE')
  o=$(sed -n 's/.*orbits=\([0-9]*\).*/\1/p' <<<"$out")
  t=$(sed -n 's/.*total=\([0-9]*\).*/\1/p' <<<"$out")
  if [[ "$o" == "$eo" && "$t" == "$et" ]]; then
    printf '  ok   %-42s orbits=%s total=%s\n' "$label" "$o" "$t"
  else
    printf '  FAIL %-42s got=(%s,%s) want=(%s,%s)\n' "$label" "$o" "$t" "$eo" "$et"; fail=1
  fi
}

echo "== exact-count controls (symmetry off) =="
chk "k=2 r=7 W={0,1,3,4}"            13330 --k 2 --s 2 --r 7 --W 0,1,3,4 --mmin 0 --mmax 7
chk "k=3 r=5 W={2,3,4}"              25649 --k 3 --s 2 --r 5 --W 2,3,4   --mmin 0 --mmax 5
chk "k=5 r=5 W={2,3,4} (control)"    89430 --k 5 --s 2 --r 5 --W 2,3,4   --mmin 0 --mmax 5

echo "== Proposition 4: the two open arity-5 predicates, width 2, k=5 =="
chk "k=5 r=5 W={0,2,3}"                  0 --k 5 --s 2 --r 5 --W 0,2,3   --mmin 0 --mmax 5
chk "k=5 r=5 W={1,2,4}"                  0 --k 5 --s 2 --r 5 --W 1,2,4   --mmin 0 --mmax 5

if [[ "${1:-fast}" == "full" ]]; then
  echo "== Theorem 6 source enumeration (orbit mode) =="
  chkorb "k=5 r=7 W={0,1,3,4}" 3 70 --k 5 --s 2 --r 7 --W 0,1,3,4 --sym 7 --canon
  echo "== exact count, same case (slow) =="
  chk "k=5 r=7 W={0,1,3,4} exact" 70 --k 5 --s 2 --r 7 --W 0,1,3,4
fi

[[ $fail == 0 ]] && echo "ALL PASS" || echo "FAILURES PRESENT"
exit $fail
