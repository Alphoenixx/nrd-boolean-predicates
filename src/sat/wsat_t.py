#!/usr/bin/env python3
"""wsat - SAT decision procedure for width-s NRD patterns.

A width-s pattern on k positions for an r-ary predicate R is f_1..f_r, each
depending on at most s of v_1..v_k, with

    (f_1(v),...,f_r(v)) in R      for every v != 1^k
    (f_1(1^k),...,f_r(1^k)) not in R

Existence certifies NRD_R(n) = Omega(n^{k/s}).  s = 1 is Carbonnel's universal
k-cube test.

SAT is the right instrument here: the enumerator in search.cpp is O(T^r) with
T ~ 18700 entry types at k=9,s=3, which is hopeless, while the encoding below
is a few thousand variables.  UNSAT is a genuine barrier theorem for the whole
width-s class at that k, and the solver emits a DRAT proof for it.

Usage
  python wsat.py --r 4 --k 9 --s 3 --R 0xE917
  python wsat.py --r 7 --k 8 --s 2 --W 0,1,3,4
  python wsat.py --r 4 --k 5 --s 2 --R 0x1797 --emit
"""
import argparse
import itertools
import sys
import time

from pysat.formula import CNF
from pysat.solvers import Cadical153


# ------------------------------------------------------------------ predicate
def build_R(r, Wstr, Rstr):
    """Return a set of accepted tuple indices; bit j of the index is entry j."""
    if Wstr is not None:
        W = {int(x) for x in Wstr.split(",") if x.strip() != ""}
        return {t for t in range(1 << r) if bin(t).count("1") in W}
    m = int(Rstr, 0)
    return {t for t in range(1 << r) if (m >> t) & 1}


# ------------------------------------------------------------------- encoding
class Enc:
    def __init__(self):
        self.n = 0
        self.cls = []

    def var(self):
        self.n += 1
        return self.n

    def add(self, *lits):
        self.cls.append(list(lits))

    def lex_ge(self, X, Y):
        """Force the bit-vector X >= Y lexicographically (index 0 = most significant)."""
        e = self.var()
        self.add(e)  # empty prefix is equal
        for j in range(len(X)):
            x, y = X[j], Y[j]
            self.add(-e, x, -y)  # e_j -> x_j >= y_j
            eq = self.var()
            self.add(-eq, -x, y)
            self.add(-eq, x, -y)
            self.add(eq, -x, -y)
            self.add(eq, x, y)
            e2 = self.var()
            self.add(-e2, e)
            self.add(-e2, eq)
            self.add(e2, -e, -eq)
            e = e2


def encode(r, k, s, R, symbreak=True, t=-1):
    ROWS = 1 << k
    OWN = ROWS - 1
    E = Enc()

    # y[j][v] = f_j(v);  d[j][i] = "entry j may read coordinate i"
    y = [[E.var() for _ in range(ROWS)] for _ in range(r)]
    d = [[E.var() for _ in range(k)] for _ in range(r)]

    # (1) width: at most s of d[j][*].  Naive forbid-(s+1)-subsets is tiny here.
    for j in range(r):
        for S in itertools.combinations(range(k), s + 1):
            E.add(*[-d[j][i] for i in S])

    # (2) independence: not reading i means f_j is constant along direction i.
    for j in range(r):
        for i in range(k):
            bit = 1 << i
            for v in range(ROWS):
                if v & bit:
                    continue
                w = v | bit
                E.add(d[j][i], -y[j][v], y[j][w])
                E.add(d[j][i], y[j][v], -y[j][w])

    # (3) rows arising from the source land inside R.  With a source whose
    # pairwise intersections are at most t, only rows of weight <= t occur;
    # rows with t < |v| < k are UNCONSTRAINED.  t = k-1 is the complete source.
    tt = (k - 1) if t < 0 else t
    rejected = [u for u in range(1 << r) if u not in R]
    for v in range(ROWS):
        if v == OWN or bin(v).count("1") > tt:
            continue
        for u in rejected:
            E.add(*[(-y[j][v] if (u >> j) & 1 else y[j][v]) for j in range(r)])

    # (4) the own row lands outside R
    for t in sorted(R):
        E.add(*[(-y[j][OWN] if (t >> j) & 1 else y[j][OWN]) for j in range(r)])

    # (5) Sym(k) symmetry break: coordinate columns of d lex-non-increasing.
    # Permuting coordinates permutes these columns and relabels rows
    # consistently, so sorting them keeps a representative of every orbit.
    if symbreak:
        for i in range(k - 1):
            E.lex_ge([d[j][i] for j in range(r)], [d[j][i + 1] for j in range(r)])

    return E, y, d


# ------------------------------------------------------------------- decoding
def extract(model, y, d, r, k):
    """Recover each f_j as (support mask, truth table over that support)."""
    ROWS = 1 << k
    val = [[1 if model[y[j][v] - 1] > 0 else 0 for v in range(ROWS)] for j in range(r)]
    out = []
    for j in range(r):
        supp = 0
        for i in range(k):
            bit = 1 << i
            if any(val[j][v] != val[j][v | bit] for v in range(ROWS) if not (v & bit)):
                supp |= bit
        co = [i for i in range(k) if (supp >> i) & 1]
        ftab = 0
        for a in range(1 << len(co)):
            v = 0
            for pos, i in enumerate(co):
                if (a >> pos) & 1:
                    v |= 1 << i
            if val[j][v]:
                ftab |= 1 << a
        out.append((supp, ftab, val[j]))
    return out


def verify(pat, r, k, R):
    """Independent re-check of a decoded pattern, sharing nothing with the solver."""
    ROWS = 1 << k
    OWN = ROWS - 1
    cover = 0
    for supp, ftab, _ in pat:
        cover |= supp
        if bin(supp).count("1") > args.s:
            return False, "width exceeded"
    tt = (k - 1) if args.t < 0 else args.t
    for v in range(ROWS):
        if v != OWN and bin(v).count("1") > tt:
            continue
        t = 0
        for j, (supp, ftab, _) in enumerate(pat):
            co = [i for i in range(k) if (supp >> i) & 1]
            a = 0
            for pos, i in enumerate(co):
                if (v >> i) & 1:
                    a |= 1 << pos
            if (ftab >> a) & 1:
                t |= 1 << j
        inR = t in R
        if v == OWN and inR:
            return False, "own row accepted"
        if v != OWN and not inR:
            return False, f"row {v} rejected"
    return True, "ok"


# ----------------------------------------------------------------------- main
if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--r", type=int, required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--s", type=int, required=True)
    ap.add_argument("--W")
    ap.add_argument("--R")
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--no-symbreak", action="store_true")
    ap.add_argument("--t", type=int, default=-1, help="max pairwise intersection of source; -1 means complete source (t=k-1)")
    args = ap.parse_args()
    if (args.W is None) == (args.R is None):
        sys.exit("give exactly one of --W / --R")

    R = build_R(args.r, args.W, args.R)
    t0 = time.time()
    E, y, d = encode(args.r, args.k, args.s, R, symbreak=not args.no_symbreak, t=args.t)
    cnf = CNF(from_clauses=E.cls)
    ttv = (args.k - 1) if args.t < 0 else args.t
    tag = f"r={args.r} k={args.k} s={args.s} t={ttv} exp={ttv+1}/{args.s}"
    print(f"# {tag} |R|={len(R)} vars={E.n} clauses={len(E.cls)} "
          f"enc={time.time()-t0:.2f}s", flush=True)

    t1 = time.time()
    with Cadical153(bootstrap_with=cnf) as S:
        sat = S.solve()
        el = time.time() - t1
        if not sat:
            print(f"RESULT UNSAT  {tag}  secs={el:.2f}   "
                  f"[no width-{args.s} pattern on {args.k} positions]")
            sys.exit(0)
        model = S.get_model()

    pat = extract(model, y, d, args.r, args.k)
    ok, why = verify(pat, args.r, args.k, R)
    print(f"RESULT SAT    {tag}  secs={el:.2f}  verify={'OK' if ok else 'FAIL:'+why}")
    print("PATTERN " + ",".join(f"{supp}:{ftab}" for supp, ftab, _ in pat))
