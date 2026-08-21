#!/usr/bin/env python3
"""Solve one gadget-existence instance with a parallel solver portfolio.

Encodes exactly as wsat_t.py, then runs several independent CDCL solvers on the
same formula in separate processes and reports whichever finishes first. On
hard instances the spread between solvers is large and unpredictable, so a
portfolio is materially faster than any fixed choice.

  python src/sat/portfolio.py --r 7 --W 1,2,4,5 --k 12 --s 4 --timeout 28800
"""
import argparse, multiprocessing as mp, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wsat_t as W

SOLVERS = ["Cadical195", "Kissat404", "Glucose42", "MapleCM", "Lingeling", "Cadical153"]


def solve(name, clauses, q):
    try:
        import pysat.solvers as S
        t0 = time.time()
        with getattr(S, name)(bootstrap_with=clauses) as s:
            res = s.solve()
            model = s.get_model() if res else None
        q.put((name, res, model, time.time() - t0))
    except Exception as e:                      # a solver may be unavailable
        q.put((name, None, None, str(e)))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--r", type=int, required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--s", type=int, required=True)
    ap.add_argument("--t", type=int, default=-1)
    ap.add_argument("--W")
    ap.add_argument("--R")
    ap.add_argument("--timeout", type=int, default=28800)
    args = ap.parse_args()
    W.args = args                                # wsat_t.verify reads this

    R = W.build_R(args.r, args.W, args.R)
    E, y, d = W.encode(args.r, args.k, args.s, R, symbreak=True, t=args.t)
    tt = (args.k - 1) if args.t < 0 else args.t
    print("# r=%d k=%d s=%d t=%d exp=%d/%d vars=%d clauses=%d portfolio=%s"
          % (args.r, args.k, args.s, tt, tt + 1, args.s, E.n, len(E.cls),
             ",".join(SOLVERS)), flush=True)

    q = mp.Queue()
    procs = [mp.Process(target=solve, args=(n, E.cls, q), daemon=True) for n in SOLVERS]
    for p in procs: p.start()

    deadline, winner = time.time() + args.timeout, None
    while time.time() < deadline:
        try:
            name, res, model, el = q.get(timeout=5)
        except Exception:
            if not any(p.is_alive() for p in procs): break
            continue
        if res is None:
            print("# %s unavailable (%s)" % (name, model), flush=True); continue
        winner = (name, res, model, el); break
    for p in procs: p.terminate()

    if winner is None:
        print("RESULT UNDECIDED  timeout=%ds" % args.timeout); sys.exit(1)

    name, res, model, el = winner
    tag = "r=%d k=%d s=%d t=%d exp=%d/%d" % (args.r, args.k, args.s, tt, tt + 1, args.s)
    if not res:
        print("RESULT UNSAT  %s  secs=%.1f  solver=%s" % (tag, el, name)); sys.exit(0)
    pat = W.extract(model, y, d, args.r, args.k)
    ok, why = W.verify(pat, args.r, args.k, R)
    print("RESULT SAT    %s  secs=%.1f  solver=%s  verify=%s"
          % (tag, el, name, "OK" if ok else "FAIL:" + why))
    print("PATTERN " + ",".join("%d:%d" % (m, f) for m, f, _ in pat))
