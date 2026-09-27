#!/usr/bin/env python3
"""Erdos problem #617 (Erdos-Gyarfas): is there a balanced r-colouring of K_{r^2+1}?

A balanced colouring is one in which every r+1 vertices span all r colours, i.e. a
counterexample to the conjecture.  The conjecture is known false for r=2, and proved by
Erdos and Gyarfas for r=3 and r=4; r=5 is the first open case.

Encoding: one variable per (edge, colour); exactly one colour per edge; for every (r+1)-set
and every colour, at least one edge of that set carries the colour.  Colour permutations are
broken by forbidding colour c on the i-th edge whenever c > i.

The ladder below is its own positive control.  K_{r^2} carries a balanced colouring whenever
an affine plane of order r exists, so (r,r^2) must come back SAT; a run that reports UNSAT
there has an encoding error, not a theorem.
Requires python-sat (`python3 -m pip install --user python-sat`); the import is deferred to the
solve so that reading the encoding costs nothing when the solver is absent.
"""
import sys, time, itertools, json

def build(n, r):
    verts = range(n)
    edges = list(itertools.combinations(verts, 2))
    idx = {e: i for i, e in enumerate(edges)}
    def v(e_i, c):
        return e_i * r + c + 1
    cls = []
    for i in range(len(edges)):
        cls.append([v(i, c) for c in range(r)])
        for a in range(r):
            for b in range(a + 1, r):
                cls.append([-v(i, a), -v(i, b)])
    for i in range(min(r, len(edges))):        # colour-permutation symmetry
        for c in range(i + 1, r):
            cls.append([-v(i, c)])
    for S in itertools.combinations(verts, r + 1):
        inner = [idx[e] for e in itertools.combinations(S, 2)]
        for c in range(r):
            cls.append([v(i, c) for i in inner])
    return edges, cls

def run(n, r, budget):
    from pysat.solvers import Cadical153
    t0 = time.time()
    edges, cls = build(n, r)
    nv = len(edges) * r
    with Cadical153(bootstrap_with=cls) as s:
        s.conf_budget(budget)
        res = s.solve_limited(expect_interrupt=False)
        model = s.get_model() if res else None
    out = {"n": n, "r": r, "vars": nv, "clauses": len(cls),
           "result": {True: "SAT", False: "UNSAT", None: "BUDGET-EXHAUSTED"}[res],
           "seconds": round(time.time() - t0, 1)}
    if model:
        col = {}
        for i, e in enumerate(edges):
            for c in range(r):
                if model[i * r + c] > 0:
                    col["%d-%d" % e] = c
        out["colouring"] = col
    print(json.dumps(out), flush=True)
    return out

if __name__ == "__main__":
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else -1
    ladder = [(5, 2), (9, 3), (10, 3), (16, 4), (17, 4), (25, 5), (26, 5)]
    for n, r in ladder:
        o = run(n, r, budget)
        if o["result"] == "BUDGET-EXHAUSTED":
            print(json.dumps({"stopped_at": [n, r]}), flush=True)
