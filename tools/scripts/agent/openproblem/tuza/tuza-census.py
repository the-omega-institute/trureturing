"""The link census at degree eight: classify the connected graphs on eight vertices by
whether maximum matching equals minimum vertex cover.

The class where they agree is the Koenig-Egervary class; the literature's degree-seven
argument ranges over the links outside it, so that is the side whose size decides the cost
of the degree-eight analogue.
"""
import itertools, sys, time
sys.path.insert(0, "/Users/macstudio/omega-op")
from importlib import import_module
gen = import_module("tuza-gen") if False else None
exec(open("/Users/macstudio/omega-op/tuza-gen.py").read().split('if __name__')[0])

def alpha(n, adj, subs):
    best = 0
    for S in subs:
        T = S; ok = True
        while T:
            v = (T & -T).bit_length() - 1; T &= T - 1
            if adj[v] & S: ok = False; break
        if ok:
            c = bin(S).count("1")
            if c > best: best = c
    return best

def maxmatch(n, adj):
    best = 0
    def rec(v, used, cur):
        nonlocal best
        if v == n:
            if cur > best: best = cur
            return
        if cur + (n - v) // 2 <= best: return
        if used >> v & 1:
            rec(v + 1, used, cur); return
        rec(v + 1, used | (1 << v), cur)
        w = adj[v] & ~used
        while w:
            u = (w & -w).bit_length() - 1; w &= w - 1
            if u > v: rec(v + 1, used | (1 << v) | (1 << u), cur + 1)
    rec(0, 0, 0)
    return best

def census(n):
    t0 = time.time()
    level = {canon(1, (0,)): (0,)}
    for k in range(2, n + 1):
        nxt = {}
        for g in level.values():
            for nbhd in range(1 << (k - 1)):
                adj = list(g) + [nbhd]
                for u in range(k - 1):
                    if nbhd >> u & 1: adj[u] |= 1 << (k - 1)
                adj = tuple(adj)
                c = canon(k, adj)
                if c not in nxt: nxt[c] = adj
        level = nxt
    graphs = [g for g in level.values() if connected(n, g)]
    subs = list(range(1 << n))
    ke = 0; out = 0; outdeg = {}
    for g in graphs:
        if maxmatch(n, g) == n - alpha(n, g, subs):
            ke += 1
        else:
            out += 1
            d = tuple(sorted(bin(x).count("1") for x in g))
            outdeg[d] = outdeg.get(d, 0) + 1
    print(f"n={n}: connected={len(graphs)}  Koenig-Egervary={ke}  outside={out}"
          f"  ({100*out/len(graphs):.1f}%)  {time.time()-t0:.1f}s", flush=True)
    return graphs, ke, out, outdeg

if __name__ == "__main__":
    for n in (5, 6, 7, 8):
        graphs, ke, out, outdeg = census(n)
        if n == 8:
            print("outside-class 8-vertex links by degree sequence, ten most common:")
            for d, c in sorted(outdeg.items(), key=lambda kv: -kv[1])[:10]:
                print(f"   {d}  {c}")
            reg = sum(c for d, c in outdeg.items() if len(set(d)) == 1)
            print(f"regular graphs among the outside class: {reg}")
