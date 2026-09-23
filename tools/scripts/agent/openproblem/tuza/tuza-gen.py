"""Isomorph-free generation of simple graphs by vertex augmentation.

A graph on n vertices is a tuple of n adjacency bitmasks.  Graphs on n vertices are
obtained from the graphs on n-1 vertices by adding one vertex with every possible
neighbourhood, then keeping one representative per isomorphism class.

The representative is the maximum upper-triangular code over the vertex orderings that
respect the colour refinement, so only orderings within a colour class are tried.  On a
graph whose refinement is discrete this is one ordering; the cost concentrates on the
regular graphs, which are the minority.
"""
import itertools, sys, time

def refine(n, adj):
    colours = [0] * n
    while True:
        sig = [(colours[v], tuple(sorted(colours[u] for u in range(n) if adj[v] >> u & 1)))
               for v in range(n)]
        vals = sorted(set(sig))
        newc = [vals.index(sig[v]) for v in range(n)]
        if newc == colours:
            return colours
        colours = newc

def canon(n, adj):
    colours = refine(n, adj)
    classes = {}
    for v in range(n):
        classes.setdefault(colours[v], []).append(v)
    keys = sorted(classes)
    best = -1
    for combo in itertools.product(*[itertools.permutations(classes[k]) for k in keys]):
        order = [v for part in combo for v in part]
        code = 0
        bit = 0
        for j in range(1, n):
            oj = order[j]
            for i in range(j):
                if adj[order[i]] >> oj & 1:
                    code |= 1 << bit
                bit += 1
        if code > best:
            best = code
    return best

def connected(n, adj):
    if n == 0:
        return True
    seen = 1
    frontier = [0]
    while frontier:
        v = frontier.pop()
        w = adj[v] & ~seen
        while w:
            u = (w & -w).bit_length() - 1
            w &= w - 1
            seen |= 1 << u
            frontier.append(u)
    return seen == (1 << n) - 1

def generate(limit):
    level = {canon(1, (0,)): (0,)}
    counts = {1: 1}
    conn = {1: 1}
    for n in range(2, limit + 1):
        t0 = time.time()
        nxt = {}
        for g in level.values():
            for nbhd in range(1 << (n - 1)):
                adj = list(g) + [nbhd]
                for u in range(n - 1):
                    if nbhd >> u & 1:
                        adj[u] |= 1 << (n - 1)
                adj = tuple(adj)
                c = canon(n, adj)
                if c not in nxt:
                    nxt[c] = adj
        level = nxt
        counts[n] = len(level)
        conn[n] = sum(1 for g in level.values() if connected(n, g))
        print(f"n={n}  all={counts[n]}  connected={conn[n]}  {time.time()-t0:.1f}s", flush=True)
    return counts, conn

if __name__ == "__main__":
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    counts, conn = generate(limit)
    A000088 = [1, 1, 2, 4, 11, 34, 156, 1044, 12346]
    A001349 = [1, 1, 1, 2, 6, 21, 112, 853, 11117]
    print("--- against the published counts ---")
    for n in sorted(counts):
        ok_all = counts[n] == A000088[n]
        ok_con = conn[n] == A001349[n]
        print(f"n={n}  all {counts[n]} vs {A000088[n]} {'ok' if ok_all else 'MISMATCH'};"
              f"  connected {conn[n]} vs {A001349[n]} {'ok' if ok_con else 'MISMATCH'}")
