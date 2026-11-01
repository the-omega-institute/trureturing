"""Graph polynomial library for refereeing 'The Loopy Polynomial ...'.

Graph = (n, edges) where edges is a list of (u,v) pairs, 0<=u,v<n; u==v means loop.
Edge order = list index (0 smallest).  Least-edge external activity convention.
"""
from itertools import combinations, chain
from functools import lru_cache
from collections import defaultdict

# ---------- basic graph ops ----------

class DSU:
    def __init__(self, n): self.p = list(range(n))
    def find(self, a):
        while self.p[a] != a:
            self.p[a] = self.p[self.p[a]]; a = self.p[a]
        return a
    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb: return False
        self.p[ra] = rb; return True

def comps(n, edges):
    """component id per vertex, using given edge list (loops ignored)."""
    d = DSU(n)
    for (u, v) in edges:
        if u != v: d.union(u, v)
    return [d.find(i) for i in range(n)]

def loops_at(n, edges):
    L = [0]*n
    for (u, v) in edges:
        if u == v: L[u] += 1
    return L

def delete_edge(n, edges, i):
    return (n, edges[:i] + edges[i+1:])

def loopy_contract(n, edges, i):
    """identify endpoints of edges[i]; edge i BECOMES A LOOP (kept)."""
    u, v = edges[i]
    assert u != v
    hi, lo = max(u, v), min(u, v)
    def relabel(w):
        if w == hi: return lo
        return w - 1 if w > hi else w
    new = [(relabel(a), relabel(b)) for (a, b) in edges]
    return (n-1, new)

def ordinary_contract(n, edges, i):
    """identify endpoints of edges[i]; edge i is DELETED."""
    u, v = edges[i]
    assert u != v
    hi, lo = max(u, v), min(u, v)
    def relabel(w):
        if w == hi: return lo
        return w - 1 if w > hi else w
    new = [(relabel(a), relabel(b)) for j, (a, b) in enumerate(edges) if j != i]
    return (n-1, new)

# ---------- polynomial helpers (dict monomial -> int) ----------

def padd(A, B, c=1):
    for k, v in B.items():
        A[k] = A.get(k, 0) + c*v
        if A[k] == 0: del A[k]
    return A

def pmul(A, B, combine):
    C = {}
    for k1, v1 in A.items():
        for k2, v2 in B.items():
            k = combine(k1, k2)
            C[k] = C.get(k, 0) + v1*v2
            if C[k] == 0: del C[k]
    return C

# ---------- loopy polynomial: monomial key = (t_exp, sorted tuple of x-indices) ----------

def _lcomb(k1, k2):
    return (k1[0]+k2[0], tuple(sorted(k1[1]+k2[1])))

def loopy_recursive(n, edges):
    """L_G(t,x) by loopy deletion-contraction (recursive definition)."""
    nonloop = [i for i, (u, v) in enumerate(edges) if u != v]
    if not nonloop:
        Lp = loops_at(n, edges)
        return {(0, tuple(sorted(Lp))): 1}
    i = nonloop[-1]                      # largest non-loop edge
    nc, ec = loopy_contract(n, edges, i)
    nd, ed = delete_edge(n, edges, i)
    res = dict(loopy_recursive(nc, ec))
    D = loopy_recursive(nd, ed)
    padd(res, {(k[0]+1, k[1]): v for k, v in D.items()})
    return res

def spanning_forests(n, edges):
    """yield (F, comp_of_vertex) for every acyclic subset F of non-loop edges."""
    nonloop = [i for i, (u, v) in enumerate(edges) if u != v]
    for r in range(len(nonloop)+1):
        for S in combinations(nonloop, r):
            d = DSU(n); ok = True
            for i in S:
                u, v = edges[i]
                if not d.union(u, v): ok = False; break
            if ok:
                yield set(S), [d.find(x) for x in range(n)]

def _path_in_forest(n, edges, F, a, b):
    """edge indices on the unique a-b path inside forest F (set of edge idx)."""
    adj = defaultdict(list)
    for i in F:
        u, v = edges[i]; adj[u].append((v, i)); adj[v].append((u, i))
    stack = [(a, None, [])]; seen = {a}
    while stack:
        x, _, path = stack.pop()
        if x == b: return path
        for (y, i) in adj[x]:
            if y not in seen:
                seen.add(y); stack.append((y, i, path+[i]))
    return None

def activity(n, edges, F, cid):
    """returns (dict comp->#active, total). Least-edge convention; loops always active."""
    act = defaultdict(int); tot = 0
    for i, (u, v) in enumerate(edges):
        if i in F: continue
        if u == v:
            act[cid[u]] += 1; tot += 1
        elif cid[u] == cid[v]:
            path = _path_in_forest(n, edges, F, u, v)
            if all(i < j for j in path):
                act[cid[u]] += 1; tot += 1
    return act, tot

def loopy_forest(n, edges):
    """L_G via the spanning-forest expansion (eq:forests)."""
    m = len(edges); out = {}
    for F, cid in spanning_forests(n, edges):
        act, tot = activity(n, edges, F, cid)
        size = defaultdict(int)
        for x in range(n): size[cid[x]] += 1
        xs = tuple(sorted(size[c]-1+act[c] for c in size))
        key = (m - len(F) - tot, xs)
        out[key] = out.get(key, 0) + 1
    return out

def Lhat(n, edges):
    """refined loopy polynomial: monomial = sorted tuple of (|V(T)|, eps(T))."""
    out = {}
    for F, cid in spanning_forests(n, edges):
        act, tot = activity(n, edges, F, cid)
        size = defaultdict(int)
        for x in range(n): size[cid[x]] += 1
        key = tuple(sorted((size[c], act[c]) for c in size))
        out[key] = out.get(key, 0) + 1
    return out

# ---------- Tutte's universal V-function ----------

def V_recursive(n, edges):
    """monomial key = sorted tuple of v-indices."""
    nonloop = [i for i, (u, v) in enumerate(edges) if u != v]
    if not nonloop:
        Lp = loops_at(n, edges)
        return {tuple(sorted(Lp)): 1}
    i = nonloop[-1]
    nd, ed = delete_edge(n, edges, i)
    nc, ec = ordinary_contract(n, edges, i)
    res = dict(V_recursive(nd, ed))
    padd(res, V_recursive(nc, ec))
    return res

def V_forest(n, edges):
    """Wang-Sachs / BPR forest expansion (eq:V-forest)."""
    out = {}
    for F, cid in spanning_forests(n, edges):
        act, tot = activity(n, edges, F, cid)
        size = defaultdict(int)
        for x in range(n): size[cid[x]] += 1
        key = tuple(sorted(act[c] for c in size))
        out[key] = out.get(key, 0) + 1
    return out

def loop_augment(n, edges):
    return (n, list(edges) + [(v, v) for v in range(n)])

# ---------- spanning-subgraph invariants ----------

def all_subgraph_terms(n, edges):
    """yield (A, list of (|V(D)|, nu(D)) per component, |A|)."""
    m = len(edges)
    for r in range(m+1):
        for S in combinations(range(m), r):
            d = DSU(n)
            for i in S:
                u, v = edges[i]; d.union(u, v)
            cid = [d.find(x) for x in range(n)]
            size = defaultdict(int); ec = defaultdict(int)
            for x in range(n): size[cid[x]] += 1
            for i in S:
                u, v = edges[i]; ec[cid[u]] += 1
            data = tuple(sorted((size[c], ec[c]-size[c]+1) for c in size))
            yield S, data, len(S)

def U_ext(n, edges):
    out = {}
    for S, data, k in all_subgraph_terms(n, edges):
        out[data] = out.get(data, 0) + 1
    return out

def U_poly(n, edges):
    """monomial key = (sorted tuple of comp sizes, total nullity) ; coeff in (y-1)^nu."""
    out = {}
    for S, data, k in all_subgraph_terms(n, edges):
        key = (tuple(sorted(s for s, _ in data)), sum(nu for _, nu in data))
        out[key] = out.get(key, 0) + 1
    return out

def XB(n, edges):
    """key = (sorted tuple of comp sizes -> p_lambda, |A| -> q^|A|)."""
    out = {}
    for S, data, k in all_subgraph_terms(n, edges):
        key = (tuple(sorted(s for s, _ in data)), k)
        out[key] = out.get(key, 0) + 1
    return out

def polychromate(n, edges):
    """eta_G: key = (sorted block sizes, #internal edges)."""
    out = {}
    verts = list(range(n))
    def parts(lst):
        if not lst: yield []; return
        first, rest = lst[0], lst[1:]
        for p in parts(rest):
            for i in range(len(p)):
                yield p[:i] + [[first]+p[i]] + p[i+1:]
            yield [[first]] + p
    for p in parts(verts):
        blk = [set(b) for b in p]
        ie = 0
        for (u, v) in edges:
            for b in blk:
                if u in b and v in b: ie += 1; break
        key = (tuple(sorted(len(b) for b in blk)), ie)
        out[key] = out.get(key, 0) + 1
    return out

def tutte(n, edges):
    """T_G(X,Y): key=(i,j) coeff of (X-1)^i (Y-1)^j."""
    m = len(edges); rE = n - len(set(comps(n, edges)))
    out = {}
    for r in range(m+1):
        for S in combinations(range(m), r):
            sub = [edges[i] for i in S]
            rA = n - len(set(comps(n, sub)))
            key = (rE-rA, len(S)-rA)
            out[key] = out.get(key, 0) + 1
    return out

def matching_poly(n, edges):
    mk = defaultdict(int)
    m = len(edges)
    for r in range(m+1):
        for S in combinations(range(m), r):
            vs = []
            ok = True
            for i in S:
                u, v = edges[i]
                if u == v: ok = False; break
                vs += [u, v]
            if ok and len(set(vs)) == len(vs): mk[r] += 1
    return dict(mk)

# ---------- pretty printing ----------

def show_L(P):
    terms = []
    for (te, xs), c in sorted(P.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        s = ""
        if c != 1 or (te == 0 and not xs): s += str(c)
        if te: s += ("t" if te == 1 else f"t^{te}")
        cnt = defaultdict(int)
        for i in xs: cnt[i] += 1
        for i in sorted(cnt):
            s += f"x{i}" + (f"^{cnt[i]}" if cnt[i] > 1 else "")
        terms.append(s)
    return " + ".join(terms)

