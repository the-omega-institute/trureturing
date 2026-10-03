# CFMP: adjacent three-edge degree-eight clusters

## Scope

Let (N,T) be a finite, connected, orientable ideal triangulation of a compact
3-manifold whose boundary components have genus at least two. Assume every
global edge has degree exactly 8 or at least 12. Write L for the degree-eight
edges and H for the remaining edges.

For a tetrahedron sigma, let S_sigma be the set of its six local edges whose
global edge lies in L. Assume that |S_sigma|=3 and every member of S_sigma is adjacent (in the tetrahedron) to exactly two other members of S_sigma, so each packet is a three-star or three-cycle. In addition, every high local edge is opposite a low local edge and has at least two high neighbours. These high-occurrence conditions follow for either allowed three-edge packet. This is
an incidence condition on actual local edge occurrences; it does not identify
distinct global edges or impose equal lengths.

The theorem below is a paper proof of a valence-eight subcase at high-edge
threshold 12. The geometric theorem and topology certificate are not yet
formalized in Lean. In particular, checking isolated rational inequalities
would not formalize this theorem. The existing four-cycle theorem in
CFMP_GEOMETRIC_REALIZATION, Section 16, already has threshold 12; that local
packet has four low edges and is different from the three-edge packets here.

## Six-variable cosine

Use the local order (12,13,14,34,24,23), with opposite pairs (1,4), (2,5),
and (3,6). Put x_i = cosh l_i and

A = 2*x1*x2*x6 + x1^2 + x2^2 + x6^2 - 1,
B = 2*x1*x3*x5 + x1^2 + x3^2 + x5^2 - 1,

P = x2*x3 + x5*x6 + x1*x2*x5 + x1*x3*x6
    - (x1^2 - 1)*x4,
phi_1 = P / sqrt(A B).

For a genuine hyper-ideal tetrahedron the dihedral angle at edge 1 is
alpha_1 = arccos(phi_1). The length-domain criterion and the formula are
Zhao, Lemma 2.2 and Proposition 2.4. On [1,2]^6, phi_1 is nondecreasing in
x2,x3,x5,x6 by Zhao, Lemma 3.4. It is nonincreasing in x4 directly from

  partial phi_1 / partial x4 = -(x1^2 - 1) / sqrt(A B) <= 0.

The explicit derivative sign is also formalized in the repository's
mixed-coordinate comparison.

## Theorem

Under the incidence hypotheses above, the given triangulation admits a
nondegenerate hyper-ideal metric with zero cone curvature at every edge.
Consequently its face pairings give a hyperbolic metric with totally geodesic
boundary in the strict hyper-ideal sense.

## Proof

Let D be the maximum global edge degree. Set
a = 5/4 and c = 10/7. Let q_D = cos(2*pi/D), and choose

  0 < delta < min(1/3, 2*(1-q_D)/(2+q_D)),  h = 1 + delta.

Use the common global cosh-length box

  a <= x_e <= 2       (e in L),
  h <= x_e <= c       (e in H).

The box is nonempty since h < 4/3 < c. To check its geometric domain,
monotonicity gives, for any target coordinate 1 < u <= 2,

  0 <= 2*(2-u)/(u+1) <= phi_1 <= (9-u)/(7+u) < 1.

The lower and upper envelopes use (u,1,1,2,1,1) and
(u,2,2,1,2,2), respectively. These bounds apply after relabeling to all
six edges. Zhao, Proposition 2.4, therefore places the whole closed box
in the genuine hyper-ideal length domain, not merely its closure.

### Degree-eight lower faces

Fix a local degree-eight edge as edge 1 and put x1=a. By monotonicity, the
cosine is bounded below by the relaxed endpoint values listed below. The
entries list (x2,x3,x4,x5,x6); coordinates 1 and 2 used for high edges
can be outside [h,c], so these are conservative bounds, not attained minima.

  three-star:   (a,a,2,1,1)       phi_1 = 73/100
  three-cycle:  (a,1,2,1,a)       phi_1 = 8*sqrt(6)/27

Each displayed number has square strictly larger than 1/2:
5329/10000 > 1/2 and 384/729 > 1/2. Both numbers are positive,
so taking squares preserves the comparison with 1/sqrt(2).
Therefore every occurrence has alpha_1 < pi/4. A degree-eight edge has eight
occurrences, so its cone angle is strictly less than 2*pi and K_e > 0.

### Degree-eight upper faces

Put x1=2. Relaxing the high opposite coordinate to 1 gives these upper
bounds for the cosine:

  three-star:   (2,2,1,c,c)       phi_1 = 709/1003
  three-cycle:  (2,c,1,c,2)       phi_1 = 11*sqrt(249)/249

Each square is strictly smaller than 1/2:
2*709^2 < 1003^2 and 2*(11^2*249) < 249^2. The endpoint
values are positive, so each is strictly below 1/sqrt(2).
Thus alpha_1 > pi/4 at every occurrence, the cone angle is strictly larger
than 2*pi, and K_e < 0.

### High-edge lower faces

For x1=h, the universal lower envelope on [1,2]^6 gives

  phi_1 >= 2*(2-h)/(h+1) > q_D.

Hence alpha_1 < 2*pi/D <= 2*pi/d(e), so the cone angle at every high edge
is strictly less than 2*pi and K_e > 0. The first strict inequality is exactly
the choice of delta above.

### High-edge upper faces

Put x1=c and lower the opposite low coordinate to a. Select two high
neighbours and increase them to c; increase the other two neighbours to 2.
Monotonicity permits this relaxation even if there are additional high
neighbours. There are six choices of the selected positions:

| selected high positions | endpoint cosine |
|---|---|
| {2,3}, {5,6} | 281/332 |
| {2,5}, {3,6} | 5965/6972 |
| {2,6}, {3,5} | 145*sqrt(91273)/52156 |

All values are positive. With Q=5965/6972, the exact square comparisons are

  Q^2 - (281/332)^2 = 47464/3038049 > 0,
  Q^2 - (145*sqrt(91273)/52156)^2
      = 1051170700/39613120911 > 0,
  3/4 - Q^2 = 875363/48608784 > 0.

Thus phi_1 <= Q < sqrt(3)/2 = cos(pi/6). Every high-edge occurrence
has alpha_1 > pi/6. Since d(e) >= 12, the cone angle is strictly greater
than 2*pi and K_e < 0. Some of the six relaxed choices cannot occur in
one allowed packet; including them only weakens this sufficient bound.

### Co-volume minimum

Let l_e = arccosh(x_e), and let Omega be the corresponding compact length box.
The standard co-volume identity (Luo--Yang) gives, for the global co-volume

  H(l) = sum_sigma cov_sigma(l|sigma) - 2*pi*sum_e l_e,

  partial H / partial l_e = -K_e.

At a lower face of Omega, K_e > 0, so increasing l_e decreases H. At an upper
face, K_e < 0, so decreasing l_e decreases H. Every boundary point therefore
admits an inward direction of strict decrease. A minimizer of H on Omega lies
in the interior, where all partial derivatives vanish. Thus K_e=0 for every
global edge. The common global lengths make every paired hexagonal face
isometric; zero cone curvature removes all interior edge singularities. This
is the claimed nondegenerate hyperbolic realization.

No Ricci-flow convergence theorem is used to assume existence. The only
external geometric inputs are the six-variable formula, its monotonicity and
length-domain criterion, and the co-volume gradient identity. Convexity
is not needed for this compact interior-minimum argument.

## Relation to the CFMP conjecture

Costantino--Frigerio--Martelli--Petronio, Conjecture 0.8
(arXiv:math/0402339; Conjecture 1.8 in the published version), asks for a geometric realization of an ideal
triangulation of a compact 3-manifold whose edge valences are at least six by
hyperbolic truncated (partially truncated) tetrahedra. The theorem above is a strict hyper-ideal subcase:
it does not claim the full minimum-six conjecture, arbitrary degree-eight
packets, or the partially truncated boundary cases. Zhao's 2026 theorem for
minimum valence nine does not cover the degree-eight edges here. A realization
of a different subdivision would not alone prove that this prescribed
triangulation is geometric. No novelty claim is made for the compact-box
co-volume argument or the underlying analytic comparison. Relative to the
repository baseline, Section 16 has four low edges per tetrahedron, while
Section 26.3 has high-edge thresholds 16 and 17; neither directly covers
the three-edge packets with degree-12 high edges considered here.

## References

- F. Costantino, R. Frigerio, B. Martelli, C. Petronio,
  *Triangulations of 3-manifolds, hyperbolic relative handlebodies, and Dehn
  filling*, arXiv:math/0402339, Conjecture 0.8:
  https://arxiv.org/abs/math/0402339
  Published source: https://ems.press/content/serial-article-files/43143
- X. Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class of
  Compact 3-Manifolds with Boundary*, arXiv:2601.15174v2:
  https://arxiv.org/html/2601.15174v2
- F. Luo and T. Yang, *Volume and rigidity of hyperbolic polyhedral
  3-manifolds*, arXiv:1404.5365:
  https://arxiv.org/abs/1404.5365


## Face compatibility and the next threshold

The two packet types cannot mix in a connected triangulation. A three-star
has one HHH face and three LLH faces. A three-cycle has one LLL face and
three LHH faces. An affine face pairing preserves the global low/high
labels, so it preserves the number of low edges in the face. The two sets
of face signatures are disjoint. Dual-graph connectivity therefore forces
all tetrahedra to have the same packet type.

In the all-three-star case, every high local edge belongs to one HHH face
and one LLH face. Its circular edge link consequently alternates the two
face signatures. Every global high edge then has even degree. In particular,
a numerical upper-angle estimate for degree 11 in this class would not
extend the theorem to any new triangulation: degree at least 11 already
means degree at least 12. The three-cycle case does not have this same
high-edge parity obstruction. These observations make no general claim
that threshold 12 is optimal, either for CFMP or for other length boxes.

## Explicit nonempty packet

The hypotheses occur in a genuine orientable ideal triangulation. Take 16 tetrahedra
indexed by 0,...,15, with face (t,f) opposite vertex f. Pair the following
unordered faces; the displayed permutation sends source vertices to target
vertices (the reverse pairing uses its inverse):

| source | target | permutation |
|---|---|---|
| (0,1) | (8,1) | 0123 |
| (0,2) | (4,2) | 0123 |
| (0,3) | (2,3) | 0123 |
| (1,1) | (9,1) | 0123 |
| (1,2) | (5,2) | 0123 |
| (1,3) | (3,3) | 0123 |
| (2,1) | (10,1) | 0123 |
| (2,2) | (6,2) | 0123 |
| (3,1) | (11,1) | 0123 |
| (3,2) | (7,2) | 0123 |
| (4,1) | (12,1) | 0123 |
| (4,3) | (7,3) | 0123 |
| (5,1) | (13,1) | 0123 |
| (5,3) | (6,3) | 0123 |
| (6,1) | (14,1) | 0123 |
| (7,1) | (15,1) | 0123 |
| (8,2) | (13,2) | 0123 |
| (8,3) | (11,3) | 0123 |
| (9,2) | (12,2) | 0123 |
| (9,3) | (10,3) | 0123 |
| (10,2) | (15,2) | 0123 |
| (11,2) | (14,2) | 0123 |
| (12,3) | (14,3) | 0123 |
| (13,3) | (15,3) | 0123 |
| (7,0) | (11,0) | 0132 |
| (2,0) | (6,0) | 0312 |
| (8,0) | (13,0) | 0231 |
| (9,0) | (1,0) | 0312 |
| (10,0) | (0,0) | 0132 |
| (15,0) | (4,0) | 0213 |
| (12,0) | (5,0) | 0312 |
| (14,0) | (3,0) | 0321 |

The 96 local edges fall into eight global classes. Six classes have size 8,
one has size 12 and one has size 36. A direct transitive-closure check gives
the six degree-eight classes
{0,6,12,18,24,30,36,42}, {1,7,13,19,49,55,61,67},
{2,8,26,32,50,56,74,80}, {14,20,38,44,62,68,86,92},
{25,31,37,43,73,79,85,91}, {48,54,60,66,72,78,84,90},
where local edge number is 6t+j in order (01,02,03,12,13,23).
The remaining classes have sizes 12 and 36. Every tetrahedron has local
degree-eight edges (01,02,03), a three-star. The two vertex links are connected
orientable surfaces with (F,V,chi)=(16,6,-2) and (48,10,-14), hence genera 2
and 8. Each edge link is a single circle and no edge is identified with its
reverse. Therefore this is a genuine compact orientable manifold after ideal
vertices are truncated, with one degree-eight packet type and high degrees 12
and 36.


## Reproducible topology certificate

The following Python 3 standard-library checker reads the actual pairing
table above from this document. Save it as `verify_packet.py` and run
`python verify_packet.py CFMP_EIGHT_TRIANGLE_CLUSTERS.md`. It verifies face
completeness, dual connectivity, a coherent orientation, global edge classes,
local stars, circular edge links without reversal, and the vertex-link data.
The link-surface justification is included in the code comments; Euler
characteristics alone would not suffice.

```python
import itertools
import re
import sys
from collections import defaultdict
from pathlib import Path

text = Path(sys.argv[1]).read_text()
rows = re.findall(r"\| \((\d+),(\d+)\) \| \((\d+),(\d+)\) \| ([0-3]{4}) \|", text)
n = 16
V = range(4)
edges = list(itertools.combinations(V, 2))
edge_index = {e: i for i, e in enumerate(edges)}

class DSU:
    def __init__(self, size):
        self.p = list(range(size))
    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x
    def union(self, x, y):
        self.p[self.find(x)] = self.find(y)
    def classes(self):
        out = defaultdict(list)
        for x in range(len(self.p)):
            out[self.find(x)].append(x)
        return list(out.values())

edge = DSU(6*n)
directed = DSU(12*n)
vertex = DSU(4*n)
tetrahedron = DSU(n)
pair = {}
orientation = [(-1)**((t >> 1).bit_count()) for t in range(n)]
assert len(rows) == 2*n
for ts, fs, us, gs, ps in rows:
    t, f, u, g = map(int, (ts, fs, us, gs))
    p = tuple(map(int, ps))
    assert 0 <= t < n and 0 <= u < n and sorted(p) == list(V)
    assert p[f] == g and (t, f) != (u, g)
    assert (t, f) not in pair and (u, g) not in pair
    sign = (-1)**sum(p[i] > p[j] for i in V for j in V if i < j)
    assert sign == -orientation[t]*orientation[u]
    inverse = tuple(p.index(i) for i in V)
    pair[t, f] = (u, p)
    pair[u, g] = (t, inverse)
    tetrahedron.union(t, u)
    for v in V:
        if v != f:
            vertex.union(4*t+v, 4*u+p[v])
    for i, (a, b) in enumerate(edges):
        if f not in (a, b):
            c, d = p[a], p[b]
            j = edge_index[tuple(sorted((c, d)))]
            edge.union(6*t+i, 6*u+j)
            reverse = int(c > d)
            for end in (0, 1):
                directed.union(12*t+2*i+end, 12*u+2*j+(end ^ reverse))
assert len(pair) == 4*n and len(tetrahedron.classes()) == 1
classes = edge.classes()
degrees = sorted(map(len, classes))
assert degrees == [8, 8, 8, 8, 8, 8, 12, 36]
low = {e for block in classes if len(block) == 8 for e in block}
for t in range(n):
    assert {i for i in range(6) if 6*t+i in low} == {0, 1, 2}

# Each equivalence class is exactly one edge-link circle, with no reversal.
for block in classes:
    assert all(directed.find(2*k) != directed.find(2*k+1) for k in block)
    t, i = divmod(min(block), 6)
    ab = edges[i]
    f = min(set(V)-set(ab))
    start = (t, ab, f)
    state = start
    cycle = []
    while True:
        t, ab, f = state
        cycle.append(6*t+edge_index[tuple(sorted(ab))])
        u, p = pair[t, f]
        cd = tuple(p[v] for v in ab)
        ff = next(v for v in V if v not in cd and v != p[f])
        state = (u, cd, ff)
        if (u, set(cd), ff) == (start[0], set(start[1]), start[2]):
            break
        assert len(cycle) <= len(block)
    assert state == start and sorted(cycle) == sorted(block)

# Vertex equivalence is precisely adjacency-connectivity of link triangles.
# Edge-link circles give disc neighborhoods at every link vertex; together
# with the paired link edges this verifies closed surfaces, not just Euler data.
links = []
for block in vertex.classes():
    link_vertices = set()
    for tv in block:
        t, v = divmod(tv, 4)
        for i, (a, b) in enumerate(edges):
            if v in (a, b):
                link_vertices.add(directed.find(12*t+2*i+int(v == b)))
    F, W = len(block), len(link_vertices)
    assert (3*F) % 2 == 0
    links.append((F, W, W-F//2))
assert sorted(links) == [(16, 6, -2), (48, 10, -14)]
print('PASS: connected oriented manifold, no reversed edges, circular edge links')
print('degrees =', degrees)
print('vertex links (F,V,chi) =', sorted(links))
```

Expected output (verified on the table above):

```text
PASS: connected oriented manifold, no reversed edges, circular edge links
degrees = [8, 8, 8, 8, 8, 8, 12, 36]
vertex links (F,V,chi) = [(16, 6, -2), (48, 10, -14)]
```
