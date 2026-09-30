# CFMP: an explicit degree-ten high edge in a three-star packet

## Scope and theorem

This is a paper-first strict hyper-ideal realization of one explicit ideal
triangulation. It is a new finite incidence class beyond the degree-eight /
degree-at-least-twelve three-edge packet theorem: the same three-star packet
has a global edge of degree exactly ten (and another of degree 38).

Take the 16 tetrahedra and the face pairings in the table below. Local edges
are ordered `(01,02,03,12,13,23)`. The six degree-eight classes are the local
edges 0,1,2 in every tetrahedron; thus every tetrahedron has one three-star
packet. The remaining classes have degrees 10 and 38. Every degree-ten
occurrence has a degree-38 high neighbour in the actual local incidence
(table audit below).

**Generalized incidence theorem.** The same argument applies to any finite
orientable ideal triangulation whose global degrees lie in
`{8,10} ∪ {d:d>=38}`, with three-star packets in every tetrahedron, provided
that every degree-ten occurrence admits a formula-coordinate relabelling with
low neighbours in positions 2 and 6, opposite low edge in position 4, and high
neighbours in positions 3 and 5, with at least one of those two high neighbours
of degree at least 38 (the other may have degree 10 or at least 38). For each high edge of degree `d>=38`, use an upper endpoint `21/20` and
choose a lower endpoint `1+delta_d` with
`0<delta_d<2*(1-cos(2*pi/d))/(2+cos(2*pi/d))`; the interval is nonempty
(and the finite product is compact). The degree-ten interval is the one below.
The explicit 16-tetrahedron table supplies a nonempty orientable instance.

**Theorem.** This triangulation has a nondegenerate hyper-ideal length vector
with zero cone curvature at every edge, hence a hyperbolic realization with
totally geodesic boundary. Its edge degrees are
`[8,8,8,8,8,8,10,38]`.

No unrestricted minimum-eight or minimum-six CFMP claim is made. The proof is
an actual shared-edge co-volume minimum on a heterogeneous global box; no
zero-curvature solution is assumed in advance.

## Six-variable cosine and heterogeneous box

Use Zhao's local order `(12,13,14,34,24,23)` and

```
A = 2*x1*x2*x6 + x1^2 + x2^2 + x6^2 - 1
B = 2*x1*x3*x5 + x1^2 + x3^2 + x5^2 - 1
P = x2*x3 + x5*x6 + x1*x2*x5 + x1*x3*x6 - (x1^2 - 1)*x4
phi_1 = P / sqrt(A*B),       alpha_1 = arccos(phi_1).
```

On `[1,2]^6`, `phi_1` is nondecreasing in the four neighbouring
coordinates and nonincreasing in the opposite coordinate (Zhao, Lemma 3.4;
`partial phi_1/partial x4 = -(x1^2-1)/sqrt(A B)`). The universal envelope
`2(2-u)/(u+1) <= phi_1 <= (9-u)/(7+u) < 1` puts every following box in the
nondegenerate hyper-ideal length domain.

Use this common global cosh-length box:

```
 degree 8:   11/8 <= x_e <= 2
 degree 10:  11/10 <= x_e <= 71/50
 degree 38:  1009/1000 <= x_e <= 21/20.
```

All endpoints are strictly above one and the intervals are nonempty.

## Exact face-sign certificates

A direct audit of every local occurrence, with all vertex relabellings that
send the target edge to coordinate 1, gives the following conservative
endpoint bounds. For degree ten the upper row uses the actual incidence fact
that each of the ten occurrences has the two low neighbours and two high
neighbours, at least one of degree at least 38, in the coordinate placement
shown. The other high coordinate is conservatively relaxed to the larger degree-10
upper endpoint 71/50; the four stabilizer placements give the same value.

| global degree | lower-face cosine bound | upper-face cosine bound |
|---:|---:|---:|
| 8 | `143/200` | `35941/50941` |
| 10 | `6/7` | `19195*sqrt(880915135)/704732108` |
| 38 | `1982/2009` | `4489*sqrt(8216635)/13146616` |

The degree-eight lower row is `phi(11/8,11/8,11/8,71/50,1,1)`; the
upper row is `phi(2,2,2,1,71/50,71/50)`. The degree-ten upper row is
`phi(71/50,2,71/50,11/8,21/20,2)`. For a degree-38 target in a three-star, the two actual formula-coordinate
patterns put the high neighbours in positions `{3,5}` or `{2,6}`. In either
case monotonicity relaxes to one of
`phi(21/20,2,71/50,11/8,71/50,2)` and
`phi(21/20,71/50,2,11/8,2,71/50)`; both equal
`4489*sqrt(8216635)/13146616`. Lower faces of degrees 10 and 38 use the
universal envelope at `u=11/10` and `u=1009/1000`, respectively.

The strict comparisons are exact:

```
(143/200)^2 - 1/2 = 449/40000 > 0
1/2 - (35941/50941)^2 = 11474519/5189970962 > 0

cos(pi/5) < 5/6 < 6/7
```

For the degree-ten upper row, its squared cosine is
`1842240125/2818928432`. Put
`r = 785141963/352366054 = 8*q^2 - 3`; then

```
5 - r^2 = 4361277994161211/124161836011530916 > 0,
```

so `q^2 < (3+sqrt(5))/8 = cos(pi/5)^2`.

For the degree-38 lower face, let `t=pi/19`. Since `pi>157/50`,
`t>157/950`; the Taylor upper polynomial
`T4(s)=1-s^2/2+s^4/24` is decreasing on `(0,1)`, and
`cos t <= T4(t)`, so

```
cos(pi/19) < 1-(157/950)^2/2+(157/950)^4/24
             < 1982/2009,
```

with exact final difference
`7279213469191/39272233350000000`. For the degree-38 upper row,
`q=4489*sqrt(8216635)/13146616` and
`q^2=100755605/105172928`. Since `pi<22/7`,

```
cos(pi/19) > 1-(22/133)^2/2 = 17447/17689,
```

and the squared comparison has positive difference
`69701057146221/4701240714411584`.

Therefore every degree-eight lower/upper occurrence has angle respectively
less/greater than `pi/4`; every degree-ten occurrence has angle respectively
less/greater than `pi/5`; and every degree-38 occurrence has angle
respectively less/greater than `pi/19`. Summing over 8, 10 and 38 occurrences
puts the lower faces at positive curvature and upper faces at negative
curvature.

Let `H` be the shared-edge Luo--Yang co-volume minus `2*pi*sum l_e` on the
compact product box after `x_e=cosh l_e`. Its derivative is
`partial H/partial l_e = -K_e`. Every lower face has `K_e>0`, and every upper
face has `K_e<0`; an inward coordinate direction strictly decreases `H` at
every boundary point. A minimizer is interior, where all `K_e=0`. Shared
lengths make paired hexagonal faces isometric, so the resulting metric is the
claimed nondegenerate realization.

## Face pairings and topology audit

A row `(t,f) -- (u,g) : p0p1p2p3` pairs the face opposite vertex `f` to the
face opposite `g`, sending source vertex `i` to target vertex `p_i`; reverse
rows use the inverse permutation.

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
| (0,0) | (3,0) | 0231 |
| (5,0) | (6,0) | 0312 |
| (14,0) | (10,0) | 0231 |
| (13,0) | (12,0) | 0321 |
| (2,0) | (7,0) | 0231 |
| (9,0) | (8,0) | 0132 |
| (15,0) | (4,0) | 0213 |
| (11,0) | (1,0) | 0321 |

Transitive closure of local edge identifications gives six classes of size 8,
one of size 10 and one of size 38. The six size-eight classes consist exactly
of local indices `6*t+0,6*t+1,6*t+2`, so every tetrahedron is the same
three-star packet. The two other classes are the degree-ten and degree-38
high edges. Direct incidence enumeration verifies that each degree-ten local
occurrence has a degree-38 high neighbour and that its opposite edge is
low. Face completeness, dual connectivity, a coherent orientation, circular
edge links with no reversed edge, and the two connected orientable vertex
links are checked by the standalone standard-library verifier accompanying
this document (`verify_degree10_star.py` and `audit_degree10_bounds.py`); the links have `(F,V,chi)=(16,6,-2)` and `(48,10,-14)`
(genus 2 and 8). The second verifier uses only exact rational arithmetic for
all endpoint squares and checks every formula-coordinate stabilizer placement.

## Relation to existing CFMP work

The existing Section 16 theorem treats a four-low-edge cycle and already has
high threshold 12; it does not cover this three-star packet. Section 26's
transition estimates use high thresholds 16/17 in a different mixed packet
system. The previous three-edge theorem used a common high interval ending at
`10/7` and required every high degree to be at least 12. The present result
uses actual incidence and degree-dependent intervals to realize a degree-10
high edge in a nonempty orientable manifold. It is not a claim about arbitrary
three-star triangulations, arbitrary minimum-eight triangulations, or the
original CFMP minimum-six conjecture.

## References

- F. Costantino, R. Frigerio, B. Martelli, C. Petronio,
  *Triangulations of 3-manifolds, hyperbolic relative handlebodies, and Dehn
  filling*, arXiv:math/0402339, Conjecture 0.8.
- X. Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class of
  Compact 3-Manifolds with Boundary*, arXiv:2601.15174v2, Lemma 2.2,
  Proposition 2.4 and Lemma 3.4.
- F. Luo and T. Yang, *Volume and rigidity of hyperbolic polyhedral
  3-manifolds*, arXiv:1404.5365.
