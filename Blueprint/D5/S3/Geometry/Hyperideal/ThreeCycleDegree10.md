# CFMP pure three-cycle: a degree-10 theorem and center-link divisibility

## Scope and novelty

Let `(M,T)` be a finite, connected, orientable ideal triangulation of a
compact 3-manifold whose boundary components have genus at least two. Assume
every tetrahedron is a pure three-cycle packet. Thus, after a local naming
`(p_0,p_1,p_2,c)`, the three low edges are the peripheral triangle
`p_0p_1,p_0p_2,p_1p_2` and the three high edges are the center star
`cp_0,cp_1,cp_2`. Assume the low quotient edges all have degree eight and
the high quotient edges all have degree ten. (The incidence theorem below
allows arbitrary high degrees `d_e >= 10`.) Since low and high degrees are
distinct, every face map preserves the low/high classes automatically.

This is the complementary packet to the pure three-star theorem. It is not
covered by the earlier threshold-12 three-edge box. The exact box below gives
strict degree `(8,10)` geometricity for the cycle packet. The center-link
cell count gives a separate necessary divisibility law. Uemura,
arXiv:2609.34108v1, has no three-cycle/LLL/LHH or center-link-divisibility
statement; its local-bichromatic theorem instead requires at most two quotient
classes in each low-valence tetrahedron, which a generic cycle packet does not
satisfy.

## Face signatures and role separation

The face opposite `c` is LLL. Each face opposite a peripheral vertex is LHH,
with a unique low edge. A face pairing preserves the low/high class of each
edge. Hence LLL faces pair only with LLL faces, and LHH faces only with LHH
faces. In an LHH face, the unique low edge has opposite vertex `c`; therefore
a face map sends `c` to `c`. An LLL face contains no `c`. Consequently center
ideal vertices and peripheral ideal vertices form disjoint link components.

This argument only uses role-homogeneous pairings. It is automatic when low
edges have degree eight and all high edges have degree at least ten. It must
not be used if a degree-eight quotient class is allowed in both local roles.

## Center-link theorem (arbitrary high degrees)

Fix a center-link component `S`. Let `N_S` be the number of tetrahedra whose
center lies in `S`, and let `H_S` be the set of high quotient edges whose
center endpoint belongs to `S`; write `h_S=|H_S|`.

Each tetrahedron contributes one center truncation triangle, so `F(S)=N_S`.
Its three incident LHH faces give `E(S)=3N_S/2`. Every high edge has a center
endpoint, and role preservation keeps all of its local occurrences at that
same center component. Thus each high quotient class in `H_S` contributes one
link vertex and `V(S)=h_S`. Since valid orientable ideal triangulations have
closed orientable links,

```
chi(S) = h_S - N_S/2 = 2 - 2g_S,
N_S = 2h_S - 4 + 4g_S.
```

Moreover, counting the three center-star edge occurrences per tetrahedron,

```
3 N_S = sum_{e in H_S} d_e.
```

If every high class meeting `S` has a common degree `d`, then
`d h_S=3N_S` and

```
chi(S) = N_S(3/d - 1/2),
N_S(d-6)=4d(g_S-1).
```
For `d=10`, this is `N_S=10(g_S-1)` and therefore `10 | N_S` for every
center-link component. Independently, the three low occurrences per
 tetrahedron and low degree eight give `3N/8` low quotient classes globally,
so `8 | N`. Hence an all-(8,10) pure-cycle triangulation satisfies
`40 | N` (and, componentwise, `10 | N_S`).

No geometric assumption enters this topological obstruction.

## Degree-(8,10) static-box realization

Put `x_e=cosh(l_e)` and use the Luo--Yang six-variable cosine in a compatible
ordering `(e_1,...,e_6)`:

```
phi = (x2*x3 + x5*x6 + x1*x2*x5 + x1*x3*x6
       - (x1^2-1)*x4) / sqrt(A*B),
A = 2*x1*x2*x6 + x1^2+x2^2+x6^2-1,
B = 2*x1*x3*x5 + x1^2+x3^2+x5^2-1.
```
The angle at the target edge is `alpha=arccos(phi)`. Zhao's monotonicity
lemma gives that `phi` is nondecreasing in the four adjacent coordinates and
nonincreasing in the opposite coordinate. The universal envelope on
`[1,2]^6`,
`2(2-u)/(u+1) <= phi_u <= (9-u)/(7+u) < 1`, puts the full box below in the
nondegenerate hyper-ideal length domain.

Use the common global box

```
low:  5/4 <= x_e <= 2,
high: 6/5 <= x_e <= 8/5.
```

For a low target edge, choose an endpoint ordering with adjacent coordinates
(low, high), opposite high, and opposite partners (high, low). Monotonicity
reduces the lower and upper faces to

```
L_low = phi(5/4, 5/4, 6/5, 8/5, 6/5, 5/4)
      = 52*sqrt(1878)/2817,
L_up  = phi(2, 2, 8/5, 6/5, 8/5, 2)
      = 26*sqrt(17)/153.
```
The compatible ordering based at the other endpoint swaps the two symmetric
pairs and gives the same values. Exact comparisons are

```
L_low^2 = 5408/8451 > 1/2,     L_up^2 = 676/1377 < 1/2.
```
Thus every degree-eight occurrence has `alpha < pi/4` on a low lower face and
`alpha > pi/4` on a low upper face.

For a high target edge, its two adjacent low edges, two adjacent high edges,
and opposite low edge give

```
H_low = phi(6/5, 5/4, 5/4, 2, 6/5, 6/5) = 763/939,
H_up  = phi(8/5, 2, 2, 5/4, 8/5, 8/5) = 55/68.
```
The endpoint ordering based at the other high endpoint is symmetric and has the
same values. Since all quantities are positive,

```
H_low > cos(pi/5),   H_up < cos(pi/5).
```
For the lower comparison, square and use
`H_low^2=582169/881721`; equivalently
`2012189^2 - 5*881721^2 = 161744962516 > 0`.
For the upper comparison, `H_up^2=3025/4624` and
`8H_up^2-3=1291/578`; the strict inequality
`1291/578 < sqrt(5)` follows from
`5*578^2 - 1291^2 = 3739 > 0`.

Consequently, around every low degree-eight edge the angle sum is strictly
below `8*pi/4=2*pi` on a lower face and strictly above `2*pi` on an upper
face. Around every high degree-ten edge the sum is strictly below
`10*pi/5=2*pi` on a lower face and strictly above `2*pi` on an upper face.
Let `H_cov` be the shared-edge Luo--Yang co-volume minus
`2*pi*sum_e l_e` on the compact box. Its derivative is
`partial H_cov/partial l_e = -K_e`. At each lower boundary face `K_e>0`, so
moving inward by increasing `l_e` strictly decreases `H_cov`; at each upper
face `K_e<0`, so moving inward by decreasing `l_e` strictly decreases it.
A minimizer is interior and has `K_e=0` for every edge. The global lengths make
paired right-angled hexagonal faces isometric, so the triangulation has a
nondegenerate hyperbolic realization with totally geodesic boundary.

This is a strict compact-box/co-volume proof and does not assume a Ricci-flow
limit or a zero-curvature metric in advance.

## Comparison with Uemura (arXiv:2609.34108v1)

Uemura's Theorem 3.5 (local bichromaticity) is a different hypothesis: every
tetrahedron containing valence 7--9 edges must use at most two quotient-edge
classes. A role-homogeneous three-cycle tetrahedron generally uses six classes,
so that theorem does not apply. Uemura's Theorem 5.5 and Corollary 5.9 are
parameterized invariant-box angle-sum tests; they do not state the cycle
face-signature separation, the center-link formula, or the `(8,10)` box above.
The present result is therefore a packet-specific theorem, with exact endpoint
certificates and a necessary topological count rather than a restatement of
Uemura's criterion.

## References

- S. Uemura, *Local Combinatorial Criteria for Geometric Hyper-ideal
  Triangulations via Combinatorial Ricci Flow*, arXiv:2609.34108v1 (2026),
  Sections 3 and 5: https://arxiv.org/html/2609.34108
- X. Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class of
  Compact 3-Manifolds with Boundary*, arXiv:2601.15174v3 (2026).
- F. Costantino, R. Frigerio, C. Petronio, *Triangulations of 3-manifolds,
  hyperbolic relative handlebodies, and Dehn filling*, arXiv:math/0402339.
- X. Luo and T. Yang, *Volume and rigidity of hyperbolic polyhedral
  3-manifolds*, arXiv:1404.5365.
