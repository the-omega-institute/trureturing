# CFMP pure three-cycle degree-(8,10) theorem

This note records a new packet-specific strict hyper-ideal realization and a
necessary center-link count. It is complementary to the pure three-star
threshold-12 result and to the star degree-10 construction: the low local
edges form a peripheral triangle and the high local edges form the center
star.

## Main theorem

Let `(M,T)` be a finite connected orientable ideal triangulation of a compact
3-manifold with boundary components of genus at least two. In each tetrahedron
name the vertices `(p0,p1,p2,c)`, require low local edges
`p0p1,p0p2,p1p2`, and high local edges `cp0,cp1,cp2`. Assume all low quotient
edges have degree eight and all high quotient edges have degree ten. Then the
triangulation admits a nondegenerate hyper-ideal metric with zero cone
curvature at every quotient edge.

Use `x_e=cosh(l_e)` and the global box

```
low  5/4 <= x_e <= 2,
high 6/5 <= x_e <= 8/5.
```

Zhao's six-variable cosine is monotone nondecreasing in the four adjacent
coordinates and nonincreasing in the opposite coordinate. The four extremal
values for a low target are

```
52*sqrt(1878)/2817,  26*sqrt(17)/153,
```
whose squares are `5408/8451 > 1/2` and `676/1377 < 1/2`. The four extremal
values for a high target are

```
763/939,  55/68,
```
with squares `582169/881721` and `3025/4624`. The strict comparisons with
`cos(pi/5)^2=(3+sqrt(5))/8` follow from

```
2012189^2 - 5*881721^2 = 161744962516 > 0,
5*578^2 - 1291^2 = 3739 > 0.
```
Therefore lower/upper faces have respectively positive/negative curvature at
low degree-eight and high degree-ten edges. The shared-edge Luo--Yang
co-volume has derivative `-K_e`; its compact-box minimum is interior, giving
`K_e=0` for every edge. The universal `[1,2]^6` cosine envelope places the
whole box in the genuine hyper-ideal length domain.

## Center-link necessity

Role-homogeneous face maps preserve the LLL face (opposite `c`) and the three
LHH faces. The unique low edge in an LHH face has opposite vertex `c`, so
center ideal vertices cannot identify with peripheral vertices. For a center
link component `S`, let `N_S` be its tetrahedron count and `h_S` the number of
high quotient classes with center endpoint in `S`. Its link cell counts are

```
F=N_S,  E=3*N_S/2,  V=h_S,
chi=h_S-N_S/2=2-2*g_S,
3*N_S = sum_{e in H_S} degree(e).
```
If all high classes in `S` have common degree `d`, then
`N_S(d-6)=4d(g_S-1)`. At `d=10`, `N_S=10(g_S-1)`, so `10 | N_S`. Globally,
three low occurrences per tetrahedron and low degree eight imply `8 | N`;
hence an all-(8,10) pure-cycle triangulation has `40 | N`.

The theorem is conditional on the stated incidence and manifold hypotheses;
no explicit face pairing is asserted here. It is independent of Uemura's
local-bichromatic criterion (which assumes at most two quotient-edge classes
in each low-valence tetrahedron) and of his parameterized invariant-box
angle-sum criterion.

## References

- [Blueprint theorem](../../Blueprint/D5/S3/Geometry/Hyperideal/ThreeCycleDegree10.md)
- S. Uemura, *Local Combinatorial Criteria for Geometric Hyper-ideal
  Triangulations via Combinatorial Ricci Flow*, arXiv:2609.34108v1,
  Sections 3 and 5, https://arxiv.org/html/2609.34108
- X. Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class of
  Compact 3-Manifolds with Boundary*, arXiv:2601.15174v3.
- X. Luo and T. Yang, *Volume and rigidity of hyperbolic polyhedral
  3-manifolds*, arXiv:1404.5365.
