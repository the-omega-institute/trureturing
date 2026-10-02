# CFMP pure three-cycle packet at degree (8,9): exact box certificate

This paper-first note proves a restricted packet theorem: all low global edges have
degree 8 and all high global edges have degree 9 in a role-homogeneous pure
three-cycle packet.

## Statement

Let `(M,T)` be a finite connected orientable ideal triangulation of a compact
3-manifold with boundary components of genus at least two. In every
 tetrahedron label vertices `(p0,p1,p2,c)`, with low local edges
`p0p1,p0p2,p1p2` and high local edges `cp0,cp1,cp2`. Suppose each low quotient
edge has degree 8 and each high quotient edge has degree 9. Then the prescribed
triangulation has a nondegenerate hyper-ideal length vector with zero cone
curvature at every quotient edge.

The prescribed-triangulation theorem assumes the stated manifold and incidence
hypotheses. The finite Coxeter-sector construction below proves their
non-vacuity without claiming an explicit minimal face-pairing or the
unrestricted CFMP minimum-eight theorem.

## Role separation and necessary topology counts

The three peripheral low edges form the unique LLL face opposite `c`.
The other faces are LHH, with a unique low edge opposite the center vertex.
Because degrees 8 and 9 are distinct, face maps preserve low and high classes,
so LLL pairs only with LLL and LHH only with LHH; every LHH map preserves
the center role. Center vertices therefore cannot identify with peripheral
vertices.

For a center-link component `S`, let `N_S` be its number of center triangles
and `h_S` its number of incident high quotient edges. Each high edge has one
center endpoint and contributes one link vertex. Hence
`F=N_S`, `E=3*N_S/2`, `V=h_S`, and `9*h_S=3*N_S`. Therefore
`chi(S)=-N_S/6=2-2*g_S`, so `N_S=12*(g_S-1)`.
Globally the low-edge count is `3*N/8`, which is integral and forces `8|N`.
Summing the center counts gives `12|N`; thus `24|N`.
These counts are necessary conditions only; the construction below supplies
existence at some finite count, without asserting that N=24 is attained.

## Cosine and monotonicity

Use the standard local ordering `(e1,...,e6)` with opposite pairs `(1,4),
(2,5),(3,6)` and

```
phi = (x2*x3 + x5*x6 + x1*x2*x5 + x1*x3*x6
       - (x1^2-1)*x4) / sqrt(A*B),
A = 2*x1*x2*x6 + x1^2+x2^2+x6^2-1,
B = 2*x1*x3*x5 + x1^2+x3^2+x5^2-1.
```

On `[1,2]^6`, `phi` is nondecreasing in the four adjacent coordinates and
nonincreasing in the opposite coordinate (Zhao Lemma 3.4; the opposite
partial derivative is `-(x1^2-1)/sqrt(A B)`). For target `1<u<=2`, the universal `[1,2]^6` envelope is
`2*(2-u)/(u+1) <= phi_u <= (9-u)/(7+u) < 1`. Thus every coordinate in the box below is strictly greater than 1 and has `0<=phi_u<1`; the length-domain criterion puts the entire box in the genuine hyper-ideal domain.

Source locators: Zhao, arXiv:2601.15174v2, Lemma 3.4 (coordinate monotonicity), Lemma 2.2 and Proposition 2.4 (the six-variable cosine and genuine length domain), https://arxiv.org/html/2601.15174v2. The co-volume differential is Luo--Yang, arXiv:1404.5365v2, Section 4.3 (the displayed Schlaefli identity), Corollary 4.12, and Section 5, formula (5.1) and the following gradient paragraph, https://arxiv.org/html/1404.5365v2#S4.SS3 and https://arxiv.org/html/1404.5365v2#S5. The compact-box minimum argument is given below, not attributed to the volume-maximization Theorems 1.4/6.3.

Use a shared global cosh-length box

```
low:  low_box_A=73/50 <= x_e <= 2,
high: high_box_C=53/40 <= x_e <= high_box_D=347/200.
```

For a low target edge, the cycle packet has adjacent low/high coordinates and
opposite high, so monotonicity gives the lower/upper-face endpoint tuples
`(low_box_A,low_box_A,high_box_C,high_box_D,high_box_C,low_box_A)` and `(2,2,high_box_D,high_box_C,high_box_D,2)`. For a high target, adjacent coordinates
are low,low,high,high and the opposite is low, giving `(high_box_C,low_box_A,low_box_A,2,high_box_C,high_box_C)` and
`(high_box_D,2,2,low_box_A,high_box_D,high_box_D)`.

The exact squared endpoint cosines are

```
Llo^2 = phi(low_box_A,low_box_A,high_box_C,high_box_D,high_box_C,low_box_A)^2 = 23001041/45748800 > 1/2,
Lup^2 = phi(2,2,high_box_D,high_box_C,high_box_D,2)^2 = 1261129/2527362 < 1/2,
Hlo^2 = phi(high_box_C,low_box_A,low_box_A,2,high_box_C,high_box_C)^2 = 1111822336/1885209561,
Hup^2 = phi(high_box_D,2,2,low_box_A,high_box_D,high_box_D)^2 = 12826261216129/21905208090000.
```

Let `q=cos(2*pi/9)`. It is the root in `(3/4,4/5)` of
`8q^3-6q+1=0`. Rational bracketing gives

```
766044/10^6 < q < 766045/10^6.
```
Indeed `f(766044/10^6) = -6996234169/1953125000000000`,
`f(766045/10^6) = 4501708329/10^15`, and `f'(u)>0` on `[3/4,4/5]`.
The root's membership in this interval follows from the alternating cosine
Taylor bounds with `157/225 < 2*pi/9 < 44/63` (using `3.14<pi<22/7`).
The exact margins needed for the high target are

```
Hlo^2 - (766045/10^6)^2
 = 221373786447971959/75408382440000000000 > 0,
(766044/10^6)^2 - Hup^2
 = 176423066265334889/136907550562500000000 > 0.
```

All endpoint numerators and denominators are positive. Therefore every low
occurrence has lower-face angle `< pi/4` and upper-face angle `> pi/4`; every
high occurrence has lower-face angle `< 2*pi/9` and upper-face angle
`>2*pi/9`. Summing 8 or 9 occurrences gives strict inward signs:
`K_e>0` on every lower box face and `K_e<0` on every upper face.

## Variational conclusion

The Luo--Yang shared-edge co-volume minus `2*pi*sum_e l_e` is continuous on
the compact global box and has derivative `-K_e` in each global length
coordinate. The strict face signs exclude a minimizer on any boundary face.
The interior minimizer has `K_e=0` for all quotient edges. The common global
lengths make paired right-angled hexagons isometric, yielding the required
nondegenerate hyper-ideal realization of the prescribed triangulation.

This uses the same cited ordinary geometric inputs as the current CFMP notes;
only the packet-specific endpoint arithmetic is new. It does not claim Lean
formalization, an explicit 24-tetrahedron pairing, or the unrestricted
minimum-eight CFMP conjecture.

## Provenance and scope

The abstract invariant-box method is prior art: Uemura, arXiv:2609.34108v1,
Theorem 3.2, https://arxiv.org/html/2609.34108v1#S3.Thmtheorem2.
This note supplies the exact packet-specific degree-(8,9) certificate; it
does not claim a new variational method. The repository's pure-cycle
degree-(8,10) packet in PR #11648 has a different degree class. Zhao's
unrestricted minimum-nine theorem does not directly apply here because the
prescribed triangulation has degree-eight edges. No exhaustive literature
priority claim is made.


## Non-vacuity witness: finite Coxeter-sector quotient


A finite connected orientable compact 3-manifold with boundary components of genus at least two admits an ideal triangulation consisting of pure three-cycle packets, with all low quotient edges degree 8 and all high quotient edges degree 9.

This proves existence at some finite tetrahedron count, not N=24 or minimality.

## Geometric seed and six-chamber regrouping

By Luo–Yang Proposition 4.1, there exists a unique compact strictly hyperideal tetrahedron T with dihedral angles α=π/4 on its peripheral low triangle and β=2π/9 on its high center star. Indeed, its center angle sum is 3β=2π/3<π, and each peripheral sum is 2α+β=13π/18<π. Uniqueness realizes every permutation of the three peripheral vertices as an isometry. Transpositions are reflections; their mirrors bound six S3 fundamental sectors.

Choose one such sector Q. Label its four original facets A,B,C,D, where A is a piece of the LLL base, B a piece of one LHH side, and C,D symmetry mirrors. Their Coxeter labels are
m_AB=4, m_BC=9, m_CD=3, m_AC=m_AD=m_BD=2.
The low angle is unchanged π/4, the high angle is bisected to π/9, and adjacent symmetry planes meet at π/3. Q is a compact doubly truncated Coxeter orthoscheme. It has hyperideal endpoints ABC and BCD, and finite vertices ABD and ACD. The latter are respectively a low-edge midpoint and the base-face center; they are subdivision points only.

Write a,b,c,d for the four facet reflections, U for the ABC truncation face, V for the BCD truncation face, and K=<c,d>≅S3 (order 6). The six chambers kQ tile T by construction. One can also verify the coarsening by stabilizers of the supporting planes
(or, equivalently, the corresponding complete faces of T), not of the
individual Q-face polygons:
- A: Stab_K(A)=K, since a commutes with c,d. Six sectors give one base hexagon
- B: Stab_K(B)=<d>. The three K-translates of its supporting face each comprise B∪dB, giving three side hexagons
- U: Stab_K(U)=<c>. Three peripheral truncation triangles each comprise U∪cU
- V: Stab_K(V)=K. Six pieces give one center truncation triangle
- C and D are entirely internal interfaces; no pieces remain in the block boundary

For a direct polygon check, A is a quadrilateral (one truncation corner), and
the six A sectors join collinearly along C,D to one hexagon. B is a pentagon
(two truncation corners); B and dB join along their D seam to one hexagon.
U is a triangle with angles (π/4,π/9,π/2); U and cU join along C to a
triangle with angles (π/4,π/4,2π/9), and K gives three peripheral copies.
V is a triangle with angles (π/9,π/3,π/2); its six K sectors give one
equilateral triangle of angle 2π/9. Thus KQ=T has four outer hexagons and
four truncation triangles.

## Finite quotient and whole-face pairings

Include reflections u,v in the two truncation facets U,V and let
\(\widehat W=\langle a,b,c,d,u,v\rangle\).  The compact polyhedron Q has
only Coxeter ridges (labels 4,9,3,2 and right-angled truncation ridges), so
the standard Coxeter/Poincare theorem gives a discrete \(\widehat W\)-tiling of
\(\mathbb H^3\) by copies of Q.  Let \(W=\langle a,b,c,d\rangle\), the
standard parabolic subgroup omitting u,v.  Its chamber residue
\(\Omega=\bigcup_{w\in W}wQ\) has all A,B,C,D facets paired and all U,V
facets unpaired.  Full-tile disjointness gives disjoint interiors; the
incident u- or v-mirrors are orthogonal to every incident original mirror, so
the omitted facets form smooth totally geodesic boundary patches.

The development is a manifold with totally geodesic boundary. More precisely,
let \(J=\{a,b,c,d\}\), and let a point \(x\in wQ\), \(w\in W\), lie on the
Q-facets indexed by I. The full-tiling point stabilizer is the finite
\(w\widehat W_Iw^{-1}\); its intersection with W is
\(wW_{I\cap J}w^{-1}\), by the standard intersection property of special
Coxeter subgroups. Away from truncation facets this is the full local
stabilizer, so the residue contains a ball. At a truncation point I contains
exactly one of u,v, which commutes with every incident original generator.
Omitting that reflection leaves exactly half of the full local star, a
half-ball. This covers interiors, edges, and corners of all truncation
facets, excludes hidden boundary contacts, and gives totally geodesic boundary.
The finite vertices ABD and ACD have spherical stabilizers of orders 16
and 12 and become ordinary points after coarsening.

Let \(W^+\) be the orientation-preserving index-two subgroup.  It has a
finite-index torsion-free subgroup \(\Gamma\) by Selberg's lemma: W is a
finitely generated characteristic-zero linear reflection group, and the
intersection of any torsion-free finite-index subgroup with \(W^+\) has the
required properties.  The quotient \(M=\Omega/\Gamma\) is compact,
connected and orientable.  Its T-blocks are indexed by
\(\Gamma\backslash W/K\).  Every K-orbit has six chambers: Γ has trivial
intersection with every conjugate of finite K.

Whole-face adjacency is consistent. Across the base, a commutes with all K, so the six exterior A pieces lead to the single neighboring block aKQ. Across a side, B and dB lead to bKQ and dbKQ=bKQ since bd=db. Their two maps coincide as the reflection in their common supporting plane. Translating by W gives the same statement for every base and side. Therefore the blocks yield actual complete tetrahedral face pairings, not piecewise or overlapping pairings.

## All edge links

At a generic point of a low edge A∩B, the dihedral group <a,b> has order 8. Its eight Q-sectors have angle π/4, with one per T-block. Hence the low edge has eight tetrahedral occurrences and total angle 2π.

At a high edge B∩C, the dihedral group <b,c> has order 18. Its eighteen Q-sectors are grouped in adjacent pairs by c∈K. Each T-block contributes exactly two sectors, and hence there are nine blocks around the edge, each of angle 2π/9. The sum is 2π.

No further sectors are identified in the Γ quotient: an edge stabilizer in the discrete development is finite, while Γ is torsionfree. Thus the edge links are circles, with the indicated degrees. The low-edge midpoint and base-face center have the full spherical chamber links cited above; coarsening introduces no extra triangulation vertices.

## All vertex links

The two ideal-vertex types stay separate under the full face maps. The center truncation triangle has angles (2π/9,2π/9,2π/9); every peripheral triangle has (π/4,π/4,2π/9). All truncation sides are paired because they lie on paired original hexagons. Their vertices have total angle 2π by the edge-link check. Thus each boundary component is a closed hyperbolic surface. Orientation is inherited from Γ<W⁺. Compactness and Gauss–Bonnet give genus at least two for every component.

Collapsing each boundary component gives the end-compactification of the
usual topological ideal triangulation of the interior of M. Removing the
ideal vertices recovers the interior, while truncating them recovers M.
The geometric tetrahedra are strictly hyperideal, not metric ideal.
This proves every incidence/manifold hypothesis of the degree-(8,9) packet theorem.

## Sources and scope

- Luo–Yang, "Volume and rigidity of hyperbolic polyhedral 3-manifolds," Proposition 4.1 (existence and uniqueness of a strictly hyperideal tetrahedron from positive angles with vertex sums <π): https://arxiv.org/html/1404.5365v2#S4.SS1
- T. H. Marshall, "Truncated tetrahedra and their reflection groups," J. Austral. Math. Soc. 64 (1998), 54–72, pp. 58–60 (Poincare reflection presentation), pp. 64–65 (open/truncated reflection groups and torsionfree subgroups), pp. 69–70 (chamber coarsening/manifold construction): https://doi.org/10.1017/S1446788700001294
- Felikson--Tumarkin, *On hyperbolic Coxeter polytopes with mutually intersecting facets*, arXiv:math/0604248v3 (intro: integer-submultiple dihedral angles give a discrete reflection tiling): https://arxiv.org/abs/math/0604248
- Selberg's lemma: finitely generated characteristic-zero linear groups have finite-index torsionfree subgroups; see Nica, *Linear groups — Malcev's theorem and Selberg's lemma*, arXiv:1306.2385, Theorem 1.2: https://arxiv.org/abs/1306.2385. No effective index bound is claimed.
- The six-sector grouping, full-face adjacency, and explicit (8,9) edge count are the argument here, not a claim that Marshall stated this mixed packet.

The direct Coxeter-chamber quotient without coarsening has degree 2m, not m. It fails for odd degree 9. The present construction avoids that failure by two Q-sectors per high edge, one per low edge, and does not identify sectors via torsion.
