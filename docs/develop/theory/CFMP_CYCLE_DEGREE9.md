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

No explicit face-pairing is asserted here; the theorem is conditional on the
stated manifold and incidence hypotheses. It is not the unrestricted CFMP
minimum-eight theorem.

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
These are necessary conditions only. No sufficient pairing construction or
non-vacuity is claimed.

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
