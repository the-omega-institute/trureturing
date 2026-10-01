# CFMP pure three-cycle packet at degree (8,9): exact box certificate

This is a local research note, not a repository change. It records a
nonduplicate extension of the current dev results: all low global edges have
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
partial derivative is `-(x1^2-1)/sqrt(A B)`). The universal `[1,2]^6`
envelope places the box below in the genuine hyper-ideal length domain.

Use a shared global cosh-length box

```
low:  A=73/50 <= x_e <= 2,
high: C=53/40 <= x_e <= D=347/200.
```

For a low target edge, the cycle packet has adjacent low/high coordinates and
opposite high, so monotonicity gives the lower/upper-face endpoint tuples
`(A,A,C,D,C,A)` and `(2,2,D,C,D,2)`. For a high target, adjacent coordinates
are low,low,high,high and the opposite is low, giving `(C,A,A,2,C,C)` and
`(D,2,2,A,D,D)`.

The exact squared endpoint cosines are

```
Llo^2 = phi(A,A,C,D,C,A)^2 = 23001041/45748800 > 1/2,
Lup^2 = phi(2,2,D,C,D,2)^2 = 1261129/2527362 < 1/2,
Hlo^2 = phi(C,A,A,2,C,C)^2 = 1111822336/1885209561,
Hup^2 = phi(D,2,2,A,D,D)^2 = 12826261216129/21905208090000.
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
