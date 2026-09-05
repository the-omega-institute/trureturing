# Exact algebraic X-construction seed: local roots and induced graph

This is a certificate instance supporting the single theory volume
`docs/develop/theory/MUB_SIX_FOURTH_BASIS_THEORY.md`. It is not another theory
volume and does not assert a complete classification or a four-MUB exclusion.

## Result and scope

At the exact algebraic seed specified below, integer outward-rounded interval
arithmetic certifies 60 distinct projective common-unbiased rays. Their induced
orthogonality graph is exactly

```
K6 disjoint-union 9 K3,3.
```

Of the 1770 unordered pairs, 1674 have strictly positive certified squared inner
product. The remaining 96 pairs are proved exactly orthogonal by the explicit
cyclic/antiunitary symmetries and certified identification of their root boxes.
No floating-point smallness test is used to accept an orthogonality edge.

There is exactly one six-clique among these 60 rays. This is a finite induced
subgraph statement. It does not exclude undiscovered rays outside the boxes,
additional completions containing such rays, or a quartet in dimension six.
Strict-X nonmembership in Fourier equivalence seams is also not asserted.

## Exact input, with no random matrix coefficients

Let t0<t1<t2 be the three real roots of

```
5 t^3 + t^2 - 11 t + 1 = 0,
```

and let u0<u1<u2 be the three real roots of

```
3 u^3 - u^2 - 13 u - 1 = 0.
```

Each root is specified by a rational isolating interval in the JSON certificate.
Strict endpoint sign changes on three disjoint intervals prove that a cubic
has exactly one simple real root in each interval and no other roots.

Set c(t)=(1+i t)/(1-i t), rj=c(tj), sj=c(uj), alpha=(1+i)/4.
The Cayley polynomial identities are

```
(1-i t)^3 [c(t)^3-alpha c(t)^2+conj(alpha)c(t)-1]
  = -(i/2)(5 t^3+t^2-11t+1),
(1-i u)^3 [c(u)^3+alpha c(u)^2-conj(alpha)c(u)-1]
  = -(i/2)(3 u^3-u^2-13u-1).
```

Thus all rj,sj have modulus one; their products are one, their sums are alpha
and -alpha respectively. Define circ(a,b,c)=[[a,b,c],[c,a,b],[b,c,a]], and

```
A = circ(r0*r1,r1,1), B = circ(s0*s1,s1,1),
H = [[A,B],[B*, -A*]], T=H/sqrt(6).
```

The cyclic row-ratio sums of A and B add to zero. Since circulant matrices
commute, block multiplication gives HH*=6I. Every entry of H has modulus one.
This is exactly an algebraic member of the two-circulant X construction. The
parameter label alone is not used to claim exclusion from other equivalence
families.

## Root system and interval certificate

A projective ray is represented by u0=1 and

```
uj = sign_j * (1+i xj)/(1-i xj), j=1,...,5,
sign_j in {-1,1}.
```

The normalized ket is u/sqrt(6). Five real equations are

```
f_a(x) = |(H* u)_a|^2 - 6 = 0, a=0,...,4.
```

The sixth equation follows from HH*=6I and sum |uj|^2=6. The use of signed
Cayley charts avoids a phase coordinate at infinity.

All certificate centers are dyadic with denominator 2^48. Every box has radius
2^-30. The replay checker reconstructs H using 120-bit dyadic intervals with
outward rounding after every arithmetic operation. It evaluates an interval
Jacobian, builds a rational midpoint inverse and rounds the inverse to a dyadic
preconditioner C. That inverse is only a proposed preconditioner, not a trusted
claim about the true Jacobian.

For each box X centered at x0, the checker verifies

```
x0-C f(x0)+(I-C J(X))(X-x0) is strictly contained in X,
||I-C J(X)||_infinity < 1.
```

The preconditioned Newton map is therefore a contraction from the complete box
to itself. It has one and only one fixed point in X. The strict contraction
bound implies C is nonsingular, so that fixed point is exactly a zero of f.
Its enclosure is then sharpened to the certified Newton image. Distinctness is
checked in dephased physical complex coordinates, including across Cayley
charts.

At the checked instance the largest contraction bound is less than 1/500000,
and every inclusion margin is greater than 9/10^10. These coarse rational
inequalities should be replayed, not substituted for the exact report.

## Exact edges, rather than near-zero edges

Use physical coordinates in two blocks of length three. Define

```
R u = (u1,u2,u0,u4,u5,u3),
Theta u = (-conj(u3),-conj(u5),-conj(u4),
             conj(u0), conj(u2), conj(u1)).
```

Direct circulant block algebra gives R^3=I, Theta^2=-I,
Theta R=R^-1 Theta, RT=TR, and Theta T=-T Theta. These operations preserve the
common-unbiased equations. Projective normalization divides by the first
coordinate, which is never zero.

The checker encloses each transformed root, converts it to the target signed
Cayley chart, and proves that it lies strictly inside exactly one already
certified uniqueness box. This identifies the exact transformed root, not just
a nearby floating-point vector.

Writing Theta=M conjugation, R^a M is a real skew-symmetric matrix. Consequently

```
<u, R^a Theta u> = 0, a=0,1,2.
```

This proves the complete bipartite orbit edges. Six roots are projectively fixed
by R, hence are exact R-eigenvectors. Disjoint eigenvalue enclosures identify
distinct eigenvalues, whose eigenspaces are orthogonal. Within each eigenmode,
Theta supplies the remaining orthogonal partner. Together these prove all 96
edges left unresolved by interval nonzero tests.

The same argument proves modewise orthogonality for every edge of this induced
graph. It does not prove the global-to-modewise implication for arbitrary
common-unbiased roots outside the certified collection.

## Reproduction and trust boundary

Run the standard-library-only checker from the repository root:

```
python3 scripts/check_x_seed_boxes.py \
  docs/develop/certificates/x_quarter_seed/root_boxes.json \
  --report /tmp/x_quarter_seed_report.json
```

The discovery script may use NumPy/SciPy to find centers. Acceptance uses only
Python integer arithmetic and fractions.Fraction. Deliberately changing a root
center, seed interval, or chart must cause the replay to fail unless it still
describes a valid certificate.

The checker is an exact computational certificate verifier using the standard
contraction theorem and the analytic identities explained above. It is not a
Lean kernel proof. The accompanying Lean source only certifies the seed's
Hadamard block identity, and needs its own successful admission. No passing
canonical report is asserted by this artifact.

## Next missing obligation

The remaining obstacle at this one seed is global root coverage. The known boxes
certify at least 60 rays, not at most 60. A covering subdivision, exact real-root
count, or rational univariate representation is needed to prove no other rays
exist. Only after that may this induced graph be promoted to the entire
common-unbiased orthogonality graph. Moving from the single seed to a parameter
cell additionally requires discriminant and guard coverage.
