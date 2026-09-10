# Gribinski Convolution in Degree Three

## Abstract

The degree-three generalized rectangular convolution preserves nonnegative real roots for every real alpha greater than minus one.

This is the fixed degree-three development. The coefficient operation is defined for arbitrary real polynomials before specialization to two root triples. The displayed statements use E, W, N, Q, B, R and Delta for the definitions below, and C for the embedding of a real constant into a polynomial.

**Definition 1.1 (Signed Coefficients).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.elementaryCoeff`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.elementaryCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real polynomial p and natural number k, E(p,k) is elementaryCoeff p k: (-1)^k times the coefficient of X^(3-k) in p. The subtraction 3-k is natural subtraction.

**Definition 1.2 (Product Prefactor).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.weight`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real alpha and natural k, W(alpha,k) is weight alpha k: the product of the kth descending Pochhammer polynomial evaluated at 3 and the same polynomial evaluated at 3+alpha.

**Definition 1.3 (Normalized Coefficients).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.normalizedCoeff`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.normalizedCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real alpha, real polynomial p and natural k, N(alpha,p,k) is normalizedCoeff alpha p k, namely E(p,k)/W(alpha,k). This uses Lean's total real division.

**Definition 1.4 (Coefficient Convolution).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.convolutionCoeff`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.convolutionCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real alpha, real polynomials p,q and natural k, Q(alpha,p,q,k) is convolutionCoeff alpha p q k: W(alpha,k) times the sum of N(alpha,p,i)*N(alpha,q,k-i) over i in Finset.range(k+1).

**Definition 1.5 (Polynomial Reconstruction).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.boxplus3`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.boxplus3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real alpha and real polynomials p,q, B(alpha,p,q) denotes boxplus3 alpha p q. It is C(Q(alpha,p,q,0))*X^3 - C(Q(alpha,p,q,1))*X^2 + C(Q(alpha,p,q,2))*X - C(Q(alpha,p,q,3)).

**Definition 1.6 (Three Linear Factors).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.rootTriple`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.rootTriple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,b,c, R(a,b,c) is rootTriple a b c, the real polynomial (X-C(a))*(X-C(b))*(X-C(c)).

**Theorem 1.7 (All Four Defining Coefficients).**

$$\forall \alpha\in\mathbb{R}, \forall p,q\in\mathbb{R}[X], \forall k\in\mathbb{N}, k\le3 \implies \operatorname{E}\left(\operatorname{B}\left(\alpha, p, q\right), k\right)=\operatorname{Q}\left(\alpha, p, q, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThree.definition_consistency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real alpha, real polynomials p,q and natural k with k<=3, E(B(alpha,p,q),k)=Q(alpha,p,q,k). This includes k=0,1,2,3 and imposes no restriction on alpha.

**Definition 1.8 (Second-Coefficient Cross Weight).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.kappa`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real alpha, kappa(alpha)=2*(alpha+2)/(3*(alpha+3)).

**Definition 1.9 (Third-Coefficient Cross Weight).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.rho`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real alpha, rho(alpha)=(alpha+1)/(3*(alpha+3)).

**Theorem 1.10 (Four Explicit Coefficient Sums).**

$$\forall \alpha,a,b,c,d,e,f\in\mathbb{R}, (\alpha\neq-1 \land \alpha\neq-2 \land \alpha\neq-3) \implies \operatorname{Q}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right), 0\right)=1 \land \operatorname{Q}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right), 1\right)=a+b+c+(d+e+f) \land \operatorname{Q}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right), 2\right)=a\cdot b+a\cdot c+b\cdot c+(d\cdot e+d\cdot f+e\cdot f)+\kappa(\alpha)\cdot(a+b+c)\cdot(d+e+f) \land \operatorname{Q}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right), 3\right)=a\cdot b\cdot c+d\cdot e\cdot f+\rho(\alpha)\cdot((a+b+c)\cdot(d\cdot e+d\cdot f+e\cdot f)+(a\cdot b+a\cdot c+b\cdot c)\cdot(d+e+f))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThree.convolution_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha,a,b,c,d,e,f with alpha different from -1, -2 and -3, all four coefficients of the two root triples satisfy: Q0=1; Q1=a+b+c+(d+e+f); Q2=a*b+a*c+b*c+(d*e+d*f+e*f)+kappa(alpha)*(a+b+c)*(d+e+f); Q3=a*b*c+d*e*f+rho(alpha)*((a+b+c)*(d*e+d*f+e*f) +(a*b+a*c+b*c)*(d+e+f)). Here Qj abbreviates Q(alpha,R(a,b,c),R(d,e,f),j). No root signs are assumed.

**Theorem 1.11 (The Explicit Cubic).**

$$\forall \alpha,a,b,c,d,e,f\in\mathbb{R}, (\alpha\neq-1 \land \alpha\neq-2 \land \alpha\neq-3) \implies \operatorname{B}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right)\right)=X^{3}-\operatorname{C}\left(a+b+c+(d+e+f)\right)\cdot X^{2}+\operatorname{C}\left(a\cdot b+a\cdot c+b\cdot c+(d\cdot e+d\cdot f+e\cdot f)+\kappa(\alpha)\cdot(a+b+c)\cdot(d+e+f)\right)\cdot X-\operatorname{C}\left(a\cdot b\cdot c+d\cdot e\cdot f+\rho(\alpha)\cdot((a+b+c)\cdot(d\cdot e+d\cdot f+e\cdot f)+(a\cdot b+a\cdot c+b\cdot c)\cdot(d+e+f))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_explicit_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha,a,b,c,d,e,f with alpha different from -1, -2 and -3, B(alpha,R(a,b,c),R(d,e,f)) equals X^3-C(a+b+c+(d+e+f))*X^2 +C(a*b+a*c+b*c+(d*e+d*f+e*f) +kappa(alpha)*(a+b+c)*(d+e+f))*X -C(a*b*c+d*e*f+rho(alpha)*((a+b+c)*(d*e+d*f+e*f) +(a*b+a*c+b*c)*(d+e+f))).

**Theorem 1.12 (Positive Weights).**

$$\forall \alpha\in\mathbb{R}, \forall k\in\mathbb{N}, (-1<\alpha \land k\le3) \implies 0<\operatorname{W}\left(\alpha, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThree.weight_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha with -1<alpha and every natural k with k<=3, the defining weight W(alpha,k) is strictly positive.

**Theorem 1.13 (Three Nonnegative Signed Coefficients).**

$$\forall \alpha,a,b,c,d,e,f\in\mathbb{R}, (-1<\alpha \land 0\le a \land 0\le b \land 0\le c \land 0\le d \land 0\le e \land 0\le f) \implies 0\le \operatorname{E}\left(\operatorname{B}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right)\right), 1\right) \land 0\le \operatorname{E}\left(\operatorname{B}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right)\right), 2\right) \land 0\le \operatorname{E}\left(\operatorname{B}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right)\right), 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_nonnegative_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha,a,b,c,d,e,f with -1<alpha and 0<=a, 0<=b, 0<=c, 0<=d, 0<=e, 0<=f, set p=B(alpha,R(a,b,c),R(d,e,f)). The conclusion is the conjunction 0<=E(p,1), 0<=E(p,2) and 0<=E(p,3).

**Definition 1.14 (Signed Cubic Discriminant).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.discriminant`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThree.discriminant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real polynomial p, Delta(p) denotes discriminant p. Let S=E(p,1), T=E(p,2) and U=E(p,3). Then this definition is S^2*T^2-4*T^3-4*S^3*U-27*U^2+18*S*T*U.

**Theorem 1.15 (Nonnegative Gap Coordinates).**

$$\forall a,b,c\in\mathbb{R}, (0\le a \land 0\le b \land 0\le c) \implies \exists x,u,v\in\mathbb{R}, 0\le x \land 0\le u \land 0\le v \land \operatorname{R}\left(a, b, c\right)=\operatorname{R}\left(x, x+u, x+u+v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThree.nonnegative_rootTriple_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a,b,c with 0<=a, 0<=b and 0<=c, there exist real x,u,v such that 0<=x, 0<=u, 0<=v and R(a,b,c)=R(x,x+u,x+u+v). All three inequalities and the polynomial equality are part of the conclusion.

**Theorem 1.16 (Nonnegative Discriminant on the Full Root Domain).**

$$\forall \alpha,a,b,c,d,e,f\in\mathbb{R}, (-1<\alpha \land 0\le a \land 0\le b \land 0\le c \land 0\le d \land 0\le e \land 0\le f) \implies 0\le \operatorname{Delta}\left(\operatorname{B}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_discriminant_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha,a,b,c,d,e,f with -1<alpha and 0<=a, 0<=b, 0<=c, 0<=d, 0<=e, 0<=f, 0<=Delta(B(alpha,R(a,b,c),R(d,e,f))).

**Theorem 1.17 (Preservation of Nonnegative Real Roots).**

$$\forall \alpha,a,b,c,d,e,f\in\mathbb{R}, (-1<\alpha \land 0\le a \land 0\le b \land 0\le c \land 0\le d \land 0\le e \land 0\le f) \implies \exists r,s,t\in\mathbb{R}, 0\le r \land 0\le s \land 0\le t \land \operatorname{B}\left(\alpha, \operatorname{R}\left(a, b, c\right), \operatorname{R}\left(d, e, f\right)\right)=\operatorname{R}\left(r, s, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_nonnegative_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha,a,b,c,d,e,f with -1<alpha and 0<=a, 0<=b, 0<=c, 0<=d, 0<=e, 0<=f, there exist real r,s,t such that 0<=r, 0<=s, 0<=t and B(alpha,R(a,b,c),R(d,e,f))=R(r,s,t). The conclusion retains all three sign conditions and the full factorization.

## References

- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.boxplus3`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.convolutionCoeff`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.convolution_coefficients`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.definition_consistency`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.discriminant`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.elementaryCoeff`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.kappa`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_discriminant_nonneg`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_explicit_coefficients`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_nonnegative_coefficients`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_nonnegative_roots`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.nonnegative_rootTriple_coordinates`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.normalizedCoeff`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.rho`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.rootTriple`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.weight`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThree.weight_pos`
- Dependency: [D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeSix](FiniteFreeCommutatorDegreeSix.md)
- Dependency: [D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant](GribinskiDegreeThreeDiscriminant.md)
