# Newton connections and monic annihilators

## Abstract

Monic Newton connection coefficients give factorial-row reflections and finite transforms of arbitrary complex sequences with a positive-order monic annihilator.

**Definition 1.1 (Monic Newton polynomials).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; (\operatorname{N}\left(a, b, 0\right) = 1) \land (\forall n \in \mathbb{N},\; \operatorname{N}\left(a, b, n + 1\right) = \operatorname{N}\left(a, b, n\right) \cdot \left(X - \operatorname{C}\left(a + b \cdot n\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.newton` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

This recursion is the finite product of X-a-bi for i=0 through n-1. The generalized connection and inverse-basis conventions are classical; the Maier and Mansour-Schork-Shattuck locators are given in the cited note and below. No priority claim is made for them.

**Definition 1.2 (Connection rows).**

$$\forall alpha \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall a \in \mathbb{C},\; (\operatorname{F}\left(alpha, b, a, 0\right) = 1) \land (\forall n \in \mathbb{N},\; \operatorname{F}\left(alpha, b, a, n + 1\right) = \left(X + \operatorname{C}\left(a - alpha \cdot n\right)\right) \cdot \operatorname{F}\left(alpha, b, a, n\right) + \operatorname{C}\left(b\right) \cdot X \cdot \operatorname{derivative}\left(\operatorname{F}\left(alpha, b, a, n\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.connectionRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

F denotes connectionRow. Its coefficient recurrence is valid for every complex parameter.

**Definition 1.3 (Connection coefficients).**

$$\forall alpha \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall a \in \mathbb{C},\; \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{S}\left(alpha, b, a, n, m\right) = \operatorname{coeff}\left(\operatorname{F}\left(alpha, b, a, n\right), m\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

S is the coefficient of X to m in the connection row F.

**Definition 1.4 (Factorial rows).**

$$\forall alpha \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall a \in \mathbb{C},\; (\operatorname{G}\left(alpha, b, a, 0\right) = 1) \land (\forall n \in \mathbb{N},\; \operatorname{G}\left(alpha, b, a, n + 1\right) = \left(\operatorname{C}\left(a - alpha \cdot n\right) + X\right) \cdot \operatorname{G}\left(alpha, b, a, n\right) + X \cdot \left(\operatorname{C}\left(b\right) + X\right) \cdot \operatorname{derivative}\left(\operatorname{G}\left(alpha, b, a, n\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.G` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

The coefficient of X to m is m! S(alpha,b,a,n,m); all coefficients above degree n vanish.

**Definition 1.5 (Newton-to-power coefficients).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{R}\left(a, b, n, m\right) = \operatorname{coeff}\left(\operatorname{N}\left(a, b, n\right), m\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.R` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

R reads the coefficients of the monic Newton polynomials.

**Definition 1.6 (Power-to-Newton coefficients).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{T}\left(a, b, n, m\right) = \operatorname{S}\left(0, b, a, n, m\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

T is the alpha=0 connection family, including b=0.

**Theorem 1.7 (The literal Newton expansion).**

$$\forall alpha \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall a \in \mathbb{C},\; \forall n \in \mathbb{N},\; \operatorname{N}\left(0, alpha, n\right) = \sum_{m \in \operatorname{range}\left(n + 1\right)} (\operatorname{C}\left(\operatorname{S}\left(alpha, b, a, n, m\right)\right) \cdot \operatorname{N}\left(a, b, m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.connection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

For complex a and b, N(a,b,n) is the product of X-a-bi over 0 <= i < n, with empty product one. The coefficient S(alpha,b,a,n,m) is the coefficient of X to m in F(alpha,b,a,n). Here F at zero is one, and F at n+1 is (X+a-alpha n) F at n plus b X times its derivative. Thus S at row zero is the Kronecker delta, its zero column satisfies S(n+1,0)=(a-alpha n) S(n,0), and its positive columns satisfy S(n+1,m+1)=S(n,m)+(a+b(m+1)-alpha n) S(n,m+1). Entries above the triangle vanish. In particular no truncated predecessor is used at column zero.

The displayed expansion identifies these recursively constructed coefficients with the monic Newton connection, including coincident nodes b=0. This is Maier's equation (4.8), with his parameters (a,b;r) corresponding to (alpha,b;a) here. Mansour, Schork and Shattuck use S(n,m;alpha,b,a); their convention excludes the all-zero triple, while the monic polynomial definition here includes it. Writing R for the coefficients of N and T=S(0,b,a), the finite connection is the triangular change of basis R(0,alpha) T(a,b). No nonzero parameter is required.

**Theorem 1.8 (The finite triangular change of basis).**

$$\forall alpha \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall a \in \mathbb{C},\; \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (\sum_{j \in \operatorname{range}\left(n + 1\right)} (\operatorname{T}\left(a, b, n, j\right) \cdot \operatorname{R}\left(a, b, j, k\right)) = \operatorname{coeff}\left((X)^{n}, k\right)) \land ((\sum_{j \in \operatorname{range}\left(n + 1\right)} (\operatorname{R}\left(a, b, n, j\right) \cdot \operatorname{T}\left(a, b, j, k\right)) = \operatorname{coeff}\left((X)^{n}, k\right)) \land (\operatorname{S}\left(alpha, b, a, n, k\right) = \sum_{j \in \operatorname{range}\left(n + 1\right)} (\operatorname{R}\left(0, alpha, n, j\right) \cdot \operatorname{T}\left(a, b, j, k\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.basis_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

R(a,b,n,k) is coeff(N(a,b,n),k) and T(a,b,n,k)=S(0,b,a,n,k). The first two equations give both triangular inverses, with coeff(X to n,k) equal to the Kronecker delta. The last is S(alpha,b;a)=R(0,alpha) T(a,b). Each product is the finite row sum over j=0 through n. Monicity makes the Newton map injective, including when b=0; the displayed equations require no node separation.

**Theorem 1.9 (Factorial-row reflection).**

$$\forall alpha \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall a \in \mathbb{C},\; \forall n \in \mathbb{N},\; \operatorname{comp}\left(\operatorname{G}\left(alpha, b, a, n\right), 0 - \operatorname{C}\left(b\right) - X\right) = \operatorname{C}\left((0 - 1)^{n}\right) \cdot \operatorname{G}\left(0 - alpha, b, b - a, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

The row G(alpha,b,a,n) is the sum of m! S(alpha,b,a,n,m) X to m for m=0 through n. Its polynomial differential recurrence is G(n+1)=(a-alpha n+X)G(n)+X(b+X)G'(n). Differentiating the inductive reflection proves the equality for every complex alpha, b and a. The argument uses polynomial operations and also applies at alpha=0, b=0, and their intersections. Maier's equation (4.4) supplies the classical generating-function normalization; the polynomial proof does not divide by alpha or b.

**Theorem 1.10 (The full annihilator transform).**

$$\forall d \in \mathbb{N},\; \forall q \in \mathbb{C},\; \forall A \in \operatorname{Polynomial}\left(\mathbb{C}\right),\; \forall alpha \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall a \in \mathbb{C},\; \forall ell \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall u \in \mathbb{N} \to \mathbb{C},\; (1 \le d) \Rightarrow ((\operatorname{degree}\left(A\right) < d) \Rightarrow ((\operatorname{eval}\left(0, A\right) = 0) \Rightarrow ((\forall n \in \mathbb{N},\; \operatorname{u}\left(n + d\right) = q \cdot \operatorname{u}\left(n\right) + \sum_{j \in \operatorname{support}\left(A\right)} (\operatorname{coeff}\left(A, j\right) \cdot \operatorname{u}\left(n + j\right))) \Rightarrow (\sum_{m \in \operatorname{range}\left(ell + 1\right)} ((0 - 1)^{m} \cdot \operatorname{factorial}\left(m\right) \cdot (b)^{m} \cdot \operatorname{S}\left(alpha, b, a, ell, m\right) \cdot (q)^{ell - m} \cdot \operatorname{u}\left(d \cdot m + c\right)) = (0 - 1)^{ell} \cdot \sum_{m \in \operatorname{range}\left(ell + 1\right)} (\operatorname{factorial}\left(m\right) \cdot (b)^{m} \cdot \operatorname{S}\left(0 - alpha, b, b - a, ell, m\right) \cdot (q)^{ell - m} \cdot \operatorname{L}\left(u, c, (A)^{m}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

For the actual sequence u define L(u,c,f) as the finite sum of coeff(f,j) u(j+c) over the support of f. The recurrence is imposed at every nonnegative index. It implies that L vanishes on every multiple of X to d minus q minus A; it also replaces (q+A) to m by X to dm inside L. Homogenizing the row reflection and substituting Y=q and X=b A proves the displayed identity.

The source class has d>=1, degree A<d and A(0)=0; A=0 is allowed, including at d=1. All first d values are arbitrary. The bounds on A specify a positive-order monic annihilator; the polynomial argument itself uses the recurrence. All outer sums contain exactly m=0 through ell. Factorials and natural indices are cast to Complex. Every exponent is natural, and exponent zero has value one even when its base is zero. At ell=0 both sides equal u(c). At q=0 the term m=ell remains, with the full pairing of A to ell. At b=0 positive columns are suppressed by b to m, while the Newton family itself remains defined. Zero initial data, repeated roots and every nonnegative offset are included.

This result concerns the stated generalized-Stirling transform. Inverting Parisse's scaled matrix at a nonzero step, factorial-free first-kind transport, the separate positive Lah companion and arbitrary hypersequence inversion require their own coefficient identifications and hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.G`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.R`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.S`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.T`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.basis_change`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.connection`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.connectionRow`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.newton`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.reflection`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.result`
- Dependency: [D5/S3/Combinatorics/BinomialBases/SecondOrderStirlingTransform](SecondOrderStirlingTransform.md)
