# Mathar's recurrence and D-finiteness for A001722

## Abstract

The signed first-kind Stirling sum defining OEIS A001722 satisfies Mathar's third-order recurrence for every index at least three. Its ordinary rational formal generating series is annihilated by a nonzero fourth-order differential operator.

**Definition 1.1 (Signed Stirling coefficients).**

$$\forall N \in \mathbb{N},\; \forall K \in \mathbb{N},\; \operatorname{s}\left(N, K\right) = \operatorname{coeff}\left(\prod_{i \in \operatorname{range}\left(N\right)} (X - \operatorname{C}\left((i : \mathbb{Z})\right)), K\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MatharA001722.s` (`✓ std3`).

*Citation.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829 and A001722*. URL: <https://oeis.org/A386829>.

*Commentary.*

The coefficient convention is signed: s(N,K) is the coefficient of X to the K in the product of X-i for i from zero through N-1. The empty product is one. Coefficients and casts are in the integers.

**Definition 1.2 (The full coefficient sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} ((-1)^{n + k} \cdot (\operatorname{choose}\left(k + 2, 2\right) : \mathbb{Z}) \cdot ((5 : \mathbb{Z}))^{k} \cdot \operatorname{s}\left(n + 2, k + 2\right))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MatharA001722.a` (`✓ std3`).

*Citation.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829 and A001722*. URL: <https://oeis.org/A386829>.

*Commentary.*

This is Borislav Crstici's all-index formula in OEIS A001722, revision 26, https://oeis.org/A001722/internal?fmt=text. The canonical entry name is Generalized Stirling numbers [n+7,7]_5. The range contains both zero and n; the binomial coefficient is computed in the naturals and cast to the integers. No recurrence or initial-value characterization is assumed.

**Definition 1.3 (Ordinary formal generating series).**

$$\forall n \in \mathbb{N},\; \operatorname{coeff}\left(n, G\right) = (\operatorname{a}\left(n\right) : \mathbb{Q})$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MatharA001722.G` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829 and A001722*. URL: <https://oeis.org/A386829>.

*Commentary.*

G is the ordinary formal power series whose nth coefficient is a(n) cast to the rationals. It is not an exponential generating series, and no convergence assertion is involved.

**Definition 1.4 (The two assertions).**

$$claim \Leftrightarrow ((\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (\operatorname{a}\left(n\right) + 3 \cdot (-(n : \mathbb{Z}) - 5) \cdot \operatorname{a}\left(n - 1\right) + (3 \cdot ((n : \mathbb{Z}))^{2} + 27 \cdot (n : \mathbb{Z}) + 61) \cdot \operatorname{a}\left(n - 2\right) - ((n : \mathbb{Z}) + 4)^{3} \cdot \operatorname{a}\left(n - 3\right) = 0)) \land (\exists r \in \mathbb{N},\; \exists p \in \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{Q}\right),\; (\exists j \in \mathbb{N},\; (j \le r) \land (\operatorname{p}\left(j\right) \ne 0)) \land (\sum_{j \in \operatorname{range}\left(r + 1\right)} (\operatorname{inclusion}\left(\operatorname{p}\left(j\right)\right) \cdot \operatorname{iterate}\left(D, j, G\right)) = 0)))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MatharA001722.claim` (`✓ std3`).

*Citation.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829 and A001722*. URL: <https://oeis.org/A386829>.

*Commentary.*

The first assertion is Mathar's recurrence in the formula field of OEIS A001722, revision 26. Every n at least three is included. Subtraction in the subscripts is natural subtraction; n is cast to the integers before computing the polynomial coefficients. The second assertion requires a homogeneous polynomial-coefficient differential equation for the same full G, with at least one nonzero coefficient polynomial. The inclusion is the canonical map from rational polynomials to rational formal power series; D is formal differentiation, and its zeroth iterate is the identity.

**Theorem 1.5 (Recurrence and a homogeneous annihilator).**

$$(\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (\operatorname{a}\left(n\right) + 3 \cdot (-(n : \mathbb{Z}) - 5) \cdot \operatorname{a}\left(n - 1\right) + (3 \cdot ((n : \mathbb{Z}))^{2} + 27 \cdot (n : \mathbb{Z}) + 61) \cdot \operatorname{a}\left(n - 2\right) - ((n : \mathbb{Z}) + 4)^{3} \cdot \operatorname{a}\left(n - 3\right) = 0)) \land (\exists r \in \mathbb{N},\; \exists p \in \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{Q}\right),\; (\exists j \in \mathbb{N},\; (j \le r) \land (\operatorname{p}\left(j\right) \ne 0)) \land (\sum_{j \in \operatorname{range}\left(r + 1\right)} (\operatorname{inclusion}\left(\operatorname{p}\left(j\right)\right) \cdot \operatorname{iterate}\left(D, j, G\right)) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MatharA001722.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829 and A001722*. URL: <https://oeis.org/A386829>.

*Commentary.*

Set B(n)=(-1)^n times the Taylor translate at -5 of the falling product of length n+2. The Hasse derivative coefficient formula gives coeff(2,B(n))=a(n), directly from the signed sum. Multiplication of the falling product by its next factor gives B(n+1)=B(n)(n+7-X). The combination B(m+3)-3(m+8)B(m+2)+(3m^2+45m+169)B(m+1)-(m+7)^3 B(m) equals -X^3 B(m); taking its second coefficient proves the recurrence. For the ordinary series, the fourth-order operator has coefficient polynomials p(0)=-18+254z-1029z^2, p(1)=1-24z+253z^2-1019z^3, p(2)=-3z^2+54z^3-289z^4, p(3)=3z^4-30z^5 and p(4)=-z^6. All higher p(j) are zero. Coefficient extraction reduces its equation to the recurrence multiplied by n+1. The two boundary coefficients use a(0)=1, a(1)=18 and a(2)=251. Thus every coefficient vanishes and p(4) is nonzero.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001722.G`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001722.a`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001722.claim`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001722.result`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001722.s`
