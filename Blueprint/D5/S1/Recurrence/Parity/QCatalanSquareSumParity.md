# q-Catalan Row Square-Sum Parity

## Abstract

The square sum of a Carlitz-Riordan q-Catalan row is odd exactly one below a power of two.

The entry cited in hanna2024a376527 defines a(n) as the sum of the squared coefficients in row n of the Carlitz-Riordan q-Catalan triangle. It asks whether the odd rows are exactly those indexed by 2^k-1.

All indices are natural numbers. The row polynomials and their coefficients are integer-valued. Write R(n) for qCatalanRow(n), T(n,k) for qCatalanCoeff(n,k), S(n) for rowSum(n), a(n) for squareSum(n), and C for the shifted integer Catalan series. The operator coeff extracts a coefficient, eval evaluates a polynomial, and monomial(i,1) is q^i.

The map pi is Int.castRingHom into ZMod(2). Polynomial rows avoid any need for a bivariate formal-series interface. Their degree bound makes the displayed finite square sum exactly the full row.

**Definition 1.1 (The q-Catalan row polynomials).**

$$\begin{aligned}\operatorname{R}\left(0\right) = 1\\\forall n: \mathbb{N}, \operatorname{R}\left(n + 1\right) = \sum_{i \in \operatorname{Fin}\left(n + 1\right)} (\operatorname{monomial}\left(i, 1\right) \cdot \operatorname{R}\left(i\right) \cdot \operatorname{R}\left(n - i\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.qCatalanRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion is obtained by comparing the coefficient of x^(n+1) in A(x,q)=1+x A(qx,q) A(x,q).

**Definition 1.2 (The q-Catalan coefficient triangle).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{T}\left(n, k\right) = \operatorname{coeff}\left(k, \operatorname{R}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.qCatalanCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The triangle entry T(n,k) is coefficient k of the row polynomial R(n).

**Definition 1.3 (The row sum).**

$$\forall n: \mathbb{N}, \operatorname{S}\left(n\right) = \operatorname{eval}\left(1, \operatorname{R}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.rowSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation at q=1 adds all coefficients of the row polynomial.

**Definition 1.4 (The finite square sum).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(\frac{n \cdot (n - 1)}{2} + 1\right)} \operatorname{T}\left(n, k\right)^{2}$$

*Formalization.* `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.squareSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper index n(n-1)/2 is the degree bound for the nth row.

**Theorem 1.5 (Coefficient-extracted row recurrence).**

$$\forall n: \mathbb{N}, \operatorname{R}\left(n + 1\right) = \sum_{i \in \operatorname{Fin}\left(n + 1\right)} (\operatorname{monomial}\left(i, 1\right) \cdot \operatorname{R}\left(i\right) \cdot \operatorname{R}\left(n - i\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.qCatalanRow_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each split i+(n-i)=n contributes q^i R(i) R(n-i).

**Theorem 1.6 (Specialization at q=1).**

$$\forall n: \mathbb{N}, \operatorname{S}\left(n\right) = \operatorname{coeff}\left(n + 1, C\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.rowSum_eq_catalan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At q=1 the powers q^i disappear, so S obeys the Catalan convolution. The series X times the generating series of S has zero constant coefficient and satisfies F=X+F^2. Catalan uniqueness identifies it with C, including the one-place coefficient shift.

**Theorem 1.7 (Square sums modulo two).**

$$\forall n: \mathbb{N}, \operatorname{pi}\left(\operatorname{a}\left(n\right)\right) = \operatorname{coeff}\left(n + 1, \operatorname{map}\left(pi, C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.squareSum_mod_two_eq_catalan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every element u of ZMod(2) satisfies u^2=u. Summing this identity across the finite row identifies the reduced square sum with the reduced row sum, hence with the corresponding coefficient of C.

**Theorem 1.8 (Hanna's A376527 parity conjecture).**

$$\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k} - 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a376527-q-catalan-square-sum-parity` (proved) by `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a376527-q-catalan-square-sum-parity","declaration_gid":"D5/S1/Recurrence/Parity/QCatalanSquareSumParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A376527, square sums of Carlitz-Riordan q-Catalan rows and parity conjecture*. URL: <https://oeis.org/A376527>.

*Commentary.*

The binary Catalan theorem says that coefficient n+1 of C is one exactly when n+1=2^k. Positivity of powers of two makes this equivalent to n=2^k-1, including n=0 at k=0.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.qCatalanCoeff`
- Truth anchor: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.qCatalanRow`
- Truth anchor: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.qCatalanRow_succ`
- Truth anchor: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.rowSum`
- Truth anchor: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.rowSum_eq_catalan`
- Truth anchor: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.squareSum`
- Truth anchor: `D5/S1/Recurrence/Parity/QCatalanSquareSumParity.squareSum_mod_two_eq_catalan`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../Invariants/CatalanCompositionSquareParity.md)
