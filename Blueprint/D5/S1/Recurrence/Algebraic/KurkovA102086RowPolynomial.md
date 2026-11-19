# Kurkov's A102086 Row Polynomials

## Abstract

Kurkov's complete A102086 row-polynomial identity, including existence of both source tables.

The coefficient ring is Z and the variable X is formal. Rows and matrix columns are natural numbers starting at zero; P has an integer second index, including negative exterior indices. C embeds an integer as a constant polynomial. A row polynomial reads coefficients in displayed order, without reversal. All sums below are finite. Natural subtraction n-1 occurs only under k<n; the polynomial interior 0<b<a likewise forces a>0. At (0,0), the two boundary prescriptions agree because X^0=1.

**Definition 1.1 (The source matrix).**

$$\forall (T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right)), \operatorname{IsSourceTriangle}\left(T\right) \iff (\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), (n < k) \implies T\left(n, k\right) = 0) \land ((\forall (n: \mathbb{N}), T\left(n, n\right) = n + 1) \land (\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), (k < n) \implies T\left(n, k\right) = \sum_{j \in \operatorname{Finset}.\operatorname{Ico}\left(k, n\right)} (T\left(n - 1, j\right) \cdot T\left(j, k\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.IsSourceTriangle` (`✓ std3`).

*Citation.* Paul D. Hanna; Mikhail Kurkov; OEIS Foundation Inc. (2026). *OEIS A102086, Kurkov's row-polynomial conjecture for Hanna's matrix-square triangle*. URL: <https://raw.githubusercontent.com/oeis/oeisdata/07c3ba2e0a0dab01600c762da7c11349d5de8548/seq/A102/A102086.seq>.

*Commentary.*

OEIS NAME: Triangular matrix, read by rows, that satisfies: T(n,k) = [T^2](n-1,k) when n>k>=0, with T(n,n) = (n+1). Lower triangularity reduces its ordinary matrix-square entry to j in [k,n). The displayed row zero is [1].

**Definition 1.2 (The polynomial table).**

$$\forall (P: \mathbb{N} \to \left(\mathbb{Z} \to \mathbb{Z}[X]\right)), \operatorname{IsSourcePolynomialTable}\left(P\right) \iff (\forall (a: \mathbb{N}), P\left(a, a\right) = X^{a}) \land ((\forall (a: \mathbb{N}), P\left(a, 0\right) = 1) \land ((\forall (a: \mathbb{N}), \forall (b: \mathbb{Z}), ((b < 0) \lor (a < b)) \implies P\left(a, b\right) = 0) \land (\forall (a: \mathbb{N}), \forall (b: \mathbb{Z}), (0 < b) \implies (b < a) \implies P\left(a, b\right) = P\left(a, b - 1\right) + \operatorname{C}\left(b + 1\right) \cdot P\left(a - 1, b\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.IsSourcePolynomialTable` (`✓ std3`).

*Citation.* Paul D. Hanna; Mikhail Kurkov; OEIS Foundation Inc. (2026). *OEIS A102086, Kurkov's row-polynomial conjecture for Hanna's matrix-square triangle*. URL: <https://raw.githubusercontent.com/oeis/oeisdata/07c3ba2e0a0dab01600c762da7c11349d5de8548/seq/A102/A102086.seq>.

*Commentary.*

Kurkov's FORMULA: Conjecture: n-th row polynomial is P(n+1, n) where P(n, k) = P(n, k-1) + (k+1) * P(n-1, k) for 0 < k < n with P(n, n) = x^n, P(n, 0) = 1, P(n, k) = 0 for k < 0 or k > n. The attribution is Mikhail Kurkov, Jul 03 2026. No numerical value is substituted for X.

**Definition 1.3 (The complete nonvacuous conjecture).**

$$\operatorname{claim} \iff (\exists (T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right)), \operatorname{IsSourceTriangle}\left(T\right)) \land ((\exists (P: \mathbb{N} \to \left(\mathbb{Z} \to \mathbb{Z}[X]\right)), \operatorname{IsSourcePolynomialTable}\left(P\right)) \land (\forall (T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right)), \forall (P: \mathbb{N} \to \left(\mathbb{Z} \to \mathbb{Z}[X]\right)), (\operatorname{IsSourceTriangle}\left(T\right)) \implies (\operatorname{IsSourcePolynomialTable}\left(P\right)) \implies \forall (n: \mathbb{N}), \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (\operatorname{C}\left(T\left(n, k\right)\right) \cdot X^{k}) = P\left(n + 1, n\right)))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.claim` (`✓ std3`).

*Citation.* Paul D. Hanna; Mikhail Kurkov; OEIS Foundation Inc. (2026). *OEIS A102086, Kurkov's row-polynomial conjecture for Hanna's matrix-square triangle*. URL: <https://raw.githubusercontent.com/oeis/oeisdata/07c3ba2e0a0dab01600c762da7c11349d5de8548/seq/A102/A102086.seq>.

*Commentary.*

Both source tables must exist. The identity is then required for every pair of source tables and every natural n, including n=0. There is no cutoff, extra hypothesis, coefficient reversal or alteration of any boundary.

**Theorem 1.4 (The complete row-polynomial identity).**

$$(\exists (T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right)), \operatorname{IsSourceTriangle}\left(T\right)) \land ((\exists (P: \mathbb{N} \to \left(\mathbb{Z} \to \mathbb{Z}[X]\right)), \operatorname{IsSourcePolynomialTable}\left(P\right)) \land (\forall (T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right)), \forall (P: \mathbb{N} \to \left(\mathbb{Z} \to \mathbb{Z}[X]\right)), (\operatorname{IsSourceTriangle}\left(T\right)) \implies (\operatorname{IsSourcePolynomialTable}\left(P\right)) \implies \forall (n: \mathbb{N}), \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (\operatorname{C}\left(T\left(n, k\right)\right) \cdot X^{k}) = P\left(n + 1, n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a102086-row-polynomial` (proved) by `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a102086-row-polynomial","declaration_gid":"D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna; Mikhail Kurkov; OEIS Foundation Inc. (2026). *OEIS A102086, Kurkov's row-polynomial conjecture for Hanna's matrix-square triangle*. URL: <https://raw.githubusercontent.com/oeis/oeisdata/07c3ba2e0a0dab01600c762da7c11349d5de8548/seq/A102/A102086.seq>.

*Commentary.*

Construct P by recursion on a+b in the triangular domain, taking the base and diagonal values first, then extend to all integer exterior indices by zero. Both recursive interior arguments decrease a+b. Induction in a and then b proves uniqueness, and proves that P(a,b) has no coefficient above b. Put R_j=P(j+1,j). Define the Z-linear map L using Mathlib's Polynomial.lsum so that L(X^j)=R_j. This is independent of any matrix table. Induction in a and b gives L(P(a,b))=P(a+1,b) for 0<=b<=a: the base uses R_0=1, the diagonal uses the monomial rule, and the interior uses linearity and the source recurrence. At (n+2,n+1) the recurrence gives R_(n+1)=L(R_n)+(n+2)X^(n+1). Expanding R_n over its finite support gives L(R_n)=sum_(j=0)^n [X^j]R_n R_j. Taking coefficients yields the source matrix diagonal and its exact square recurrence; terms j<k vanish by the coefficient bound. Thus the coefficient table is an actual source T. Strong row induction proves uniqueness of T, since each factor on the right has row below n. Polynomial reconstruction gives the identity for the constructed pair. Uniqueness of P and T transports it to every source pair. The proof includes row zero and supplies both existential witnesses. This is a repository derivation using classical finite linear algebra; the bounded source screen supplies no worldwide priority or complete literature claim.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.IsSourcePolynomialTable`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.IsSourceTriangle`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.result`
