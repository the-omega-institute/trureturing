# Even Diagonal Coefficients of Compositional Iterates

## Abstract

The implicitly determined compositional series has even diagonal coefficients at every index at least two.

OEIS A395842 conjectures that every term after the initial term is even. Here iterate(f,0)=X and iterate(f,m+1) substitutes f into iterate(f,m). The imported iterate definition is used throughout; iteration is composition. All indices are natural numbers, and subtraction of indices is truncated at zero. Coefficients and divisibility in the final theorem are over the integers.

**Definition 1.1 (Construction of the integer series).**

$$\operatorname{generatingSeries}\left(\right) = \operatorname{limitSeries}\left(\mathbb{Z}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DiagonalIterateEven.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395842, diagonal coefficients of the compositional iterates of A177775*. URL: <https://oeis.org/A395842>.

*Commentary.*

The auxiliary approximation starts with X+X². At stage j it subtracts the degree-(j+3) diagonal residual times X^(j+3). Coefficients below that degree are preserved. limitSeries is mk applied to the function n mapped to coeff(n,approximation(n)); mk constructs a power series from its coefficients. No parity constraint enters this construction.

**Definition 1.2 (The diagonal sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}\left(\right), n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DiagonalIterateEven.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395842, diagonal coefficients of the compositional iterates of A177775*. URL: <https://oeis.org/A395842>.

*Commentary.*

The integer a(n) is exactly the degree-n coefficient of the n-th iterate of the constructed series. The normalization implies a(2)=2.

**Theorem 1.3 (The defining diagonal constraints).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\left(\right)\right) = 0) \land (\operatorname{coeff}\left(1, \operatorname{generatingSeries}\left(\right)\right) = 1) \land (\operatorname{coeff}\left(2, \operatorname{generatingSeries}\left(\right)\right) = 1) \land (\forall n: \mathbb{N}, (2 < n) \implies \operatorname{coeff}\left(n, \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}\left(\right), n\right)\right) = \operatorname{coeff}\left(n, \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}\left(\right), n - 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DiagonalIterateEven.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395842, diagonal coefficients of the compositional iterates of A177775*. URL: <https://oeis.org/A395842>.

*Commentary.*

For normalized series agreeing below degree n, the change in the degree-n coefficient of the m-th iterate is m times the change in the degree-n coefficient of the series. Subtracting adjacent iterates therefore leaves that coefficient change once. Each correction kills its residual, and coefficient stability transfers every constraint to the limit.

**Theorem 1.4 (Uniqueness).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((\operatorname{constantCoeff}\left(f\right) = 0) \land (\operatorname{coeff}\left(1, f\right) = 1) \land (\operatorname{coeff}\left(2, f\right) = 1) \land (\forall n: \mathbb{N}, (2 < n) \implies \operatorname{coeff}\left(n, \operatorname{iterate}\left(\mathbb{Z}, f, n\right)\right) = \operatorname{coeff}\left(n, \operatorname{iterate}\left(\mathbb{Z}, f, n - 1\right)\right))) \implies f = \operatorname{generatingSeries}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DiagonalIterateEven.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395842, diagonal coefficients of the compositional iterates of A177775*. URL: <https://oeis.org/A395842>.

*Commentary.*

Strong induction compares coefficients of two solutions. Degrees zero, one and two are prescribed. At every later degree, equality of the lower coefficients and vanishing residuals force equality of the next coefficient.

**Theorem 1.5 (Every diagonal coefficient from index two is even).**

$$\forall n: \mathbb{N}, (2 \le n) \implies 2 \mid \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DiagonalIterateEven.hanna_conjecture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A395842, diagonal coefficients of the compositional iterates of A177775*. URL: <https://oeis.org/A395842>.

*Commentary.*

Over ZMod(2), take H to be the compositional inverse of X+X². It satisfies H+H²=X. Doubling an iterate proves U+U^(2^(2^r))=X for U=iterate(H,2^r), so its coefficients from degree two through 2^(2^r)-1 vanish. The relation iterate(H,m+1)+iterate(H,m+1)²=iterate(H,m), together with Frobenius substitution, excludes every degree that is not a power of two by induction on degree and iteration count. These facts prove the diagonal constraints and vanishing diagonal for H. Reduction of the integer solution commutes with iteration; uniqueness identifies it with H. Its zero diagonal coefficients in ZMod(2) are exactly integer divisibility by two.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/DiagonalIterateEven.a`
- Truth anchor: `D5/S1/Recurrence/Parity/DiagonalIterateEven.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/DiagonalIterateEven.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/DiagonalIterateEven.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/DiagonalIterateEven.hanna_conjecture`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../Invariants/CompositionalIterateCongruence.md)
