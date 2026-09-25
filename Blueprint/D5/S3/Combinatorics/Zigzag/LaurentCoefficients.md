# Finite Laurent Coefficient Formula

## Abstract

A finite antidiagonal solution of the Laurent recurrence yields the exact central and shifted coefficients needed by the two parity boundaries.

**Definition 1.1 (A finite solution, not a formal infinite series).**

Lean statement: `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.closedPolynomial`

*Formalization.* `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.closedPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At depth m the sum ranges over pairs (a,b) with a+b=m. Each term has coefficient 2*choose(a,b)*2^(a-b)*3^b and Laurent exponent a-2b. The equivalent h-index presentation is 2*sum over h<=floor(m/2) of choose(m-h,h)*2^(m-2h)*3^h*z^(m-3h). All sums are finite; no analytic convergence is invoked.

**Theorem 1.2 (The antidiagonal solves the path recurrence).**

Lean statement: `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.pathPolynomial_closed_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.pathPolynomial_closed_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Pascal identity proves the finite antidiagonal sum satisfies the same second-order Laurent recurrence as pathPolynomial. Direct calculation gives common seeds 2 and 4z; two-step induction then proves equality at every natural depth. This supplies a closed expression rather than just numerical fitting.

**Theorem 1.3 (The even central coefficient).**

$$\forall s \in \mathrm{Nat},\; \operatorname{coeff}\left(\operatorname{pathPolynomial}\left(3 \cdot s\right), 0\right) = 2 \cdot 6^{s} \cdot \operatorname{choose}\left(2 \cdot s, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.pathPolynomial_coeff_three_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At depth 3s, exponent zero selects exactly the antidiagonal index (2s,s). Its coefficient is 2*6^s*choose(2s,s). The proof shows every other term has a different Laurent exponent, which is the exact even zero-charge count before adding the negative sector.

**Theorem 1.4 (The odd shifted coefficient).**

$$\forall s \in \mathrm{Nat},\; \operatorname{coeff}\left(\operatorname{pathPolynomial}\left(3 \cdot s + 2\right), -1\right) = 6^{s + 1} \cdot \operatorname{choose}\left(2 \cdot s + 1, s + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.pathPolynomial_coeff_three_mul_add_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At depth 3s+2, the odd singleton shift asks for exponent -1. Only the index (2s+1,s+1) contributes, giving 6^(s+1)*choose(2s+1,s+1). Both coefficient identities hold for every s and feed the literal balanced-count endpoint through the path equivalences.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.closedPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.pathPolynomial_closed_formula`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.pathPolynomial_coeff_three_mul`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/LaurentCoefficients.pathPolynomial_coeff_three_mul_add_two`
- Dependency: [D5/S3/Combinatorics/Zigzag/WeightedPaths](WeightedPaths.md)
