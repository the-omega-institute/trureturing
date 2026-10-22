# Dyadic parity for Hanna's cubic series

## Abstract

Every normalized rational solution of Hanna's cubic equation has integer coefficients odd exactly at powers of two.

PowerSeries.subst takes the inner argument first. The series variable A has rational coefficients. Each coefficient at a positive natural index is shown equal to an integer m; Odd applies to that integer. The integer lift comes from the prime-exponent construction with p=3 and c=9. Reducing it modulo two and using uniqueness identifies it with the existing powerTwoSeries.

**Definition 1.1 (The source generating function).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \iff ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (A^{3} = \operatorname{PowerSeries}.\operatorname{subst}\left(X^{3} + 9 \cdot X \cdot A^{3}, A\right))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A377106: cubic substitution and power-of-two parity*. URL: <https://oeis.org/A377106>.

*Commentary.*

OEIS A377106, NAME (unpaginated): "G.f. A(x) satisfies A(x)^3 = A( x^3 + 9*x*A(x)^3 ), with A(0)=0, A'(0)=1." The coefficient ring is rational and the two normalization coefficients are zero and one.

**Definition 1.2 (The parity conjecture).**

$$(\operatorname{claim}) \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, n = 2^{k}))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A377106: cubic substitution and power-of-two parity*. URL: <https://oeis.org/A377106>.

*Commentary.*

OEIS A377106, COMMENTS (unpaginated): "Conjecture: a(n) is odd iff n = 2^k for some k >= 0." The offset is one. The proposition asserts existence and the integer parity assertion for every solution and every index at least one.

**Theorem 1.3 (The parity conjecture holds).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, n = 2^{k})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a377106-hanna-parity-reversion` (proved) by `D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a377106-hanna-parity-reversion","declaration_gid":"D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A377106: cubic substitution and power-of-two parity*. URL: <https://oeis.org/A377106>.

*Commentary.*

Existence follows from integer lifting. Uniqueness over the rationals identifies any solution with that lift; uniqueness over ZMod(2) identifies its reduction with the power-of-two series.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.result`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality](HannaPrimeSubstitutionIntegrality.md)
