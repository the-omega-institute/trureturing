# Hanna's A157675 Integrality

## Abstract

Hanna's A157675 self-substitution series has integer coefficients.

**Definition 1.1 (The A157675 integrality conjecture).**

$$claim = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{HannaSelfSubstitutionIntegrality}.\operatorname{SolvesHanna}\left((fun n: \mathbb{N} \mapsto (2: \mathbb{Q})^{n}), A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{HannaSelfSubstitutionIntegrality}.\operatorname{SolvesHanna}\left((fun n: \mathbb{N} \mapsto (2: \mathbb{Q})^{n}), A\right) \Rightarrow \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(A\right)))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675.claim` (`✓ std3`).

*Citation.* P. D. Hanna (2009). *OEIS A163921 and A157675: self-substitution integrality conjectures*. URL: <https://oeis.org/A163921/internal>.

*Commentary.*

OEIS A157675, name (unpaginated): "G.f.: A(x) = exp( Sum_{n>=1} A(2^n*x)^n * x^n/n )." Comment: "Conjectured to consist entirely of integers." The equation is SolvesHanna with L(n)=2^n over the rationals. The conclusion asserts existence of a solution and integer coefficients for every solution. The entry of L at zero is unused.

**Theorem 1.2 (The A157675 series is integral).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{HannaSelfSubstitutionIntegrality}.\operatorname{SolvesHanna}\left((fun n: \mathbb{N} \mapsto (2: \mathbb{Q})^{n}), A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{HannaSelfSubstitutionIntegrality}.\operatorname{SolvesHanna}\left((fun n: \mathbb{N} \mapsto (2: \mathbb{Q})^{n}), A\right) \Rightarrow \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(A\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675.result` (`✓ std3`). ∎

*Resolves.* `Problems/hannasubst-a157675` (proved) by `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hannasubst-a157675","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. D. Hanna (2009). *OEIS A163921 and A157675: self-substitution integrality conjectures*. URL: <https://oeis.org/A163921/internal>.

*Commentary.*

The exponential input exp(Sum_{n>=1} 2^n*x^n/n) is the integer geometric series (1-2X) inverse. HannaSelfSubstitutionIntegrality.result therefore gives existence and integrality of every solution of the displayed equation.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality](HannaSelfSubstitutionIntegrality.md)
