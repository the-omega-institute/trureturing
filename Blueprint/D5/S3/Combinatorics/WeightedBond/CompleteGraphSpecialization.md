# Complete-graph weighted bond polynomials

## Abstract

Complete-graph weighted bond polynomials.

**Definition 1.1 (Mark).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.Mark`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.Mark` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The polynomial coefficient ring over the rationals.

**Definition 1.2 (reciprocalFactor).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reciprocalFactor`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reciprocalFactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The formal inverse of the finite factor rescaled by the parameter, with constant term one.

**Theorem 1.3 (psiComplete_closed).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.psiComplete_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.psiComplete_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For positive n and r at least two, evaluate the literal finite-color rank polynomial by the first coefficient extraction below.

**Theorem 1.4 (reversePsi_closed).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reversePsi_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reversePsi_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For positive n and r at least two, evaluate the printed rank reversal by the second coefficient extraction below.

**Theorem 1.5 (reversePsi_at_zero).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reversePsi_at_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reversePsi_at_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For positive n and any r, the reversed polynomial at zero equals the degree-(n minus one) coefficient of the rank polynomial.

**Theorem 1.6 (result).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{sourceSpecialization}\left(n + 1, q + 2\right) = n! \cdot \operatorname{coeff}\left(n, \operatorname{rescale}\left(1 - \left(n + 1\right) \cdot X, \operatorname{exp}\left(\mathbb{Q}[X]\right)\right) \cdot \operatorname{reciprocalFactor}\left(q, X\right)^{n + 1}\right) \land \left(\operatorname{reversePsi}\left(n + 1, q + 2\right) = n! \cdot \operatorname{coeff}\left(n, \operatorname{rescale}\left(X - \left(n + 1\right), \operatorname{exp}\left(\mathbb{Q}[X]\right)\right) \cdot \operatorname{reciprocalFactor}\left(q, 1\right)^{n + 1}\right) \land \left(\operatorname{reversePsi}\left(n + 1, q + 2\right) = \operatorname{reflect}\left(n, \operatorname{sourceSpecialization}\left(n + 1, q + 2\right)\right) \land \operatorname{eval}\left(0, \operatorname{reversePsi}\left(n + 1, q + 2\right)\right) = \operatorname{coeff}\left(n, \operatorname{sourceSpecialization}\left(n + 1, q + 2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.result` (`✓ std3`). ∎

*Resolves.* `Problems/gonzalez-dleon-wachs-question-7-1` (proved) by `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gonzalez-dleon-wachs-question-7-1","declaration_gid":"D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Question 7.1 in arXiv:2608.08692v2 is at https://arxiv.org/html/2608.08692v2#S7.Thmtheorem1. Here n+1 is the vertex count and q+2 is the number of colors. The formal variable of coefficient extraction is distinct from the polynomial indeterminate X. The two extractions give the source specialization and the printed rank-reversed polynomial. The last two equalities specify the reflection and its value at zero.

## References

- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.Mark`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.psiComplete_closed`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reciprocalFactor`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.result`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reversePsi_at_zero`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.reversePsi_closed`
- Dependency: [D5/S3/Combinatorics/WeightedBond/CountableColors](CountableColors.md)
- Dependency: [D5/S3/Combinatorics/WeightedBond/ExponentialSeries](ExponentialSeries.md)
- Dependency: [D5/S3/Combinatorics/WeightedBond/LagrangeBurmann](LagrangeBurmann.md)
