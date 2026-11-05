# CentralLabels

## Abstract

Whole-group good involutions are exactly compatible class-invariant central labels.

**Definition 1.1 (The original good-map identities).**

Lean statement: `D5/S3/FiniteGroups/Quandles/CentralLabels.IsGood`

*Formalization.* `D5/S3/FiniteGroups/Quandles/CentralLabels.IsGood` (`✓ std3`).

*Citation.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

The involution commutes with every conjugation, and conjugation by its value at x is conjugation by the inverse of x. This uses the source convention s_x(y)=xyx^-1.

**Definition 1.2 (Good maps as functions).**

Lean statement: `D5/S3/FiniteGroups/Quandles/CentralLabels.Good`

*Formalization.* `D5/S3/FiniteGroups/Quandles/CentralLabels.Good` (`✓ std3`).

*Citation.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

The subtype counts actual functions and introduces no quotient by isomorphism.

**Definition 1.3 (Central label functions).**

Lean statement: `D5/S3/FiniteGroups/Quandles/CentralLabels.Label`

*Formalization.* `D5/S3/FiniteGroups/Quandles/CentralLabels.Label` (`✓ std3`).

*Citation.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

A label assigns a central element to every group element, is constant on conjugacy classes, and is unchanged after its own twisted inversion.

**Definition 1.4 (Complete central-label classification).**

Lean statement: `D5/S3/FiniteGroups/Quandles/CentralLabels.goodLabelEquiv`

*Formalization.* `D5/S3/FiniteGroups/Quandles/CentralLabels.goodLabelEquiv` (`✓ std3`).

*Citation.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

For an arbitrary group, the label of a good map rho is z(x)=rho(x)x. Conversely rho(x)=z(x)x^-1. Centrality and class invariance give the two conjugation identities, and the label compatibility is exactly rho squared equals identity. This is the whole-group specialization of Ta Theorem 6.7; it is attributed to that source.

**Definition 1.5 (The existing whole-carrier interface).**

Lean statement: `D5/S3/FiniteGroups/Quandles/CentralLabels.wholeGoodEquiv`

*Formalization.* `D5/S3/FiniteGroups/Quandles/CentralLabels.wholeGoodEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

Transport along the evident equivalence between G and the subtype of Finset.univ identifies the pointwise whole-group definition with the repository Good definition, including both inverse identities.

## References

- Truth anchor: `D5/S3/FiniteGroups/Quandles/CentralLabels.Good`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/CentralLabels.IsGood`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/CentralLabels.Label`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/CentralLabels.goodLabelEquiv`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/CentralLabels.wholeGoodEquiv`
- Dependency: [D5/S3/FiniteGroups/Quandles/ConjugationSubquandle](ConjugationSubquandle.md)
