# Log-Determinant Information Submodularity

## Abstract

Positive matrix contributions make regularized log-determinant information submodular.

**Definition 1.1 (Regularized information operator).**

Lean statement: `D5/S3/Resource/LogDet/LogDetInformationSubmodularity.informationOperator`

*Formalization.* `D5/S3/Resource/LogDet/LogDetInformationSubmodularity.informationOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operator is constructed as lambda times the identity plus the finite sum of the selected protocol contributions.

**Definition 1.2 (Log-volume information).**

Lean statement: `D5/S3/Resource/LogDet/LogDetInformationSubmodularity.logVolumeInformation`

*Formalization.* `D5/S3/Resource/LogDet/LogDetInformationSubmodularity.logVolumeInformation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected operator's real log-determinant is normalized by the regularization-only baseline.

**Theorem 1.3 (Log-determinant information is monotone and submodular).**

$$\forall Protocol \in \operatorname{Type}, Index \in \operatorname{Type}, G \in Protocol \to \operatorname{Matrix}(Index, Index, \mathbb{C}), lambda \in \mathbb{R},\; \left(\operatorname{DecidableEq}(Protocol) \land \left(\operatorname{Fintype}(Index) \land \left(\operatorname{DecidableEq}(Index) \land \left(0 < lambda \land \left(\forall p \in Protocol,\; \operatorname{PosSemidef}(G(p))\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall A \in \operatorname{Finset}(Protocol), B \in \operatorname{Finset}(Protocol),\; A \subseteq B \Rightarrow \operatorname{logVolumeInformation}(G, lambda, A) \leq \operatorname{logVolumeInformation}(G, lambda, B)\right) \land \left(\forall A \in \operatorname{Finset}(Protocol), B \in \operatorname{Finset}(Protocol), p \in Protocol,\; A \subseteq B \Rightarrow \operatorname{logVolumeInformation}(G, lambda, \operatorname{insert}(p, A)) - \operatorname{logVolumeInformation}(G, lambda, A) \geq \operatorname{logVolumeInformation}(G, lambda, \operatorname{insert}(p, B)) - \operatorname{logVolumeInformation}(G, lambda, B)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDet/LogDetInformationSubmodularity.log_det_information_monotone_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary positive semidefinite complex matrix contributions and a positive scalar regularizer, enlarging a finite protocol set cannot decrease its log-volume information.

The marginal gain from adjoining one protocol decreases when the starting set grows. The statement includes protocols already in the larger set, where the corresponding gain is zero.

The proof bundles the raw matrix C-star components locally, applies operator monotonicity of the logarithm and inverse antitonicity, and identifies trace-log with real log-determinant spectrally.

## References

- Truth anchor: `D5/S3/Resource/LogDet/LogDetInformationSubmodularity.informationOperator`
- Truth anchor: `D5/S3/Resource/LogDet/LogDetInformationSubmodularity.logVolumeInformation`
- Truth anchor: `D5/S3/Resource/LogDet/LogDetInformationSubmodularity.log_det_information_monotone_submodular`
