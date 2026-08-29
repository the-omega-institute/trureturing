# Strategy Self Knowledge Factorization

## Abstract

Strategy self-knowledge factorization refines the current-state observation kernel.

**Theorem 1.1 (Factorization refines the strategy kernel).**

$$\forall x3 \in \left(\forall x3 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x4 \in \left(\forall x4 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x5 \in \left(\forall x5 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \left(\forall x6 \in \mathord{\cdot},\; \mathit{x4}\left(\mathit{x6}\right) = \mathit{x5}\left(\mathit{x3}\left(\mathit{x6}\right)\right)\right) \Rightarrow \left(\forall x7 \in \mathord{\cdot},\; \forall x8 \in \mathord{\cdot},\; \mathit{x3}\left(\mathit{x7}\right) = \mathit{x3}\left(\mathit{x8}\right) \Rightarrow \mathit{x4}\left(\mathit{x7}\right) = \mathit{x4}\left(\mathit{x8}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/StrategySelfKnowledgeFactorization.factorization_refines_strategy_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the strategy profile factors pointwise through the current-memory readout, and fix histories with equal current values.

Substituting the factorization on both histories transports current equality to equality of their strategy profiles.

**Theorem 1.2 (A visible profile adds no pairwise separation).**

$$\forall current: H \to M, profile: H \to P, factor: M \to P,\\{}x, y: H, ((\forall h: H, \operatorname{profile}\left(h\right) = \operatorname{factor}\left(\operatorname{current}\left(h\right)\right)) \land \operatorname{current}\left(x\right) = \operatorname{current}\left(y\right)) \Rightarrow \operatorname{pair}\left(\operatorname{current}\left(x\right), \operatorname{profile}\left(x\right)\right) = \operatorname{pair}\left(\operatorname{current}\left(y\right), \operatorname{profile}\left(y\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/StrategySelfKnowledgeFactorization.visible_profile_pair_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same factorization and current-equality hypotheses, both the current and profile components agree.

The paired agency-completion values are therefore equal for the displayed histories; no global kernel equality is asserted.

## References

- Truth anchor: `D5/S3/Observer/AgencySelf/StrategySelfKnowledgeFactorization.factorization_refines_strategy_kernel`
- Truth anchor: `D5/S3/Observer/AgencySelf/StrategySelfKnowledgeFactorization.visible_profile_pair_equality`
