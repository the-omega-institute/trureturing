# Postprocessing Strict Loss Witness

## Abstract

A collapsed distinction witnesses strict information loss under postprocessing.

**Theorem 1.1 (A collapsed distinction witnesses strict loss).**

$$\forall q: X \to Y, p: Y \to Z, x, y: X,\\{}(\operatorname{q}\left(x\right) \neq \operatorname{q}\left(y\right) \land \operatorname{p}\left(\operatorname{q}\left(x\right)\right) = \operatorname{p}\left(\operatorname{q}\left(y\right)\right)) \Rightarrow (\operatorname{Kernel}\left(p \circ q, x, y\right) \land \neg\operatorname{Kernel}\left(q, x, y\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Postprocessing/PostprocessingStrictLossWitness.collapsed_distinction_witnesses_strict_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume q separates x and y while p identifies their q-values.

The pair is therefore in the processed kernel and is not in the original kernel, recording both sides of the witness.

**Theorem 1.2 (Strict loss refutes postprocessing injectivity).**

$$\forall q: X \to Y, p: Y \to Z, x, y: X,\\{}(\operatorname{q}\left(x\right) \neq \operatorname{q}\left(y\right) \land \operatorname{p}\left(\operatorname{q}\left(x\right)\right) = \operatorname{p}\left(\operatorname{q}\left(y\right)\right)) \Rightarrow \neg\operatorname{Injective}\left(p\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Postprocessing/PostprocessingStrictLossWitness.strict_loss_refutes_image_injectivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same separated-and-collapsed pair contradicts injectivity of the postprocessing map p.

The conclusion is failure of global injectivity of p; it follows from the displayed pair in the image of q.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Postprocessing/PostprocessingStrictLossWitness.collapsed_distinction_witnesses_strict_loss`
- Truth anchor: `D5/S3/ConceptDynamics/Postprocessing/PostprocessingStrictLossWitness.strict_loss_refutes_image_injectivity`
