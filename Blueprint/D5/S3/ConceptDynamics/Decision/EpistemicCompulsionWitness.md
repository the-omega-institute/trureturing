# Epistemic Compulsion Witness

## Abstract

A coarse observation can leave no action safe across its whole fiber.

**Theorem 1.1 (Pointwise legality need not survive coarse observation).**

$$\exists q \in Bool \to Unit, Legal \in Bool \to \left(Bool \to Prop\right), z \in Unit,\; \left(\forall x \in Bool,\; \exists a \in Bool,\; Legal\left(x\right)\left(a\right)\right) \land \left(\left(\forall x \in Bool, a \in Bool,\; Legal\left(x\right)\left(a\right) \Leftrightarrow a = x\right) \land \left(\left(\forall x \in Bool,\; q\left(x\right) = z\right) \land \left(\neg \left(\exists a \in Bool,\; \forall x \in Bool,\; q\left(x\right) = z \Rightarrow Legal\left(x\right)\left(a\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/EpistemicCompulsionWitness.epistemic_compulsion_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two Boolean states share one observation. An action is legal exactly when it matches the underlying state, so each state separately has a legal action.

Because the observation cannot distinguish false from true, no single Boolean action is legal throughout the common fiber. This is an explicit finite witness of epistemic compulsion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/EpistemicCompulsionWitness.epistemic_compulsion_witness`
