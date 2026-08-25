# Counterfactual Repair Separation

## Abstract

A successful counterfactual state does not universally imply an admissible allowed repair.

**Theorem 1.1 (Counterfactual success does not imply allowed repair).**

$$\neg \forall X, U, Y: \operatorname{Type}, J: X \to Y, x: X, y: Y, A: \operatorname{Set}(U), F: U \to X \to X, Adm: X \to \operatorname{Prop},\\{}\exists xPrime: X, J(xPrime) = y \Rightarrow\\{}\exists u: U, u \in A \land J(F(u, x)) = y \land Adm(F(u, x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/CounterfactualRepairSeparation.counterfactual_success_not_imply_allowed_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

State, action, and result carriers are quantified explicitly. A target, actual state, desired result, allowed-action set, transition, and admissibility predicate are the source primitives.

The first public clause is existence of a counterfactual state with the desired target value. The second requires an allowed action whose actual transition reaches that value and is admissible.

The theorem negates the universal implication. Its Boolean witness uses the same target, actual state, transition family, and desired value on both sides; the desired state is produced only by an excluded action.

No repository theorem states this general non-implication. The proof is an explicit shared-transition countermodel with no new target-shaped definition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/CounterfactualRepairSeparation.counterfactual_success_not_imply_allowed_repair`
