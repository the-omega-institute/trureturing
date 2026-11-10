# Epistemic Change Trichotomy

## Abstract

Fixed-world conclusion changes expose an admission, evidence, or inference change.

**Theorem 1.1 (Changed conclusions expose an epistemic component).**

$$\forall x5 \in \mathord{\cdot},\; \forall x6 \in \mathord{\cdot},\; \forall x7 \in \mathord{\cdot} \to \mathrm{Type},\; \forall x8 \in \mathord{\cdot} \to \mathrm{Type},\; \forall x9 \in \mathord{\cdot} \to \mathord{\cdot},\; \forall x10 \in \mathord{\cdot} \to \mathord{\cdot},\; \forall x11 \in \mathord{\cdot} \to \mathord{\cdot},\; \forall x12 \in \mathord{\cdot} \to \mathord{\cdot},\; \forall x13 \in \left(\mathord{\cdot} \to \mathrm{Type}\right) \to \left(\left(\mathord{\cdot} \to \mathord{\cdot}\right) \to \left(\left(\mathord{\cdot} \to \mathord{\cdot}\right) \to \left(\mathord{\cdot} \to \mathord{\cdot}\right)\right)\right),\; \mathit{x5} = \mathit{x6} \Rightarrow \left(\mathit{x13}\left(\mathit{x7}, \mathit{x9}, \mathit{x11}, \mathit{x5}\right) \ne \mathit{x13}\left(\mathit{x8}, \mathit{x10}, \mathit{x12}, \mathit{x6}\right) \Rightarrow \left(\mathit{x7} \ne \mathit{x8} \lor \left(\mathit{x9} \ne \mathit{x10} \lor \mathit{x11} \ne \mathit{x12}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/EpistemicChangeTrichotomy.changed_conclusion_exposes_epistemic_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The admission predicates, evidence concepts, inference rules, worlds, and conclusion evaluator are independent source primitives.

The public fixed-world premise holds the underlying state constant. If every component were also equal, deterministic evaluation would force equal conclusions, contradicting the other premise.

The three public alternatives directly audit a change to admissible worlds, evidence distinctions, or the inference rule; no target-defined state structure or private classification is used.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/EpistemicChangeTrichotomy.changed_conclusion_exposes_epistemic_component`
