# Dependent Finite Prime-Time Tomography

## Abstract

Complete separation by a dependent observer family on a finite carrier has a finite index-time window.

**Theorem 1.1 (Complete dependent separation has a finite window).**

$$\begin{aligned}\forall I, X: \operatorname{Type}, O: I \to \operatorname{Type},\\\operatorname{Finite}\left(X\right), F: X \to X,\\q: \forall i: I, X \to \operatorname{O}\left(i\right),\\\operatorname{Injective}\left(\operatorname{jointReadout}\left((c: I \times \mathbb{N} \mapsto (x \mapsto \operatorname{q}\left(\operatorname{fst}\left(c\right), \operatorname{iterate}\left(F, \operatorname{snd}\left(c\right), x\right)\right)))\right)\right) \Rightarrow \exists J: \operatorname{Finset}\left(I\right), m: \mathbb{N},\\\operatorname{Injective}\left(\operatorname{jointReadout}\left((c: \{c: I \times \mathbb{N} \mid \operatorname{fst}\left(c\right) \in J \land \operatorname{snd}\left(c\right) \leq m\} \mapsto (x \mapsto \operatorname{q}\left(\operatorname{fst}\left(c\right), \operatorname{iterate}\left(F, \operatorname{snd}\left(c\right), x\right)\right)))\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/DependentFinitePrimeTimeTomography.dependent_finite_prime_time_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete observation is the canonical dependent joint readout on pairs of observer indices and natural-number times. Each coordinate applies the indexed readout after the corresponding iterate of the update.

Finite-state separation first yields finitely many separating index-time coordinates. Their index projection is a finite observer family, and their finite supremum is a common time horizon containing every selected coordinate.

## References

- Truth anchor: `D5/S3/Observer/Refinement/DependentFinitePrimeTimeTomography.dependent_finite_prime_time_tomography`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/FiniteFaithfulSubfamilyExtraction](../../ConceptDynamics/Faithfulness/FiniteFaithfulSubfamilyExtraction.md)
