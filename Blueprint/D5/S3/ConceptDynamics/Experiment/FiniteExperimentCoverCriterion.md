# Finite Experiment Cover Criterion

## Abstract

A finite experiment package identifies a target relative to current evidence exactly when it covers every unresolved target pair.

**Theorem 1.1 (Finite experiment design is target-pair set cover).**

$$\begin{aligned}\forall n: \mathbb{N}, E, C, Y: \operatorname{Type},\\R: E \to \operatorname{Type}, A: \operatorname{Finset}(E),\\E0: \operatorname{Fin}(n) \to C, Q: \forall e: E, \operatorname{Fin}(n) \to R(e),\\T: \operatorname{Fin}(n) \to Y,\\(\forall i: \operatorname{Fin}(n), j: \operatorname{Fin}(n), (E0(i), \operatorname{jointReadout}(\operatorname{restrict}(Q, A), i)) = (E0(j), \operatorname{jointReadout}(\operatorname{restrict}(Q, A), j)) \Rightarrow T(i) = T(j)) \iff \\\{\{i, j\} \mid E0(i) = E0(j) \land T(i) \neq T(j)\} = \operatorname{Union}(e \in A, \{\{i, j\} \mid E0(i) = E0(j) \land T(i) \neq T(j) \land Q(e)(i) \neq Q(e)(j)\}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteExperimentCoverCriterion.finite_experiment_cover_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Models are indexed by Fin n. The current evidence E0 is paired with the canonical joint readout of the finite selected experiment set A; target identifiability is fiber constancy of that combined evidence.

The unresolved universe contains exactly the unordered model pairs with equal current evidence and unequal target values. Each selected experiment contributes the unresolved pairs whose responses differ.

The selected package identifies the target exactly when the unresolved universe equals the union of those separation sets. Finite model indexing and the finite selection are sufficient; the ambient experiment type need not itself be finite.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteExperimentCoverCriterion.finite_experiment_cover_criterion`
- Dependency: [D5/S3/ConceptDynamics/Experiment/ExperimentIdentifiability](ExperimentIdentifiability.md)
- Dependency: [D5/S3/ConceptDynamics/Interventions/TargetRelativePairUniverse](../Interventions/TargetRelativePairUniverse.md)
