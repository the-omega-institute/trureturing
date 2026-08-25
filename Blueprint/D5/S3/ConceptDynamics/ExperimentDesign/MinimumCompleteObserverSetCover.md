# Minimum Complete Observers as Set Cover

## Abstract

Minimum-cost complete finite observer families are exactly minimum-cost set covers.

**Theorem 1.1 (The minimum complete observer problem is weighted set cover).**

$$\begin{aligned}\forall n: \mathbb{N}, I: \operatorname{Type}(), O: I \to \operatorname{Type}(),\\c: I \to \mathbb{R}, q: \forall i: I, \operatorname{Fin}(n) \to O(i),\\J: \operatorname{Finset}(I),\\X:= \operatorname{Fin}(n), U_{X}:= \{\{x, y\} \mid x, y \in \operatorname{Fin}(n), x \neq y\},\\\forall i \in I, D_{i}:= \{\{x, y\} \in U_{X} \mid q(i)(x) \neq q(i)(y)\}, \forall J \in \operatorname{Finset}(I), \operatorname{C}(J):= \sum_{i \in J} c(i),\\(\operatorname{Injective}(\operatorname{jointReadout}(\operatorname{restrict}(q, J))) \land (\forall K: \operatorname{Finset}(I), \operatorname{Injective}(\operatorname{jointReadout}(\operatorname{restrict}(q, K))) \Rightarrow \operatorname{C}(J) \leq \operatorname{C}(K))) \iff \\(U_{X} = \operatorname{Union}(i \in J, D_{i}) \land (\forall K: \operatorname{Finset}(I), U_{X} = \operatorname{Union}(i \in K, D_{i}) \Rightarrow \operatorname{C}(J) \leq \operatorname{C}(K))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/MinimumCompleteObserverSetCover.minimum_complete_observer_is_set_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite state carrier is X = Fin n. Its unordered-pair universe contains exactly distinct state pairs, and the detector set for observer i contains the pairs on which its readout differs.

For each finite observer selection J, C(J) is the sum of the supplied real candidate costs. No positivity assumption is added: the theorem compares the same objective over two extensionally equal feasible families.

The imported finite experiment cover criterion identifies joint-readout injectivity with coverage of the full distinct-pair universe. It therefore transports both feasibility of J and its cost comparison against every feasible candidate K.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/MinimumCompleteObserverSetCover.minimum_complete_observer_is_set_cover`
- Dependency: [D5/S3/ConceptDynamics/Experiment/FiniteExperimentCoverCriterion](../Experiment/FiniteExperimentCoverCriterion.md)
