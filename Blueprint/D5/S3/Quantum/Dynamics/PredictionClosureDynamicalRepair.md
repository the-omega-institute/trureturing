# Prediction Closure as Dynamical Repair

## Abstract

The least invariant observer closure induces dynamics on the visible quotient.

**Theorem 1.1 (Prediction closure is the least dynamical repair).**

$$\begin{gathered}\forall V: \operatorname{FiniteDimensionalRealHilbertSpace},\\\forall K: \operatorname{End}(V), \forall W: \operatorname{Submodule}(V),\\W \subseteq \operatorname{Cl}(K, W) \land \operatorname{Invariant}(K, \operatorname{Cl}(K, W)) \land \operatorname{Invariant}(\operatorname{adjoint}(K), \operatorname{Cl}(K, W)^{\perp}) \land\\(\forall x, y\in V, x - y\in \operatorname{Cl}(K, W)^{\perp} \Rightarrow \operatorname{adjoint}(K)(x) - \operatorname{adjoint}(K)(y)\in \operatorname{Cl}(K, W)^{\perp}) \land\\\overline{\operatorname{adjoint}(K)} \circ \operatorname{quotientProjection}(\operatorname{Cl}(K, W)^{\perp}) = \operatorname{quotientProjection}(\operatorname{Cl}(K, W)^{\perp}) \circ \operatorname{adjoint}(K) \land\\(\forall U: \operatorname{Submodule}(V), (W \subseteq U \land \operatorname{Invariant}(K, U)) \Rightarrow \operatorname{Cl}(K, W) \subseteq U).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PredictionClosureDynamicalRepair.prediction_closure_minimal_dynamical_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a linear evolution of observables on a finite-dimensional real Hilbert space, with no invariance assumption on the current visible subspace W. Its prediction closure C is constructed from all forward K-orbits of W, and its final invisible residual R is the orthogonal complement of C.

The existing observer-orbit theorem directly proves that C contains W, is K-invariant, and lies in every K-invariant observable extension containing W. Mathlib's exact adjoint-invariance theorem then makes R invariant under the adjoint state evolution.

Consequently, differences in R remain in R after state evolution, so final invisibility is a dynamical congruence. Mathlib's quotient map construction supplies the induced linear evolution on V/R and its canonical projection equation.

The source compares time evolution with self-reference, contextual, completion, and refinement closures only at the level of a common minimal-stability pattern. This theorem formalizes that pattern for a linear target operation and does not identify objects belonging to those different domains.

Repository search found and directly applies observer_closure_is_least_invariant. Pinned Mathlib search found and directly applies Module.End.mem_invtSubmodule_adjoint_iff, Submodule.mapQ, and Submodule.mapQ_mkQ. No theorem was found that packages all of the residual, congruence, quotient, and leastness clauses.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PredictionClosureDynamicalRepair.prediction_closure_minimal_dynamical_repair`
- Dependency: [D5/S3/Quantum/Dynamics/ObserverOrbitClosure](ObserverOrbitClosure.md)
