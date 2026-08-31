# Hamiltonian Effect Completion Generator

## Abstract

Hamiltonian effect orbits have the commutator derivative and span the reflector.

**Definition 1.1 (Hamiltonian effect orbit).**

Lean statement: `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.hamiltonianEffectOrbit`

*Formalization.* `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.hamiltonianEffectOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named orbit sends time t to the conjugate of an effect E by the canonical propagators at -t and t.

**Theorem 1.2 (The effect orbit derivative is the commutator).**

$$\forall n, \operatorname{Fintype}(n), H, E \in \operatorname{Matrix}(n, n, \mathbb{C}), \operatorname{deriv}(\operatorname{hamiltonianEffectOrbit}(H, E), 0) = i (H E - E H).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.hamiltonian_effect_orbit_hasDerivAt_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite complex matrix algebra and arbitrary matrices H and E, the derivative at time zero is i times H E minus E H.

No Hermiticity or nonemptiness hypothesis is needed for this differentiation identity.

**Theorem 1.3 (The commutator generates the effect completion).**

$$\begin{gathered}\forall n, \operatorname{Fintype}(n),\\{}H \in \operatorname{Matrix}(n, n, \mathbb{C}), initial \in \operatorname{Submodule}(\mathbb{C}, \operatorname{Matrix}(n, n, \mathbb{C})),\\{}\forall E \in \operatorname{Matrix}(n, n, \mathbb{C}), \operatorname{deriv}(\operatorname{hamiltonianEffectOrbit}(H, E), 0) = i (H E - E H) \land\\{}\operatorname{span}(\mathbb{C}, \{A | \exists t \in \mathbb{R}, E \in initial, A = \operatorname{hamiltonianEffectOrbit}(H, E, t)\}) = \operatorname{iSup}(k \in \mathbb{N}, \operatorname{map}(initial, \operatorname{ad}(H)^k)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.hamiltonian_effect_completion_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every effect has the zero-time commutator derivative, while the complex span of all real-time orbit points equals the supremum of the initial subspace under all commutator powers.

The span equality is reused from the established analytic-flow generation theorem.

**Theorem 1.4 (The zero Hamiltonian gives a constant orbit).**

$$\forall n, \operatorname{Fintype}(n), E \in \operatorname{Matrix}(n, n, \mathbb{C}), \forall t \in \mathbb{R}, \operatorname{hamiltonianEffectOrbit}(0, E, t) = E.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.zero_hamiltonian_effect_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero Hamiltonian has identity propagators, so every effect is fixed at every real time.

**Theorem 1.5 (The empty-index orbit is constant).**

$$\forall H, E \in \operatorname{Matrix}(Empty, Empty, \mathbb{C}), \forall t \in \mathbb{R}, \operatorname{hamiltonianEffectOrbit}(H, E, t) = E.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.empty_hamiltonian_effect_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For matrices indexed by the empty type, every orbit is the unique constant matrix-valued function.

**Theorem 1.6 (The zero-dimensional orbit is constant).**

$$\forall H, E \in \operatorname{Matrix}(\operatorname{Fin}(0), \operatorname{Fin}(0), \mathbb{C}), \forall t \in \mathbb{R}, \operatorname{hamiltonianEffectOrbit}(H, E, t) = E.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.fin_zero_hamiltonian_effect_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fin 0 specialization records the natural-number zero-dimensional degeneracy explicitly.

**Theorem 1.7 (The one-dimensional derivative vanishes).**

$$\forall H, E \in \operatorname{Matrix}(\operatorname{Fin}(1), \operatorname{Fin}(1), \mathbb{C}), \operatorname{deriv}(\operatorname{hamiltonianEffectOrbit}(H, E), 0) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.fin_one_hamiltonian_effect_orbit_hasDerivAt_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One-by-one complex matrices commute, so the commutator derivative vanishes at time zero.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.empty_hamiltonian_effect_orbit`
- Truth anchor: `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.fin_one_hamiltonian_effect_orbit_hasDerivAt_zero`
- Truth anchor: `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.fin_zero_hamiltonian_effect_orbit`
- Truth anchor: `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.hamiltonianEffectOrbit`
- Truth anchor: `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.hamiltonian_effect_completion_generator`
- Truth anchor: `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.hamiltonian_effect_orbit_hasDerivAt_zero`
- Truth anchor: `D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.zero_hamiltonian_effect_orbit`
- Dependency: [D5/S3/Quantum/Dynamics/AnalyticFlowGeneration](AnalyticFlowGeneration.md)
