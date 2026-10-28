# Finite-Time Tomography Saturation

## Abstract

All-future observability is decided by the first trace-zero carrier dimension layers.

**Theorem 1.1 (The ambient dimension truncates the future kernel).**

$$\forall K, V, Y: Type,\operatorname{Field}(K) \land \operatorname{AddCommGroup}(V) \land \operatorname{Module}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land \operatorname{AddCommGroup}(Y) \land \operatorname{Module}(K, Y) \Rightarrow\\{}\forall A: \operatorname{LinearMap}(K, V, V), C: \operatorname{LinearMap}(K, V, Y),\\{}\operatorname{iInf}(k \in \mathbb{N}, \operatorname{ker}(C \circ A^{k})) = \operatorname{iInf}(k \in \operatorname{Fin}(\operatorname{finrank}(K, V)), \operatorname{ker}(C \circ A^{k})).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation.all_future_kernel_eq_finrank_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite-dimensional module V over any field K, an endomorphism A and a linear readout C into any K-module Y, the intersection of all future kernels equals the intersection indexed by Fin(finrank K V). The zero-dimensional case is included. This general statement also applies to complex structural Hilbert spaces with their classicality-defect readout.

**Theorem 1.2 (The exact trace-zero dimension controls every future readout).**

$$\forall d\in \mathbb{N}, \operatorname{NeZero}(d), Y: Type,\\{}\operatorname{AddCommGroup}(Y) \land \operatorname{Module}(\mathbb{R}, Y),\\{}A: \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianTraceZero}(\operatorname{Fin}(d)), \operatorname{HermitianTraceZero}(\operatorname{Fin}(d))), C: \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianTraceZero}(\operatorname{Fin}(d)), Y) \Rightarrow\\{}N_{\infty} := \operatorname{iInf}(k \in \mathbb{N}, \operatorname{ker}(C \circ A^{k})); N_{d^{2} - 1} := \operatorname{iInf}(k \in \operatorname{Fin}(d^{2} - 1), \operatorname{ker}(C \circ A^{k}));\\{}(N_{\infty} = \operatorname{bot}() \Rightarrow N_{d^{2} - 1} = \operatorname{bot}()) \land N_{\infty} = N_{d^{2} - 1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation.finite_time_tomography_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive matrix dimension d. The state carrier is the imported real subspace HermitianTraceZero(Fin d), the evolution A is a real-linear endomorphism of that carrier, and C is a real-linear readout into an arbitrary real module Y.

The all-future kernel is constructed by intersecting ker(C composed with A to the kth power) over every natural k. The finite kernel uses the same source test over the exact index type Fin(d squared minus one).

The public statement contains both source clauses: a trivial all-future kernel forces the finite kernel to be trivial, and more strongly the two constructed kernels are equal.

The proof applies Cayley--Hamilton polynomial reduction to express every later evolution power through the first ambient-finrank powers. The imported finrank theorem identifies that ambient real dimension as d squared minus one.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation.all_future_kernel_eq_finrank_kernel`
- Truth anchor: `D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation.finite_time_tomography_saturation`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../../Quantum/Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence](../../Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence.md)
