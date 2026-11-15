# Pauli flow with arbitrary finite quantum memory

## Abstract

Actual amplified Pauli channels connect noncommuting trace entropy to dissipative dynamics.

The qubit factor and its Pauli spin matrices are fixed. The finite quantum memory and real unit axes are arbitrary within this model. These results do not cover arbitrary algebras or conditional expectations.

All matrix traces are ordinary unnormalized traces, and derivatives use the L2 operator norm. The faithful-memory derivative is a local milestone. The all-state arbitrary-memory two-axis inequality, its angular comparison, singular endpoint passage, amplified Pythagoras identity and sharpness remain separate mathematical obligations. No external open-problem resolution or literature novelty is asserted.

**Definition 1.1 (Spin matrices with quantum memory).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.spinLift`

*Formalization.* `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.spinLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real three-vector v, spinLift(v) is spin(v) tensor I_R on Fin 2 times an arbitrary finite memory R. A unit vector is specified by v dot v = 1. The existing Pauli Hermiticity and square identities make this lift a Hermitian unitary.

**Definition 1.2 (The actual Pauli pinching).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.pinching`

*Formalization.* `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.pinching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real linear map E_v sends X to (X+U_v X U_v-adjoint)/2 on every complex matrix. For a unit vector v this is the two-Kraus pinching channel. Its definition retains the actual matrix action.

**Definition 1.3 (The memory reference expectation).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibrium`

*Formalization.* `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibrium` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E0(X) is (I_2/2) tensor partialTraceLeft(X). The partial trace is taken on the input matrix itself. It is not supplied as a separate marginal or as an assumed invariant.

**Theorem 1.4 (Orthogonal pinchings compose to complete qubit erasure).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.pinching_comp_eq_equilibrium`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.pinching_comp_eq_equilibrium` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be real three-vectors with a dot a = b dot b = 1 and a dot b = 0. For every complex matrix X on Fin 2 times R, E_a(E_b(X)) = E_b(E_a(X)) = E0(X). The proof first uses the original spin triple-product identity on arbitrary qubit blocks, and then applies it to all memory matrix entries. No state, trace, or Hermiticity condition is needed.

**Theorem 1.5 (The actual memory marginal is preserved).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.partialTraceLeft_pinching`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.partialTraceLeft_pinching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit real three-vector v and every complex matrix X on the joint system, partialTraceLeft(E_v(X)) = partialTraceLeft(X). This follows by taking the qubit trace of the actual conjugation in each memory block.

**Theorem 1.6 (A faithful memory gives a faithful reference).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibrium_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibrium_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If partialTraceLeft(X) is positive definite, then E0(X) is positive definite. The statement requires faithfulness only of the actual marginal, not of the joint input X.

**Definition 1.7 (A matrix curve on the whole real line).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow`

*Formalization.* `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For s=exp(-t), T_t(X)=s^2 X+s(1-s)(E_a(X)+E_b(X))+(1-s)^2 E0(X). This formula defines a matrix for every real t. State and channel conclusions are restricted to t>=0; the all-real formula supplies the domain for ordinary two-sided differentiation at positive times.

**Definition 1.8 (The sign of the dissipative generator).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.generator`

*Formalization.* `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.generator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(X)=2X-E_a(X)-E_b(X). The evolution equation uses minus this generator: T-prime=-L(T). Entropy production is paired with L, so the entropy derivative is minus that pairing.

**Theorem 1.9 (Marginal preservation along the matrix curve).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.partialTraceLeft_flow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.partialTraceLeft_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit a and b, partialTraceLeft(T_t(X)) = partialTraceLeft(X) for every complex X and every real t. Orthogonality is not required for this preservation law. Taking the full trace also proves trace preservation.

**Theorem 1.10 (A concrete lower bound at nonnegative times).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive semidefinite X and t>=0, T_t(X)>=(1-exp(-t))^2 E0(X) in Loewner order. The remaining terms are positive semidefinite with nonnegative coefficients. This bound does not assume a spectral gap or a dissipation identity.

**Theorem 1.11 (Faithfulness at positive times).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If X is positive semidefinite and its actual memory marginal is positive definite, then T_t(X) is positive definite for every t>0. The input joint matrix is allowed to be singular. The lower bound by a positive multiple of E0(X) gives the conclusion.

**Theorem 1.12 (The negative-generator equation).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.hasDerivAt_flow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.hasDerivAt_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For orthonormal real axes a and b, every complex input X, and every real t, the raw matrix curve has real derivative -L(T_t(X)) in the L2 operator norm. The proof differentiates its explicit exponential coefficients and uses the actual pinching composition and fixed-reference identities.

**Theorem 1.13 (The fixed logarithmic reference cancels).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.generator_log_equilibrium_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.generator_log_equilibrium_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit axes a,b and arbitrary complex X,Y, Tr(L(Y) log E0(X))=0. The local spin lifts commute with the actual tensor reference, and CFC preserves this commutation for its logarithm. Cyclicity of trace and the unitary square identities then remove each pinching from the pairing. Orthogonality, positivity and commutation of X with Y are not hypotheses.

**Definition 1.14 (The raw relative entropy observable).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.relativeEntropyCurve`

*Formalization.* `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.relativeEntropyCurve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real observable F(t)=Re Tr(T_t(X)(log T_t(X)-log E0(X))) is defined on the whole real line using the total CFC logarithm. At positive times under faithful memory it agrees with supported canonical relative entropy.

**Theorem 1.15 (The four-unitary channel realization).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_quantumChannel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_quantumChannel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For orthonormal a,b and t>=0, a canonical all-amplification QuantumChannel has matrix action T_t on every complex input. With p=(1+s)/2 and q=(1-s)/2, its unitary weights are p^2,pq,pq,q^2 on I,U_a,U_b,U_a U_b. Their square roots give an actual complete Kraus family; the existing finite-Kraus constructor supplies complete positivity and trace preservation.

**Definition 1.16 (Canonical states from the channel).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flowState`

*Formalization.* `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flowState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a joint DensityState rho and t>=0, flowState is the image under the actual four-unitary QuantumChannel. Its matrix is T_t applied to the matrix of rho. The channel realization therefore enters the entropy statement through the state itself.

**Definition 1.17 (The canonical reference state).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibriumState`

*Formalization.* `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibriumState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference DensityState has matrix (I_2/2) tensor the actual memory marginal of rho. Positivity and unit trace follow from the partial-trace suppliers and the explicit reference map.

**Theorem 1.18 (Entropy dissipation for arbitrary finite quantum memory).**

Lean statement: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.supported_relativeEntropy_flow_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.supported_relativeEntropy_flow_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be any nonempty finite memory type, a,b real orthonormal axes, and rho any joint DensityState whose actual memory marginal is positive definite. For each t>0 the raw observable has a genuine two-sided real derivative -Re Tr(L(T_t)(log T_t-log tau)), equal to -Re Tr(L(T_t) log T_t), where tau=E0(rho). The flow preserves the actual memory marginal and has trace one. At that time flowState is supported in equilibriumState, its finiteTraceLogRelativeEntropy equals F(t), and its extendedQuantumRelativeEntropy is the finite value F(t) in WithTop Real. The proof applies the noncommuting trace-entropy chain rule with V=-L(T_t), uses zero generator trace to remove the identity correction, and proves the fixed-reference pairing cancellation from the actual maps. The hypotheses allow singular rho; they do not yet allow a singular memory marginal.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibrium`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibriumState`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibrium_posDef`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flowState`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_lower_bound`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_posDef`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_quantumChannel`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.generator`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.generator_log_equilibrium_pairing`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.hasDerivAt_flow`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.partialTraceLeft_flow`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.partialTraceLeft_pinching`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.pinching`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.pinching_comp_eq_equilibrium`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.relativeEntropyCurve`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.spinLift`
- Truth anchor: `D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.supported_relativeEntropy_flow_derivative`
- Dependency: [D5/S3/Quantum/Divergence/TraceEntropyCalculus](../Divergence/TraceEntropyCalculus.md)
- Dependency: [D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation](../Information/MixedUnitaryPinchingCommutation.md)
