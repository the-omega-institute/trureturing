# Pauli flow with arbitrary finite quantum memory

## Abstract

Actual amplified Pauli channels connect noncommuting trace entropy to dissipative dynamics.

The qubit factor and its Pauli spin matrices are fixed. The finite quantum memory and real unit axes are arbitrary within this model. These results do not cover arbitrary algebras or conditional expectations.

All matrix traces are ordinary unnormalized traces, logarithms are natural, and derivatives use the L2 operator norm. The finite-memory two-axis application below combines the actual channel and derivative suppliers with canonical channel data processing, continuous trace entropy and the qubit spectral formula. It applies to singular joint states and singular actual memory marginals. No external open-problem resolution or literature novelty is asserted.

For a nonempty finite memory R and a joint density rho, put tau=E0(rho), and let E_n,E_m be the actual spin pinchings for real unit axes n,m. Write c=abs(n dot m), and assume c<1. The canonical extended relative entropies D(rho||tau), D(rho||E_v(rho)) and D(E_v(rho)||tau) are finite for v=n,m. They satisfy D(rho||tau)=D(rho||E_v(rho))+D(E_v(rho)||tau). The two-axis comparison is D(E_n(rho)||tau)+D(E_m(rho)||tau)<=(1+c)D(rho||tau). Equivalently, (1-c)D(rho||tau)<=D(rho||E_n(rho))+D(rho||E_m(rho)). The coefficient in the latter upper bound for D(rho||tau) is exactly 1/(1-c). Orthogonal axes c=0 are included; parallel or antiparallel axes c=1 are excluded.

Support precedes finite-value conversion. Positivity of the conjugated summand gives rho/2<=E_v(rho). Applying this bound successively to two orthogonal axes and using pinching_comp_eq_equilibrium gives rho/4<=tau. Applying a pinching to this domination also controls E_v(rho) by the same reference. The nullspace consequence of Loewner domination therefore proves each required support inclusion, including when the actual marginal is singular. Only then is extendedQuantumRelativeEntropy replaced by its finiteTraceLogRelativeEntropy value. The spin lift commutes with its pinching output; CFC preserves that commutation, and cyclic trace identifies Tr(rho log E_v(rho)) with Tr(E_v(rho) log E_v(rho)). The analogous actual-reference pairing gives Pythagoras without subtracting infinities.

The angular argument first changes the sign of m when needed, leaving E_m unchanged, so that n dot m=c. Orthogonal bisectors a,b and positive alpha,beta satisfy n=alpha a+beta b, m=alpha a-beta b, alpha^2=(1+c)/2 and beta^2=(1-c)/2; no division by c occurs. The two Kraus matrices I/sqrt(2) and U_v/sqrt(2), instantiated in finite_kraus_quantum_channel, realize E_v on every joint matrix. Canonical channel data processing applies to these actual maps. For the involution U_w, the production pairing p_w(Y)=Re Tr((Y-E_w(Y))log Y) equals D(U_w Y U_w-adjoint||Y)/2 and also D(Y||U_w Y U_w-adjoint)/2. The second equality follows from involution covariance and cyclic trace, not a general symmetry of relative entropy. Strong Klein and channel data processing give its nonnegativity and the required contraction under an orthogonal pinching.

Use the flow T_t built from E_a,E_b. A tilted E_v commutes with E_a+E_b, the generator L and T_t; separate commutation with E_a or E_b is unnecessary. The actual marginal and tau are preserved. Three instances of supported_relativeEntropy_flow_derivative, combined with the angular production identity, show that G(t)=D(E_n(T_t(rho))||tau)+D(E_m(T_t(rho))||tau)-(1+c)D(T_t(rho)||tau) has nonnegative derivative for t>0 when the memory marginal is faithful. The entropy-difference form of G is continuous because x log x extends continuously at zero and continuous CFC applies on self-adjoint matrices. Since T_t tends to E0 and G(t) tends to zero, scalar derivative monotonicity and closed-order limits give G(t)<=0 and then the t=0 bound. This uses no improper integration.

For an arbitrary input, smooth the full joint density as rho_epsilon=(1-epsilon)rho+epsilon I/(2 card R). Its actual marginal is (1-epsilon)partialTraceLeft(rho)+epsilon I_R/card R, so its reference is the corresponding tau_epsilon. These actual marginals are positive definite for 0<epsilon<=1. For each fixed epsilon, finish the positive-time and zero-time flow limits first. Then let epsilon approach zero in the continuous entropy differences. This sequential passage covers a singular marginal without continuity of a moving singular logarithm and without interchanging the two limits.

Sharpness uses the positive product family rho_x=((I+x spin(a))/2) tensor (I_R/card R), with 0<x<1 and a the bisector after the sign adjustment. Its actual reference is I/(2 card R). Put F(x)=log 2-binEntropy((1+x)/2). The qubit_spectral_entropy_det supplier and vonNeumannEntropy_productState give D(rho_x||tau)=F(x), each output relative entropy F(alpha x), and the AT denominator 2(F(x)-F(alpha x)). Pinned binary-entropy derivatives and two applications of lHopital_zero_nhdsGT give F(d x)/x^2 tending to d^2/2. Consequently the output-sum ratio tends to 1+c, the AT denominator is eventually strictly positive, and the AT ratio tends to 1/(1-c). For every smaller real coefficient, a sufficiently small positive x violates that proposed bound. No nonzero attained extremizer is asserted.

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
