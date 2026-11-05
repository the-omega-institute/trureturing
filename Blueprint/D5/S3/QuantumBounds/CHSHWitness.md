# A Tight CHSH Witness

## Abstract

A normalized Bell state and fixed Pauli observables attain the positive Tsirelson value.

**Theorem 1.1 (The square root normalization is nonzero).**

$$(\sqrt{2} : \mathbb{C}) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive real square root of two remains nonzero in the complex numbers.

**Theorem 1.2 (The inverse square root normalization).**

$$((\sqrt{2} : \mathbb{C})^{-1}) \cdot ((\sqrt{2} : \mathbb{C})^{-1}) = (2 : \mathbb{C})^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_inv_mul_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the complex numbers, the product of two inverses of the positive real square root of two is the inverse of two. This is the normalization factor for the Bell density matrix.

The classical comparison uses four measurable sign-valued random variables on one probability space whose law is independent of the settings. The commutative CHSH inequality bounds the absolute value pointwise by two. Integrating with respect to that same probability law gives the bound for the four correlations; finite support is not required. The Bell witness uses the Pauli Z and X observables and their normalized sum and difference to attain twice the square root of two.

For finite local positive operator-valued measurements, summing the joint trace probabilities over the second outcome replaces its effects by the identity. The first marginal therefore depends only on the first effect and the common density matrix, independently of the second setting. The argument uses normalization of each local measurement and a shared quantum state, and does not require a shared classical table of answers for all incompatible settings.

**Theorem 1.3 (The Bell density is a normalized positive state).**

$$\operatorname{PosSemidef}(\rho_{Bell}) \land \operatorname{tr}(\rho_{Bell})=1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized Bell vector defines a rank-one positive semidefinite density matrix. Its trace is one.

**Theorem 1.4 (Bob's fixed observables are self-adjoint involutions).**

$$\forall j\in\{0,1\},\ B_j^{*}=B_j \land B_j^{2}=I$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.bob_observables_are_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bob's sum and difference of the Pauli Z and X matrices, each divided by square root two, are self-adjoint and square to the identity.

**Theorem 1.5 (The Kronecker operator equals the lifted CHSH combination).**

$$S=A_0^{L}B_0^{L}+A_0^{L}B_1^{L}+A_1^{L}B_0^{L}-A_1^{L}B_1^{L}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.chsh_operator_eq_lifted_chsh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lift Alice's observables by tensoring on the right with the identity, and Bob's by tensoring on the left. The original sum of Kronecker products is exactly the CHSH combination of these lifted matrices; the superscript L denotes this lift.

**Theorem 1.6 (The lifted observables satisfy the CHSH tuple conditions).**

$$\operatorname{IsCHSHTuple}(A_0^{L},A_1^{L},B_0^{L},B_1^{L})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.lifted_observables_form_chsh_tuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four lifted observables are self-adjoint involutions in the two-qubit matrix algebra. Each lifted Alice observable commutes with each lifted Bob observable, as required by IsCHSHTuple.

**Theorem 1.7 (The Bell witness attains the positive Tsirelson value).**

$$\operatorname{tr}(\rho_{Bell} S)=2\sqrt{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A0 be the Pauli Z matrix and A1 the Pauli X matrix. Let B0 be the sum of Pauli Z and Pauli X divided by square root two, and let B1 be their difference divided by square root two. The named matrix S is the CHSH combination of the four corresponding Kronecker products. The state rhoBell is the rank-one density matrix obtained by flattening the existing bellCoefficients matrix and normalizing it by square root two.

The checked trace is exactly positive two times square root two. The companion Lean certificate bell_density_is_state proves that rhoBell is positive semidefinite with trace one, while bob_observables_are_valid proves that B0 and B1 are self-adjoint involutions. Thus the equality is a qualified state-observable witness, not an unnormalized matrix identity.

Mathlib's tsirelson_inequality is the upstream source for the general CHSH upper bound. This declaration establishes only its explicit finite-dimensional tightness witness: it introduces no operator norm, eigenvalue classification, spectral order, C-star matrix instance, or second proof of the upper bound.

## References

- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.bob_observables_are_valid`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.chsh_operator_eq_lifted_chsh`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_inv_mul_self`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_ne_zero`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.lifted_observables_form_chsh_tuple`
- Dependency: [D5/S3/Quantum/QubitWitnesses](../Quantum/QubitWitnesses.md)
