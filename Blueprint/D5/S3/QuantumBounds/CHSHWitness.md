# A Tight CHSH Witness

## Abstract

A normalized Bell state and fixed Pauli observables attain the positive Tsirelson value.

**Theorem 1.1 (The Bell witness attains the positive Tsirelson value).**

$$\operatorname{tr}(\rho_{Bell} S)=2\sqrt{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A0 be the Pauli Z matrix and A1 the Pauli X matrix. Let B0 be the sum of Pauli Z and Pauli X divided by square root two, and let B1 be their difference divided by square root two. The named matrix S is the CHSH combination of the four corresponding Kronecker products. The state rhoBell is the rank-one density matrix obtained by flattening the existing bellCoefficients matrix and normalizing it by square root two.

The checked trace is exactly positive two times square root two. The companion Lean certificate bell_density_is_state proves that rhoBell is positive semidefinite with trace one, while bob_observables_are_valid proves that B0 and B1 are self-adjoint involutions. Thus the equality is a qualified state-observable witness, not an unnormalized matrix identity.

Mathlib's tsirelson_inequality is the upstream source for the general CHSH upper bound. This declaration establishes only its explicit finite-dimensional tightness witness: it introduces no operator norm, eigenvalue classification, spectral order, C-star matrix instance, or second proof of the upper bound.

## References

- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value`
- Dependency: [D5/S3/Quantum/QubitWitnesses](../Quantum/QubitWitnesses.md)
