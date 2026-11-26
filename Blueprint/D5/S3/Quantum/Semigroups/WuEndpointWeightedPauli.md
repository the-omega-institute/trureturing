# Weighted Pauli conjugations at the Wu endpoint

## Abstract

Pauli expansion identifies both the actual endpoint map and the unweighted twirl.

With α = (1 + λ)/2 and β = (1 − λ)/2, a product of k distinct conjugating words has weight α^(4−k)β^k. Multiplying the four sign factors on each Pauli word gives the eigenvalue λᵈ, and the Pauli basis determines the linear map.

**Theorem 1.1 (Weighted Pauli representation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli.A1_eq_weighted_pauli`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli.A1_eq_weighted_pauli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted sum of all sixteen ordered Pauli conjugations equals the signed two-mode map.

**Theorem 1.2 (Unweighted Pauli twirl).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli.endpoint_pauli_twirl`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli.endpoint_pauli_twirl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unweighted sum of the sixteen conjugations sends any two-mode matrix X to 4 tr(X) times the identity.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli.A1_eq_weighted_pauli`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli.endpoint_pauli_twirl`
- Dependency: [D5/S3/Quantum/Semigroups/WuEndpointPauliFrame](WuEndpointPauliFrame.md)
