# Finite-copy trace distance on a closed Bloch chord

## Abstract

Projective readout and pure-endpoint preparation give Bernoulli product bounds on finite-copy qubit trace distance along a closed Bloch chord.

Write ρ(t) for the trace-one qubit matrix with Bloch vector m + t e, where m and e are real three-vectors, e is a unit vector, and m is perpendicular to e. The physical points satisfy ‖m + t e‖ ≤ 1. Let ℓ = √(1 − ‖m‖²) be the chord radius and B(t) the sign law with probabilities (1 + t)/2 and (1 − t)/2, in that order.

**Theorem 1.1 (Projective measurement along the chord).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.chordProjector_isProjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.chordProjector_isProjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit Bloch direction e, the qubit matrices with Bloch vectors e and −e form a two-outcome POVM whose effects are idempotent. On a physical state ρ(t) the readout has law B(t).

**Theorem 1.2 (Pure endpoint states).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.chordEndpoint_isPure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.chordEndpoint_isPure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If e is a unit vector, m is perpendicular to e, and ‖m‖² ≤ 1, each endpoint matrix ρ(ℓ) and ρ(−ℓ) is positive semidefinite, has trace one, and is idempotent.

**Theorem 1.3 (Two finite-copy bounds).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.finite_copy_chord_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.finite_copy_chord_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

`Wu.QubitChordFiniteCopy.finite_copy_chord_comparison` holds for every natural n and all real a and b with ‖m + a e‖ ≤ 1 and ‖m + b e‖ ≤ 1. The trace distance between the actual tensor powers ρ(a)⊗ⁿ and ρ(b)⊗ⁿ is at least TV(B(a)⊗ⁿ, B(b)⊗ⁿ) and at most TV(B(a/ℓ)⊗ⁿ, B(b/ℓ)⊗ⁿ), with TV the total variation of the sign-string laws. The lower bound reads each copy with the projective measurement along e. Grouping the strings on which the first law is at least the second gives a binary outcome whose probability gap equals the lower total variation. The upper bound uses mixtures of the same tensor products of pure endpoints, with independent signs of means a/ℓ and b/ℓ, respectively. The closed chord includes its pure endpoints. When ℓ = 0, both states coincide since a = b = 0, and the normalized means are zero under Lean’s real division. For n = 0, there is one empty record and both states are the same scalar matrix, so all three distances are zero.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.chordEndpoint_isPure`
- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.chordProjector_isProjective`
- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy.finite_copy_chord_comparison`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../../Information/ActualQubitChordObstruction.md)
- Dependency: [D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability](../AdvantageQuantumNonSimulability.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/DiamondBounds](../Auric/DiamondBounds.md)
- Dependency: [D5/S3/TotalVariation/Pinsker](../../../TotalVariation/Pinsker.md)
