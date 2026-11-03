# Four-qubit correlation monogamy

## Abstract

The twenty-seven squared two-body Pauli correlations of a normalized four-qubit vector sum to at most three.

The qubits are ordered A, B, C, D, with positions 0, 1, 2, 3. The target index X = 0, 1, 2 denotes B, C, D, respectively, and each Pauli index i or j = 0, 1, 2 denotes the x, y, z spin direction. The amplitude vector ψ is indexed by functions from Fin 4 to Fin 2, the sixteen computational basis states.

**Definition 1.1 (A two-body Pauli word).**

$$\forall (X: \operatorname{Fin}\left(3\right)), (\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), ((\operatorname{D5.S3.QuantumStates.FourQubitCorrelationMonogamy.twoBodyWord}\left(X, i, j\right): (\operatorname{Fin}\left(4\right)) \to (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli})) = \lambda (q: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{ite}\left(q = (0: \operatorname{Fin}\left(4\right)), ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}]\left(i\right), \operatorname{ite}\left(q = \operatorname{Fin.succ}\left(X\right), ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}]\left(j\right), \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}\right)\right)))))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.twoBodyWord` (`✓ std3`).

*Citation.* Shuming Cheng, Antony Milne, Michael J. W. Hall, Howard M. Wiseman (2016). *Volume monogamy of quantum steering ellipsoids for multi-qubit systems*. DOI: [10.1103/PhysRevA.94.042105](https://doi.org/10.1103/PhysRevA.94.042105). URL: <https://arxiv.org/abs/1606.02390v2>.

*Commentary.*

The word places Pauli i on A and Pauli j on the target X, with the identity on the other two qubits. Fin.succ sends X to its position among B, C, D. The ordered vector ![Pauli.X, Pauli.Y, Pauli.Z] supplies the three spin labels from `D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli`. These are the two-body observables in the source's correlation entries Tᵢⱼ, defined in arXiv:1606.02390v2, finalversion.tex, lines 123–133.

**Definition 1.2 (A reduced-state correlation entry).**

$$\forall (\psi: ((\operatorname{Fin}\left(4\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), (\forall (X: \operatorname{Fin}\left(3\right)), (\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), ((\operatorname{D5.S3.QuantumStates.FourQubitCorrelationMonogamy.correlation}\left(\psi, X, i, j\right): \mathbb{R}) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\psi\right) \cdot \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.wordOp}\left(\operatorname{D5.S3.QuantumStates.FourQubitCorrelationMonogamy.twoBodyWord}\left(X, i, j\right)\right)\right)\right)))))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.correlation` (`✓ std3`).

*Citation.* Shuming Cheng, Antony Milne, Michael J. W. Hall, Howard M. Wiseman (2016). *Volume monogamy of quantum steering ellipsoids for multi-qubit systems*. DOI: [10.1103/PhysRevA.94.042105](https://doi.org/10.1103/PhysRevA.94.042105). URL: <https://arxiv.org/abs/1606.02390v2>.

*Commentary.*

The matrix `D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity` is the outer product ψψ†, and `D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.wordOp` turns the word into its four-qubit tensor-product observable. The correlation is the real part of the trace of their product. For normalized ψ this is Tᵢⱼ of the AX reduced state: the identity factors on the two remaining qubits give the same expectation before or after the partial trace. This expresses the source's definition in finalversion.tex, lines 129–133, on the full four-qubit space. The displayed definition also applies to unnormalized vectors.

**Definition 1.3 (The conjectured sum of squared correlations).**

$$(\operatorname{D5.S3.QuantumStates.FourQubitCorrelationMonogamy.claim}: \operatorname{Prop}) = (\forall (\psi: ((\operatorname{Fin}\left(4\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), ((\operatorname{dotProduct}\left(\operatorname{star}\left(\psi\right), \psi\right) = (1: \mathbb{C})) \to (\sum_{X: \operatorname{Fin}\left(3\right)} (\sum_{i: \operatorname{Fin}\left(3\right)} (\sum_{j: \operatorname{Fin}\left(3\right)} ((\operatorname{D5.S3.QuantumStates.FourQubitCorrelationMonogamy.correlation}\left(\psi, X, i, j\right))^{2}))) \le (3: \mathbb{R}))))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuming Cheng, Antony Milne, Michael J. W. Hall, Howard M. Wiseman (2016). *Volume monogamy of quantum steering ellipsoids for multi-qubit systems*. DOI: [10.1103/PhysRevA.94.042105](https://doi.org/10.1103/PhysRevA.94.042105). URL: <https://arxiv.org/abs/1606.02390v2>.

*Commentary.*

The source conjectures equation (36) for all pure four-qubit states in arXiv:1606.02390v2, finalversion.tex, lines 395–399. Its three terms are the squared Frobenius norms of the AB, AC and AD correlation matrices. Here each norm is the sum of the nine squared real correlation entries, and purity is expressed by a vector whose conjugate dot product with itself is one. The source states this as a conjecture supported by numerical observations.

**Theorem 1.4 (The correlation sum is at most three).**

$$\forall (\psi: ((\operatorname{Fin}\left(4\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), ((\operatorname{dotProduct}\left(\operatorname{star}\left(\psi\right), \psi\right) = (1: \mathbb{C})) \to (\sum_{X: \operatorname{Fin}\left(3\right)} (\sum_{i: \operatorname{Fin}\left(3\right)} (\sum_{j: \operatorname{Fin}\left(3\right)} ((\operatorname{D5.S3.QuantumStates.FourQubitCorrelationMonogamy.correlation}\left(\psi, X, i, j\right))^{2}))) \le (3: \mathbb{R})))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.result` (`✓ std3`). ∎

*Resolves.* `Problems/cheng-milne-hall-wiseman-2016-four-qubit-correlation-monogamy` (proved) by `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cheng-milne-hall-wiseman-2016-four-qubit-correlation-monogamy","declaration_gid":"D5/S3/QuantumStates/FourQubitCorrelationMonogamy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shuming Cheng, Antony Milne, Michael J. W. Hall, Howard M. Wiseman (2016). *Volume monogamy of quantum steering ellipsoids for multi-qubit systems*. DOI: [10.1103/PhysRevA.94.042105](https://doi.org/10.1103/PhysRevA.94.042105). URL: <https://arxiv.org/abs/1606.02390v2>.

*Commentary.*

For each k in Fin 3, index nine words by u in Fin 3 × Fin 3, taking the target u.1, the Pauli direction k + u.1 on A, and the direction u.2 on the target. Addition here is modulo three. For distinct u and v, the product of the four letter commutation signs is −1. When the targets agree, the target letters differ; when the targets differ, the letters on A differ. In either case exactly one position contributes a negative sign. The Hermitian Pauli-word matrices square to the identity, and the signed word commutation law makes each of the three families pairwise anticommuting.

For a finite family P of Hermitian involutions with these anticommutation relations, let ρ be any density state and set a i = expectation ρ (P i), H = ∑ i, (a i : ℂ) • P i and s = ∑ i, (a i)². The real coefficients make H Hermitian. Apply `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.cliffordLinear_anticommutator` to the two identical coefficient families i ↦ (a i : ℂ). After cancelling the nonzero complex scalar 2, it gives H² = (s : ℂ) • I.

Expanding `D5/S3/Quantum/Information/CovarianceSumBound.expectation` through the finite sum and the real scalar coefficients gives expectation ρ H = s. The square identity and trace ρ = 1 give expectation ρ (H²) = s. Hence `D5/S3/Quantum/Information/CovarianceSumBound.variance_nonneg` yields 0 ≤ s − s². Since 0 ≤ (s − 1)² ≤ 1 − s, it follows that s ≤ 1.

Applying this bound to each nine-element family bounds its squared expectations by one. To sum the families, first exchange the i and j sums. For each fixed X and j, the bijection k ↦ k + X of Fin 3 replaces the i sum by the k sum. Exchanging the remaining finite sums then partitions all twenty-seven terms into the three families. Summing their bounds gives ∑ k : Fin 3, 1 = 3 for every density state on the four-qubit space.

For a normalized vector ψ, `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.pureDensityState` supplies the density state with matrix ψψ†. Its expectations of the two-body words are exactly correlation ψ X i j. Substituting this density state into the preceding bound proves the displayed proposition for every normalized pure four-qubit vector.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.pureDensityState`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.expectation`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.variance_nonneg`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.wordOp`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.cliffordLinear_anticommutator`
- Truth anchor: `D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity`
- Truth anchor: `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.claim`
- Truth anchor: `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.correlation`
- Truth anchor: `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.result`
- Truth anchor: `D5/S3/QuantumStates/FourQubitCorrelationMonogamy.twoBodyWord`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](../Quantum/Dynamics/EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum](../Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.md)
