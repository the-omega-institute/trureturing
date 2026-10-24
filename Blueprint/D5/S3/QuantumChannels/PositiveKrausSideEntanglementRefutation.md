# Positive Kraus operators with an entanglement advantage

## Abstract

Two qubit depolarizing channels have strictly positive-definite tetrahedral Kraus operators, yet a Bell-assisted discrimination strategy succeeds with probability 33/56 while every unassisted strategy succeeds with probability at most 47/84.

**Definition 1.1 (Unassisted success probability).**

$$\forall (n: \mathbb{N}), \forall (K1: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (K2: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{successUn}\left(K1, K2, rho, M\right) = ((\frac{1}{2}: \mathbb{R})) \cdot (((M) \cdot (\sum_{i: \operatorname{Fin}\left(n\right)} (((K1\left(i\right)) \cdot (rho)) \cdot (\operatorname{conjTranspose}\left(K1\left(i\right)\right))))).trace.re) + ((\frac{1}{2}: \mathbb{R})) \cdot (((1 - M) \cdot (\sum_{i: \operatorname{Fin}\left(n\right)} (((K2\left(i\right)) \cdot (rho)) \cdot (\operatorname{conjTranspose}\left(K2\left(i\right)\right))))).trace.re)$$

*Formalization.* `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.successUn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For equal prior probabilities, outcome M guesses the first channel and outcome 1-M guesses the second. The Kraus action is the sum of K i times rho times its conjugate transpose. Matrices have complex entries and indices in Fin 2; trace.re is the real part of the trace.

**Definition 1.2 (Success probability with a qubit ancilla).**

$$\forall (n: \mathbb{N}), \forall (K1: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (K2: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \forall (M: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \operatorname{successAs}\left(K1, K2, rho, M\right) = ((\frac{1}{2}: \mathbb{R})) \cdot (((M) \cdot (\sum_{i: \operatorname{Fin}\left(n\right)} (((\operatorname{Matrix.kroneckerMap}\left(fun (x: \mathbb{C}) \mapsto fun (y: \mathbb{C}) \mapsto (x) \cdot (y), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), K1\left(i\right)\right)) \cdot (rho)) \cdot (\operatorname{conjTranspose}\left(\operatorname{Matrix.kroneckerMap}\left(fun (x: \mathbb{C}) \mapsto fun (y: \mathbb{C}) \mapsto (x) \cdot (y), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), K1\left(i\right)\right)\right))))).trace.re) + ((\frac{1}{2}: \mathbb{R})) \cdot (((1 - M) \cdot (\sum_{i: \operatorname{Fin}\left(n\right)} (((\operatorname{Matrix.kroneckerMap}\left(fun (x: \mathbb{C}) \mapsto fun (y: \mathbb{C}) \mapsto (x) \cdot (y), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), K2\left(i\right)\right)) \cdot (rho)) \cdot (\operatorname{conjTranspose}\left(\operatorname{Matrix.kroneckerMap}\left(fun (x: \mathbb{C}) \mapsto fun (y: \mathbb{C}) \mapsto (x) \cdot (y), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), K2\left(i\right)\right)\right))))).trace.re)$$

*Formalization.* `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.successAs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ancilla is the first factor of Fin 2 × Fin 2. Matrix.kroneckerMap multiplies scalar entries, so the identity acts on the ancilla and each Kraus operator acts on the second factor. Equal priors and the outcome rule agree with successUn.

**Definition 1.3 (The identity polar-factor conjecture).**

$$claim = (\forall (n: \mathbb{N}), \forall (K1: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (K2: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{PosDef}\left(K1\left(i\right)\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{PosDef}\left(K2\left(i\right)\right)) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{conjTranspose}\left(K1\left(i\right)\right)) \cdot (K1\left(i\right))) = 1) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{conjTranspose}\left(K2\left(i\right)\right)) \cdot (K2\left(i\right))) = 1) \Rightarrow (\forall (rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \forall (M: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{SLDSpectralEnergy.IsDensity}\left(rho\right)) \Rightarrow (((\operatorname{PosSemidef}\left(M\right)) \land (\operatorname{PosSemidef}\left(1 - M\right))) \Rightarrow (\exists (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \exists (N: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{SLDSpectralEnergy.IsDensity}\left(sigma\right)) \land (((\operatorname{PosSemidef}\left(N\right)) \land (\operatorname{PosSemidef}\left(1 - N\right))) \land (\operatorname{successAs}\left(K1, K2, rho, M\right) \le \operatorname{successUn}\left(K1, K2, sigma, N\right))))))))))$$

*Formalization.* `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.claim` (`✓ std3`).

*Citation.* M. Rexiti; L. Memarzadeh; S. Mancini (2022). *Discrimination of dephasing channels*. DOI: [10.1088/1751-8121/ac6d2c](https://doi.org/10.1088/1751-8121/ac6d2c). URL: <https://arxiv.org/abs/2201.00388>.

*Commentary.*

Section 7, printed pages 16–17: "About the discrimination with side entanglement, it is worth observing the following: i) Side entanglement is very useful for Pauli channels [16]; ii) Side entanglement is partially useful for amplitude damping [6]; iii) Side entanglement is not useful for phase damping channel (present work). Then, we are led to conjecture that side entanglement is useful in channel discrimination if the Kraus operators of the channel admit a polar decomposition with non-trivial unitaries (i.e., not identities). Actually, if the Kraus operators are unitaries, then there is maximal benefit from side entanglement. In contrast, if all Kraus operators have simply the identity as unitary part in the polar decomposition, there is no benefit from side entanglement." The negative clause is encoded for qubit channels and a qubit ancilla. Strict positive definiteness ensures that the polar unitary is uniquely the identity. Both Kraus families have n operators and right Gram sum equal to the identity. IsDensity is the positive-semidefinite trace-one predicate of SLDSpectralEnergy. Each effect and its complement are positive semidefinite. For every assisted input and effect, the assertion asks for an unassisted input and effect with at least the same success probability. The positive-definite qubit restriction is sufficient for a counterexample to the general negative clause.

**Theorem 1.4 (Refutation by positive tetrahedral Kraus operators).**

$$\neg (\forall (n: \mathbb{N}), \forall (K1: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (K2: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{PosDef}\left(K1\left(i\right)\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{PosDef}\left(K2\left(i\right)\right)) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{conjTranspose}\left(K1\left(i\right)\right)) \cdot (K1\left(i\right))) = 1) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{conjTranspose}\left(K2\left(i\right)\right)) \cdot (K2\left(i\right))) = 1) \Rightarrow (\forall (rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \forall (M: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{SLDSpectralEnergy.IsDensity}\left(rho\right)) \Rightarrow (((\operatorname{PosSemidef}\left(M\right)) \land (\operatorname{PosSemidef}\left(1 - M\right))) \Rightarrow (\exists (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \exists (N: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{SLDSpectralEnergy.IsDensity}\left(sigma\right)) \land (((\operatorname{PosSemidef}\left(N\right)) \land (\operatorname{PosSemidef}\left(1 - N\right))) \land (\operatorname{successAs}\left(K1, K2, rho, M\right) \le \operatorname{successUn}\left(K1, K2, sigma, N\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/rexiti-memarzadeh-mancini-2022-positive-kraus-side-entanglement` (refuted) by `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rexiti-memarzadeh-mancini-2022-positive-kraus-side-entanglement","declaration_gid":"D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Rexiti; L. Memarzadeh; S. Mancini (2022). *Discrimination of dephasing channels*. DOI: [10.1088/1751-8121/ac6d2c](https://doi.org/10.1088/1751-8121/ac6d2c). URL: <https://arxiv.org/abs/2201.00388>.

*Commentary.*

For a=2 and a=3, use four Kraus operators (aI+sX+tY+uZ)/(2√(a²+3)), with (s,t,u)=(1,1,1),(1,−1,−1),(−1,1,−1),(−1,−1,1). X and Z are the qubit Pauli matrices and Y=Complex.I times XZ. A positive multiple of the identity plus a positive Gram matrix proves strict positive definiteness. The resulting channel sends A to ((a²−1)/(a²+3))A+(2/(a²+3))trace(A)I. Two nonnegative trace pairings bound every unassisted success probability by 47/84. The frozen Bell density is both input and effect for the assisted strategy, whose success probability is 33/56. The strict gap is 5/168. The paper's phase-damping result concerns its particular channel family and is unaffected by this counterexample to the general negative clause.

## References

- Truth anchor: `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.result`
- Truth anchor: `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.successAs`
- Truth anchor: `D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.successUn`
- Dependency: [D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal](../Quantum/Entanglement/BellPureStateMixedMarginal.md)
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../Quantum/Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/EnvironmentRecords](../Quantum/EnvironmentRecords.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../Quantum/FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Quantum/Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation](../Quantum/Measurements/BroadcastingChannelExtremaRefutation.md)
- Dependency: [D5/S3/Quantum/QubitWitnesses](../Quantum/QubitWitnesses.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../QuantumBounds/CHSHWitness.md)
