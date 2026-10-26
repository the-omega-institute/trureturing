# Advantage-quantum measurements cannot be simulated with finitely many copies

## Abstract

No binary advantage-quantum measurement admits an exact quantum simulation on any finite number of copies.

Consider two finite-dimensional complex systems and a binary measurement with effects E and I − E. Arai's dual-operator-valued measurements have Hermitian effects that are nonnegative on every product vector. The matrices below use Fin dA × Fin dB as the joint basis. The symbol 1 denotes the identity matrix, and brackets on typeclasses denote anonymous assumptions.

**Definition 1.1 (The two complementary effects).**

$$\forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall E \in \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; \forall i \in \operatorname{\mathit{Fin}}\left(2\right),\; \operatorname{\mathit{binaryEffect}}\left(E, i\right) = ![E, 1 - E]\left(i\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.binaryEffect` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

Outcome zero has effect E and outcome one has effect I − E. Their sum is the identity, without any positivity assumption on E.

**Definition 1.2 (Hermitian effects nonnegative on product vectors).**

$$\forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall E \in \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; (\operatorname{\mathit{IsDovm}}\left(E\right)) \Leftrightarrow (\forall i \in \operatorname{\mathit{Fin}}\left(2\right),\; (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{IsHermitian}}\left(\operatorname{\mathit{binaryEffect}}\left(E, i\right)\right)) \land (\forall a \in \operatorname{\mathit{Fin}}\left(\mathit{dA}\right) \to \mathit{Complex},\; \forall b \in \operatorname{\mathit{Fin}}\left(\mathit{dB}\right) \to \mathit{Complex},\; 0 \le \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left((j:\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right)) \mapsto (a\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(j\right)\right)) \cdot (b\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(j\right)\right))\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{binaryEffect}}\left(E, i\right), (j:\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right)) \mapsto (a\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(j\right)\right)) \cdot (b\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(j\right)\right))\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.IsDovm` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

Each effect is Hermitian and block positive. The displayed quadratic form tests every pair of local vectors a and b: their product vector has coordinate a(x) b(y). Here star is coordinatewise complex conjugation, dotProduct sums coordinate products, and mulVec is matrix-vector multiplication. This is the dual cone of the separable cone in the thesis's definition of a DOVM.

**Definition 1.3 (The infimum of the eigenvalues).**

$$\forall I \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(I\right)], [\operatorname{\mathit{DecidableEq}}\left(I\right)], \forall A \in \operatorname{\mathit{Matrix}}\left(I, I, \mathit{Complex}\right),\; \forall hA \in \operatorname{\mathit{Matrix}}.\operatorname{\mathit{IsHermitian}}\left(A\right),\; \operatorname{\mathit{aqLeastEigenvalue}}\left(\mathit{hA}\right) = \operatorname{\mathit{sInf}}\left(\operatorname{\mathit{Set}}.\operatorname{\mathit{range}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{IsHermitian}}.\operatorname{\mathit{eigenvalues}}\left(\mathit{hA}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.aqLeastEigenvalue` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

For a Hermitian matrix A on a finite index type, take the infimum of the range of its real eigenvalue function. This definition also applies to an empty index type. On a nonempty finite type the infimum is an attained least eigenvalue.

**Definition 1.4 (The supremum of the eigenvalues).**

$$\forall I \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(I\right)], [\operatorname{\mathit{DecidableEq}}\left(I\right)], \forall A \in \operatorname{\mathit{Matrix}}\left(I, I, \mathit{Complex}\right),\; \forall hA \in \operatorname{\mathit{Matrix}}.\operatorname{\mathit{IsHermitian}}\left(A\right),\; \operatorname{\mathit{aqGreatestEigenvalue}}\left(\mathit{hA}\right) = \operatorname{\mathit{sSup}}\left(\operatorname{\mathit{Set}}.\operatorname{\mathit{range}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{IsHermitian}}.\operatorname{\mathit{eigenvalues}}\left(\mathit{hA}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.aqGreatestEigenvalue` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

The corresponding supremum defines the greatest eigenvalue. On a nonempty finite index type it is attained. Neither extreme requires an ordering of the eigenvector indices.

**Definition 1.5 (The advantage-quantum inequalities).**

$$\forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall E \in \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; \forall hE \in \operatorname{\mathit{IsDovm}}\left(E\right),\; (\operatorname{\mathit{IsAdvantageQuantum}}\left(E, \mathit{hE}\right)) \Leftrightarrow (\exists i \in \operatorname{\mathit{Fin}}\left(2\right),\; (\operatorname{\mathit{aqLeastEigenvalue}}\left(\operatorname{\mathit{And}}.\operatorname{\mathit{left}}\left(\mathit{hE}\left(i\right)\right)\right) < 0) \land ((1 + \operatorname{\mathit{aqLeastEigenvalue}}\left(\operatorname{\mathit{And}}.\operatorname{\mathit{left}}\left(\mathit{hE}\left(i\right)\right)\right) < \operatorname{\mathit{aqGreatestEigenvalue}}\left(\operatorname{\mathit{And}}.\operatorname{\mathit{left}}\left(\mathit{hE}\left(i\right)\right)\right)) \land (\operatorname{\mathit{aqGreatestEigenvalue}}\left(\operatorname{\mathit{And}}.\operatorname{\mathit{left}}\left(\mathit{hE}\left(i\right)\right)\right) < 1)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.IsAdvantageQuantum` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

One of the two effects has a negative least eigenvalue, while its greatest eigenvalue is strictly between one plus the least eigenvalue and one. These are exactly Arai's AQ inequalities; hE supplies the Hermitian proof for each effect.

**Definition 1.6 (The density matrices with nonnegative probabilities).**

$$\forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall E \in \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; \forall rho \in \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; (\operatorname{\mathit{InMeasurementDomain}}\left(E, \mathit{rho}\right)) \Leftrightarrow ((\operatorname{\mathit{Matrix}}.\operatorname{\mathit{PosSemidef}}\left(\mathit{rho}\right)) \land ((\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left(\mathit{rho}\right) = 1) \land (\forall i \in \operatorname{\mathit{Fin}}\left(2\right),\; 0 \le \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left((\mathit{rho}) \cdot (\operatorname{\mathit{binaryEffect}}\left(E, i\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.InMeasurementDomain` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

A domain state is positive semidefinite, has complex trace equal to one, and gives a nonnegative real trace pairing with each effect. Thus both outcome probabilities lie between zero and one. This is the trace-one part of the thesis's domain, which also allows unnormalized positive semidefinite matrices.

**Definition 1.7 (The tensor power in coordinates).**

$$\forall I \in \mathit{Type},\; \forall n \in \mathit{Nat},\; \forall rho \in \operatorname{\mathit{Matrix}}\left(I, I, \mathit{Complex}\right),\; \forall x \in \operatorname{\mathit{Fin}}\left(n\right) \to I,\; \forall y \in \operatorname{\mathit{Fin}}\left(n\right) \to I,\; \operatorname{\mathit{copyState}}\left(n, \mathit{rho}\right)\left(x, y\right) = \prod_{(k:\operatorname{\mathit{Fin}}\left(n\right))}(\mathit{rho}\left(x\left(k\right), y\left(k\right)\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.copyState` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

A basis index for n copies is a function from Fin n to the original basis. The matrix entry of the tensor power is the product of the n corresponding entries of rho. For zero copies the empty product gives the one-dimensional identity.

**Definition 1.8 (One POVM must reproduce every domain state).**

$$\forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall E \in \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; \forall n \in \mathit{Nat},\; (\operatorname{\mathit{QuantumSimulable}}\left(E, n\right)) \Leftrightarrow (\exists N \in \operatorname{\mathit{Fin}}\left(2\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; (\operatorname{\mathit{IsPOVM}}\left(N\right)) \land (\forall rho \in \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; (\operatorname{\mathit{InMeasurementDomain}}\left(E, \mathit{rho}\right)) \Rightarrow (\forall i \in \operatorname{\mathit{Fin}}\left(2\right),\; \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left((\operatorname{\mathit{copyState}}\left(n, \mathit{rho}\right)) \cdot (N\left(i\right))\right)\right) = \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left((\mathit{rho}) \cdot (\operatorname{\mathit{binaryEffect}}\left(E, i\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.QuantumSimulable` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

For the specified natural number n, there must be a binary POVM N on the n-copy space whose real trace probabilities agree with those of the original effects for every trace-one domain state and both outcomes. IsPOVM means that each N(i) is positive semidefinite and their sum is the identity. The same N must work for every state.

**Definition 1.9 (Finite-copy non-simulability of every AQ DOVM).**

$$(\mathit{claim}) \Leftrightarrow (\forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; (1 \le \mathit{dA}) \Rightarrow ((1 \le \mathit{dB}) \Rightarrow (\forall E \in \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right),\; \forall hE \in \operatorname{\mathit{IsDovm}}\left(E\right),\; (\operatorname{\mathit{IsAdvantageQuantum}}\left(E, \mathit{hE}\right)) \Rightarrow (\forall n \in \mathit{Nat},\; \neg (\operatorname{\mathit{QuantumSimulable}}\left(E, n\right))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.claim` (`✓ std3`).

*Citation.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

For every pair of positive dimensions and every binary DOVM, the AQ condition rules out quantum n-simulability for every natural n, including zero. This states the negative answer to the AQ simulability question in Section 5.2 of the thesis. Requiring agreement only on density matrices already suffices for the obstruction.

**Theorem 1.10 (A zero probability at a full-rank state forces a contradiction).**

$$\mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.result` (`✓ std3`). ∎

*Resolves.* `Problems/arai-2023-advantage-quantum-non-simulability` (proved) by `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"arai-2023-advantage-quantum-non-simulability","declaration_gid":"D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hayato Arai (2023). *The Diversity of Entanglement Structures with Self-Duality and Non-Orthogonal State Discrimination in General Probabilistic Theories*. URL: <https://arxiv.org/abs/2302.12361v1>.

*Commentary.*

Choose the AQ effect A. Every product-basis diagonal entry is nonnegative by block positivity, so Tr A ≥ 0. Write d = dA dB, and let lambda_1 and lambda_d be its least and greatest eigenvalues. Since lambda_1 < 0 and the sum of all eigenvalues is nonnegative, lambda_d > 0; the AQ hypothesis gives lambda_d < 1. For a unit top eigenvector w, the state rho_+ = |w⟩⟨w| has selected probability lambda_d in (0,1). Its complementary probability is 1 − lambda_d, so it belongs to the measurement domain.

Let v be a unit bottom eigenvector, put a = Tr A / d ≥ 0, and set p = −lambda_1 / (a − lambda_1). Then 0 < p ≤ 1, and rho_0 = (p/d) I + (1 − p)|v⟩⟨v| is a trace-one positive definite matrix. Its selected probability is p a + (1 − p) lambda_1 = 0, and the complementary probability is one. Hence rho_0 is a full-rank domain state.

If a POVM N simulated the measurement on n copies, its selected effect would satisfy Re Tr(rho_0 tensor-power n · N(i)) = 0. The tensor power of rho_0 is positive definite for every n, including zero. A positive semidefinite effect with zero trace pairing against a positive definite matrix is zero, so N(i) = 0. Its probability on rho_+ tensor-power n would then be zero, contradicting the required value lambda_d > 0. This proves claim. The argument uses the negative least eigenvalue and the greatest eigenvalue being below one; it does not need the additional AQ inequality 1 + lambda_1 < lambda_d.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.InMeasurementDomain`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.IsAdvantageQuantum`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.IsDovm`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.QuantumSimulable`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.aqGreatestEigenvalue`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.aqLeastEigenvalue`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.binaryEffect`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.copyState`
- Truth anchor: `D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.result`
- Dependency: [D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation](../Entanglement/EnergyRestrictedUnitaryEncodingRefutation.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Resource/CompositeCones](../../Resource/CompositeCones.md)
