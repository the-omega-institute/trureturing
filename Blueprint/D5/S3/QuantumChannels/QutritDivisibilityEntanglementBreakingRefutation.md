# Divisibility does not force entanglement breaking for qutrits

## Abstract

A divisible qutrit channel lies outside the closure of P-divisible dynamical endpoints and is not entanglement breaking.

**Definition 1.1 (Unitary conjugation).**

$$\forall \left(t: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsUnitaryChannel}\left(t\right)\right) \Leftrightarrow \left(\exists \left(U: \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\forall \left(X: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(t\left(X\right) = \left(\operatorname{Subtype.val}\left(U\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right) \cdot X \cdot \operatorname{Matrix.conjTranspose}\left(\left(\operatorname{Subtype.val}\left(U\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsUnitaryChannel` (`✓ std3`).

*Citation.* David Davalos; Mario Ziman; Carlos Pineda (2019). *Divisibility of qubit channels and dynamical maps*. DOI: [10.22331/q-2019-05-20-144](https://doi.org/10.22331/q-2019-05-20-144). URL: <https://arxiv.org/abs/1812.11437v4>.

*Commentary.*

A complex-linear map on three by three matrices is unitary when one unitary matrix U conjugates every input X. Subtype.val explicitly includes U in the ambient complex matrix space. This is the unitary-channel definition in Section 2.1, TeX lines 252–254.

**Definition 1.2 (Two nonunitary channel factors).**

$$\forall \left(t: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsDivisible}\left(t\right)\right) \Leftrightarrow \left(\exists \left(t1: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\exists \left(t2: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsCPTP}\left(t1\right)\right) \land \left(\left(\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsCPTP}\left(t2\right)\right) \land \left(\left(t = \operatorname{LinearMap.comp}\left(t1, t2\right)\right) \land \left(\left(\neg \left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsUnitaryChannel}\left(t1\right)\right)\right) \land \left(\neg \left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsUnitaryChannel}\left(t2\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsDivisible` (`✓ std3`).

*Citation.* David Davalos; Mario Ziman; Carlos Pineda (2019). *Divisibility of qubit channels and dynamical maps*. DOI: [10.22331/q-2019-05-20-144](https://doi.org/10.22331/q-2019-05-20-144). URL: <https://arxiv.org/abs/1812.11437v4>.

*Commentary.*

The map t factors as t1 after t2, where both factors are completely positive and trace preserving and neither is a unitary conjugation. Section 2.1, TeX lines 256–261, defines indivisibility by the absence of such a factorization. The displayed predicate requires two nonunitary factors; it does not include the source's separate convention about unitary channels in lines 262–263.

**Definition 1.3 (Positive trace-preserving maps).**

$$\forall \left(v: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsPositiveTP}\left(v\right)\right) \Leftrightarrow \left(\left(\forall \left(X: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(X\right)\right) \to \left(\operatorname{Matrix.PosSemidef}\left(v\left(X\right)\right)\right)\right)\right) \land \left(\operatorname{MatrixMap.IsTracePreserving}\left(v\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsPositiveTP` (`✓ std3`).

*Citation.* David Davalos; Mario Ziman; Carlos Pineda (2019). *Divisibility of qubit channels and dynamical maps*. DOI: [10.22331/q-2019-05-20-144](https://doi.org/10.22331/q-2019-05-20-144). URL: <https://arxiv.org/abs/1812.11437v4>.

*Commentary.*

A positive trace-preserving map sends every positive semidefinite matrix to a positive semidefinite matrix and preserves the complex trace of every input. Positivity and trace preservation are the conditions in Section 2.1, TeX lines 235–240; complete positivity is not required here.

**Definition 1.4 (P-divisible dynamics).**

$$\forall \left(e: \left(\mathbb{R}\right) \to \left(\operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsPDivisibleMap}\left(e\right)\right) \Leftrightarrow \left(\left(e\left(\left(0: \mathbb{R}\right)\right) = \left(\operatorname{LinearMap.id}: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)\right) \land \left(\left(\forall \left(t: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) \le t\right) \to \left(\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsCPTP}\left(e\left(t\right)\right)\right)\right)\right) \land \left(\left(\operatorname{ContinuousOn}\left(\lambda \left(t: \mathbb{R}\right) \mapsto \left(\operatorname{LinearMap.toMatrix}\left(\operatorname{Matrix.stdBasis}\left(\mathbb{C}, \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Matrix.stdBasis}\left(\mathbb{C}, \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), e\left(t\right)\right)\right), \operatorname{Set.Ici}\left(\left(0: \mathbb{R}\right)\right)\right)\right) \land \left(\forall \left(t: \mathbb{R}\right), \left(\forall \left(s: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) \le t\right) \to \left(\left(t < s\right) \to \left(\exists \left(v: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsPositiveTP}\left(v\right)\right) \land \left(\left(e\left(s\right) = \operatorname{LinearMap.comp}\left(v, e\left(t\right)\right)\right) \lor \left(e\left(s\right) = \operatorname{LinearMap.comp}\left(e\left(t\right), v\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsPDivisibleMap` (`✓ std3`).

*Citation.* David Davalos; Mario Ziman; Carlos Pineda (2019). *Divisibility of qubit channels and dynamical maps*. DOI: [10.22331/q-2019-05-20-144](https://doi.org/10.22331/q-2019-05-20-144). URL: <https://arxiv.org/abs/1812.11437v4>.

*Commentary.*

The family e starts at the identity, is a channel at every nonnegative real time, and is continuous on the nonnegative half-line in matrix-unit coordinates. For every pair of times with 0 ≤ t < s, there is a positive trace-preserving map v with e(s) = v ∘ e(t) or e(s) = e(t) ∘ v. The coordinate matrix is LinearMap.toMatrix in the standard matrix basis on both sides. Section 2.2, TeX lines 281–295, gives the dynamical-map and P-divisibility notions. The source prints the propagator as the inverse of e(t) composed with e(s); allowing either composition order includes the source's P-divisible maps under either reading. The composition condition also applies at singular times, without requiring an inverse.

**Definition 1.5 (Limits of dynamical endpoints).**

$$\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.pDivisibleSet} = \{T: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right) \mid \operatorname{LinearMap.toMatrix}\left(\operatorname{Matrix.stdBasis}\left(\mathbb{C}, \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Matrix.stdBasis}\left(\mathbb{C}, \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), T\right) \in \operatorname{closure}\left(\{M: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)\right), \mathbb{C}\right) \mid \exists \left(E: \left(\mathbb{R}\right) \to \left(\operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsPDivisibleMap}\left(E\right)\right) \land \left(\exists \left(t: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) \le t\right) \land \left(M = \operatorname{LinearMap.toMatrix}\left(\operatorname{Matrix.stdBasis}\left(\mathbb{C}, \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Matrix.stdBasis}\left(\mathbb{C}, \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), E\left(t\right)\right)\right)\right)\right)\right)\}\right)\}$$

*Formalization.* `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.pDivisibleSet` (`✓ std3`).

*Citation.* David Davalos; Mario Ziman; Carlos Pineda (2019). *Divisibility of qubit channels and dynamical maps*. DOI: [10.22331/q-2019-05-20-144](https://doi.org/10.22331/q-2019-05-20-144). URL: <https://arxiv.org/abs/1812.11437v4>.

*Commentary.*

A map T belongs to this set when its matrix-unit coordinate matrix lies in the topological closure of the coordinate matrices of all nonnegative-time endpoints of P-divisible families E. Thus finite endpoints and their limits are included. Section 2.2, TeX lines 336–339, expresses membership through approximation to a dynamical endpoint, including infinite time. The displayed set uses the preceding composition condition even when an endpoint is singular.

**Definition 1.6 (Destruction of bipartite entanglement).**

$$\forall \left(t: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsEntanglementBreaking}\left(t\right)\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(rho: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(rho\right)\right) \to \left(\left(\operatorname{Matrix.trace}\left(rho\right) = \left(1: \mathbb{C}\right)\right) \to \left(\operatorname{D5.S3.Resource.CompositeCones.separableCone}\left(\operatorname{MatrixMap.kron}\left(\left(\operatorname{LinearMap.id}: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right), t, rho\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsEntanglementBreaking` (`✓ std3`).

*Citation.* David Davalos; Mario Ziman; Carlos Pineda (2019). *Divisibility of qubit channels and dynamical maps*. DOI: [10.22331/q-2019-05-20-144](https://doi.org/10.22331/q-2019-05-20-144). URL: <https://arxiv.org/abs/1812.11437v4>.

*Commentary.*

For every natural ancillary dimension n and every positive semidefinite matrix rho of complex trace one on the product of Fin n and Fin 3, the identity amplification of t sends rho into the separable cone. The identity acts on the ancillary factor and t on the qutrit factor. The source's Theorem 6, TeX lines 1237–1241, uses entanglement breaking in its qubit conclusion; its proof starts from the associated bipartite state in lines 1244–1249.

**Definition 1.7 (The qutrit assertion).**

$$\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.claim}\right) \Leftrightarrow \left(\forall \left(t: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsCPTP}\left(t\right)\right) \to \left(\left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsDivisible}\left(t\right)\right) \to \left(\left(\neg \left(t \in \operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.pDivisibleSet}\right)\right) \to \left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.IsEntanglementBreaking}\left(t\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Davalos; Mario Ziman; Carlos Pineda (2019). *Divisibility of qubit channels and dynamical maps*. DOI: [10.22331/q-2019-05-20-144](https://doi.org/10.22331/q-2019-05-20-144). URL: <https://arxiv.org/abs/1812.11437v4>.

*Commentary.*

Every completely positive trace-preserving qutrit map with two nonunitary channel factors and outside the displayed endpoint closure is asserted to be entanglement breaking. This is a precise qutrit reading of the higher-dimensional question in the abstract, TeX lines 162–164. The source's Theorem 6, lines 1237–1241, concerns qubits.

**Theorem 1.8 (A divisible qutrit counterexample).**

$$\neg \left(\operatorname{D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/davalos-ziman-pineda-2019-qutrit-divisibility-entanglement-breaking` (refuted) by `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"davalos-ziman-pineda-2019-qutrit-divisibility-entanglement-breaking","declaration_gid":"D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* David Davalos; Mario Ziman; Carlos Pineda (2019). *Divisibility of qubit channels and dynamical maps*. DOI: [10.22331/q-2019-05-20-144](https://doi.org/10.22331/q-2019-05-20-144). URL: <https://arxiv.org/abs/1812.11437v4>.

*Commentary.*

Write Eᵢⱼ for the matrix units and I for the three by three identity. Use the three matrices (E₀₁ − E₁₀)/√2, (E₀₂ − E₂₀)/√2 and (E₁₂ − E₂₁)/√2 as Kraus operators for W. Use I/√2 together with all nine Eᵢⱼ/√6 as Kraus operators for D. Expanding their Kraus sums gives W(X) = (Tr(X)I − Xᵀ)/2 and D(X) = X/2 + Tr(X)I/6. Their composition is T(X) = 5Tr(X)I/12 − Xᵀ/4.

For each of these two Kraus families, the sum of K†K is I. Hence W and D are completely positive and trace preserving. The products of a Kraus operator of D with one of W form a Kraus family for T, proving its complete positivity; successive trace preservation proves that T preserves trace. A Kraus representation of an arbitrary completely positive map also shows that it commutes with conjugate transpose.

Unitary conjugation preserves the trace of the square of E₀₀, which equals one. But W(E₀₀) has diagonal (0,1/2,1/2), and D(E₀₀) has diagonal (2/3,1/6,1/6); in each case the trace of the square is 1/2. Thus neither W nor D is a unitary channel, and T = D ∘ W is divisible.

For a Hermiticity-preserving map, conjugating its matrix-unit coordinate matrix exchanges the two indices within each row and each column. This simultaneous reindexing preserves the determinant. Its determinant therefore equals its complex conjugate and is real.

For a P-divisible family E, the determinant is continuous on nonnegative times and starts at one. If its real part were negative at a time u, the intermediate value theorem would give an earlier nonnegative time z with zero real part. Reality makes the determinant itself zero at z. Either factorization, E(u) = v ∘ E(z) or E(u) = E(z) ∘ v, gives det(E(u)) = det(v) det(E(z)), since the scalar determinants commute. This product has a zero factor, a contradiction. Every endpoint consequently has real nonnegative determinant. The set of coordinate matrices with zero imaginary part of the determinant and nonnegative real part is closed, so the same constraint holds throughout the endpoint closure.

To calculate the determinant of T, reorder the nine matrix units as three diagonal units followed by the pairs (E₀₁,E₁₀), (E₀₂,E₂₀) and (E₁₂,E₂₁). The diagonal block has diagonal entries 1/6 and off-diagonal entries 5/12, with determinant 1/16. Each of the three remaining blocks is the two by two matrix with zero diagonal and both off-diagonal entries −1/4. Their combined determinant is −(1/4)⁶, and the full determinant is −(1/4)⁸. It is negative, so T is outside the endpoint closure.

Let a = (e₀ ⊗ e₀ + e₁ ⊗ e₁ + e₂ ⊗ e₂)/√3 and let Ω = aa†. This maximally entangled density matrix is positive semidefinite and has trace one. Direct expansion of the matrix entries gives real quadratic value −1/9 on a for the partial transpose of (id ⊗ T)(Ω). If T were entanglement breaking, that output would lie in the separable cone. Every member of this cone has positive semidefinite partial transpose, whose real quadratic values are nonnegative. The value −1/9 is a contradiction.

Applying the asserted implication to the channel T, its nonunitary factorization and its exclusion from the endpoint closure would make T entanglement breaking. The preceding negative quadratic value disproves that conclusion, and therefore negates the assertion.

## References

- Truth anchor: `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsDivisible`
- Truth anchor: `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsEntanglementBreaking`
- Truth anchor: `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsPDivisibleMap`
- Truth anchor: `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsPositiveTP`
- Truth anchor: `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.IsUnitaryChannel`
- Truth anchor: `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.pDivisibleSet`
- Truth anchor: `D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.result`
- Dependency: [D5/S3/Observer/Existence/EmpiricalReflexiveSeparation](../Observer/Existence/EmpiricalReflexiveSeparation.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity](../Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Quantum/Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding](../Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound](../Quantum/QuantumChannels/TracePreservingEigenvalueBound.md)
- Dependency: [D5/S3/QuantumBounds/PeritoTsirelson](../QuantumBounds/PeritoTsirelson.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](CoPRelativeQuantumnessRefutation.md)
