# The steering-ellipsoid CHSH bound

## Abstract

Every two-qubit density matrix with steering-ellipsoid centre of length c has CHSH nonlocality at most max(2 sqrt(2(1 - c)), 2). At every c in [0, 1] this is the supremum over states with that centre length, proving Conjecture 1 of Milne, Jennings, Jevtic and Rudolph.

**Definition 1.1 (The CHSH operator).**

$$\forall a \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall aPrime \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall b \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall bPrime \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{bell}\left(a, aPrime, b, bPrime\right) = \operatorname{Matrix}.\operatorname{kronecker}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{spin}\left(a\right), \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{spin}\left(b + bPrime\right)\right) + \operatorname{Matrix}.\operatorname{kronecker}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{spin}\left(aPrime\right), \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{spin}\left(b - bPrime\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bell` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Section II defines B = alpha dot sigma tensor (beta + beta prime) dot sigma + alpha prime dot sigma tensor (beta - beta prime) dot sigma. The displayed variables aPrime and bPrime denote the primed directions. Matrix.kronecker is Mathlib's Kronecker product, the alias of Matrix.kroneckerMap with multiplication of complex entries. The four vectors here are arbitrary; unit lengths are required in the value set.

**Definition 1.2 (CHSH expectation values).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \operatorname{chshValues}\left(rho\right) = \{r : \mathbb{R} \mid \exists a \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \exists aPrime \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \exists b \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \exists bPrime \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(a\right) = 1) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(aPrime\right) = 1) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(b\right) = 1) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(bPrime\right) = 1) \land (r = \left\lVert \operatorname{Matrix}.\operatorname{trace}\left(rho \cdot \operatorname{bell}\left(a, aPrime, b, bPrime\right)\right) \right\rVert))))\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.chshValues` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Section II maximizes the absolute value of tr(rho B) over four measurement directions. The set contains precisely these complex norms for unit directions, with Euclidean length D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.vlen. Its definition permits any two-qubit operator rho.

**Definition 1.3 (CHSH nonlocality).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \operatorname{chsh}\left(rho\right) = \operatorname{sSup}\left(\operatorname{chshValues}\left(rho\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.chsh` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Section II: the maximal CHSH violation is beta(rho) = max_B |tr(rho B)|, where the maximization is over all four directions. The definition uses sSup of the real value set. This set is nonempty and bounded above for every two-qubit operator, and the proof uses no attainment assumption.

**Definition 1.4 (The centre bound).**

$$\forall t \in \mathbb{R},\; \operatorname{bound}\left(t\right) = \operatorname{max}\left(2 \cdot \operatorname{Real}.\operatorname{sqrt}\left(2 \cdot \left(1 - t\right)\right), 2\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bound` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Section V, Conjecture 1, gives the maximum of 2 sqrt(2(1 - t)) and 2. The function is defined for every real t with Mathlib's Real.sqrt; the tightness statement restricts t to [0, 1].

**Definition 1.5 (Conjecture 1).**

$$(claim) \Leftrightarrow ((\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \Rightarrow (\operatorname{chsh}\left(rho\right) \le \operatorname{bound}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{centre}\left(rho\right)\right)\right)))) \land (\forall t \in \mathbb{R},\; (0 \le t) \Rightarrow ((t \le 1) \Rightarrow (\forall epsilon \in \mathbb{R},\; (0 < epsilon) \Rightarrow (\exists rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{centre}\left(rho\right)\right) = t) \land (\operatorname{bound}\left(t\right) - epsilon < \operatorname{chsh}\left(rho\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.claim` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Section V, Conjecture 1: Let rho be a general two-qubit state with its steering ellipsoid centred at c. The CHSH nonlocality is tightly bounded as beta(rho) <= max[2 sqrt(2(1 - c)), 2]. Here c is the Euclidean length of D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.centre. The first clause gives the inequality for every positive semidefinite matrix of trace one. The second expresses tightness as a supremum: for each t in [0, 1] and each epsilon > 0 there is a positive semidefinite trace-one matrix with centre length exactly t and CHSH value strictly greater than bound(t) - epsilon.

**Theorem 1.6 (Agreement of Pauli indexing).**

$$\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{sigma}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.sigma_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For every index i in Fin 3, the Pauli operator sigma at the successor index in Fin 4 equals pauli i.

**Theorem 1.7 (Squared Euclidean length).**

$$\forall u \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(u\right))^{2} = \operatorname{dotProduct}\left(u, u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.vlen_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For every real three-vector, the square of its Euclidean length equals its dot product with itself.

**Theorem 1.8 (Unit normalization).**

$$\forall u \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; (u \ne 0) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left((\operatorname{inv}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(u\right)\right)) \cdot (u)\right) = 1) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(u\right)) \cdot ((\operatorname{inv}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(u\right)\right)) \cdot (u)) = u))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.normalized_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Every nonzero real three-vector becomes unit length after division by its Euclidean length, and rescaling the normalized vector recovers the original vector.

**Theorem 1.9 (Pauli expectations equal the correlations).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{IsHermitian}\left(rho\right)) \Rightarrow (\forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{Matrix}.\operatorname{trace}\left(rho \cdot \operatorname{Matrix}.\operatorname{kronecker}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}\left(i\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}\left(j\right)\right)\right) = \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{corr}\left(rho, i, j\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.trace_pauli_kronecker_eq_corr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For every Hermitian complex two-qubit operator rho and every pair of Pauli indices i and j in Fin 3, the trace of rho times the corresponding Kronecker product equals its real correlation entry embedded in the complex numbers. Hermiticity makes this trace real.

**Theorem 1.10 (The centre bound holds).**

$$(\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \Rightarrow (\operatorname{chsh}\left(rho\right) \le \operatorname{bound}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{centre}\left(rho\right)\right)\right)))) \land (\forall t \in \mathbb{R},\; (0 \le t) \Rightarrow ((t \le 1) \Rightarrow (\forall epsilon \in \mathbb{R},\; (0 < epsilon) \Rightarrow (\exists rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{centre}\left(rho\right)\right) = t) \land (\operatorname{bound}\left(t\right) - epsilon < \operatorname{chsh}\left(rho\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.result` (`✓ std3`). ∎

*Resolves.* `Problems/milne-jennings-jevtic-rudolph-2014-chsh-centre-bound` (proved) by `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"milne-jennings-jevtic-rudolph-2014-chsh-centre-bound","declaration_gid":"D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Write T for the correlation matrix, b for Bob's Bloch vector and Delta(X) = Re tr(X squared) - Re tr((tr_B X) squared). For orthonormal u, v and their normal n, conjugate the full transpose of rho by sigma_y tensor ((n dot sigma) sigma_y). The sum |Tu| squared + |Tv| squared plus (b dot n) squared plus twice the real trace of rho times this flipped state equals 1 + 2 Delta(rho). The flipped state is positive semidefinite, so the plane sum is at most 1 + 2 Delta(rho). The sum and difference of Bob's two unit measurement directions are orthogonal; decomposing them and applying Cauchy-Schwarz reduces each CHSH expectation to twice the square root of such a plane sum.

The two-by-two determinant polarization identity gives Delta((I tensor F)X(I tensor F) adjoint) = |det F| squared Delta(X). For a state sigma with Bob marginal I/2 and Alice Bloch length c, the canonical bound sigma <= (1 - c/2)I bounds its eigenvalues and yields Delta(sigma) <= 1/2 - c. An explicit invertible filter makes Bob's marginal maximally mixed when |b| < 1, giving Delta(rho) <= (1 - |b| squared)(1/2 - c). When |b| = 1, Bob's marginal is a projector; filtering by this projector leaves rho fixed and has determinant zero, so Delta(rho) = 0. Thus every plane sum is at most max(2(1 - c), 1), giving the stated CHSH bound.

For tightness, let R(t, s) = |v><v|/2 + t(1 - s)|01><01|/2, where v = sqrt(1 + s)|00> + sqrt((1 - t)(1 - s))|11>. For 0 <= t <= 1 and 0 <= s < 1 this is a density matrix with centre (0, 0, t). At s = 0, CHSH settings in the xy plane attain 2 sqrt(2(1 - t)), proving tightness when t <= 1/2. For 1/2 < t < 1, the four z directions give 2(1 - t + ts); choosing s = 2/(2 + epsilon) makes this strictly greater than 2 - epsilon. At t = s = 1 the product state |00><00| has centre length one and CHSH value two.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bell`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.chsh`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.chshValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.normalized_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.sigma_succ`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.trace_pauli_kronecker_eq_corr`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.vlen_sq`
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction](SteeringEllipsoidFullyEntangledFraction.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitCostInfimum](../Information/ActualPureQubitCostInfimum.md)
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../Information/ActualQubitChordObstruction.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
- Dependency: [D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness](../../QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.md)
