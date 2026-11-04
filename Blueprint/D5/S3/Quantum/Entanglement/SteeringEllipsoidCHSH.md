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

**Definition 1.10 (The difference of global and marginal purities).**

$$\forall (X: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{delta}\left(X\right) = \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(X \cdot X\right)\right) - \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(X\right) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(X\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Delta(X) is the real trace of X squared minus the real trace of its Alice marginal squared. The partial trace is over Bob's factor. This real-valued definition applies to every complex two-qubit matrix X.

**Definition 1.11 (A direction-dependent spin flip).**

$$\forall (n: \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\operatorname{flipMatrix}\left(n\right) = \operatorname{Matrix}.\operatorname{kronecker}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}\left((1: \operatorname{Fin}\left(3\right))\right), \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{spin}\left(n\right) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}\left((1: \operatorname{Fin}\left(3\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.flipMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For a real three-vector n, the conjugating matrix is the tensor product of the second Pauli matrix with spin(n) times that Pauli matrix. No unit-length condition is imposed in this definition.

**Definition 1.12 (The flipped matrix).**

$$\forall (X: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (n: \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\operatorname{flipped}\left(X, n\right) = \operatorname{flipMatrix}\left(n\right) \cdot \operatorname{Matrix}.\operatorname{transpose}\left(X\right) \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{flipMatrix}\left(n\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.flipped` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Transpose X in the product basis and multiply it on the left by flipMatrix(n) and on the right by its adjoint. This construction preserves positive semidefiniteness because transposition and conjugation preserve it.

**Lemma 1.13 (The directional flip identity).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow (\forall (n: \operatorname{Fin}\left(3\right) \to \mathbb{R}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(n\right) = 1) \Rightarrow (2 \cdot \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(\rho \cdot \operatorname{flipped}\left(\rho, n\right)\right)\right) + \sum_{(i: \operatorname{Fin}\left(3\right))} (\sum_{(j: \operatorname{Fin}\left(3\right))} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{corr}\left(\rho, i, j\right))^{2})) - (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{corr}\left(\rho\right), n\right)\right))^{2} + (\operatorname{dotProduct}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochB}\left(\rho\right), n\right))^{2} = 1 + 2 \cdot \operatorname{delta}\left(\rho\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.flip_purity_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For a Hermitian trace-one matrix and a unit direction n, the real trace pairing with the flipped matrix, the squared Frobenius sum of the correlations, the squared length of Tn and Bob's squared component along n satisfy this identity. Expanding the Pauli matrices gives its homogeneous form; trace one and the unit length of n give the displayed normalization.

**Lemma 1.14 (A unit direction bounds a component).**

$$\forall (a: \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\forall (x: \operatorname{Fin}\left(3\right) \to \mathbb{R}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(a\right) = 1) \Rightarrow (\left|\operatorname{dotProduct}\left(a, x\right)\right| \le \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(x\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.unit_dot_le` (`✓ std3`). ∎

*Citation.* Sheldon Axler (2024). *Linear Algebra Done Right, fourth edition*. URL: <https://linear.axler.net/>.

*Commentary.*

The absolute component of a real three-vector x along a unit vector a is at most the Euclidean length of x. This is the real inner-product Cauchy-Schwarz inequality.

**Lemma 1.15 (Bob's Bloch vector lies in the unit ball).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochB}\left(\rho\right)\right) \le 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bob_radius_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

A positive semidefinite trace-one two-qubit matrix has a positive semidefinite trace-one Bob marginal. The norm of that marginal's Bloch vector is at most its trace, hence at most one.

**Lemma 1.16 (Purity difference bounded by the ellipsoid centre).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow (\operatorname{delta}\left(\rho\right) \le \left(1 - (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochB}\left(\rho\right)\right))^{2}\right) \cdot \left(\frac{1}{2} - \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{centre}\left(\rho\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.delta_le_centre` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

The purity difference is at most (1 - |b| squared)(1/2 - |centre(rho)|). When |b| < 1 an invertible filter makes Bob's marginal maximally mixed; determinant scaling of Delta and the canonical state's eigenvalue bound give the inequality. When |b| = 1, support on Bob's pure marginal makes Delta zero, giving the boundary case.

**Lemma 1.17 (The real correlation form of a CHSH expectation).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(\rho\right)) \Rightarrow (\forall (a: \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\forall (a': \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\forall (b: \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\forall (b': \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\operatorname{Matrix}.\operatorname{trace}\left(\rho \cdot \operatorname{bell}\left(a, a', b, b'\right)\right) = \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{dotProduct}\left(a, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{corr}\left(\rho\right), b + b'\right)\right) + \operatorname{dotProduct}\left(a', \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{corr}\left(\rho\right), b - b'\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bell_trace_real_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For a Hermitian two-qubit matrix, the CHSH expectation equals the sum of the two real correlation dot products embedded in the complex numbers. Expanding the two Pauli observables and using real Pauli expectations gives the equality for arbitrary directions.

**Definition 1.18 (The vector supported on the two equal-bit basis states).**

$$\forall (t: \mathbb{R}), (\forall (s: \mathbb{R}), (\operatorname{tightVector}\left(t, s\right) = \lambda (k: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (![![\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(1 + s\right)\right), (0: \mathbb{C})], ![(0: \mathbb{C}), \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(\left(1 - t\right) \cdot \left(1 - s\right)\right)\right)]]\left(\operatorname{Prod}.\operatorname{fst}\left(k\right), \operatorname{Prod}.\operatorname{snd}\left(k\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tightVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

The vector has amplitudes sqrt(1+s) at (0,0), sqrt((1-t)(1-s)) at (1,1), and zero at the other two product indices. The real amplitudes are explicitly embedded in the complex numbers. The definition permits arbitrary real t and s.

**Definition 1.19 (A two-term family of matrices).**

$$\forall (t: \mathbb{R}), (\forall (s: \mathbb{R}), (\operatorname{tightState}\left(t, s\right) = \operatorname{HSMul}.\operatorname{hSMul}\left((\frac{1}{2}: \mathbb{C}), \operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{tightVector}\left(t, s\right), \operatorname{Star}.\operatorname{star}\left(\operatorname{tightVector}\left(t, s\right)\right)\right)\right) + \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{ofReal}\left(\frac{t \cdot \left(1 - s\right)}{2}\right), \operatorname{Matrix}.\operatorname{vecMulVec}\left(\lambda (k: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{ev}\left(k\right)\right)), \operatorname{Star}.\operatorname{star}\left(\lambda (k: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{ev}\left(k\right)\right))\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tightState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Take half the outer product of tightVector with its adjoint and add t(1-s)/2 times the projector onto the product basis vector (0,1). The latter vector is the real vector ev embedded coordinatewise in the complex numbers. The formula defines the family for all real parameters.

**Lemma 1.20 (Positivity of the two-term family).**

$$\forall (t: \mathbb{R}), (\forall (s: \mathbb{R}), ((0 \le t) \Rightarrow ((s \le 1) \Rightarrow (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{tightState}\left(t, s\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tight_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

If t is nonnegative and s is at most one, both coefficients in tightState are nonnegative. Each outer product is positive semidefinite, so their sum is positive semidefinite.

**Lemma 1.21 (Trace, Bloch vectors and correlations of the family).**

$$\forall (t: \mathbb{R}), (\forall (s: \mathbb{R}), ((t \le 1) \Rightarrow ((0 \le s) \Rightarrow ((s \le 1) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{tightState}\left(t, s\right)\right) = (1: \mathbb{C})) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochA}\left(\operatorname{tightState}\left(t, s\right)\right) = ![0, 0, t + \left(1 - t\right) \cdot s]) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochB}\left(\operatorname{tightState}\left(t, s\right)\right) = ![0, 0, s]) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{corr}\left(\operatorname{tightState}\left(t, s\right)\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(![\operatorname{Real}.\operatorname{sqrt}\left(1 + s\right) \cdot \operatorname{Real}.\operatorname{sqrt}\left(\left(1 - t\right) \cdot \left(1 - s\right)\right), -(\operatorname{Real}.\operatorname{sqrt}\left(1 + s\right) \cdot \operatorname{Real}.\operatorname{sqrt}\left(\left(1 - t\right) \cdot \left(1 - s\right)\right)), 1 - t + t \cdot s]\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tight_readouts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For t <= 1 and 0 <= s <= 1, the matrix has trace one, both Bloch vectors lie on the third axis, and its correlation matrix is diagonal. The first two diagonal entries are opposite and equal in magnitude to sqrt(1+s) sqrt((1-t)(1-s)); the third is 1-t+ts. These equalities follow by evaluating the four product-basis entries and the Pauli traces.

**Lemma 1.22 (The centre length of the family).**

$$\forall (t: \mathbb{R}), (\forall (s: \mathbb{R}), ((0 \le t) \Rightarrow ((t \le 1) \Rightarrow ((0 \le s) \Rightarrow ((s < 1) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{centre}\left(\operatorname{tightState}\left(t, s\right)\right)\right) = t))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tight_centre` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For 0 <= t <= 1 and 0 <= s < 1, Bob's Bloch length is s, so the centre denominator, one minus s squared, is nonzero. Substituting the Bloch vectors and diagonal correlations gives Alice's centre (0,0,t), whose length is t.

**Theorem 1.23 (The centre bound holds).**

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
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bell_trace_real_expansion`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bob_radius_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.chsh`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.chshValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.delta`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.delta_le_centre`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.flipMatrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.flip_purity_identity`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.flipped`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.normalized_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.sigma_succ`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tightState`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tightVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tight_centre`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tight_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.tight_readouts`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.trace_pauli_kronecker_eq_corr`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.unit_dot_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.vlen_sq`
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction](SteeringEllipsoidFullyEntangledFraction.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitCostInfimum](../Information/ActualPureQubitCostInfimum.md)
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../Information/ActualQubitChordObstruction.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
- Dependency: [D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness](../../QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.md)
