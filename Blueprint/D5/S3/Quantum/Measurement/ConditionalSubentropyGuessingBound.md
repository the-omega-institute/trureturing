# Conditional subentropy and guessing

## Abstract

The simplex-integral conditional subentropy of a classical-quantum state is bounded by guessing min-entropy.

**Definition 1.1 (C).**

$$\forall n \in \mathbb{N},\; \operatorname{C}\left(n\right) = \sum_{k\in \operatorname{Finset}.\operatorname{Icc}\left(2, n\right)}(\frac{1}{(k: \mathbb{R})})$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.C` (`✓ std3`).

*Citation.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.48550/arXiv.1310.1312](https://doi.org/10.48550/arXiv.1310.1312). URL: <https://arxiv.org/abs/1310.1312v1>.

*Commentary.*

Equation (2), PDF page 2: "Q(ρ) = ⟨H(M(ρ))⟩_M − C_n where C_n := 1/2 + 1/3 + … + 1/n." The sum runs from 2 through n, inclusive.

**Definition 1.2 (simplexCoords).**

$$\forall n \in \mathbb{N},\; \operatorname{simplexCoords}\left(n\right) = \{y: \operatorname{Fin}\left(n - 1\right) \to \mathbb{R} | (\forall i \in \operatorname{Fin}\left(n - 1\right),\; 0 \le y\left(i\right)) \land (\sum_{i\in \operatorname{Fin}\left(n - 1\right)}(y\left(i\right)) \le 1)\}$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.simplexCoords` (`✓ std3`).

*Citation.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.48550/arXiv.1310.1312](https://doi.org/10.48550/arXiv.1310.1312). URL: <https://arxiv.org/abs/1310.1312v1>.

*Commentary.*

Equation (3), PDF page 2: "this uniform measure (normalised to have total volume unity) is given by dx = (n − 1)! dx_1 … dx_{n−1}." The first n−1 coordinates are nonnegative and have sum at most one.

**Definition 1.3 (subentropySpectrum).**

$$\forall n \in \mathbb{N},\; \forall lam \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \operatorname{subentropySpectrum}\left(n, lam\right) = (n: \mathbb{R}) \cdot ((\operatorname{Nat}.\operatorname{factorial}\left(n - 1\right): \mathbb{R}) \cdot \int_{y\in \operatorname{simplexCoords}\left(n\right)}(\operatorname{Real}.\operatorname{negMulLog}\left(\sum_{i\in \operatorname{Fin}\left(n\right)}(lam\left(i\right) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Geometry}.\operatorname{AlphaGeometry}.\operatorname{PositiveSimplexGeometryAndMixing}.\operatorname{chart}\left(y, i\right))\right)) dy) - \operatorname{C}\left(n\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.subentropySpectrum` (`✓ std3`).

*Citation.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.48550/arXiv.1310.1312](https://doi.org/10.48550/arXiv.1310.1312). URL: <https://arxiv.org/abs/1310.1312v1>.

*Commentary.*

Equation (4), PDF page 2: "Introducing η(y) := −y ln y, we then obtain a third expression for the subentropy from eq.(2): Q(ρ) = n ∫_{Δn} η(λ · x) dx − C_n." Real.negMulLog is η. The Lebesgue integral is multiplied by (n−1)!, as in equation (3).

**Definition 1.4 (subentropy).**

$$\forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall R \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; \forall hR \in \operatorname{Matrix}.\operatorname{IsHermitian}\left(R\right),\; \operatorname{subentropy}\left(R, hR\right) = \operatorname{subentropySpectrum}\left(\operatorname{Fintype}.\operatorname{card}\left(I\right), \left(\operatorname{Matrix}.\operatorname{IsHermitian}.\operatorname{eigenvalues}_{0}\right)\left(hR\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.subentropy` (`✓ std3`).

*Citation.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.48550/arXiv.1310.1312](https://doi.org/10.48550/arXiv.1310.1312). URL: <https://arxiv.org/abs/1310.1312v1>.

*Commentary.*

Equation (4), PDF page 2: "Introducing η(y) := −y ln y, we then obtain a third expression for the subentropy from eq.(2): Q(ρ) = n ∫_{Δn} η(λ · x) dx − C_n." R supplies its real Hermitian eigenvalues, including zero and repeated eigenvalues.

**Definition 1.5 (pGuess).**

$$\forall X \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(X\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall A \in X \to \operatorname{Matrix}\left(B, B, \mathbb{C}\right),\; \operatorname{pGuess}\left(A\right) = \operatorname{sSup}\left(\{s: \mathbb{R} | \exists E \in X \to \operatorname{Matrix}\left(B, B, \mathbb{C}\right),\; (\forall x \in X,\; \operatorname{Matrix}.\operatorname{PosSemidef}\left(E\left(x\right)\right)) \land ((\sum_{x\in X}(E\left(x\right)) = 1) \land (s = \operatorname{Complex}.\operatorname{re}\left(\sum_{x\in X}(\operatorname{Matrix}.\operatorname{trace}\left(E\left(x\right) \cdot A\left(x\right)\right))\right)))\}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.pGuess` (`✓ std3`).

*Citation.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.48550/arXiv.1310.1312](https://doi.org/10.48550/arXiv.1310.1312). URL: <https://arxiv.org/abs/1310.1312v1>.

*Commentary.*

PDF page 9: "p_guess(X|B) = max_{{E_x}:POVM} Σ_x p_x Tr(E_x ρ^x_B), where the maximization is over all possible POVMs: {E_x : E_x ≥ 0 ∀ x; Σ_x E_x = I}." A x is p_xρ_B^x. The supremum is over these finite-POVM scores.

**Definition 1.6 (claim).**

$$\operatorname{claim} = (\forall X \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(X\right)] [\operatorname{DecidableEq}\left(X\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall A \in X \to \operatorname{Matrix}\left(B, B, \mathbb{C}\right),\; (\forall x \in X,\; \operatorname{Matrix}.\operatorname{PosSemidef}\left(A\left(x\right)\right)) \Rightarrow ((\sum_{x\in X}(\operatorname{Matrix}.\operatorname{trace}\left(A\left(x\right)\right)) = 1) \Rightarrow (\forall hXB \in \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{Matrix}.\operatorname{blockDiagonal}\left(A\right)\right),\; \forall hB \in \operatorname{Matrix}.\operatorname{IsHermitian}\left(\sum_{x\in X}(A\left(x\right))\right),\; \operatorname{subentropy}\left(\operatorname{Matrix}.\operatorname{blockDiagonal}\left(A\right), hXB\right) - \operatorname{subentropy}\left(\sum_{x\in X}(A\left(x\right)), hB\right) \le -\operatorname{Real}.\operatorname{log}\left(\operatorname{pGuess}\left(A\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.claim` (`✓ std3`).

*Citation.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.48550/arXiv.1310.1312](https://doi.org/10.48550/arXiv.1310.1312). URL: <https://arxiv.org/abs/1310.1312v1>.

*Commentary.*

Conjecture 2, PDF page 9: "For a c-q state ρ_XB, the conditional subentropy Q(X|B) satisfies the following bound: Q(X|B) ≤ H_min(X|B) = − ln p_guess(X|B)." Equation (13), PDF page 8: "we define the conditional subentropy to be Q(A|B)_ρ := Q(ρ_AB) − Q(ρ_B)". X and B are arbitrary finite types with decidable equality. A has positive semidefinite blocks of total trace one. Matrix.blockDiagonal A is the joint state, and the sum of A is its B marginal. Natural logarithms are used.

**Theorem 1.7 (result).**

$$\forall X \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(X\right)] [\operatorname{DecidableEq}\left(X\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall A \in X \to \operatorname{Matrix}\left(B, B, \mathbb{C}\right),\; (\forall x \in X,\; \operatorname{Matrix}.\operatorname{PosSemidef}\left(A\left(x\right)\right)) \Rightarrow ((\sum_{x\in X}(\operatorname{Matrix}.\operatorname{trace}\left(A\left(x\right)\right)) = 1) \Rightarrow (\forall hXB \in \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{Matrix}.\operatorname{blockDiagonal}\left(A\right)\right),\; \forall hB \in \operatorname{Matrix}.\operatorname{IsHermitian}\left(\sum_{x\in X}(A\left(x\right))\right),\; \operatorname{subentropy}\left(\operatorname{Matrix}.\operatorname{blockDiagonal}\left(A\right), hXB\right) - \operatorname{subentropy}\left(\sum_{x\in X}(A\left(x\right)), hB\right) \le -\operatorname{Real}.\operatorname{log}\left(\operatorname{pGuess}\left(A\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/datta-dorlas-jozsa-benatti-2014-conditional-subentropy-conjecture-2` (proved) by `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"datta-dorlas-jozsa-benatti-2014-conditional-subentropy-conjecture-2","declaration_gid":"D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.48550/arXiv.1310.1312](https://doi.org/10.48550/arXiv.1310.1312). URL: <https://arxiv.org/abs/1310.1312v1>.

*Commentary.*

The simplex integral equals the determinant-integral subentropy on positive semidefinite trace-one matrices. Gaussian radial decomposition proves this equality without a simple-spectrum assumption. Normalizing the nonzero blocks gives a probability ensemble; zero blocks contribute zero. The ensemble guessing bound gives the inequality.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.C`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.pGuess`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.result`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.simplexCoords`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.subentropy`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.subentropySpectrum`
- Dependency: [D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing](../../Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace](FiniteDetectionDarkSpace.md)
- Dependency: [D5/S3/Quantum/Subentropy/Basic](../Subentropy/Basic.md)
- Dependency: [D5/S3/Quantum/Subentropy/ClassicalQuantumGram](../Subentropy/ClassicalQuantumGram.md)
- Dependency: [D5/S3/Quantum/Subentropy/GaussianMatrix](../Subentropy/GaussianMatrix.md)
- Dependency: [D5/S3/Quantum/Subentropy/GaussianQuadratic](../Subentropy/GaussianQuadratic.md)
- Dependency: [D5/S3/Quantum/Subentropy/GuessingProbability](../Subentropy/GuessingProbability.md)
- Dependency: [D5/S3/Quantum/Subentropy/POVMGram](../Subentropy/POVMGram.md)
- Dependency: [D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation](../../StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.md)
