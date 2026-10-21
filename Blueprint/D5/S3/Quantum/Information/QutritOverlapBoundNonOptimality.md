# The qutrit overlap entropy bound is unattainable

## Abstract

The Tsallis-two overlap bound is not attained by qutrit observables at interior overlaps.

All indices range over Fin 3, and complex moduli and real parts have their usual meanings. The two probability maps read the diagonal in the standard basis and after conjugating a density matrix by T. The overlap parameter c is real.

**Definition 1.1 (Standard-basis probabilities).**

$$\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{probA}\left(rho\right) = \lambda (i: \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{Complex}.\operatorname{re}\left(rho\left(i\right)\left(i\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.probA` (`✓ std3`).

*Citation.* Steeve Zozor; Gustavo Martín Bosyk; Mariela Portesi (2014). *General entropy-like uncertainty relations in finite dimensions*. DOI: [10.1088/1751-8113/47/49/495302](https://doi.org/10.1088/1751-8113/47/49/495302). URL: <https://arxiv.org/abs/1311.5602v3>.

*Commentary.*

For a complex 3 by 3 matrix ρ, the standard-basis probability p_i is the real part of its diagonal entry ρᵢᵢ.

**Definition 1.2 (Transformed-basis probabilities).**

$$\forall (T: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{probB}\left(T, rho\right) = \lambda (j: \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{Complex}.\operatorname{re}\left(\left(((T) \cdot (rho)) \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(T\right))\right)\left(j\right)\left(j\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.probB` (`✓ std3`).

*Citation.* Steeve Zozor; Gustavo Martín Bosyk; Mariela Portesi (2014). *General entropy-like uncertainty relations in finite dimensions*. DOI: [10.1088/1751-8113/47/49/495302](https://doi.org/10.1088/1751-8113/47/49/495302). URL: <https://arxiv.org/abs/1311.5602v3>.

*Commentary.*

For a complex 3 by 3 matrix T and state ρ, the transformed probability q_j is the real part of the jth diagonal entry of TρT*, where T* is the conjugate transpose.

**Definition 1.3 (The source function D).**

$$\forall (theta: \mathbb{R}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{boundD}\left(theta\right) = (1) - (((\left\lfloor\frac{1}{(\operatorname{Real}.\operatorname{cos}\left(theta\right))^{2}}\right\rfloor) \cdot (((\operatorname{Real}.\operatorname{cos}\left(theta\right))^{2})^{2})) + (((1) - ((\left\lfloor\frac{1}{(\operatorname{Real}.\operatorname{cos}\left(theta\right))^{2}}\right\rfloor) \cdot ((\operatorname{Real}.\operatorname{cos}\left(theta\right))^{2})))^{2})))$$

*Formalization.* `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.boundD` (`✓ std3`).

*Citation.* Steeve Zozor; Gustavo Martín Bosyk; Mariela Portesi (2014). *General entropy-like uncertainty relations in finite dimensions*. DOI: [10.1088/1751-8113/47/49/495302](https://doi.org/10.1088/1751-8113/47/49/495302). URL: <https://arxiv.org/abs/1311.5602v3>.

*Commentary.*

The source function D uses h(x) = 1 − x and φ(x) = x². Its integer floor is the floor of 1 divided by cos²θ; the displayed expression is h applied to the two nonzero masses produced by that floor term.

**Definition 1.4 (The overlap bound).**

$$\forall (c: \mathbb{R}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{overlapBound}\left(c\right) = \operatorname{sInf}\left(\operatorname{Set}.\operatorname{image}\left(\lambda (theta: \mathbb{R}) \mapsto ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{boundD}\left(theta\right)) + (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{boundD}\left((\operatorname{Real}.\operatorname{arccos}\left(c\right)) - (theta)\right))), \operatorname{Set}.\operatorname{Icc}\left(0, \operatorname{Real}.\operatorname{arccos}\left(c\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.overlapBound` (`✓ std3`).

*Citation.* Steeve Zozor; Gustavo Martín Bosyk; Mariela Portesi (2014). *General entropy-like uncertainty relations in finite dimensions*. DOI: [10.1088/1751-8113/47/49/495302](https://doi.org/10.1088/1751-8113/47/49/495302). URL: <https://arxiv.org/abs/1311.5602v3>.

*Commentary.*

The bound is the real infimum over θ in the closed interval from zero to arccos(c) of D(θ) plus D(arccos(c) − θ).

**Definition 1.5 (Attainment by a qutrit density matrix).**

$$\forall (c: \mathbb{R}), ((\frac{1}{\sqrt {2}} < c) \Rightarrow ((c \le 1) \Rightarrow (\exists (T: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), ((T \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right)) \land ((\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), (\left\lVert T\left(i\right)\left(j\right) \right\rVert \le c))) \land ((\exists (i: \operatorname{Fin}\left(3\right)), (\exists (j: \operatorname{Fin}\left(3\right)), (\left\lVert T\left(i\right)\left(j\right) \right\rVert = c))) \land (\exists (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Tomography}.\operatorname{MUB}.\operatorname{MUBModeSymmetryBudget}.\operatorname{threeModeMixing}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{probA}\left(rho\right)\right)) + (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Tomography}.\operatorname{MUB}.\operatorname{MUBModeSymmetryBudget}.\operatorname{threeModeMixing}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{probB}\left(T, rho\right)\right)) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{overlapBound}\left(c\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.claim` (`✓ std3`).

*Citation.* Steeve Zozor; Gustavo Martín Bosyk; Mariela Portesi (2014). *General entropy-like uncertainty relations in finite dimensions*. DOI: [10.1088/1751-8113/47/49/495302](https://doi.org/10.1088/1751-8113/47/49/495302). URL: <https://arxiv.org/abs/1311.5602v3>.

*Commentary.*

For every c strictly above 1/√2 and at most one, the claim asks for a unitary 3 by 3 matrix with all entry moduli at most c and one entry of modulus c, together with a positive semidefinite trace-one density matrix whose two Tsallis-two entropies attain the overlap bound.

**Theorem 1.6 (Interior qutrit overlaps cannot attain the bound).**

$$\neg (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{QutritOverlapBoundNonOptimality}.\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.result` (`✓ std3`). ∎

*Resolves.* `Problems/zozor-bosyk-portesi-2014-qutrit-overlap-bound-non-optimality` (refuted) by `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zozor-bosyk-portesi-2014-qutrit-overlap-bound-non-optimality","declaration_gid":"D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Steeve Zozor; Gustavo Martín Bosyk; Mariela Portesi (2014). *General entropy-like uncertainty relations in finite dimensions*. DOI: [10.1088/1751-8113/47/49/495302](https://doi.org/10.1088/1751-8113/47/49/495302). URL: <https://arxiv.org/abs/1311.5602v3>.

*Commentary.*

For 1/√2 < c < 1, the floor in D is one throughout the interval, so D(θ) = (1 − cos(4θ))/4 and the infimum equals 1 − c², attained only at θ = arccos(c)/2.

The entropy sum is concave in the density matrix because both probability maps are affine and Tsallis-two entropy is concave. It is therefore enough to consider a pure state, represented by a unit vector ψ; the density-matrix assertion reduces to the corresponding pair of measurement probability vectors for ψ.

If the largest probability in either measurement is at most 1/2, its entropy is at least 1/2 and the desired strict comparison follows. Otherwise write the two largest probabilities as P = cos²θ and Q = cos²η. Cauchy–Schwarz on the components orthogonal to ψ gives |⟨a,b⟩| ≥ √(PQ) − √((1−P)(1−Q)) = cos(θ+η), so the entrywise overlap bound implies θ + η ≥ arccos(c). The entropy estimates then give S₂(p) + S₂(q) ≥ 1 − c².

Equality would force ψ into the span of two standard-basis vectors and into the span of two transformed-basis vectors. Equality in Cauchy–Schwarz makes those two planes coincide. In dimension three their remaining basis vectors are both orthogonal to that plane, so their overlap has modulus one, contradicting c < 1.

At c = 3/4 the bound is 1 − (3/4)² = 7/16. The universal attainment assertion would supply a state and unitary attaining this value, but the strict inequality above rules that out.

## References

- Truth anchor: `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.boundD`
- Truth anchor: `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.claim`
- Truth anchor: `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.overlapBound`
- Truth anchor: `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.probA`
- Truth anchor: `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.probB`
- Truth anchor: `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.result`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget](../Tomography/MUB/MUBModeSymmetryBudget.md)
