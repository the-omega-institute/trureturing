# Entropy saturation forces a symmetric informationally complete measurement

## Abstract

Saturation of the Haar-averaged output entropy of a Lüders MIC channel forces a SIC.

**Definition 1.1 (Minimal informational completeness).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(e: \operatorname{Fin}\left(d^{2}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsMIC}\left(d, e\right)\right) \Leftrightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(d^{2}\right)\right), \left(\operatorname{Matrix.PosSemidef}\left(e\left(i\right)\right)\right)\right) \land \left(\left(\sum_{\left(i: \operatorname{Fin}\left(d^{2}\right)\right)} \left(e\left(i\right)\right) = \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right) \land \left(\operatorname{LinearIndependent}\left(\mathbb{C}, e\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.IsMIC` (`✓ std3`).

*Citation.* DeBrota, John B.; Stacey, Blake C. (2019). *Lüders channels and the existence of symmetric-informationally-complete measurements*. DOI: [10.1103/PhysRevA.100.062327](https://doi.org/10.1103/PhysRevA.100.062327). URL: <https://arxiv.org/abs/1907.10999v2>.

*Commentary.*

A MIC consists of d squared positive semidefinite complex matrices summing to the identity, linearly independent over the complex numbers. This is the source's definition in lmc.tex, lines 80–84. The predicate is defined for every natural dimension; positivity of the dimension is imposed in the entropy statement.

**Definition 1.2 (Rank-one equiangular MICs).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(e: \operatorname{Fin}\left(d^{2}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsSIC}\left(d, e\right)\right) \Leftrightarrow \left(\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsMIC}\left(d, e\right)\right) \land \left(\left(\forall \left(i: \operatorname{Fin}\left(d^{2}\right)\right), \left(\exists \left(c: \mathbb{R}\right), \left(\exists \left(p: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.IsHermitian}\left(p\right)\right) \land \left(\left(p \cdot p = p\right) \land \left(\left(\operatorname{Matrix.trace}\left(p\right) = \left(1: \mathbb{C}\right)\right) \land \left(e\left(i\right) = \left(\operatorname{Complex.ofReal}\left(c\right)\right) \cdot \left(p\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\exists \left(a: \mathbb{C}\right), \left(\exists \left(b: \mathbb{C}\right), \left(\forall \left(i: \operatorname{Fin}\left(d^{2}\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(d^{2}\right)\right), \left(\operatorname{Matrix.trace}\left(e\left(i\right) \cdot e\left(j\right)\right) = \operatorname{ite}\left(i = j, a, b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.IsSIC` (`✓ std3`).

*Citation.* DeBrota, John B.; Stacey, Blake C. (2019). *Lüders channels and the existence of symmetric-informationally-complete measurements*. DOI: [10.1103/PhysRevA.100.062327](https://doi.org/10.1103/PhysRevA.100.062327). URL: <https://arxiv.org/abs/1907.10999v2>.

*Commentary.*

A SIC is a MIC whose effects are real scalar multiples of Hermitian, idempotent, trace-one matrices, and whose trace inner products have one common diagonal value and one common off-diagonal value. A Hermitian idempotent of trace one is a rank-one orthogonal projector. The scalars are quantified over all real numbers; the MIC conditions force them to be positive. The two common trace values are quantified as complex numbers, as are the traces. This restates lmc.tex, lines 84–90.

**Definition 1.3 (Haar-averaged Lüders output entropy).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{NeZero}\left(d\right)\right) \to \left(\forall \left(e: \operatorname{Fin}\left(d^{2}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.typicalEntropy}\left(d, e\right) = \int_{\left(u: \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)} \left(-\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{CStarMatrix.ofMatrix}\left(\operatorname{ite}\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsMIC}\left(d, e\right), \sum_{\left(i: \operatorname{Fin}\left(d^{2}\right)\right)} \left(\sqrt{e\left(i\right)} \cdot u.1 \cdot \operatorname{Matrix.single}\left(\left(0: \operatorname{Fin}\left(d\right)\right), \left(0: \operatorname{Fin}\left(d\right)\right), \left(1: \mathbb{C}\right)\right) \cdot \operatorname{Matrix.conjTranspose}\left(u.1\right) \cdot \sqrt{e\left(i\right)}\right), \operatorname{Matrix.diagonal}\left(\lambda \left(j: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\operatorname{ite}\left(j = \left(0: \operatorname{Fin}\left(d\right)\right), \left(1: \mathbb{C}\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right) \cdot \operatorname{CFC.log}\left(\operatorname{CStarMatrix.ofMatrix}\left(\operatorname{ite}\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsMIC}\left(d, e\right), \sum_{\left(i: \operatorname{Fin}\left(d^{2}\right)\right)} \left(\sqrt{e\left(i\right)} \cdot u.1 \cdot \operatorname{Matrix.single}\left(\left(0: \operatorname{Fin}\left(d\right)\right), \left(0: \operatorname{Fin}\left(d\right)\right), \left(1: \mathbb{C}\right)\right) \cdot \operatorname{Matrix.conjTranspose}\left(u.1\right) \cdot \sqrt{e\left(i\right)}\right), \operatorname{Matrix.diagonal}\left(\lambda \left(j: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\operatorname{ite}\left(j = \left(0: \operatorname{Fin}\left(d\right)\right), \left(1: \mathbb{C}\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \mathrm{d} \operatorname{MeasureTheory.Measure.haarMeasure}\left(\left(\operatorname{Top.top}: \operatorname{TopologicalSpace.PositiveCompacts}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.typicalEntropy` (`✓ std3`).

*Citation.* DeBrota, John B.; Stacey, Blake C. (2019). *Lüders channels and the existence of symmetric-informationally-complete measurements*. DOI: [10.1103/PhysRevA.100.062327](https://doi.org/10.1103/PhysRevA.100.062327). URL: <https://arxiv.org/abs/1907.10999v2>.

*Commentary.*

The unitary group carries its normalized Haar probability measure, Measure.haarMeasure of the top positive compact set. Conjugating the coordinate projector at zero by a Haar unitary gives the pure input. For a MIC, its output is the unread measurement state with the positive square roots of the effects:

$$
\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{NeZero}\left(d\right)\right) \to \left(\forall \left(e: \operatorname{Fin}\left(d^{2}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Observer.Conditioning.unreadState}\left(\lambda \left(i: \operatorname{Fin}\left(d^{2}\right)\right) \mapsto \left(\sqrt{e\left(i\right)}\right), x\right) = \sum_{\left(i: \operatorname{Fin}\left(d^{2}\right)\right)} \left(\sqrt{e\left(i\right)} \cdot x \cdot \sqrt{e\left(i\right)}\right)\right)\right)\right)\right)
$$

This is the Lüders channel of lmc.tex, lines 104–114. Integrating its von Neumann entropy gives the pure-input average used in Theorem 2, lines 385–390. The displayed definition expands the entropy as minus the real part of the trace of the density times its matrix logarithm. CStarMatrix.ofMatrix makes the matrix conversion explicit. To define the function also on families that are not MICs, the conditional uses the coordinate density at zero in that case; its entropy is zero. This extension supplies no additional hypothesis to the saturation implication.

**Definition 1.4 (The entropy-saturation conjecture).**

$$\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{NeZero}\left(d\right)\right) \to \left(\forall \left(e: \operatorname{Fin}\left(d^{2}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsMIC}\left(d, e\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.typicalEntropy}\left(d, e\right) = \operatorname{Real.log}\left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) + 1\right) - \frac{2}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) + 1} \cdot \operatorname{Real.log}\left(2\right)\right) \to \left(\exists \left(f: \operatorname{Fin}\left(d^{2}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsSIC}\left(d, f\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.claim` (`✓ std3`).

*Citation.* DeBrota, John B.; Stacey, Blake C. (2019). *Lüders channels and the existence of symmetric-informationally-complete measurements*. DOI: [10.1103/PhysRevA.100.062327](https://doi.org/10.1103/PhysRevA.100.062327). URL: <https://arxiv.org/abs/1907.10999v2>.

*Commentary.*

For every positive natural dimension and every MIC, equality with the stated Haar-averaged entropy bound implies that a SIC exists in that dimension. This is Conjecture 1 in lmc.tex, lines 416–420, with the Haar average taken over unitary conjugates of the fixed coordinate projector. All logarithms are natural. The premise requires entropy saturation; the conclusion does not assert SIC existence in dimensions where that premise is unavailable.

**Theorem 1.5 (Entropy saturation forces SIC existence).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{NeZero}\left(d\right)\right) \to \left(\forall \left(e: \operatorname{Fin}\left(d^{2}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsMIC}\left(d, e\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.typicalEntropy}\left(d, e\right) = \operatorname{Real.log}\left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) + 1\right) - \frac{2}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) + 1} \cdot \operatorname{Real.log}\left(2\right)\right) \to \left(\exists \left(f: \operatorname{Fin}\left(d^{2}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.IsSIC}\left(d, f\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.result` (`✓ std3`). ∎

*Resolves.* `Problems/debrota-stacey-2019-luders-entropy-saturation-sic` (proved) by `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"debrota-stacey-2019-luders-entropy-saturation-sic","declaration_gid":"D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* DeBrota, John B.; Stacey, Blake C. (2019). *Lüders channels and the existence of symmetric-informationally-complete measurements*. DOI: [10.1103/PhysRevA.100.062327](https://doi.org/10.1103/PhysRevA.100.062327). URL: <https://arxiv.org/abs/1907.10999v2>.

*Commentary.*

Fix a positive dimension and a MIC e attaining the entropy value in the premise. For a unitary u let P be the conjugate of the coordinate projector at zero, let Aᵢ be the positive square root of e i, and put ρ = ∑ᵢ Aᵢ P Aᵢ. Thus ρ is Conditioning.unreadState applied to those square roots and P. The projector P is positive, idempotent and has trace one. Positivity of each sandwich and the identity ∑ᵢ Aᵢ² = I make ρ a density matrix. Write S for von Neumann entropy and D for Umegaki relative entropy. Set σₚ = (I + P)/(d + 1), c = 2/(d + 1), and let B be the entropy value in the premise. The density σₚ is strictly positive. Functional calculus on the two eigenspaces of P gives log σₚ = −log(d + 1) I + log 2 P. Expanding relative entropy therefore gives:

$$
B - S\left(\rho\right) = D\left(\rho, \sigma_{P}\right) + \left(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(P \cdot \rho\right)\right) - c\right) \cdot \operatorname{Real.log}\left(2\right)
$$

Write t for the sum of the squares of the real traces of the Aᵢ, and a for the Haar average of the real trace of Pρ. Apply D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.pure_quadratic to each Aᵢ. Its trace is real and Aᵢ² = e i, so the Haar second moment, summed over the effects, gives:

$$
a = \frac{t + \left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) \cdot \left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) + 1\right)}
$$

For a positive matrix A, its squared trace is at least the trace of A². Applied to the Aᵢ, this gives t at least d and a at least c. The equality case also identifies the rank. If A is nonzero and the two traces agree, dividing A by its positive trace produces a mixed state with purity one. By MState.pure_iff_purity_one this state is pure, and MState.pure_mul_self makes its matrix p idempotent. The matrix p is Hermitian and has trace one. Multiplying p by tr A recovers A. Consequently, equality for Aᵢ makes e i a real scalar multiple of such a p. Linear independence of the MIC effects ensures that no Aᵢ is zero.

The strong Klein bound supplies nonnegativity and rigidity of relative entropy. Every density matrix is bounded above by I, and strict positivity of σₚ supplies the support condition. The bound with spectral ceiling one is:

$$
\frac{\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{Matrix.conjTranspose}\left(\left(\rho - \sigma_{P}\right)\right) \cdot \left(\rho - \sigma_{P}\right)\right)\right)}{2} \le D\left(\rho, \sigma_{P}\right)
$$

The output and its entropy are continuous in u; continuity of the entropy follows from continuity of x log x, including at zero. The entropy-gap identity then also makes the relative entropy continuous. Compactness of the unitary group makes these functions integrable. Integrate the entropy-gap identity. Saturation gives zero as the sum of the nonnegative average relative entropy and (a − c) log 2. Since log 2 is positive, a = c, t = d, and the relative entropy is zero almost everywhere. The nonnegative individual trace gaps sum to zero, so each vanishes. The rank argument above therefore makes every effect rank one.

Where the relative entropy is zero, the strong Klein bound forces the Hilbert–Schmidt square of ρ − σₚ to vanish, hence ρ = σₚ. Both sides are continuous functions of u, and normalized Haar measure gives positive measure to every nonempty open set. Their almost-everywhere equality thus holds everywhere.

The Lüders map and the following depolarizing map are complex linear. They agree on every unitary conjugate of the coordinate projector at zero. Permutation unitaries give agreement for each coordinate projector; spectral decomposition then gives agreement on every Hermitian matrix. Decomposing an arbitrary complex matrix into its Hermitian real and imaginary parts gives:

$$
\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\sum_{\left(i: \operatorname{Fin}\left(d^{2}\right)\right)} \left(\sqrt{e\left(i\right)} \cdot x \cdot \sqrt{e\left(i\right)}\right) = \left(\frac{1}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{C}\right) + 1}\right) \cdot \left(x + \left(\operatorname{Matrix.trace}\left(x\right)\right) \cdot \left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right)\right)
$$

Choose the rank-one representation e i = c i · p i obtained above. Taking traces gives c i nonnegative. Each p i is positive, and the square root of e i is sqrt(c i) · p i. The trace-one projector sandwich identity p i · x · p i = tr(p i · x) · p i therefore writes the Lüders output as ∑ᵢ tr(p i · x) · e i. Apply the depolarizing identity with x = e j, replace I by ∑ᵢ e i, and compare coefficients in the linearly independent family e:

$$
\forall \left(j: \operatorname{Fin}\left(d^{2}\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(d^{2}\right)\right), \left(\operatorname{Matrix.trace}\left(p\left(i\right) \cdot e\left(j\right)\right) = \frac{1}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{C}\right) + 1} \cdot \left(\operatorname{ite}\left(i = j, \left(1: \mathbb{C}\right), \left(0: \mathbb{C}\right)\right) + \operatorname{Complex.ofReal}\left(c\left(j\right)\right)\right)\right)\right)
$$

At i = j, idempotence and trace one give c j = (1 + c j)/(d + 1), so c j = 1/d. Substituting these weights back gives the two trace values:

$$
\forall \left(i: \operatorname{Fin}\left(d^{2}\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(d^{2}\right)\right), \left(\operatorname{Matrix.trace}\left(e\left(i\right) \cdot e\left(j\right)\right) = \operatorname{ite}\left(i = j, \left(\frac{1}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{C}\right)}\right)^{2}, \frac{\left(\frac{1}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{C}\right)}\right)^{2}}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{C}\right) + 1}\right)\right)\right)
$$

The original MIC is therefore rank one and equiangular. It satisfies IsSIC, and choosing f = e proves the existential conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.IsMIC`
- Truth anchor: `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.IsSIC`
- Truth anchor: `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.result`
- Truth anchor: `D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.typicalEntropy`
- Dependency: [D5/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy](../Divergence/SpectralCeilingRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus](../Matrix/TwoPointFunctionalCalculus.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../RandomCircuits/HaarTwoCopyTwirl.md)
