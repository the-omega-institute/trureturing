# A mixed-state counterexample to the quantum inverse sumset bound

## Abstract

The equal mixture of two levels in dimension seven violates the proposed mixed-state quantum inverse sumset bound.

**Definition 1.1 (The clock-first Weyl operator).**

$$\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\forall \left(p: \operatorname{ZMod}\left(d\right)\right), \left(\forall \left(q: \operatorname{ZMod}\left(d\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.weyl}\left(d, p, q\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right) = \left(\left(\operatorname{D5.S3.Observer.WindowRegister.windowRoot}\left(d\right)^{\operatorname{Nat.div}\left(d + 1, 2\right)}\right)^{\operatorname{ZMod.val}\left(-\left(p \cdot q\right)\right)}\right) \cdot \left(\operatorname{D5.S3.Observer.WindowRegister.clockMatrix}\left(d\right)^{\operatorname{ZMod.val}\left(p\right)} \cdot \operatorname{D5.S3.Observer.WindowRegister.shiftMatrix}\left(d\right)^{\operatorname{ZMod.val}\left(q\right)}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.weyl` (`✓ std3`).

*Citation.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

For a nonzero natural dimension d, the clock-first Weyl operator multiplies the clock power by the shift power and the phase shown above. The exponents use the natural representatives ZMod.val; the phase exponent first negates the product in ZMod d. The division (d + 1)/2 is natural-number division. This is the source's odd-dimensional convention in IEEE_Final_BGJ.tex, lines 726–750. The formula is defined for every nonzero d; the source uses its odd-prime specialization and gives a separate phase convention for d = 2.

**Definition 1.2 (The characteristic function).**

$$\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(x: \operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.charFun}\left(\rho, x\right): \mathbb{C}\right) = \operatorname{Matrix.trace}\left(\rho \cdot \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.weyl}\left(d, -\operatorname{Prod.fst}\left(x\right), -\operatorname{Prod.snd}\left(x\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.charFun` (`✓ std3`).

*Citation.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

The characteristic function is the trace pairing with the Weyl operator at the negative phase-space point. Here x is a pair of residues and its two projections are negated separately. This is the single-qudit characteristic function of IEEE_Final_BGJ.tex, lines 760–773, extended to arbitrary complex matrices.

**Definition 1.3 (The mean-state operator).**

$$\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.meanState}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right) = \left(\operatorname{Inv.inv}\left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{C}\right)\right)\right) \cdot \left(\operatorname{Finset.sum}\left(\operatorname{Finset.filter}\left(\lambda \left(x: \operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right) \mapsto \left(\left\lVert \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.charFun}\left(\rho, x\right) \right\rVert = \left(1: \mathbb{R}\right)\right), \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right)\right)\right), \lambda \left(x: \operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right) \mapsto \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.charFun}\left(\rho, x\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.weyl}\left(d, \operatorname{Prod.fst}\left(x\right), \operatorname{Prod.snd}\left(x\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.meanState` (`✓ std3`).

*Citation.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

Retain precisely the characteristic coefficients of norm one, reconstruct their Weyl expansion, and divide by the dimension, cast to the complex scalars. The sum ranges over all phase-space points satisfying that norm condition. This combines the reconstruction formula in IEEE_Final_BGJ.tex, lines 767–773, with the mean state in lines 842–856. The displayed operator formula applies to arbitrary matrices, without assuming positivity or trace one.

**Definition 1.4 (The rank of the mean state).**

$$\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.meanRank}\left(\rho\right): \mathbb{N}\right) = \operatorname{Matrix.rank}\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.meanState}\left(\rho\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.meanRank` (`✓ std3`).

*Citation.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

The natural-valued matrix rank of the mean-state operator is the quantity R of IEEE_Final_BGJ.tex, line 1000.

**Definition 1.5 (The magic gap and its empty-set convention).**

$$\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{let} \left(a: \operatorname{Finset}\left(\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right)\right) := \operatorname{Finset.filter}\left(\lambda \left(x: \operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right) \mapsto \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.charFun}\left(\rho, x\right) \ne \left(0: \mathbb{C}\right)\right) \land \left(\left\lVert \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.charFun}\left(\rho, x\right) \right\rVert \ne \left(1: \mathbb{R}\right)\right)\right), \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right)\right)\right); \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.magicGap}\left(\rho\right): \mathbb{R}\right) = \operatorname{ite}\left(\operatorname{Finset.Nonempty}\left(a\right), \left(1: \mathbb{R}\right) - \max_{x \in a} \left\lVert \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.charFun}\left(\rho, x\right) \right\rVert, \left(0: \mathbb{R}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.magicGap` (`✓ std3`).

*Citation.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

The finite set a contains the nonzero characteristic coefficients whose norm is different from one. If this set is nonempty, subtract its largest coefficient norm from one; if it is empty, assign zero. The finite maximum is Finset.sup' on its nonempty branch. This is the convention of IEEE_Final_BGJ.tex, lines 870–876.

**Definition 1.6 (The squared gap factor).**

$$\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.gapFactor}\left(\rho\right): \mathbb{R}\right) = \left(\left(1: \mathbb{R}\right) - \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.magicGap}\left(\rho\right)\right)^{2}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.gapFactor` (`✓ std3`).

*Citation.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

The factor lambda is the square of one minus the magic gap, as in the inverse sumset bound of IEEE_Final_BGJ.tex, lines 2026–2037, and its mixed-state expectation in lines 2101–2108.

**Definition 1.7 (The real trace of the square).**

$$\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.purity}\left(\rho\right): \mathbb{R}\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\rho \cdot \rho\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.purity` (`✓ std3`).

*Citation.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

The purity expression takes the real part of the trace of the matrix square. For density matrices this is the purity factor in equation (58), IEEE_Final_BGJ.tex, lines 2101–2108. The definition also assigns a real value to an arbitrary complex matrix.

**Definition 1.8 (Quantum convolution by a linear permutation).**

$$\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\forall \left(s: \operatorname{ZMod}\left(d\right)\right), \left(\forall \left(t: \operatorname{ZMod}\left(d\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{let} \left(u: \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right) := \lambda \left(a: \operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right) \mapsto \left(\lambda \left(b: \operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)\right) \mapsto \left(\operatorname{ite}\left(a = \left(s \cdot \operatorname{Prod.fst}\left(b\right) + t \cdot \operatorname{Prod.snd}\left(b\right), -t \cdot \operatorname{Prod.fst}\left(b\right) + s \cdot \operatorname{Prod.snd}\left(b\right)\right), \left(1: \mathbb{C}\right), \left(0: \mathbb{C}\right)\right)\right)\right); \left(\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.convolution}\left(s, t, \rho, \sigma\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(u \cdot \operatorname{Matrix.kroneckerMap}\left(\lambda \left(x1: \mathbb{C}\right) \mapsto \left(\lambda \left(x2: \mathbb{C}\right) \mapsto \left(x1 \cdot x2\right)\right), \rho, \sigma\right) \cdot \operatorname{Matrix.conjTranspose}\left(u\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.convolution` (`✓ std3`).

*Citation.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

The matrix u sends the basis pair (i,j) to (si + tj, −ti + sj). Conjugate the tensor product by u and take the partial trace over the right factor. For nonzero s and t satisfying s squared plus t squared equal to one, u is the unitary of IEEE_Final_BGJ.tex, lines 885–896. The displayed matrix formula is defined without imposing those parameter conditions or density assumptions on its arguments.

**Definition 1.9 (The mixed-state inverse sumset expectation).**

$$\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right) [\operatorname{NeZero}\left(d\right)], \left(\left(\operatorname{Nat.Prime}\left(d\right)\right) \to \left(\forall \left(s: \operatorname{ZMod}\left(d\right)\right), \left(\forall \left(t: \operatorname{ZMod}\left(d\right)\right), \left(\left(s \ne \left(0: \operatorname{ZMod}\left(d\right)\right)\right) \to \left(\left(t \ne \left(0: \operatorname{ZMod}\left(d\right)\right)\right) \to \left(\left(s^{2} + t^{2} = \left(1: \operatorname{ZMod}\left(d\right)\right)\right) \to \left(\forall \left(\rho: \operatorname{D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState}\left(\operatorname{ZMod}\left(d\right)\right)\right), \left(\forall \left(\sigma: \operatorname{D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState}\left(\operatorname{ZMod}\left(d\right)\right)\right), \left(\forall \left(\tau: \operatorname{D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState}\left(\operatorname{ZMod}\left(d\right)\right)\right), \left(\forall \left(c: \mathbb{R}\right), \left(\left(\left(\operatorname{Subtype.val}\left(\sigma\right): \operatorname{CStarMatrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right) = \operatorname{CStarMatrix.ofMatrix}\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.meanState}\left(\left(\operatorname{Subtype.val}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right)\right)\right)\right) \to \left(\left(\left(\operatorname{Subtype.val}\left(\tau\right): \operatorname{CStarMatrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right) = \operatorname{CStarMatrix.ofMatrix}\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.convolution}\left(s, t, \left(\operatorname{Subtype.val}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{Subtype.val}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right)\right)\right)\right) \to \left(\operatorname{let} \left(\delta: \mathbb{R}\right) := \operatorname{Real.exp}\left(\operatorname{D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy}\left(\tau\right) - \operatorname{D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy}\left(\rho\right)\right); \left(\operatorname{let} \left(r: \mathbb{R}\right) := \left(\operatorname{Nat.cast}\left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.meanRank}\left(\left(\operatorname{Subtype.val}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right)\right)\right): \mathbb{R}\right); \left(\operatorname{let} \left(l: \mathbb{R}\right) := \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.gapFactor}\left(\left(\operatorname{Subtype.val}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right)\right); \left(\left(\left(1: \mathbb{R}\right) < \delta\right) \to \left(\left(\delta \le c\right) \to \left(\left(\left(0: \mathbb{R}\right) < \left(1: \mathbb{R}\right) + l \cdot \left(r \cdot \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.purity}\left(\left(\operatorname{Subtype.val}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right)\right) - \left(1: \mathbb{R}\right)\right)\right) \to \left(\left(\left(0: \mathbb{R}\right) < \operatorname{Real.log}\left(r\right) - \operatorname{Real.log}\left(\left(1: \mathbb{R}\right) + l \cdot \left(r \cdot \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.purity}\left(\left(\operatorname{Subtype.val}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right)\right) - \left(1: \mathbb{R}\right)\right)\right)\right) \to \left(\operatorname{D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy}\left(\rho, \sigma\right) \le \frac{\operatorname{Real.log}\left(r\right)}{\operatorname{Real.log}\left(r\right) - \operatorname{Real.log}\left(\left(1: \mathbb{R}\right) + l \cdot \left(r \cdot \operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.purity}\left(\left(\operatorname{Subtype.val}\left(\rho\right): \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right)\right) - \left(1: \mathbb{R}\right)\right)\right)} \cdot \operatorname{Real.log}\left(c\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

This is a single-qudit formulation of the expected mixed-state inequality (58) in Remark 45, IEEE_Final_BGJ.tex, lines 2101–2123. The dimension is prime and nonzero, and s and t are nonzero residues with s squared plus t squared equal to one. The density states σ and τ represent the mean state of ρ and its self-convolution through the stated equalities in CStarMatrix. Each density state is a positive semidefinite complex matrix of trace one. The notation Subtype.val extracts that matrix. The real number δ is the quantum-doubling constant of lines 1982–1994; r is the mean-state rank cast from the naturals to the reals, and l is the squared gap factor. For every real c with 1 < δ ≤ c, the proposed relative-entropy upper bound is required whenever the logarithm argument and the denominator are both positive. The entropy and relative entropy use natural logarithms.

**Theorem 1.10 (The seven-dimensional counterexample).**

$$\neg \left(\operatorname{D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bu-gu-jaffe-2025-mixed-state-inverse-sumset` (refuted) by `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bu-gu-jaffe-2025-mixed-state-inverse-sumset","declaration_gid":"D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kaifeng Bu; Weichen Gu; Arthur Jaffe (2025). *Quantum Ruzsa Divergence to Quantify Magic*. DOI: [10.1109/TIT.2025.3543276](https://doi.org/10.1109/TIT.2025.3543276). URL: <https://arxiv.org/abs/2401.14385v3>.

*Commentary.*

In dimension seven, let ρ be diagonal with weights 1/2 at levels 0 and 1 and zero elsewhere. Let σ be the identity matrix divided by seven, and let τ be diagonal with weights 1/4, 1/2 and 1/4 at levels 0, 2 and 4. Their diagonal entries are nonnegative and sum to one, so all three are density states.

Set s = t = 2 in ZMod 7. The convolution matrix sends (i,j) to (2i + 2j, −2i + 2j). The diagonal tensor product has four equally weighted input pairs (0,0), (0,1), (1,0) and (1,1), whose left outputs are respectively 0, 2, 2 and 4. Expanding matrix multiplication and the right partial trace over the seven residues therefore gives ρ convolved with itself equal to τ. The logarithm of a diagonal matrix is diagonal with the scalar logarithms of its entries. Consequently the entropy of ρ is log 2, and the entropy of τ is (3/2) log 2; zero entries contribute zero.

The diagonal entry of the Weyl operator at (p,q) vanishes unless q = 0. When q = 0, its entry at i is windowRoot(7) to the power val(i) val(p). Thus the characteristic function of ρ vanishes off the q = 0 axis and equals (1 + windowRoot(7) to the power val(−p))/2 on that axis. Every power of this primitive seventh root has norm one. Equality in the triangle inequality forces the characteristic-function norm to equal one only when that power is one. Primitivity and the natural representative val(−p) < 7 then force p = 0. Conversely the coefficient at (0,0) equals one. The triangle inequality also bounds every characteristic-function norm by one.

Only the coefficient at (0,0) therefore remains in the mean-state expansion, giving σ. All seven diagonal entries of σ are nonzero, so its rank is seven. If the finite set defining the magic gap is nonempty, its maximum norm lies between zero and one; if it is empty, the gap is zero. In either case l = gapFactor(ρ) satisfies 0 ≤ l ≤ 1. Direct diagonal multiplication gives purity(ρ) = 1/2. The logarithm of σ is the identity matrix multiplied by −log 7. Writing relative entropy as minus the entropy minus the trace against that logarithm gives D(ρ ∥ σ) = log 7 − log 2.

The entropy difference gives δ = exp((1/2) log 2) > 1. Choose c equal to this value. For every real l between zero and one, the argument A = 1 + l(7/2 − 1) lies in [1,7/2]. Monotonicity of the logarithm gives log 7 − log A ≥ log 2 > 0. The proposed right side is consequently at most (log 7/log 2)((1/2) log 2) = (1/2) log 7. On the other hand, 4 < 7 implies 2 log 2 < log 7, hence (1/2) log 7 < log 7 − log 2.

Seven is prime, both convolution parameters are nonzero, and 2 squared plus 2 squared equals one in ZMod 7. The computed mean state and convolution supply the two required matrix equalities, and the bounds on A supply both positivity hypotheses. Applying the proposed universal inequality to these density states and c would put log 7 − log 2 at most (1/2) log 7, contradicting the strict inequality above.

## References

- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.charFun`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.convolution`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.gapFactor`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.magicGap`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.meanRank`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.meanState`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.purity`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.result`
- Truth anchor: `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.weyl`
- Dependency: [D5/S3/Observer/MatrixUnitCertificate](../../Observer/MatrixUnitCertificate.md)
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](../Divergence/GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation](../Subentropy/StrongSubadditivityRefutation.md)
