# Bound coherence in every dimension at least three

## Abstract

Every dimension at least three admits a coherent, nonmaximal density matrix whose positive modes cannot increase under an allowed interaction of two identical copies.

**Definition 1.1 (The truncated number observable).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \operatorname{Matrix.diagonal}\left(\lambda \left(n: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\left(\operatorname{Nat.cast}\left(\operatorname{Fin.val}\left(n\right)\right): \mathbb{C}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.numberOp` (`✓ std3`).

*Citation.* Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk (2026). *Unspeakable coherence concentration*. DOI: [10.1103/fj8w-v1bb](https://doi.org/10.1103/fj8w-v1bb). URL: <https://arxiv.org/abs/2512.04255v1>.

*Commentary.*

The number observable is diagonal in the number basis, with eigenvalues zero through d minus one. The natural value of each index is cast to a complex scalar. This is the local observable in Section II, main.tex line 224.

**Definition 1.2 (Interactions conserving total number).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(v: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.IsAllowedUnitary}\left(v\right)\right) \Leftrightarrow \left(\left(v \in \operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right) \land \left(\left(v\right) \cdot \left(\left(\operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right), \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right) + \left(\operatorname{Matrix.kronecker}\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right)\right)\right)\right) = \left(\left(\operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right), \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right) + \left(\operatorname{Matrix.kronecker}\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right)\right)\right)\right) \cdot \left(v\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.IsAllowedUnitary` (`✓ std3`).

*Citation.* Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk (2026). *Unspeakable coherence concentration*. DOI: [10.1103/fj8w-v1bb](https://doi.org/10.1103/fj8w-v1bb). URL: <https://arxiv.org/abs/2512.04255v1>.

*Commentary.*

An allowed interaction is a unitary matrix on the product basis that commutes with the sum of the two local number observables. The two identity matrices act on the respective local systems. Section II, main.tex lines 219–224, gives this conservation condition.

**Definition 1.3 (A signed number-difference mode).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(j: \mathbb{Z}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.mode}\left(j, \rho\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \lambda \left(r: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\lambda \left(s: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\operatorname{ite}\left(\left(\left(\operatorname{Nat.cast}\left(\operatorname{Fin.val}\left(r\right)\right): \mathbb{Z}\right)\right) - \left(\left(\operatorname{Nat.cast}\left(\operatorname{Fin.val}\left(s\right)\right): \mathbb{Z}\right)\right) = j, \rho\left(r, s\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.mode` (`✓ std3`).

*Citation.* Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk (2026). *Unspeakable coherence concentration*. DOI: [10.1103/fj8w-v1bb](https://doi.org/10.1103/fj8w-v1bb). URL: <https://arxiv.org/abs/2512.04255v1>.

*Commentary.*

The jth mode retains exactly those entries whose row number minus column number equals the integer j. Both natural index values are cast to integers before subtraction. Entries outside this diagonal are zero. This is the entrywise form of the mode in Section III, main.tex lines 230–232; the definition also applies to arbitrary matrices and arbitrary integer j.

**Definition 1.4 (The trace norm of a mode).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(j: \mathbb{Z}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.modeCoherence}\left(j, \rho\right): \mathbb{R}\right) = \operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.mode}\left(j, \rho\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.modeCoherence` (`✓ std3`).

*Citation.* Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk (2026). *Unspeakable coherence concentration*. DOI: [10.1103/fj8w-v1bb](https://doi.org/10.1103/fj8w-v1bb). URL: <https://arxiv.org/abs/2512.04255v1>.

*Commentary.*

Coherence in mode j is the real trace norm of that mode. Section IV, main.tex lines 260–261, uses this quantity. The trace norm here is the real part of the trace of the positive square root of the conjugate transpose times the matrix; the source writes the equivalent square root of the matrix times its conjugate transpose.

**Definition 1.5 (The first output marginal).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(v: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.concentrated}\left(v, \rho\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\left(\left(v\right) \cdot \left(\operatorname{Matrix.kronecker}\left(\rho, \rho\right)\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(v\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.concentrated` (`✓ std3`).

*Citation.* Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk (2026). *Unspeakable coherence concentration*. DOI: [10.1103/fj8w-v1bb](https://doi.org/10.1103/fj8w-v1bb). URL: <https://arxiv.org/abs/2512.04255v1>.

*Commentary.*

Form the tensor product of two identical matrices, conjugate it by v, and trace out the second system. For a density matrix and an allowed unitary this is the first output state of the two-copy concentration experiment in Section IV, main.tex line 265. The definition itself imposes neither positivity nor unitarity.

**Definition 1.6 (Equal-amplitude pure states).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.IsMaximallyCoherent}\left(\rho\right)\right) \Leftrightarrow \left(\exists \left(\theta: \operatorname{Fin}\left(d\right) \to \mathbb{R}\right), \left(\rho = \operatorname{Matrix.vecMulVec}\left(\lambda \left(n: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\frac{\operatorname{Complex.exp}\left(\left(\operatorname{Complex.ofReal}\left(\theta\left(n\right)\right)\right) \cdot \left(\operatorname{Complex.I}\right)\right)}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)\right)\right)}\right), \operatorname{Star.star}\left(\lambda \left(n: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\frac{\operatorname{Complex.exp}\left(\left(\operatorname{Complex.ofReal}\left(\theta\left(n\right)\right)\right) \cdot \left(\operatorname{Complex.I}\right)\right)}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)\right)\right)}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.IsMaximallyCoherent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk (2026). *Unspeakable coherence concentration*. DOI: [10.1103/fj8w-v1bb](https://doi.org/10.1103/fj8w-v1bb). URL: <https://arxiv.org/abs/2512.04255v1>.

*Commentary.*

A maximally coherent matrix is the outer product of a vector with its conjugate, where every coordinate has modulus one over the square root of d. The real phase θ n is cast to a complex number before multiplication by the imaginary unit. The natural dimension is first cast to a real number for the square root, and that square root is then cast to a complex number. This specifies the general-dimensional meaning of maximal coherence used here.

**Definition 1.7 (No positive mode can be concentrated).**

$$\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\left(3 \le d\right) \Rightarrow \left(\exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \land \left(\left(\operatorname{Matrix.trace}\left(\rho\right) = \left(1: \mathbb{C}\right)\right) \land \left(\left(\left(\rho\right) \cdot \left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right)\right) \ne \left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right)\right) \cdot \left(\rho\right)\right) \land \left(\left(\neg \left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.IsMaximallyCoherent}\left(\rho\right)\right)\right) \land \left(\forall \left(v: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.IsAllowedUnitary}\left(v\right)\right) \Rightarrow \left(\forall \left(j: \mathbb{N}\right), \left(\left(1 \le j\right) \Rightarrow \left(\left(j \le \left(d\right) - \left(1\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.modeCoherence}\left(\left(\operatorname{Nat.cast}\left(j\right): \mathbb{Z}\right), \operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.concentrated}\left(v, \rho\right)\right) \le \operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.modeCoherence}\left(\left(\operatorname{Nat.cast}\left(j\right): \mathbb{Z}\right), \rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk (2026). *Unspeakable coherence concentration*. DOI: [10.1103/fj8w-v1bb](https://doi.org/10.1103/fj8w-v1bb). URL: <https://arxiv.org/abs/2512.04255v1>.

*Commentary.*

For every natural dimension d at least three, there is a positive semidefinite matrix of trace one that does not commute with the number observable and is not an equal-amplitude pure state. For every allowed unitary on two copies, each positive local mode from one through d minus one has output coherence at most its input coherence. This gives a precise reading of the higher-dimensional question in Section IX, main.tex line 387. The statement concerns two identical copies and the first marginal.

**Theorem 1.8 (Existence in all dimensions at least three).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(3 \le d\right) \Rightarrow \left(\exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \land \left(\left(\operatorname{Matrix.trace}\left(\rho\right) = \left(1: \mathbb{C}\right)\right) \land \left(\left(\left(\rho\right) \cdot \left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right)\right) \ne \left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.numberOp}\left(d\right)\right) \cdot \left(\rho\right)\right) \land \left(\left(\neg \left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.IsMaximallyCoherent}\left(\rho\right)\right)\right) \land \left(\forall \left(v: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.IsAllowedUnitary}\left(v\right)\right) \Rightarrow \left(\forall \left(j: \mathbb{N}\right), \left(\left(1 \le j\right) \Rightarrow \left(\left(j \le \left(d\right) - \left(1\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.modeCoherence}\left(\left(\operatorname{Nat.cast}\left(j\right): \mathbb{Z}\right), \operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.concentrated}\left(v, \rho\right)\right) \le \operatorname{D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.modeCoherence}\left(\left(\operatorname{Nat.cast}\left(j\right): \mathbb{Z}\right), \rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.result` (`✓ std3`). ∎

*Resolves.* `Problems/stratton-hsieh-skrzypczyk-2025-bound-coherence-higher-dimensions` (proved) by `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"stratton-hsieh-skrzypczyk-2025-bound-coherence-higher-dimensions","declaration_gid":"D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk (2026). *Unspeakable coherence concentration*. DOI: [10.1103/fj8w-v1bb](https://doi.org/10.1103/fj8w-v1bb). URL: <https://arxiv.org/abs/2512.04255v1>.

*Commentary.*

Fix d at least three and put D = d − 1, z = 0 and l = D in the number basis. Take ρ to have every diagonal entry 1/d, the two entries ρ(l,z) = ρ(z,l) = 1/d, and all other entries zero. The indices z and l are distinct. First bound the output entry between l and z for an arbitrary allowed unitary v.

The total number observable is diagonal on pairs a, with diagonal entry a₁ + a₂. Commutation therefore gives v(a,b) = 0 whenever a₁ + a₂ differs from b₁ + b₂. For a fixed k, the portion of ρ ⊗ ρ from total number k to total number D + k has only two possible entries: from (z,k) to (l,k), and from (k,z) to (k,l), each with coefficient 1/d². Expanding the conjugation and partial trace consequently gives the output entry q = d⁻² ∑ₖ t(k), where t(k) = v((l,k),(l,k)) conjugate(v((z,k),(z,k))) + v((l,k),(k,l)) conjugate(v((z,k),(k,z))).

If k is neither endpoint, the two selected columns in each of the rows (l,k) and (z,k) are distinct. The sums of the squared moduli of the two selected entries in each row are at most one, because v is unitary. The triangle inequality and Cauchy–Schwarz then give |t(k)| ≤ 1.

At the endpoints the repeated entries must be combined. One has t(z) = (v((l,z),(l,z)) + v((l,z),(z,l))) conjugate(v((z,z),(z,z))) and t(l) = v((l,l),(l,l)) conjugate(v((z,l),(z,l)) + v((z,l),(l,z))). The columns indexed by (l,z) and (z,l) are orthonormal, so their sum has squared norm two. Thus the squared moduli of its coordinates at (l,z) and (z,l) sum to at most two. Each remaining diagonal factor has modulus at most one. Cauchy–Schwarz bounds the sum of the two selected moduli by two, and hence |t(z)| + |t(l)| ≤ 2.

There are d − 2 interior indices. Splitting the sum into the interior and the two endpoints, the triangle inequality gives |∑ₖ t(k)| ≤ (d − 2) + 2 = d. Multiplying by d⁻² proves |q| ≤ 1/d.

To verify positivity of ρ, let u have value one at z and l and zero elsewhere, and let f have value zero at those endpoints and one elsewhere. Then ρ = d⁻¹(uu† + diagonal(f)), a nonnegative real multiple of a sum of positive semidefinite matrices. Its d diagonal entries are 1/d, so its trace is one. The (l,z) entries of ρ times the number observable and of the number observable times ρ are respectively zero and D/d. Since D/d is nonzero, ρ is coherent. Its entry at (0,1) is zero, whereas every such entry of an equal-amplitude pure state is a product of two nonzero exponential amplitudes. The denominator square root is nonzero because d is positive. Thus ρ is not maximally coherent.

For a natural j with 1 ≤ j < D, the tensor product has no entry with total number difference j: each factor has number differences only zero, D and −D, so a positive sum smaller than D is impossible. In an output entry of difference j, the conservation condition forces the intermediate tensor entry to have that same total difference; it is therefore zero. Summing over the traced index proves that every lower positive output mode vanishes.

For any matrix x, its mode D consists of the single entry x(l,z). The conjugate transpose of this single-entry matrix times itself has the positive square root with sole entry |x(l,z)| at (z,z). Taking its trace shows that mode D has trace norm |x(l,z)|. For ρ this equals 1/d, and the bound on q proves the required comparison in mode D. For each smaller positive mode the output trace norm is zero and the input trace norm is nonnegative. These two cases cover every j from one through d minus one. Together with positivity, unit trace, coherence and nonmaximality, they establish the asserted existence for every d at least three.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.IsAllowedUnitary`
- Truth anchor: `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.IsMaximallyCoherent`
- Truth anchor: `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.concentrated`
- Truth anchor: `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.mode`
- Truth anchor: `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.modeCoherence`
- Truth anchor: `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.numberOp`
- Truth anchor: `D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
