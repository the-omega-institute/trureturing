# The geometric measure of the flip-conjugate symmetric subspaces

## Abstract

The geometric measure is constant on each flip-conjugate symmetric subspace in every local dimension at least two.

Use the computational basis of three copies of ℂᵈ. Coordinates are indexed by Fin d, with the threefold index associated as Fin d × (Fin d × Fin d). A typed expression (d : ℝ) denotes the natural-to-real cast, and (r : ℂ), for real r, denotes the real-to-complex cast. Complex conjugation is written with an overline. All norms of coordinate vectors are Euclidean.

**Definition 1.1 (Three-qudit coordinate vectors).**

$$\forall (d: \mathbb{N}), (\operatorname{State}\left(d\right) = ((\operatorname{Fin}\left(d\right) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))) \to \mathbb{C}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

State d is the complex vector space of functions on the threefold computational basis. This coordinate description is defined for every natural dimension d.

**Definition 1.2 (Euclidean normalization).**

$$\forall (iota: Type*), ([\operatorname{Fintype}\left(iota\right)] \forall (v: (iota \to \mathbb{C})), ((\operatorname{UnitVector}\left(v\right)) \Leftrightarrow (\left\lVert \operatorname{WithLp}.\operatorname{toLp}\left(2, v\right) \right\rVert = 1)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.UnitVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite index type and any complex coordinate vector, UnitVector means Euclidean norm one. The map WithLp.toLp with exponent two equips the same coordinates with their Euclidean norm.

**Definition 1.3 (The dimension-dependent complex coefficient).**

$$\forall (d: \mathbb{N}), (\operatorname{z}\left(d\right) = \frac{(1: \mathbb{C}) + \operatorname{Complex}.\operatorname{I} \cdot (\sqrt{\frac{(d: \mathbb{R}) + 1}{(d: \mathbb{R}) - 1}}: \mathbb{C})}{(2: \mathbb{C})})$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.z` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

The coefficient z_d is the one used by Denker, Imai and Gühne in the flip-conjugate basis. The square root and the quotient inside it are real; only their square root is then included into ℂ.

**Definition 1.4 (The flip-conjugate basis vectors).**

$$\forall (d: \mathbb{N}), (\forall (n: \operatorname{Fin}\left(d\right)), (\forall (i: \operatorname{Fin}\left(d\right)), (\forall (j: \operatorname{Fin}\left(d\right)), (\forall (k: \operatorname{Fin}\left(d\right)), (\varphi\left(d, n, (i, (j, k))\right) = \frac{\overline{\operatorname{z}\left(d\right)} \cdot (\begin{cases}(1: \mathbb{C})&(j = n) \land (k = i)\\(0: \mathbb{C})&\text{otherwise}\end{cases}) + \operatorname{z}\left(d\right) \cdot (\begin{cases}(1: \mathbb{C})&(j = i) \land (k = n)\\(0: \mathbb{C})&\text{otherwise}\end{cases})}{(\sqrt{(d: \mathbb{R}) + 1}: \mathbb{C})})))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.φ` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

The coordinate formula is the computational-basis expansion of φ_n = (conj(z_d) ∑ᵢ |i n i⟩ + z_d ∑ᵢ |i i n⟩)/√(d+1). For d at least two these vectors form an orthonormal family.

**Definition 1.5 (The conjugate basis vectors).**

$$\forall (d: \mathbb{N}), (\forall (n: \operatorname{Fin}\left(d\right)), (\forall (i: \operatorname{Fin}\left(d\right)), (\forall (j: \operatorname{Fin}\left(d\right)), (\forall (k: \operatorname{Fin}\left(d\right)), (\overline{\varphi}\left(d, n, (i, (j, k))\right) = \frac{\operatorname{z}\left(d\right) \cdot (\begin{cases}(1: \mathbb{C})&(j = n) \land (k = i)\\(0: \mathbb{C})&\text{otherwise}\end{cases}) + \overline{\operatorname{z}\left(d\right)} \cdot (\begin{cases}(1: \mathbb{C})&(j = i) \land (k = n)\\(0: \mathbb{C})&\text{otherwise}\end{cases})}{(\sqrt{(d: \mathbb{R}) + 1}: \mathbb{C})})))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.φbar` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

Interchanging z_d and its conjugate gives the coordinatewise conjugate of φ_n, with the same real normalization factor.

**Definition 1.6 (The flip-conjugate symmetric subspace).**

$$\forall (d: \mathbb{N}), (\left(H_{I}\right)\left(d\right) = \operatorname{Submodule}.\operatorname{span}\left(\mathbb{C}, \operatorname{Set}.\operatorname{range}\left(\varphi\left(d\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.H_I` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

The complex span of the vectors φ_n is the flip-conjugate symmetric subspace H_I of the source. For d at least two it has dimension d.

**Definition 1.7 (The conjugate symmetric subspace).**

$$\forall (d: \mathbb{N}), (\left(H_{\overline{I}}\right)\left(d\right) = \operatorname{Submodule}.\operatorname{span}\left(\mathbb{C}, \operatorname{Set}.\operatorname{range}\left(\overline{\varphi}\left(d\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.H_Ibar` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

The complex span of the vectors φbar_n is the conjugate subspace H_Ibar of the source. Coordinatewise complex conjugation interchanges the two subspaces.

**Definition 1.8 (The amplitude against a product vector).**

$$\forall (d: \mathbb{N}), (\forall (a: (\operatorname{Fin}\left(d\right) \to \mathbb{C})), (\forall (b: (\operatorname{Fin}\left(d\right) \to \mathbb{C})), (\forall (c: (\operatorname{Fin}\left(d\right) \to \mathbb{C})), (\forall (\psi: \operatorname{State}\left(d\right)), (\operatorname{overlap}\left(a, b, c, \psi\right) = \sum_{(i: \operatorname{Fin}\left(d\right))} (\sum_{(j: \operatorname{Fin}\left(d\right))} (\sum_{(k: \operatorname{Fin}\left(d\right))} (\overline{a\left(i\right)} \cdot \overline{b\left(j\right)} \cdot \overline{c\left(k\right)} \cdot \psi\left((i, (j, k))\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.overlap` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

For arbitrary local coordinate vectors a, b and c, the overlap is ⟨a ⊗ b ⊗ c, ψ⟩. Each local coordinate in the first argument is conjugated; normalization is imposed separately when optimizing this amplitude.

**Definition 1.9 (Squared overlaps with unit product vectors).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \operatorname{State}\left(d\right)), (\operatorname{overlapSet}\left(\psi\right) = \{t: \mathbb{R} \mid \exists (a: (\operatorname{Fin}\left(d\right) \to \mathbb{C})), (\exists (b: (\operatorname{Fin}\left(d\right) \to \mathbb{C})), (\exists (c: (\operatorname{Fin}\left(d\right) \to \mathbb{C})), ((\operatorname{UnitVector}\left(a\right)) \land ((\operatorname{UnitVector}\left(b\right)) \land ((\operatorname{UnitVector}\left(c\right)) \land (t = (\left\lVert \operatorname{overlap}\left(a, b, c, \psi\right) \right\rVert)^{2}))))))\}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.overlapSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

The set contains precisely the squared absolute overlaps with three normalized local vectors. The definition allows arbitrary ψ, including vectors outside the two symmetric subspaces.

**Definition 1.10 (The geometric measure of entanglement).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \operatorname{State}\left(d\right)), (\operatorname{G}\left(\psi\right) = 1 - \operatorname{sSup}\left(\operatorname{overlapSet}\left(\psi\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.G` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

The geometric measure is one minus the supremum of the squared product overlaps. For a unit vector in a positive finite dimension this supremum is a maximum, so this is the geometric measure defined in the source.

**Definition 1.11 (The proposed maximal squared product overlap).**

$$\forall (d: \mathbb{N}), (\operatorname{sharpValue}\left(d\right) = \frac{((d: \mathbb{R}))^{2}}{(((d: \mathbb{R}))^{2} - 1) \cdot ((d: \mathbb{R}) + 1)})$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.sharpValue` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

The dimension-dependent scalar is the squared product overlap proposed in the source's conjecture. Its denominator is positive whenever d is at least two.

**Definition 1.12 (The constant geometric measure in both subspaces).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (d: \mathbb{N}), ((2 \le d) \Rightarrow (\forall (\psi: \operatorname{State}\left(d\right)), ((\operatorname{UnitVector}\left(\psi\right)) \Rightarrow (((\psi \in \left(H_{I}\right)\left(d\right)) \lor (\psi \in \left(H_{\overline{I}}\right)\left(d\right))) \Rightarrow (\operatorname{G}\left(\psi\right) = 1 - \operatorname{sharpValue}\left(d\right)))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.claim` (`✓ std3`).

*Citation.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

For every natural d at least two and every normalized state in either H_I or H_Ibar, the geometric measure equals 1 − d²/((d²−1)(d+1)). This is the conjecture in the source's appendix on the flip-conjugate symmetric subspace, with both conjugate subspaces included.

**Theorem 1.13 (The sharp bound and its attaining product vector).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.result` (`✓ std3`). ∎

*Resolves.* `Problems/denker-imai-guhne-2025-flip-conjugate-geometric-measure` (proved) by `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"denker-imai-guhne-2025-flip-conjugate-geometric-measure","declaration_gid":"D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sophia Denker; Satoya Imai; Otfried Gühne (2025). *Chiral Symmetries and Multiparticle Entanglement*. URL: <https://arxiv.org/abs/2506.15609v1>.

*Commentary.*

Fix d ≥ 2. The vectors φ_n are orthonormal. If ψ = ∑ₙ α_n φ_n is unit, then α is unit and extends to the first column of a unitary U. The local unitary conj(U) ⊗ U ⊗ U sends φ_0 to ψ, as in the source's local-unitary proposition. Local unitaries permute unit product vectors and preserve overlaps, so it suffices to compute the maximum for φ_0. Complex conjugation gives the same maximum for H_Ibar.

Write z = z_d and, for unit b and c, set χ_i = conj(z) conj(b_0) conj(c_i) + z conj(c_0) conj(b_i). Then √(d+1) ⟨a ⊗ b ⊗ c, φ_0⟩ = ⟨a, χ⟩. The maximum of |⟨a, χ⟩|² over unit a equals ‖χ‖², attained by a = χ/‖χ‖ when χ is nonzero; for χ = 0 every unit a attains it. Thus the maximal squared product overlap is the maximum of ‖χ‖²/(d+1).

Put x = |b_0|² and y = |c_0|², so x,y ∈ [0,1]. The coefficient identities are |z|² = d/(2(d−1)) and Re(z²) = −1/(2(d−1)). Cauchy–Schwarz on the remaining coordinates, followed by 2√(x(1−x)y(1−y)) ≤ x(1−x) + y(1−y), gives ‖χ‖² ≤ F(x,y)/(d−1), where F(x,y) = d(x+y) − (d/2)(x²+y²) − xy. The identity F(x,y) = d²/(d+1) − (d+1)(x+y−2d/(d+1))²/4 − (d−1)(x−y)²/4 shows that its maximum on the unit square is d²/(d+1), at x = y = d/(d+1). Dividing by (d−1)(d+1) gives the upper bound d²/((d²−1)(d+1)) for the squared product overlap.

For attainment, take r = √(d/(d+1)), t = √(1/(d+1)), ρ = conj(z)/z, b = r e_0 + t e_1 and c = r e_0 + ρ t e_1. These are unit vectors since |ρ| = 1. They have x = y = d/(d+1) and χ = r² e_0 + 2zrt e_1, so ‖χ‖² = d²/(d²−1). Choosing a = χ/‖χ‖ attains the upper bound. Transport by the local unitaries, and then by conjugation for H_Ibar, yields the asserted constant geometric measure for every unit state in either subspace.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.G`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.H_I`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.H_Ibar`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.State`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.UnitVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.overlap`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.overlapSet`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.sharpValue`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.z`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.φ`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.φbar`
