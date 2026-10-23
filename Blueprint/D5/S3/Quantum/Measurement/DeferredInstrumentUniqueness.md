# Uniqueness of the upper-boundary deferred-measurement instrument

## Abstract

The upper-boundary joint instrument of a noisy sharp meter and a depolarizing channel is unique.

**Definition 1.1 (The sharp meter).**

$$\forall (d : \mathbb{N}), \forall (U : \operatorname{Matrix}.\operatorname{unitaryGroup}\left(Fin\left(d\right), \mathbb{C}\right)), \forall (x : Fin\left(d\right)), Q\left(U, x\right) = (((U : Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)) \cdot \operatorname{Matrix}.\operatorname{single}\left(x, x, (1 : \mathbb{C})\right)) \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left((U : Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right))\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.Q` (`✓ std3`).

*Citation.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

The columns of U form the orthonormal basis of the sharp meter. Its x-th effect is the conjugate of the standard rank-one projection. This is the sharp meter underlying Eq. (eq:QsPt).

**Definition 1.2 (The noisy meter).**

$$\forall (d : \mathbb{N}), \forall (U : \operatorname{Matrix}.\operatorname{unitaryGroup}\left(Fin\left(d\right), \mathbb{C}\right)), \forall (s : \mathbb{R}), \forall (x : Fin\left(d\right)), Qs\left(U, s, x\right) = (((\operatorname{Complex}.\operatorname{ofReal}\left(s\right) : \mathbb{C}) \cdot Q\left(U, x\right)) + ((\operatorname{Complex}.\operatorname{ofReal}\left(\frac{(1 - s)}{(\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R})}\right) : \mathbb{C}) \cdot (1 : Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.Qs` (`✓ std3`).

*Citation.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

Equation (eq:QsPt) mixes each sharp effect with the uniform effect. The definition is a matrix formula for every real s; its use as a meter is subject to positivity. Every displayed cast specifies its target field.

**Definition 1.3 (The depolarizing map).**

$$\forall (d : \mathbb{N}), \forall (t : \mathbb{R}), \forall (rho : Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)), It\left(t, rho\right) = (((\operatorname{Complex}.\operatorname{ofReal}\left(t\right) : \mathbb{C}) \cdot rho) + (((\operatorname{Complex}.\operatorname{ofReal}\left(\frac{(1 - t)}{(\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R})}\right) : \mathbb{C}) \cdot \operatorname{Matrix}.\operatorname{trace}\left(rho\right)) \cdot (1 : Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.It` (`✓ std3`).

*Citation.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

It is the depolarizing channel depolarized id (1 - t) from the frozen TracePreservingEigenvalueBound. Its action is specified on every complex matrix, without a positivity or trace-one restriction on the argument. The formula is t ρ + (1 - t)/d · tr(ρ) 1; the trace factor is complex, while the noise coefficient is formed in ℝ before being cast to ℂ.

**Definition 1.4 (The upper-boundary noise).**

$$\forall (d : \mathbb{N}), \forall (t : \mathbb{R}), sMax\left(d, t\right) = \frac{(((((\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R}))^{2} - 2) \cdot (1 - t)) + (2 \cdot \sqrt{((((1 - ((\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R}))^{2}) \cdot (t)^{2}) + ((((\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R}))^{2} - 2) \cdot t)) + 1)}))}{((\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R}))^{2}}$$

*Formalization.* `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.sMax` (`✓ std3`).

*Citation.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

Solving the upper equality in Eq. (eq:QI_comp_neg) for s gives this expression. The compatibility theorem uses d ≥ 2 and −1/(d²−1) ≤ t ≤ 1. The real-valued definition itself is total and imposes none of these restrictions.

**Definition 1.5 (The second square-root coefficient).**

$$\forall (d : \mathbb{N}), \forall (t : \mathbb{R}), a2\left(d, t\right) = \frac{(\sqrt{((t \cdot (((\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R}))^{2} - 1)) + 1)} - \sqrt{(1 - t)})}{(\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R})}$$

*Formalization.* `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.a2` (`✓ std3`).

*Citation.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

This is the k = 2 coefficient in Eq. (eq:ab_bis), with √(d²) replaced by d for a natural dimension. All arithmetic inside the square roots and the quotient takes place in ℝ.

**Definition 1.6 (The noise square root).**

$$\forall (t : \mathbb{R}), b\left(t\right) = \sqrt{(1 - t)}$$

*Formalization.* `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.b` (`✓ std3`).

*Citation.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

The coefficient b in Eq. (eq:ab_bis) is the nonnegative real square root of 1 − t. As a real square-root expression it is defined for every real t.

**Definition 1.7 (The boundary instrument).**

$$\forall (d : \mathbb{N}), \forall (U : \operatorname{Matrix}.\operatorname{unitaryGroup}\left(Fin\left(d\right), \mathbb{C}\right)), \forall (t : \mathbb{R}), \forall (x : Fin\left(d\right)), \forall (rho : Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)), Itilde\left(U, t, x, rho\right) = (\frac{(1 : \mathbb{C})}{(\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{C})} \cdot (((((\operatorname{Complex}.\operatorname{ofReal}\left((b\left(t\right))^{2}\right) : \mathbb{C}) \cdot \operatorname{Matrix}.\operatorname{trace}\left((rho \cdot Q\left(U, x\right))\right)) \cdot (1 : Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right))) + ((\operatorname{Complex}.\operatorname{ofReal}\left((a2\left(d, t\right) \cdot b\left(t\right))\right) : \mathbb{C}) \cdot ((rho \cdot Q\left(U, x\right)) + (Q\left(U, x\right) \cdot rho)))) + ((\operatorname{Complex}.\operatorname{ofReal}\left((a2\left(d, t\right))^{2}\right) : \mathbb{C}) \cdot rho)))$$

*Formalization.* `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.Itilde` (`✓ std3`).

*Citation.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

Equation (eq:tildeJ) gives this outcome map. The three terms respectively contain the Born trace, the symmetrized product with the sharp effect, and the input matrix. Each real coefficient is cast to ℂ after its indicated product or square is formed, and the outer denominator is the direct cast of d to ℂ.

**Definition 1.8 (The full uniqueness assertion).**

$$claim = (\forall (d : \mathbb{N}), (2 \leq d) \to (\forall (U : \operatorname{Matrix}.\operatorname{unitaryGroup}\left(Fin\left(d\right), \mathbb{C}\right)), \forall (t : \mathbb{R}), (\frac{-1}{(((\operatorname{Nat}.\operatorname{cast}\left(d\right) : \mathbb{R}))^{2} - 1)} \leq t) \to ((t \leq 1) \to (\forall (J : Fin\left(d\right) \to MatrixMap\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)), ((\forall (x : Fin\left(d\right)), \operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(J\left(x\right)\right)) \land (((\sum_{x : Fin\left(d\right)} J\left(x\right)) = It\left(t\right)) \land (\forall (x : Fin\left(d\right)), \forall (rho : Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)), \operatorname{Matrix}.\operatorname{trace}\left(J\left(x\right)\left(rho\right)\right) = \operatorname{Matrix}.\operatorname{trace}\left((rho \cdot Qs\left(U, sMax\left(d, t\right), x\right))\right)))) \iff (\forall (x : Fin\left(d\right)), J\left(x\right) = Itilde\left(U, t, x\right))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.claim` (`✓ std3`).

*Citation.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

The question following the proof of the W-covariant upper-boundary result asks whether there exist other, necessarily noncovariant, joint instruments. This proposition states uniqueness among all completely positive outcome maps in every dimension d ≥ 2 and throughout the closed upper boundary. The two marginal conditions are those of Eq. (eq:joint_J), with the meter condition written as a trace identity on every complex matrix. The biconditional also asserts that the displayed instrument has these marginals; it assumes no covariance of a competitor.

**Theorem 1.9 (Uniqueness without a covariance assumption).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.result` (`✓ std3`). ∎

*Resolves.* `Problems/carmeli-heinosaari-toigo-2025-upper-boundary-instrument-uniqueness` (proved) by `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"carmeli-heinosaari-toigo-2025-upper-boundary-instrument-uniqueness","declaration_gid":"D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Claudio Carmeli; Teiko Heinosaari; Alessandro Toigo (2025). *Postponing the choice: advantage of deferred measurements in quantum information processing*. DOI: [10.1088/1367-2630/adf87c](https://doi.org/10.1088/1367-2630/adf87c). URL: <https://arxiv.org/abs/2502.19871v1>.

*Commentary.*

Work first in the standard basis, and put α = a₂(d,t), β = b(t), γ = √(t(d²−1)+1) = β+dα and κ = α+β. Write eⱼᵢ for the tensor basis with output index j and input index i, Ω = ∑ᵢ eᵢᵢ, and vₓ = αΩ+βeₓₓ. The Choi matrix of the displayed outcome map is Aₓ = (vₓvₓ* + β²∑ⱼ≠ₓ eⱼₓeⱼₓ*)/d. These matrices are positive semidefinite, sum to B = tΩΩ*+(β²/d)1, and have output partial traces Qs(1,sMax(d,t),x). Thus they give the instrument described in Eq. (eq:tildeJ) of Carmeli, Heinosaari and Toigo.

For −1/(d²−1) < t < 1, the quadratic certificate on a complex array w is qₓ(w) = ∑ᵢ≠ₓ ∑ⱼ≠ᵢ |wⱼᵢ|² + (κ/β)(∑ᵢ |wᵢᵢ|² − (α/γ)|∑ᵢ wᵢᵢ|²) − |wₓₓ|². Here β, γ and κ are positive. Subtracting (wₓₓ/κ)vₓ from the diagonal reduces its diagonal part to κ/β times ∑ᵢ |zᵢ|² − (α/γ)|∑ᵢ zᵢ|². If α ≥ 0, Cauchy–Schwarz bounds this last expression below by (β/γ)∑ᵢ |zᵢ|²; if α < 0, it bounds itself below by ∑ᵢ |zᵢ|². Consequently qₓ is nonnegative and vanishes exactly when w lies in Sₓ = span{vₓ} ⊕ span{eⱼₓ : j ≠ x}.

For a competitor write Cₓ = Bₓ*Bₓ. The fixed channel and trace marginals make the sum of qₓ over all conjugate Gram rows of all Bₓ equal to zero. Nonnegativity makes each term zero, so every such row belongs to Sₓ and Cₓ is supported there. Set Hₓ = Cₓ−Aₓ. The channel condition gives ∑ₓHₓ = 0. For j ≠ x, eⱼₓ is orthogonal to Sᵧ whenever y ≠ x, so this sum forces the corresponding rows and columns of Hₓ to vanish. The remaining Hermitian difference is a multiple of vₓvₓ*. Its output partial trace is zero by the trace condition, and vₓ ≠ 0, so that multiple is zero. Choi injectivity then identifies every outcome map.

At t = −1/(d²−1), γ = 0 and BΩ = 0. Positivity and the channel sum force CₓΩ = 0, so each conjugate Gram row has zero diagonal sum. On this subspace the certificate is ∑ᵢ≠ₓ ∑ⱼ≠ᵢ |wⱼᵢ|² + (κ/β)∑ᵢ |wᵢᵢ|² − |wₓₓ|². Subtracting its component along vₓ proves nonnegativity with the same zero space Sₓ, and the same elimination applies. At t = 1, B = ΩΩ* has rank one. Each positive Cₓ is therefore a nonnegative multiple of ΩΩ*, and the trace marginal fixes that multiple as 1/d, which is Aₓ.

For a general unitary U, the transformed outcome map ρ ↦ U*Jₓ(UρU*)U is completely positive and has the standard-basis marginals. Unitary invariance of the depolarizing map and cyclicity of the trace preserve the two marginal conditions. Standard-basis uniqueness and conjugation back by U give Itilde(U,t,x). Conversely the positive Choi formula and its unitary transport establish complete positivity of Itilde, while its channel sum and trace identity give both required marginals. This proves the biconditional, including both endpoints.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.It`
- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.Itilde`
- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.Q`
- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.Qs`
- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.a2`
- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.b`
- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.result`
- Truth anchor: `D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.sMax`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound](../QuantumChannels/TracePreservingEigenvalueBound.md)
