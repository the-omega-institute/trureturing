# A coherence-vector and spectrum product bound

## Abstract

Every majorization upper bound of the coherence set has first component times largest eigenvalue at least one over the dimension.

**Definition 1.1 (Decreasing rearrangement).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.decreasingRearrangement}\left(x\right): \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right) = \operatorname{Function.comp}\left(x, \operatorname{Equiv.toFun}\left(\left(\operatorname{Tuple.sort}_{\operatorname{OrderDual}\left(\mathbb{R}\right)}\right)\left(x\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.decreasingRearrangement` (`✓ std3`).

*Citation.* Yanet Alvarez; Marcelo Losada; Mariela Portesi; Gustavo M Bosyk (2023). *Complementarity between quantum coherence and mixedness: a majorization approach*. DOI: [10.1088/1572-9494/acc92f](https://doi.org/10.1088/1572-9494/acc92f). URL: <https://ctp.itp.ac.cn/EN/PDF/10.1088/1572-9494/acc92f>.

*Commentary.*

Sorting in the order dual of the reals permutes the coordinates into decreasing order. The permutation is viewed as a function before composition with x. Applied to the squared-amplitude vector of a pure state, this is the ordered vector used in Section 2.2, Eqs. (9)–(11), PDF p. 3. The definition also applies to arbitrary real vectors, including the empty vector.

**Definition 1.2 (Averages over pure-state decompositions).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.coherenceSet}\left(\rho\right): \operatorname{Set}\left(\left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right)\right) = \{\left(u: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right) \mid \left(\exists \left(k: \mathbb{N}\right), \left(\exists \left(p: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\mathbb{R}\right)\right), \left(\exists \left(\psi: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.IsDecomposition}\left(\rho, k, p, \psi\right)\right) \land \left(u = \lambda \left(i: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\sum_{j: \operatorname{Fin}\left(k\right)} \left(\left(p\left(j\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.decreasingRearrangement}\left(\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.coherenceVector}\left(\psi\left(j\right)\right), i\right)\right)\right)\right)\right)\right)\right)\right)\right)\}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.coherenceSet` (`✓ std3`).

*Citation.* Yanet Alvarez; Marcelo Losada; Mariela Portesi; Gustavo M Bosyk (2023). *Complementarity between quantum coherence and mixedness: a majorization approach*. DOI: [10.1088/1572-9494/acc92f](https://doi.org/10.1088/1572-9494/acc92f). URL: <https://ctp.itp.ac.cn/EN/PDF/10.1088/1572-9494/acc92f>.

*Commentary.*

The set consists of all averages of decreasing pure-state coherence vectors over finite decompositions of ρ. In a decomposition, p is nonnegative and sums to one, every ψ j has squared norm one, and ρ is the sum of their rank-one density matrices weighted by the complex embeddings of p j. The coherence vector of ψ j has ith entry equal to the squared modulus of ψ j i. Thus this is Dᵖˢᵈ(ρ) from Section 2.2, Eqs. (9)–(11), PDF p. 3.

**Definition 1.3 (Majorization upper bounds of the coherence set).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(\nu: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.IsMajorizationUpperBound}\left(\rho, \nu\right)\right) \Leftrightarrow \left(\left(\operatorname{Antitone}\left(\nu\right)\right) \land \left(\left(\forall \left(i: \operatorname{Fin}\left(d\right)\right), \left(\left(0: \mathbb{R}\right) \le \nu\left(i\right)\right)\right) \land \left(\left(\sum_{i: \operatorname{Fin}\left(d\right)} \left(\nu\left(i\right)\right) = \left(1: \mathbb{R}\right)\right) \land \left(\forall \left(u: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(u \in \operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.coherenceSet}\left(\rho\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation.Majorizes}\left(\operatorname{List.ofFn}\left(\nu\right), \operatorname{List.ofFn}\left(\operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.decreasingRearrangement}\left(u\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.IsMajorizationUpperBound` (`✓ std3`).

*Citation.* Yanet Alvarez; Marcelo Losada; Mariela Portesi; Gustavo M Bosyk (2023). *Complementarity between quantum coherence and mixedness: a majorization approach*. DOI: [10.1088/1572-9494/acc92f](https://doi.org/10.1088/1572-9494/acc92f). URL: <https://ctp.itp.ac.cn/EN/PDF/10.1088/1572-9494/acc92f>.

*Commentary.*

An upper bound is a decreasing, nonnegative real vector with total mass one whose partial sums dominate those of the decreasing rearrangement of every member of the coherence set. Majorizes takes the dominating list first and also requires equality of the total sums. Section 2.2, Eq. (12), PDF pp. 3–4, defines ν(ρ) as the majorization supremum of Dᵖˢᵈ(ρ). The predicate requires only the upper-bound property and makes no leastness assertion.

**Definition 1.4 (The largest spectral value).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.maxEigenvalue}\left(\rho\right): \mathbb{R}\right) = \operatorname{dite}\left(\operatorname{Matrix.IsHermitian}\left(\rho\right), \lambda \left(h: \operatorname{Matrix.IsHermitian}\left(\rho\right)\right) \mapsto \left(\operatorname{D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability.aqGreatestEigenvalue}\left(h\right)\right), \operatorname{Function.const}\left(\neg \left(\operatorname{Matrix.IsHermitian}\left(\rho\right)\right), \left(0: \mathbb{R}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.maxEigenvalue` (`✓ std3`).

*Citation.* Yanet Alvarez; Marcelo Losada; Mariela Portesi; Gustavo M Bosyk (2023). *Complementarity between quantum coherence and mixedness: a majorization approach*. DOI: [10.1088/1572-9494/acc92f](https://doi.org/10.1088/1572-9494/acc92f). URL: <https://ctp.itp.ac.cn/EN/PDF/10.1088/1572-9494/acc92f>.

*Commentary.*

For a Hermitian matrix, take the real supremum of its finite set of eigenvalues. For a non-Hermitian matrix the value is defined to be zero. For a density matrix in positive dimension, this is the largest component λ₁(ρ) of the ordered spectrum in Section 2.3, PDF p. 4, and Section 3.4, Conjecture 5, Eq. (20), PDF p. 7.

**Theorem 1.5 (The product bound in every positive dimension).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(hd: 1 \le d\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Divergence.CoherenceL1RelativeEntropyBound.IsState}\left(\rho\right)\right) \Rightarrow \left(\forall \left(\nu: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.IsMajorizationUpperBound}\left(\rho, \nu\right)\right) \Rightarrow \left(\frac{\left(1: \mathbb{R}\right)}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)} \le \left(\nu\left(\operatorname{Fin.mk}\left(0, hd\right)\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.maxEigenvalue}\left(\rho\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/alvarez-losada-portesi-bosyk-2023-coherence-spectrum-product-bound` (proved) by `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alvarez-losada-portesi-bosyk-2023-coherence-spectrum-product-bound","declaration_gid":"D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yanet Alvarez; Marcelo Losada; Mariela Portesi; Gustavo M Bosyk (2023). *Complementarity between quantum coherence and mixedness: a majorization approach*. DOI: [10.1088/1572-9494/acc92f](https://doi.org/10.1088/1572-9494/acc92f). URL: <https://ctp.itp.ac.cn/EN/PDF/10.1088/1572-9494/acc92f>.

*Commentary.*

Let d be positive, let ρ be a positive semidefinite complex matrix of trace one, and let ν be any majorization upper bound of its coherence set. Set a = √ρ and p j = Re(ρ j j). Positivity gives p j ≥ 0, and the trace condition gives Σⱼ p j = 1. The matrix a is Hermitian and a² = ρ, so the squared norm of its jth column is p j. If p j is nonzero, divide that column by the complex embedding of √(p j) to obtain ψ j. If p j is zero, every entry of that column vanishes; take ψ j to be the coordinate vector at the index ⟨0, hd⟩ instead. In both cases ψ j has squared norm one and p j |ψ j i|² = |a i j|² for every i and j. Multiplying the rank-one matrices by the complex embeddings of p j and summing gives aa* = ρ. Thus these d weighted vectors form a pure-state decomposition, including the zero weights.

For any real vector x, every coordinate is at most the first coordinate of its decreasing rearrangement. This follows by monotonicity of the sorted vector in the order dual, comparing index zero with the inverse permutation's index of the chosen coordinate. Now let u i = Σⱼ p j decreasingRearrangement(coherenceVector(ψ j)) i. The decomposition places u in the coherence set. Majorization at partial-sum length one bounds the first coordinate of decreasingRearrangement u by ν ⟨0, hd⟩. For each column, (Re(a j j))² ≤ |a j j|² = p j |ψ j j|². Nonnegativity of p j and the rearrangement comparison bound their sum by u ⟨0, hd⟩, which is at most the first coordinate of decreasingRearrangement u. Consequently s = Σⱼ (Re(a j j))² satisfies s ≤ ν ⟨0, hd⟩.

Cauchy–Schwarz applied to the d real diagonal entries gives t² ≤ (d : ℝ) s, where t = Re(trace a). The trace formula for the continuous functional calculus expresses t as Σᵢ √λᵢ, with λᵢ the Hermitian eigenvalues of ρ. Positivity makes these eigenvalues nonnegative, and their sum is one.

Write L = maxEigenvalue ρ. Every λᵢ is at most L because L is the supremum of their finite range. Positive dimension supplies an eigenvalue, so L ≥ 0. If L were not positive, all the nonnegative eigenvalues would be zero, contradicting their sum being one. Thus L > 0. For each i, λᵢ = √λᵢ √λᵢ ≤ √λᵢ √L. Summing gives 1 ≤ t √L, hence 1/√L ≤ t.

The last inequality makes t nonnegative. Squaring it and multiplying by L gives 1 ≤ L t². Combine the diagonal estimate and the first-coordinate bound to obtain 1 ≤ L t² ≤ L ((d : ℝ) s) ≤ L ((d : ℝ) ν ⟨0, hd⟩). Since the real embedding of d is positive, division by it yields the stated product inequality. In particular, the majorization supremum ν(ρ) of Eq. (12) is an upper bound, so this establishes Conjecture 5, Eq. (20), in Section 3.4, PDF pp. 6–7, without requiring a construction of that supremum.

## References

- Truth anchor: `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.IsMajorizationUpperBound`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.coherenceSet`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.decreasingRearrangement`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.maxEigenvalue`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.result`
- Dependency: [D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality](CoherenceAssistanceRoofEquality.md)
- Dependency: [D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation](../Matrix/LinDTIMajorizationRefutation.md)
- Dependency: [D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability](../Measurement/AdvantageQuantumNonSimulability.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../Resource/LogDet/PathSpectralClassical.md)
