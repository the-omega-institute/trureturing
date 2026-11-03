# The three-distinguishability product conjecture fails

## Abstract

Three orthogonal pure states exclude every labelling of the product ansatz.

**Definition 1.1 (The three-distinguishability region).**

$$\forall \left(p: \left(\operatorname{Fin}\left(4\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation.InRegion}\left(p\right)\right) \Leftrightarrow \left(\left(\left(\forall \left(k: \operatorname{Fin}\left(4\right)\right), \left(\left(0: \mathbb{R}\right) \le p\left(k\right)\right)\right) \land \left(\sum_{\left(k: \operatorname{Fin}\left(4\right)\right)} \left(p\left(k\right)\right) = \left(1: \mathbb{R}\right)\right)\right) \land \left(\exists \left(\rho: \left(\operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(3\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\left(i\right)\right)\right) \land \left(\operatorname{Matrix.trace}\left(\rho\left(i\right)\right) = \left(1: \mathbb{C}\right)\right)\right)\right) \land \left(\left(\forall \left(i: \operatorname{Fin}\left(3\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(3\right)\right), \left(\left(i \ne j\right) \Rightarrow \left(\left(\rho\left(i\right)\right) \cdot \left(\rho\left(j\right)\right) = \left(0: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)\right)\right)\right)\right)\right) \land \left(\forall \left(i: \operatorname{Fin}\left(3\right)\right), \left(\forall \left(k: \operatorname{Fin}\left(4\right)\right), \left(\operatorname{Complex.re}\left(\operatorname{Matrix.diag}\left(\rho\left(i\right), k\right)\right) = p\left(k\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.InRegion` (`✓ std3`).

*Citation.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Commentary.*

A real function p on Fin 4 lies in the region when it belongs to the standard simplex and there are three complex 4 by 4 positive semidefinite matrices of trace one whose pairwise products vanish and whose diagonal real parts all equal p. This is the source's M-distinguishability definition, Distinguishability.tex lines 147–149 and 236–241, specialized to d = 4 and M = 3.

**Definition 1.2 (The two-parameter product form).**

$$\forall \left(f: \left(\operatorname{Fin}\left(4\right)\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\forall \left(p: \left(\operatorname{Fin}\left(4\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation.ProductForm}\left(f, p\right)\right) \Leftrightarrow \left(\exists \left(a: \mathbb{R}\right), \left(\exists \left(b: \mathbb{R}\right), \left(\left(\left(\left(0: \mathbb{R}\right) \le a\right) \land \left(\left(a \le \left(1: \mathbb{R}\right)\right) \land \left(\left(\left(0: \mathbb{R}\right) \le b\right) \land \left(b \le \left(1: \mathbb{R}\right)\right)\right)\right)\right) \land \left(p = \left(\left(\left(\left(\left(a\right) \cdot \left(b\right)\right) \cdot \left(f\left(\left(0: \operatorname{Fin}\left(4\right)\right)\right)\right)\right) + \left(\left(\left(a\right) \cdot \left(\left(\left(1: \mathbb{R}\right)\right) - \left(b\right)\right)\right) \cdot \left(f\left(\left(1: \operatorname{Fin}\left(4\right)\right)\right)\right)\right)\right) + \left(\left(\left(\left(\left(1: \mathbb{R}\right)\right) - \left(a\right)\right) \cdot \left(b\right)\right) \cdot \left(f\left(\left(2: \operatorname{Fin}\left(4\right)\right)\right)\right)\right)\right) + \left(\left(\left(\left(\left(1: \mathbb{R}\right)\right) - \left(a\right)\right) \cdot \left(\left(\left(1: \mathbb{R}\right)\right) - \left(b\right)\right)\right) \cdot \left(f\left(\left(3: \operatorname{Fin}\left(4\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.ProductForm` (`✓ std3`).

*Citation.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Commentary.*

ProductForm f p means that p is the convex combination of f 0, f 1, f 2 and f 3 with weights ab, a(1−b), (1−a)b and (1−a)(1−b), for real a and b in the unit interval. The four functions f are supplied separately so that the definition can express any labelling of the face centres. This is equation (30) of the source, Distinguishability.tex lines 462–467.

**Definition 1.3 (The labelled product conjecture).**

$$\left(\operatorname{D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation.claim}\right) \Leftrightarrow \left(\exists \left(\sigma: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(4\right)\right)\right), \left(\forall \left(p: \left(\operatorname{Fin}\left(4\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation.InRegion}\left(p\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation.ProductForm}\left(\left(\lambda \left(i: \operatorname{Fin}\left(4\right)\right) \mapsto \operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.target}\left(\sigma\left(i\right)\right)\right), p\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.claim` (`✓ std3`).

*Citation.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Commentary.*

The conjecture asks for one permutation σ of Fin 4 such that every p in the three-distinguishability region has the product form built from the relabelled face centres i ↦ target (σ i). The permutation is existential because the source presents the four face centres with a labelling convention, while the mathematical assertion concerns some labelling.

**Theorem 1.4 (A counterexample to every labelling).**

$$\neg \left(\exists \left(\sigma: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(4\right)\right)\right), \left(\forall \left(p: \left(\operatorname{Fin}\left(4\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation.InRegion}\left(p\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation.ProductForm}\left(\left(\lambda \left(i: \operatorname{Fin}\left(4\right)\right) \mapsto \operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.target}\left(\sigma\left(i\right)\right)\right), p\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/korzekwa-et-al-2019-three-distinguishability-product-refutation` (refuted) by `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"korzekwa-et-al-2019-three-distinguishability-product-refutation","declaration_gid":"D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Commentary.*

Let r = √5 and let p on Fin 4 have coordinates ((5 − r)/10, (5 − r)/20, (5 − r)/10, (r − 1)/4). The radical bounds 2 < r < 9/4 prove that p has nonnegative coordinates, and direct summation proves that p belongs to the standard simplex.

Set ζ = exp((π/5) i) and use the three phase rows in the construction. The identity conj ζ · ζ = 1 gives unit phases, while ζ⁵ = −1 and the quadratic relation ζ² = ((1 + √5)/2)ζ − 1 yield the powers ζ³, ζ⁴, ζ⁷ and ζ⁹ and the conjugate of ζ. Substitution into the weighted sums proves that the three weighted frame vectors are pairwise orthogonal.

The diagonal calculation gives each constructed vector xᵢ the coordinate identity xᵢ k · conj(xᵢ k) = p k. Rank-one density matrices built from the three vectors therefore have trace one, are positive semidefinite, have pairwise zero products by orthogonality, and share the diagonal p. Thus p lies in InRegion.

For any permutation σ, a product-form representation of p implies the equal-product identity (1 − 3 p (σ 0))(1 − 3 p (σ 3)) = (1 − 3 p (σ 1))(1 − 3 p (σ 2)). The four-element involutive pairing argument transfers this identity to one of the three pairings of the values 1 − 3 p k: (1 − 3 p 0)(1 − 3 p 1) = (1 − 3 p 2)(1 − 3 p 3), (1 − 3 p 0)(1 − 3 p 2) = (1 − 3 p 1)(1 − 3 p 3), or (1 − 3 p 0)(1 − 3 p 3) = (1 − 3 p 1)(1 − 3 p 2).

Substituting the four coordinates of p and using (√5)² = 5 shows that all three pairing equalities are false. Hence p has no ProductForm representation for any permutation σ. Applying the asserted claim to p and its InRegion witness gives this impossible product representation, so the claim is false.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.InRegion`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.ProductForm`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.result`
- Dependency: [D5/S0/Carrier/GoldenRatio](../../../S0/Carrier/GoldenRatio.md)
- Dependency: [D5/S3/Analytic/Adelic/FiniteToroidalFrameReconstruction](../../Analytic/Adelic/FiniteToroidalFrameReconstruction.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](../../Combinatorics/PerfectMatchings/FiniteBandSwitch.md)
- Dependency: [D5/S3/Observer/WindowRegister](../../Observer/WindowRegister.md)
- Dependency: [D5/S3/Quantum/Dynamics/PositivePauliClockOrder](../Dynamics/PositivePauliClockOrder.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/QuantumBounds/RebitExclusionDistance](../../QuantumBounds/RebitExclusionDistance.md)
