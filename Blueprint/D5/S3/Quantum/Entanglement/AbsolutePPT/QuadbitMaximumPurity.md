# Exact quadbit–quadbit APPT maximum purity

## Abstract

The literal 4-by-4 APPT purity maximum is 2/27 and is attained by the explicit diagonal spectrum (1/6,1/18,...,1/18).

**Theorem 1.1 (Unit dot product gives real squared norm one).**

$$\forall (I:Type), [Fintype\left(I\right)] \forall (v:I\to \mathbb{C}), (dotProduct\left(star\left(v\right), v\right)=1)\Rightarrow \sum_{i:I} norm\left(v\left(i\right)\right)^{2}=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.norm_of_dot_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

For every finite index type I and complex vector v, star v dot v = 1 implies that the sum of squared coordinate norms is the real number one. This converts unitary preservation of the complex dot product to the normalization used by the separable rank-one ray.

**Theorem 1.2 (Separable matrices have positive partial transpose).**

$$\forall (m:Nat), \forall (n:Nat), \forall (W:Matrix\left((Fin\left(m\right)\times Fin\left(n\right)), (Fin\left(m\right)\times Fin\left(n\right)), \mathbb{C}\right)), (separableCone\left(W\right))\Rightarrow Matrix.PosSemidef\left(partialTranspose\left(W\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

For all natural local dimensions, second-factor partial transpose preserves positivity of a matrix in the separable cone. Each product of two positive matrices becomes the Kronecker product of the first factor and the transpose of the second, both positive; finite sums preserve positivity.

**Definition 1.3 (Upper bound, supremum and explicit attaining state).**

$$claim\iff (\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(4\right)), (Fin\left(4\right)\times Fin\left(4\right)), \mathbb{C}\right)), (((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)\leq \frac{2}{27})\land (sSup\left(\{p:\mathbb{R} | \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(4\right)), (Fin\left(4\right)\times Fin\left(4\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=p)\}\right)=\frac{2}{27})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(4\right)), (Fin\left(4\right)\times Fin\left(4\right)), \mathbb{C}\right)), (rho=Matrix.diagonal\left((fun (ij:(Fin\left(4\right)\times Fin\left(4\right))) \mapsto if (ij=(0,0)) then (\frac{1}{6}:\mathbb{C}) else (\frac{1}{18}:\mathbb{C}))\right))\land (((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=\frac{2}{27})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Conjecture 6.7, page 29, conjectures that the inscribed absolute-PPT polytope has the same maximum purity as the full APPT set, attained at the spectra in Eq. (44). This claim is precisely its m=n=4 sector: rho is a complex matrix on Fin 4 × Fin 4, positive semidefinite with trace one, and APPT means the second-factor partial transpose of U rho Uᴴ is positive semidefinite for every global unitary U. Purity is the real part of trace(rho*rho). It asserts the universal upper bound, equality of the real supremum with 2/27, and a density matrix equal to the prescribed diagonal state, with one complex diagonal entry 1/6 and fifteen entries 1/18. It does not classify all maximizers, address other local dimensions, or equate APPT with absolute separability.

**Theorem 1.4 (Exact maximum in the 4-by-4 sector).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.result` (`✓ std3`). ∎

*Resolves.* `Problems/ahiable-kothakonda-winter-2026-appt-quadbit-maximum-purity` (proved) by `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ahiable-kothakonda-winter-2026-appt-quadbit-maximum-purity","declaration_gid":"D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

The proof derives necessary rank-three Bell-corner matrices from the literal APPT predicate. With t the tenth decreasing eigenvalue, positivity gives t≤1/13. Inserting two copies of t for t≤1/18, or deleting t for t≥1/18, preserves both boundary matrices after positive normalization. The original dimension-18 and dimension-15 sharp spectral certificates then give the upper bound 2/27. These are reused certificate theorems, with no copied certificates and no assumption of Hildebrand sufficiency in local dimension four. The known low-rank separable ray proves APPT for the explicit attaining state. This resolves only the stated 4-by-4 sector; worldwide priority remains outside the formal theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.norm_of_dot_eq_one`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound](QuadbitSpectralPurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralReduction](QuadbitSpectralReduction.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment](QutritPerturbationAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../AbsoluteSeparability/LowRankRays.md)
