# Exact quadbit–sextit APPT maximum purity

## Abstract

The literal 4-by-6 APPT purity maximum is 8/169 and is attained by the explicit diagonal spectrum (3/26,1/26,...,1/26).

**Definition 1.1 (Upper bound, supremum and explicit attaining state).**

$$claim\iff (\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(6\right)), (Fin\left(4\right)\times Fin\left(6\right)), \mathbb{C}\right)), (((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)\leq \frac{8}{169})\land (sSup\left(\{p:\mathbb{R} | \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(6\right)), (Fin\left(4\right)\times Fin\left(6\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=p)\}\right)=\frac{8}{169})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(6\right)), (Fin\left(4\right)\times Fin\left(6\right)), \mathbb{C}\right)), (rho=Matrix.diagonal\left((fun (ij:(Fin\left(4\right)\times Fin\left(6\right))) \mapsto if (ij=(0,0)) then (\frac{3}{26}:\mathbb{C}) else (\frac{1}{26}:\mathbb{C}))\right))\land (((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=\frac{8}{169})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Conjecture 6.7, page 29, conjectures that the inscribed absolute-PPT polytope has the same maximum purity as the full APPT set, attained at the spectra in Eq. (44). This claim is precisely its m=4, n=6 sector: rho is a complex matrix on Fin 4 × Fin 6, positive semidefinite with trace one, and APPT means the second-factor partial transpose of U rho Uᴴ is positive semidefinite for every global unitary U. Purity is the real part of trace(rho*rho). It asserts the universal upper bound, equality of the real supremum with 8/169, and a density matrix equal to the prescribed diagonal state, with one complex diagonal entry 3/26 and twenty-three entries 1/26. It does not classify all maximizers, address other local dimensions, or equate APPT with absolute separability.

**Theorem 1.2 (Exact maximum in the 4-by-6 sector).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.result` (`✓ std3`). ∎

*Resolves.* `Problems/ahiable-kothakonda-winter-2026-appt-quadbit-sextit-maximum-purity` (proved) by `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ahiable-kothakonda-winter-2026-appt-quadbit-sextit-maximum-purity","declaration_gid":"D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

FiniteBellCorner.spectral_reduction produces both necessary rank-three boundary matrices on the largest three and smallest six entries of the decreasing twenty-four-dimensional spectrum. Its boundary selector equals QutritSpectralReduction.boundaryValues 5, so QutritN8PurityBound.certificate_bound gives 32/26²=8/169. No Hildebrand sufficiency characterization is used. For the computational basis vector psi, the state (I+2|psi><psi|)/26 has trace one and purity (24+8)/26². After every global unitary its unscaled matrix belongs to the separable cone by LowRankRays.separableCone_one_add_two_rankOne; second-factor partial transpose preserves positivity of each separable product term. The diagonal entries are exactly 3/26 at (0,0) and 1/26 elsewhere. The upper bound and this witness give the real supremum. This is only the m=4,n=6 sector of the same conjecture; it does not classify all maximizers or establish worldwide priority.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner](FiniteBellCorner.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity](QuadbitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN8PurityBound](QutritN8PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment](QutritPerturbationAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../AbsoluteSeparability/LowRankRays.md)
