# Exact quadbit–sextit APPT maximum purity

## Abstract

The known 4-by-6 APPT purity maximum 8/169, attained by (3/26,1/26,...,1/26), is an application of the generic finite Bell-corner formal mechanism.

**Definition 1.1 (Upper bound, supremum and explicit attaining state).**

$$claim\iff (\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(6\right)), (Fin\left(4\right)\times Fin\left(6\right)), \mathbb{C}\right)), (((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)\leq \frac{8}{169})\land (sSup\left(\{p:\mathbb{R} | \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(6\right)), (Fin\left(4\right)\times Fin\left(6\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=p)\}\right)=\frac{8}{169})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(6\right)), (Fin\left(4\right)\times Fin\left(6\right)), \mathbb{C}\right)), (rho=Matrix.diagonal\left((fun (ij:(Fin\left(4\right)\times Fin\left(6\right))) \mapsto if (ij=(0,0)) then (\frac{3}{26}:\mathbb{C}) else (\frac{1}{26}:\mathbb{C}))\right))\land (((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=\frac{8}{169})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Conjecture 6.7, page 29, conjectures that the inscribed absolute-PPT polytope has the same maximum purity as the full APPT set, attained at the spectra in Eq. (44). The displayed claim is the m=4, n=6 application: rho is a complex matrix on Fin 4 × Fin 6, positive semidefinite with trace one, and APPT means the second-factor partial transpose of U rho Uᴴ is positive semidefinite for every global unitary U. Purity is the real part of trace(rho*rho). It asserts the universal upper bound, equality of the real supremum with 8/169, and a density matrix equal to the prescribed diagonal state, with one complex diagonal entry 3/26 and twenty-three entries 1/26. Hildebrand, quant-ph/0502170, Theorem 2 on PDF page 5, gives APPT 4×6→3×8 at total dimension 24 because the minimum local dimension decreases from four to three. Unitary identification preserves trace and purity. The established qutrit maximum and known attaining ray already imply the scalar value. Issue 17734 is research history, not novelty authority. This application adds no independent open-problem count and does not classify all maximizers, address other local dimensions, or equate APPT with absolute separability.

**Theorem 1.2 (Exact maximum in the 4-by-6 sector).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

FiniteBellCorner.spectral_reduction produces both necessary rank-three boundary matrices on the largest three and smallest six entries of the decreasing twenty-four-dimensional spectrum. Its boundary selector equals QutritSpectralReduction.boundaryValues 5, so QutritN8PurityBound.certificate_bound gives 32/26²=8/169. This direct Lean proof uses the product-corner construction instead of formalizing the fixed-total-dimension monotonicity theorem as a new prerequisite. For the computational basis vector psi, the state (I+2|psi><psi|)/26 has trace one and purity (24+8)/26². After every global unitary its unscaled matrix belongs to the separable cone by LowRankRays.separableCone_one_add_two_rankOne; second-factor partial transpose preserves positivity of each separable product term. The diagonal entries are exactly 3/26 at (0,0) and 1/26 elsewhere. The upper bound and this witness give the real supremum. Against immutable baseline 8a32282e7f57c3a751640623624ee9d1ac5b3a25, result is content under escape-witness: unfolding density_bound and the same-delivery FiniteBellCorner.spectral_reduction leaves the new product-corner necessity inference on the live path to the universal upper bound and supremum. The baseline qutrit reduction does not instantiate to a 4-by-6 product. The scalar value is known mathematically; admission rests on the new formal inference, not an open-problem exception. The attainment helpers are bind-only and consumed by result. Utility is none: the delivered inference concerns arbitrary complex densities and all global unitaries; it introduces no enumeration, checker, numerical premise or finite certificate instance. The already-frozen rational certificate is reused, and evaluating the explicit ray is helper normalization. This application establishes no maximizer classification or priority claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner](FiniteBellCorner.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity](QuadbitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN8PurityBound](QutritN8PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment](QutritPerturbationAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../AbsoluteSeparability/LowRankRays.md)
