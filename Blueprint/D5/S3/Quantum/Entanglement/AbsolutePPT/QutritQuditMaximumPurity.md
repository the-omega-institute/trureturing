# Exact qutrit–qudit APPT maximum purity

## Abstract

For every n at least three, the literal qutrit APPT purity supremum equals the larger candidate purity and is attained by the prescribed diagonal state.

**Definition 1.1 (Exact maximum and attainment).**

$$claim\iff \forall (n:\mathbb{N}), (3\leq n)\Rightarrow (sSup\left(\{p:\mathbb{R} | \exists (rho:Matrix\left((Fin\left(3\right)\times Fin\left(n\right)), (Fin\left(3\right)\times Fin\left(n\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=p)\}\right)=max\left(\frac{3\cdot (n:\mathbb{R})+8}{(3\cdot (n:\mathbb{R})+2)^{2}}, \frac{3}{8\cdot (n:\mathbb{R})}\right))\land (\exists (rho:Matrix\left((Fin\left(3\right)\times Fin\left(n\right)), (Fin\left(3\right)\times Fin\left(n\right)), \mathbb{C}\right)), (rho=Matrix.diagonal\left((fun (ij:(Fin\left(3\right)\times Fin\left(n\right))) \mapsto Complex.ofReal\left((if (n\leq 8) then \frac{(if ((Prod.fst\left(ij\right)=0)\land (Fin.val\left(Prod.snd\left(ij\right)\right)=0)) then 3 else 1)}{3\cdot (n:\mathbb{R})+2} else \frac{(if (Prod.fst\left(ij\right)=0) then 2 else 1)}{4\cdot (n:\mathbb{R})}:\mathbb{R})\right))\right))\land (((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=max\left(\frac{3\cdot (n:\mathbb{R})+8}{(3\cdot (n:\mathbb{R})+2)^{2}}, \frac{3}{8\cdot (n:\mathbb{R})}\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

Ahiable–Kothakonda–Winter, Conjecture 6.7, page 29: Let 𝒫_{m,n} ⊆ APPT_{m,n} be the inscribed absolute PPT polytope with 2 ≤ m ≤ n, n > 2. Then max_{λ∈APPT_{m,n}} ∑_{i=1}^{mn} λ_i² = max_{λ∈𝒫_{m,n}} ∑_{i=1}^{mn} λ_i² and occurs at the spectra given by Eq. (44). The encoding substitutes m=3 and Corollary 6.4's two candidate values, quantifies every natural n≥3, uses density matrices on Fin 3 × Fin n, and expresses a maximum by the real sSup together with attainment at an explicit computational-basis diagonal state. For 3≤n≤8 the entry at (0,0) is 3/(3n+2) and all other entries are 1/(3n+2), giving the spectrum (3,1,…,1)/(3n+2). For n≥9 the entries with first-factor index 0 are 2/(4n) and the other entries are 1/(4n), giving n copies of 2/(4n) and 2n copies of 1/(4n). The second index test uses Fin.val, and the real diagonal entries are cast to complex numbers by Complex.ofReal. APPT is the literal predicate defined in QutritPerturbationAttainment; the purity is Complex.re of Matrix.trace (rho*rho). All displayed quotients are real division. Tran, remark after Theorem A, page 4: Determining the exact maximum APPT purity remains open.

**Theorem 1.2 (Unconditional exact maximum).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity.result` (`✓ std3`). ∎

*Resolves.* `Problems/ahiable-kothakonda-winter-2026-appt-qutrit-maximum-purity` (proved) by `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ahiable-kothakonda-winter-2026-appt-qutrit-maximum-purity","declaration_gid":"D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Acknowledgement.* Anh T. Tran (2026). *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*. DOI: [10.48550/arXiv.2609.18568](https://doi.org/10.48550/arXiv.2609.18568). URL: <https://arxiv.org/abs/2609.18568v1>.

*Commentary.*

The unconditional proof combines exact finite-sector dual certificates with a K1-only uniform cone estimate and the prescribed explicit diagonal density matrices. It proves this qutrit sector of the source conjecture and leaves m≥4 and APPT versus absolute separability open.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN10PurityBound](QutritN10PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN3PurityBound](QutritN3PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN4PurityBound](QutritN4PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN5PurityBound](QutritN5PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound](QutritN6PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN7PurityBound](QutritN7PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN8PurityBound](QutritN8PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN9PurityBound](QutritN9PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSpectralBound](UniformSpectralBound.md)
