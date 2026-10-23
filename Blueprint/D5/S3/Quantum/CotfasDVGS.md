# Cotfas discrete Gaussian positivity

## Abstract

The covariance uncertainty condition makes the trace-normalized mixed discrete Gaussian a density operator.

The indices are the integers from −s to s, with d = 2s + 1. The covariance is a real positive-definite two by two matrix. Matrix positivity uses the complex Hermitian order. Infinite lattice sums are tsums.

**Definition 1.1 (Continuous Gaussian Wigner function).**

$$\forall (h : \mathbb{R}), \forall (sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)), \forall (q : \mathbb{R}), \forall (p : \mathbb{R}), \operatorname{W}\left(h, sigma, q, p\right) = (\frac{2}{(h) \cdot (\operatorname{Real}.\operatorname{sqrt}\left(\operatorname{Matrix}.\operatorname{det}\left(sigma\right)\right))}) \cdot (\operatorname{Real}.\operatorname{exp}\left((-(\frac{(2) \cdot (\operatorname{Real}.\operatorname{pi})}{h})) \cdot (\operatorname{dotProduct}\left(![q, p], \operatorname{Matrix}.\operatorname{mulVec}\left(sigma^{-(1)}, ![q, p]\right)\right))\right))$$

*Formalization.* `D5/S3/Quantum/CotfasDVGS.W` (`✓ std3`).

*Citation.* Nicolae Cotfas (2026). *Frame-dependent coherence of Gaussian quantum states*. DOI: [10.48550/arXiv.2610.05623](https://doi.org/10.48550/arXiv.2610.05623). URL: <https://arxiv.org/abs/2610.05623v1>.

*Commentary.*

Page 2, Eq. (10): Wσ(q, p) = 2/(h√det σ) exp(−(2π/h) (q p) σ⁻¹ (q p)ᵀ). The two coordinates form the vector ![q, p]; dotProduct and Matrix.mulVec express the quadratic form.

**Definition 1.2 (Discrete displaced parity).**

$$\forall (s : \mathbb{N}), \forall (n : \operatorname{Finset}.\operatorname{Icc}\left(-((s : \mathbb{Z})), (s : \mathbb{Z})\right)), \forall (k : \operatorname{Finset}.\operatorname{Icc}\left(-((s : \mathbb{Z})), (s : \mathbb{Z})\right)), \forall (m : \operatorname{Finset}.\operatorname{Icc}\left(-((s : \mathbb{Z})), (s : \mathbb{Z})\right)), \forall (j : \operatorname{Finset}.\operatorname{Icc}\left(-((s : \mathbb{Z})), (s : \mathbb{Z})\right)), \operatorname{parity}\left(s, n, k, m, j\right) = \operatorname{if} (j : \mathbb{Z}) = \operatorname{ZMod}.\operatorname{valMinAbs}\left(((2) \cdot ((n : \mathbb{Z})) - (m : \mathbb{Z}) : \operatorname{ZMod}\left((2) \cdot (s) + 1\right))\right) \operatorname{then} \operatorname{Complex}.\operatorname{exp}\left(\frac{((((4) \cdot (\operatorname{Real}.\operatorname{pi})) \cdot (\operatorname{Complex}.\operatorname{I})) \cdot (((k : \mathbb{Z}) : \mathbb{C}))) \cdot (((m : \mathbb{Z}) : \mathbb{C}) - ((n : \mathbb{Z}) : \mathbb{C}))}{(2) \cdot ((s : \mathbb{C})) + 1}\right) \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/CotfasDVGS.parity` (`✓ std3`).

*Citation.* Nicolae Cotfas (2026). *Frame-dependent coherence of Gaussian quantum states*. DOI: [10.48550/arXiv.2610.05623](https://doi.org/10.48550/arXiv.2610.05623). URL: <https://arxiv.org/abs/2610.05623v1>.

*Commentary.*

Page 2, Eq. (18): “Π̃(n, k)ψ(m) = e^{(4πi/d) k(m−n)} ψ(2n − m).” The (m, j) entry is the coefficient of ψ(j), with centered modular reduction in the selected column. Page 2 fixes “the addition is modulo d.” ZMod.valMinAbs selects the unique representative in {−s, …, s} for d = 2s + 1.

**Definition 1.3 (Signed Gaussian lattice sum).**

$$\forall (s : \mathbb{N}), \forall (h : \mathbb{R}), \forall (sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)), \forall (n : \operatorname{Finset}.\operatorname{Icc}\left(-((s : \mathbb{Z})), (s : \mathbb{Z})\right)), \forall (k : \operatorname{Finset}.\operatorname{Icc}\left(-((s : \mathbb{Z})), (s : \mathbb{Z})\right)), \operatorname{wSum}\left(s, h, sigma, n, k\right) = \operatorname{tsum}\left(((z : (\mathbb{Z} \times \mathbb{Z})) \mapsto ((-(1) : \mathbb{R})^{(z.1) \cdot (z.2)}) \cdot (\operatorname{W}\left(h, sigma, (((n : \mathbb{Z}) : \mathbb{R}) + \frac{((z.1 : \mathbb{R})) \cdot ((2) \cdot ((s : \mathbb{R})) + 1)}{2}) \cdot (\operatorname{Real}.\operatorname{sqrt}\left(\frac{h}{(2) \cdot ((s : \mathbb{R})) + 1}\right)), (((k : \mathbb{Z}) : \mathbb{R}) + \frac{((z.2 : \mathbb{R})) \cdot ((2) \cdot ((s : \mathbb{R})) + 1)}{2}) \cdot (\operatorname{Real}.\operatorname{sqrt}\left(\frac{h}{(2) \cdot ((s : \mathbb{R})) + 1}\right))\right)))\right)$$

*Formalization.* `D5/S3/Quantum/CotfasDVGS.wSum` (`✓ std3`).

*Citation.* Nicolae Cotfas (2026). *Frame-dependent coherence of Gaussian quantum states*. DOI: [10.48550/arXiv.2610.05623](https://doi.org/10.48550/arXiv.2610.05623). URL: <https://arxiv.org/abs/2610.05623v1>.

*Commentary.*

Page 3, Eq. (22): W̃σ(n, k) = c′σ Σα,β (−1)^{αβ} Wσ((n + αd/2)√(h/d), (k + βd/2)√(h/d)). The expression omits only the scalar c′σ. Both lattice coordinates are integers, while every division inside the Wigner arguments is real division.

**Definition 1.4 (Discrete Gaussian before normalization).**

$$\forall (s : \mathbb{N}), \forall (h : \mathbb{R}), \forall (sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)), \operatorname{unnormalized}\left(s, h, sigma\right) = \sum_{(n : \operatorname{Finset}.\operatorname{Icc}\left(-((s : \mathbb{Z})), (s : \mathbb{Z})\right))} (\sum_{(k : \operatorname{Finset}.\operatorname{Icc}\left(-((s : \mathbb{Z})), (s : \mathbb{Z})\right))} (((\operatorname{wSum}\left(s, h, sigma, n, k\right) : \mathbb{C})) \cdot (\operatorname{parity}\left(s, n, k\right))))$$

*Formalization.* `D5/S3/Quantum/CotfasDVGS.unnormalized` (`✓ std3`).

*Citation.* Nicolae Cotfas (2026). *Frame-dependent coherence of Gaussian quantum states*. DOI: [10.48550/arXiv.2610.05623](https://doi.org/10.48550/arXiv.2610.05623). URL: <https://arxiv.org/abs/2610.05623v1>.

*Commentary.*

Page 3, Eq. (21): “Mixed DVGS - Inspired by the formulas (17) and (20), we have introduced in [21], for any d = 3, 5, 7, ..., the discrete version ρ̃_σ = Σ_{n,k=−s}^{s} W̃_σ(n, k) Π̃(n, k).” The two finite sums range over Finset.Icc (−s) s, and the real lattice weight is coerced to the complex scalars.

**Definition 1.5 (Trace normalization).**

$$\forall (s : \mathbb{N}), \forall (h : \mathbb{R}), \forall (sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)), \operatorname{rhoTilde}\left(s, h, sigma\right) = ((\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{unnormalized}\left(s, h, sigma\right)\right))^{-(1)}) \cdot (\operatorname{unnormalized}\left(s, h, sigma\right))$$

*Formalization.* `D5/S3/Quantum/CotfasDVGS.rhoTilde` (`✓ std3`).

*Citation.* Nicolae Cotfas (2026). *Frame-dependent coherence of Gaussian quantum states*. DOI: [10.48550/arXiv.2610.05623](https://doi.org/10.48550/arXiv.2610.05623). URL: <https://arxiv.org/abs/2610.05623v1>.

*Commentary.*

Page 3 describes c′κ as “a normalizing constant”. The normalized matrix is its unnormalized value multiplied by the inverse of its complex trace. The positivity proof establishes that this trace is nonzero.

**Definition 1.6 (Cotfas conjecture).**

$$\operatorname{claim} = (\forall (s : \mathbb{N}), (1 \le s) \Rightarrow (\forall (h : \mathbb{R}), (0 < h) \Rightarrow (\forall (sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)), (\operatorname{Matrix}.\operatorname{PosDef}\left(sigma\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{Matrix}.\operatorname{map}\left(sigma, ((x : \mathbb{R}) \mapsto (x : \mathbb{C}))\right) + (\operatorname{Complex}.\operatorname{I}) \cdot (!![(0 : \mathbb{C}), 1; -(1), 0])\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{rhoTilde}\left(s, h, sigma\right)\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{rhoTilde}\left(s, h, sigma\right)\right) = 1))))))$$

*Formalization.* `D5/S3/Quantum/CotfasDVGS.claim` (`✓ std3`).

*Citation.* Nicolae Cotfas (2026). *Frame-dependent coherence of Gaussian quantum states*. DOI: [10.48550/arXiv.2610.05623](https://doi.org/10.48550/arXiv.2610.05623). URL: <https://arxiv.org/abs/2610.05623v1>.

*Commentary.*

Page 3, after Eq. (22): “As concern ρ̃_σ, we do not know if (11) is sufficient in order to have ρ̃_σ ≥ 0. Based on our numerical investigations, we conjecture that this is true.” Eq. (11) is “where the covariance matrix σ = (σ11 σ12; σ12 σ22), satisfying σ + i(0 1; −1 0) ≥ 0, is a real 2×2 symmetric positive-definite matrix.” The dimension is d = 2s + 1 with s ≥ 1. All positive h and all real positive-definite covariances satisfying the uncertainty condition are quantified. The conclusion also states trace one.

**Theorem 1.7 (The uncertainty condition suffices).**

$$\forall (s : \mathbb{N}), (1 \le s) \Rightarrow (\forall (h : \mathbb{R}), (0 < h) \Rightarrow (\forall (sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)), (\operatorname{Matrix}.\operatorname{PosDef}\left(sigma\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{Matrix}.\operatorname{map}\left(sigma, ((x : \mathbb{R}) \mapsto (x : \mathbb{C}))\right) + (\operatorname{Complex}.\operatorname{I}) \cdot (!![(0 : \mathbb{C}), 1; -(1), 0])\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{rhoTilde}\left(s, h, sigma\right)\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{rhoTilde}\left(s, h, sigma\right)\right) = 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CotfasDVGS.result` (`✓ std3`). ∎

*Resolves.* `Problems/cotfas-2026-uncertainty-condition-conjecture` (proved) by `D5/S3/Quantum/CotfasDVGS.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cotfas-2026-uncertainty-condition-conjecture","declaration_gid":"D5/S3/Quantum/CotfasDVGS.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nicolae Cotfas (2026). *Frame-dependent coherence of Gaussian quantum states*. DOI: [10.48550/arXiv.2610.05623](https://doi.org/10.48550/arXiv.2610.05623). URL: <https://arxiv.org/abs/2610.05623v1>.

*Commentary.*

Scaling reduces the Planck parameter to d. Poisson summation identifies the exact matrix with twice a periodized Gaussian kernel. Its Gaussian Gram factor is positive semidefinite when det σ ≥ 1. A rank-one lower bound and theta nonvanishing give a strictly positive diagonal entry, hence a nonzero trace. The argument includes det σ = 1 and det σ > 1.

## References

- Truth anchor: `D5/S3/Quantum/CotfasDVGS.W`
- Truth anchor: `D5/S3/Quantum/CotfasDVGS.claim`
- Truth anchor: `D5/S3/Quantum/CotfasDVGS.parity`
- Truth anchor: `D5/S3/Quantum/CotfasDVGS.result`
- Truth anchor: `D5/S3/Quantum/CotfasDVGS.rhoTilde`
- Truth anchor: `D5/S3/Quantum/CotfasDVGS.unnormalized`
- Truth anchor: `D5/S3/Quantum/CotfasDVGS.wSum`
- Dependency: [D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation](../Estimation/GaussianThermometryJointMeasurementRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Weil/Probability/FiniteGaussianSchoenberg](../Weil/Probability/FiniteGaussianSchoenberg.md)
