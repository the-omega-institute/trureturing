# Cubic entropy along Gibbs translations

## Abstract

Exact cubic entropy slopes, their BKM correction, and a scalar Jensen comparison.

Use complex matrices on an arbitrary finite index type, ordinary trace, and real spectral functional calculus for the matrix logarithm. Put T = Re Tr(M³). The entropy at M with fixed reference cube B³ is Re Tr(M³(log M³ − log B³)) − T log T. The translation is M + sB. Write J = Re Tr((BM² − MBM) log B).

## Derivative of the actual entropy

**Theorem 1.1 (Two-sided derivative).**

Lean statement: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive definite B and M the derivative at s = 0 is 9 Re Tr(BM²(log M − log B)) − 3 Re Tr(BM²) log T + 3J. The cube derivative is BM² + MBM + M²B. In the pairing with log M, cyclicity makes the three terms equal. In the pairing with log B the two outer terms agree, and the middle term gives the correction. Differentiating T log T cancels the identity contribution from trace entropy. The formula allows arbitrary trace of B³.

**Theorem 1.2 (Right derivative on the positive boundary).**

Lean statement: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive definite B and positive semidefinite M the same coefficient is the derivative at zero within s ≥ 0. The function x² log x extends continuously at zero with value zero and supplies the boundary limit. The zero matrix has right slope zero by cubic scaling along the Gibbs ray.

## The noncommuting correction

**Theorem 1.3 (Correction in a reference eigenbasis).**

Lean statement: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian B and M, write bᵢ for the eigenvalues of B and U for M in the chosen orthonormal eigenbasis of B. Then J is half the sum over i,j of (bᵢ − bⱼ)(log bᵢ − log bⱼ)|Uᵢⱼ|². The expression allows repeated eigenvalues and uses the Lean real logarithm on the whole real line.

**Theorem 1.4 (BKM pairing of the logarithmic commutator).**

Lean statement: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_eq_bkm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_eq_bkm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive definite B and Hermitian M, set C = (log B)M − M(log B). Then J = ½ Re Tr(Cᴴ Ω_B(C)), with Ω_B the actual integral of B^t C B^(1−t) over 0 ≤ t ≤ 1. The logarithmic mean on each reference eigenvalue pair converts the squared log difference to the spectral weight above.

**Theorem 1.5 (Nonnegative correction).**

Lean statement: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive definite B and Hermitian M, the spectral weights are nonnegative by monotonicity of the logarithm on positive numbers, so J ≥ 0.

**Theorem 1.6 (Equality and commutation).**

Lean statement: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_eq_zero_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_eq_zero_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive definite B and Hermitian M, J = 0 exactly when BM = MB. The positive weights between distinct eigenvalues force the corresponding entries to vanish at equality. Entries within a repeated eigenspace are unrestricted.

## Scalar comparison in the actual spectral pair

Let mⱼ be the eigenvalues of M and let wᵢⱼ be the squared overlaps of the respective eigenvectors of B and M. For positive definite B, the Nussbaum–Szkoła reference weights of the cube pair are πᵢⱼ = bᵢ³wᵢⱼ. The ratios xᵢⱼ = mⱼ/bᵢ are the cube roots of the corresponding eigenvalue ratios.

**Theorem 1.7 (Spectral expression for the right derivative).**

Lean statement: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy_spectral_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy_spectral_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive definite B and positive semidefinite M, the right slope is 9 Σ πx² log x − 3 (Σ πx²) log(Σ πx³) + 3J. Entries with zero overlap or zero mⱼ contribute zero to the weighted sums. The reference cube may have any trace.

**Theorem 1.8 (Exact Jensen deficit of the scalar slope).**

Lean statement: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy_spectral_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy_spectral_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive definite B and M with Re Tr(B³) = 1, all x are positive. The weights π are nonnegative, sum to one, and vanish exactly on zero overlap. Set S = Re Tr(BM²), T = Re Tr(M³), and ν = πx²/S. Both traces are positive. The nonnegative weights ν sum to one, as do πx³/T. Under ν the mean of x is T/S and the mean of log x is Re Tr(BM²(log M − log B))/S. Put H = Σ πx² log(x²) − S log S and Δ = log(Σ νx) − Σ ν log x. The two-sided derivative is 3(H + J − SΔ), so 3(H + J) bounds the slope above. The Jensen deficit Δ is nonnegative and is strictly positive exactly when two pairs with nonzero π have distinct x.

## Use in the Wu cubic translation argument

In the two-mode CAR specialization of Wu v1, Remark 3.15, equation (3.54), take the Gibbs density D, G = D^(1/6), B = G², and M = GXG. The translation X + sI becomes M + sB, and B³ = D identifies the entropy above with the entropy term of the cubic deficit. The separate WuCubicTranslationEnergy result gives the energy slope in degree-weighted signed thermal coordinates.

In the occupation basis the correction uses the same Gibbs eigenvalue ratios that determine the signed charge blocks of the energy slope. Each weight is the product of a Gibbs eigenvalue difference and its log ratio. It vanishes at the tracial reference and on equal-weight blocks at every temperature. Near the tracial reference the exact weights isolate the part of the entropy slope to be controlled on the noncommuting directions, while the scalar comparison retains the signed contribution −3SΔ.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_eq_bkm`
- Truth anchor: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_eq_zero_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_nonneg`
- Truth anchor: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.correction_spectral`
- Truth anchor: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy`
- Truth anchor: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy_spectral_pair`
- Truth anchor: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy`
- Truth anchor: `D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy_spectral_pair`
- Dependency: [D5/S3/Quantum/Divergence/TraceEntropyCalculus](../TraceEntropyCalculus.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMSpectralVariance](../../Recovery/BKMSpectralVariance.md)
