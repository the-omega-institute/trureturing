# First Frozen Theorem Suite

## Abstract

Ten classical completion identities are assembled from their canonical proofs.

**Theorem 1.1 (Ten classical completion identities).**

$${\operatorname{Fourier}(\operatorname{Gaussian}(a)) = \operatorname{Gaussian}(a) \iff a = \pi} \land\\{2\operatorname{MellinGaussian}(s) = \pi^{-s / 2}\operatorname{Gamma}(s / 2)} \land\\{\forall y, \operatorname{E}(y) = \operatorname{exp}(y)} \land\\{\forall y>0, (y = 1 + \frac{1}{y}) \iff y = \frac{{1 + \sqrt{5}}}{2}} \land\\{\forall ell, \operatorname{exp}(-ell) = p^{-1} \iff ell = \operatorname{log}(p)} \land\\{\operatorname{H}(n) - \operatorname{log}(n) - gamma \to 0} \land\\{s = 1 - \operatorname{conj}(s) \iff \operatorname{Re}(s) = \frac{1}{2}} \land\\{\operatorname{S}(x) + \operatorname{T}(x) = \sqrt{\frac{{\pi \times \operatorname{exp}(x)}}{{2 \times x}}}} \land\\{\operatorname{MellinLambert}(w) = \operatorname{Gamma}(w)\operatorname{zeta}(w)\operatorname{zeta}(w + r){1 - p^{-{w + r}}}} \land\\{\operatorname{MeromorphicOn}(\operatorname{Z}(\varphi), {\operatorname{Re}(s) > 0}) \land \operatorname{Res}(\operatorname{Z}(\varphi), 1) = \frac{1}{{\sqrt{5}}}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Characterizations/FirstFrozenTheoremSuite.first_frozen_theorem_suite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem reuses the repository owners of seven clauses and proves the Gaussian Mellin and completed-tail clauses from pinned Mathlib integral identities.

The source's explicit Golden exponent is positive and strictly increasing with finite sublevel sets. Its bounded counting-density estimate is the sole parameterized premise; the general spectral continuation theorem then gives meromorphicity and residue one over square root five.

## References

- Truth anchor: `D5/S3/Constants/Characterizations/FirstFrozenTheoremSuite.first_frozen_theorem_suite`
- Dependency: [D5/S1/FixedPoints/Algebraic/GoldenFixedPoint](../../../S1/FixedPoints/Algebraic/GoldenFixedPoint.md)
- Dependency: [D5/S3/Analytic/Asymptotics/PrimeDeletedLambertMellin](../../Analytic/Asymptotics/PrimeDeletedLambertMellin.md)
- Dependency: [D5/S3/Analytic/Asymptotics/SpectralZetaContinuation](../../Analytic/Asymptotics/SpectralZetaContinuation.md)
- Dependency: [D5/S3/Analytic/Characterizations/VisibleGaussianMass](../../Analytic/Characterizations/VisibleGaussianMass.md)
- Dependency: [D5/S3/Constants/Characterizations/ExponentialFlowUniqueness](ExponentialFlowUniqueness.md)
- Dependency: [D5/S3/Constants/Characterizations/LocalPrecisionUnit](LocalPrecisionUnit.md)
- Dependency: [D5/S3/Constants/Limits/EulerResidualCancellation](../Limits/EulerResidualCancellation.md)
- Dependency: [D5/S3/Fourier/CompletionConstants/GaussianSelfDualPi](../../Fourier/CompletionConstants/GaussianSelfDualPi.md)
- Dependency: [D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry](../../Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.md)
