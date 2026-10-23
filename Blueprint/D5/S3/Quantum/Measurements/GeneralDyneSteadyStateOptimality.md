# Global steady-state optimality of aligned general-dyne monitoring

## Abstract

The aligned pure general-dyne measurement attains the smallest stationary covariance determinant for a stable thermal optical parametric oscillator, among all physical general-dyne measurements and physical stationary solutions.

**Definition 1.1 (OPO drift).**

$$\forall kappa \in \mathbb{R},\; \forall chi \in \mathbb{R},\; \operatorname{driftA}\left(kappa, chi\right) = !![\frac{-kappa}{2} - chi, 0; 0, \frac{-kappa}{2} + chi]$$

*Formalization.* `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.driftA` (`✓ std3`).

*Citation.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

Section VI, following Eq. (57), gives the diagonal drift. The symbols kappa and chi denote the real damping and pump parameters.

**Definition 1.2 (Passive system-bath coupling).**

$$\forall kappa \in \mathbb{R},\; \operatorname{coupling}\left(kappa\right) = \operatorname{HSMul.hSMul}\left(\operatorname{Real.sqrt}\left(kappa\right), !![0, 1; -1, 0]\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.coupling` (`✓ std3`).

*Citation.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

In the physical q,p coordinates, Omega is the displayed real matrix. The coupling C = sqrt(kappa) Omega produces the drift damping and diffusion following Eq. (57), and the unrotated aligned measurement of Eq. (66).

**Definition 1.3 (Correlated diffusion coefficient).**

$$\forall kappa \in \mathbb{R},\; \forall nu \in \mathbb{R},\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \operatorname{eMat}\left(kappa, nu, M\right) = !![0, 1; -1, 0] \cdot \operatorname{coupling}\left(kappa\right) \cdot \operatorname{HSMul.hSMul}\left(nu, (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right))\right) \cdot \operatorname{CFC.sqrt}\left(\left(\operatorname{HSMul.hSMul}\left(nu, (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right))\right) + M\right)^{-1}\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.eMat` (`✓ std3`).

*Citation.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

The text following Eq. (25) defines E = Omega C sigmaIn times the inverse square root of sigmaIn plus M. Here sigmaIn is nu times the identity, M is the measurement covariance, and CFC.sqrt is applied to the inverse matrix.

**Definition 1.4 (Monitoring coefficient).**

$$\forall kappa \in \mathbb{R},\; \forall nu \in \mathbb{R},\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \operatorname{bMat}\left(kappa, nu, M\right) = \operatorname{coupling}\left(kappa\right) \cdot !![0, 1; -1, 0] \cdot \operatorname{CFC.sqrt}\left(\left(\operatorname{HSMul.hSMul}\left(nu, (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right))\right) + M\right)^{-1}\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.bMat` (`✓ std3`).

*Citation.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

The text following Eq. (22) defines B = C Omega times the same inverse square root. The finite covariance domain includes arbitrary phases, squeezing and measurement impurity.

**Definition 1.5 (The stationary covariance equation).**

$$\forall kappa \in \mathbb{R},\; \forall chi \in \mathbb{R},\; \forall nu \in \mathbb{R},\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{steadyEq}\left(kappa, chi, nu, M, S\right)) \Leftrightarrow (\left(\operatorname{driftA}\left(kappa, chi\right) + \operatorname{eMat}\left(kappa, nu, M\right) \cdot \operatorname{Matrix.transpose}\left(\operatorname{bMat}\left(kappa, nu, M\right)\right)\right) \cdot S + S \cdot \operatorname{Matrix.transpose}\left(\operatorname{driftA}\left(kappa, chi\right) + \operatorname{eMat}\left(kappa, nu, M\right) \cdot \operatorname{Matrix.transpose}\left(\operatorname{bMat}\left(kappa, nu, M\right)\right)\right) + (\operatorname{HSMul.hSMul}\left(kappa \cdot nu, (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right))\right) - \operatorname{eMat}\left(kappa, nu, M\right) \cdot \operatorname{Matrix.transpose}\left(\operatorname{eMat}\left(kappa, nu, M\right)\right)) - S \cdot \operatorname{bMat}\left(kappa, nu, M\right) \cdot \operatorname{Matrix.transpose}\left(\operatorname{bMat}\left(kappa, nu, M\right)\right) \cdot S = 0)$$

*Formalization.* `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.steadyEq` (`✓ std3`).

*Citation.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

Equation (55) sets the conditional Riccati derivative to zero. S denotes the conditional covariance; diffusion is kappa times nu times the identity. Matrix.transpose is the ordinary real transpose. The equation is stated before any dimensionless reduction.

**Definition 1.6 (The exact optimal symplectic eigenvalue).**

$$\forall r \in \mathbb{R},\; \forall nu \in \mathbb{R},\; \operatorname{vStar}\left(r, nu\right) = \frac{\left(nu - 1\right) \cdot \operatorname{Real.sqrt}\left(1 - r^{2}\right) + \operatorname{Real.sqrt}\left(\left(nu - 1\right)^{2} \cdot \left(1 - r^{2}\right) + 4 \cdot nu\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.vStar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

For 0 <= r < 1 and nu >= 1, this is the positive root of v squared minus (nu minus one) times sqrt(1 minus r squared) times v minus nu. The real square roots are total functions; the theorem uses the stable thermal regime.

**Definition 1.7 (The aligned pure measurement).**

$$\forall r \in \mathbb{R},\; \operatorname{optMeas}\left(r\right) = !![\frac{1 - r}{1 + r}, 0; 0, \frac{1 + r}{1 - r}]$$

*Formalization.* `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.optMeas` (`✓ std3`).

*Citation.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

Page 12, Section VI: As regards the optimization over all the generaldyne measurement, one proves that if one fixes the measurement phase to zero, ϑ_m = 0, then the conditional steady-state purity, and as a consequence the daemonic ergotropy is maximized for the general-dyne parameter z_m,opt = (1 − χ̃)/(1 + χ̃). (66) The displayed matrix is diag(z_m,opt, 1/z_m,opt), with r = chi tilde.

**Definition 1.8 (The global optimality conjecture).**

$$(\operatorname{claim}) \Leftrightarrow (\forall kappa \in \mathbb{R},\; \forall chi \in \mathbb{R},\; \forall nth \in \mathbb{R},\; (0 < kappa) \Rightarrow ((0 \le chi) \Rightarrow ((chi < \frac{kappa}{2}) \Rightarrow ((0 \le nth) \Rightarrow ((\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsGaussianMeasurementCov} (m := 1) (M)) \Rightarrow ((\operatorname{IsGaussianMeasurementCov} (m := 1) (S)) \Rightarrow ((\operatorname{steadyEq}\left(kappa, chi, 2 \cdot nth + 1, M, S\right)) \Rightarrow (\operatorname{vStar}\left(\frac{2 \cdot chi}{kappa}, 2 \cdot nth + 1\right) \le \operatorname{Real.sqrt}\left(\operatorname{Matrix.det}\left(S\right)\right))))) \land (\exists S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsGaussianMeasurementCov} (m := 1) (S)) \land ((\operatorname{steadyEq}\left(kappa, chi, 2 \cdot nth + 1, \operatorname{optMeas}\left(\frac{2 \cdot chi}{kappa}\right), S\right)) \land (\operatorname{Real.sqrt}\left(\operatorname{Matrix.det}\left(S\right)\right) = \operatorname{vStar}\left(\frac{2 \cdot chi}{kappa}, 2 \cdot nth + 1\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.claim` (`✓ std3`).

*Citation.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

Page 12, Section VI after Eq. (66): We have also numerically verified that non-zero phases ϑ_m lead to worse result, and we can thus conjecture that this fully characterizes the optimal steady-state general-dyne monitoring. The real parameters kappa, chi and nth are κ, χ and n_th; nu = 2 nth + 1 and r = 2 chi / kappa. The matrices M and S represent σ_m and σ. IsGaussianMeasurementCov is the existing GaussianThermometryJointMeasurementRefutation predicate at m = 1: symmetry and S + i Omega positive semidefinite. The first conjunct bounds every physical stationary solution for every physical measurement; the second gives a physical stationary solution at the aligned measurement with equality. No uniqueness of the minimizing measurement is asserted.

**Theorem 1.9 (Physical one-mode covariances are positive definite).**

$$\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov} (m := 1) (M)) \Rightarrow ((\operatorname{Matrix.PosDef}\left(M\right)) \land (1 \le \operatorname{Matrix.det}\left(M\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.physical_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

A real two-by-two covariance satisfying IsGaussianMeasurementCov at m = 1 is positive definite and has determinant at least one. The stationary covariance lower bound uses these properties through physical_iff; GaussianAtemporalityEntanglement uses positive definiteness to invert both local covariance blocks.

**Theorem 1.10 (The aligned measurement achieves the global optimum).**

$$\forall kappa \in \mathbb{R},\; \forall chi \in \mathbb{R},\; \forall nth \in \mathbb{R},\; (0 < kappa) \Rightarrow ((0 \le chi) \Rightarrow ((chi < \frac{kappa}{2}) \Rightarrow ((0 \le nth) \Rightarrow ((\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsGaussianMeasurementCov} (m := 1) (M)) \Rightarrow ((\operatorname{IsGaussianMeasurementCov} (m := 1) (S)) \Rightarrow ((\operatorname{steadyEq}\left(kappa, chi, 2 \cdot nth + 1, M, S\right)) \Rightarrow (\operatorname{vStar}\left(\frac{2 \cdot chi}{kappa}, 2 \cdot nth + 1\right) \le \operatorname{Real.sqrt}\left(\operatorname{Matrix.det}\left(S\right)\right))))) \land (\exists S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsGaussianMeasurementCov} (m := 1) (S)) \land ((\operatorname{steadyEq}\left(kappa, chi, 2 \cdot nth + 1, \operatorname{optMeas}\left(\frac{2 \cdot chi}{kappa}\right), S\right)) \land (\operatorname{Real.sqrt}\left(\operatorname{Matrix.det}\left(S\right)\right) = \operatorname{vStar}\left(\frac{2 \cdot chi}{kappa}, 2 \cdot nth + 1\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.result` (`✓ std3`). ∎

*Resolves.* `Problems/kua-serafini-genoni-2025-general-dyne-optimality` (proved) by `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kua-serafini-genoni-2025-general-dyne-optimality","declaration_gid":"D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. H. Kua; A. Serafini; M. G. Genoni (2025). *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*. DOI: [10.1088/2058-9565/ae2200](https://doi.org/10.1088/2058-9565/ae2200). URL: <https://arxiv.org/abs/2506.22288>.

*Commentary.*

Write Q = (nu I + M) inverse, V = S minus nu I, D0 = diag(1+r, 1-r), and R = nu I minus (D0 S + S D0)/2. The stationary equation gives R = V Q V. The matrix N = I minus nu Q is positive definite, so W = V N V is positive semidefinite and det W = det M times det R.

With v = sqrt(det S), c = sqrt(1-r squared), h = S(0,1), and T = (1+r) S(0,0) + (1-r) S(1,1), two determinant identities express the product of the quadratic factors Fplus and Fminus as the sum of a nonnegative correlation term, a nonnegative drift-weighted imbalance term, and (det M minus one) det R. Positivity of W gives nu T <= 2 det S, while T >= 2 c v, hence v >= nu c. For positive r, Fplus = (v minus nu c) squared + (nu minus one) c (v minus nu c) + nu r squared is strictly positive. Consequently Fminus is nonnegative and v is at least vStar.

At zero pump the matrix equation forces S = nu I for every physical stationary solution. For all stable pumps, the diagonal covariance with entries c vStar/(1+r) and c vStar/(1-r) is physical and solves the stationary equation at optMeas; its determinant square root is vStar. These arguments include mixed measurement covariances and zero bath occupation. They establish the global value and an aligned attainer, without classifying all equality cases.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.bMat`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.coupling`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.driftA`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.eMat`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.optMeas`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.physical_forward`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.result`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.steadyEq`
- Truth anchor: `D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.vStar`
- Dependency: [D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation](../../Estimation/GaussianThermometryJointMeasurementRefutation.md)
- Dependency: [D5/S3/Observer/GoldenCoding/GoldenFactorCancellation](../../Observer/GoldenCoding/GoldenFactorCancellation.md)
- Dependency: [D5/S3/Quantum/Thermal/PositiveOneModeWilliamson](../Thermal/PositiveOneModeWilliamson.md)
