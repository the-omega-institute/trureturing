# Unconditional Shifted-Poisson Flow

## Abstract

Increasing the shift of the finite xi-zero phase density is exactly concrete Poisson convolution.

**Theorem 1.1 (Larger shifts are exactly Poisson smoothing).**

$$\forall T \in \mathbb{R}, omega \in \mathbb{R}, eta \in \mathbb{R},\; \forall window \in \operatorname{ShiftedZeroWindow}(T),\; \left(\frac{1}{2} \le omega \land 0 \le eta\right) \Rightarrow \left(\operatorname{shiftedPhaseDensity}(window, omega + eta) = \operatorname{conv}(\operatorname{poissonKernel}(\operatorname{toNNReal}(eta)), \operatorname{shiftedPhaseDensity}(window, omega)) \land \operatorname{shiftedPhaseDensity}(window, omega + eta) = \operatorname{conv}(\operatorname{poissonKernel}(\operatorname{toNNReal}(eta)), \operatorname{shiftedPhaseDensity}(window, omega))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.shifted_poisson_semigroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive-height finite window containing exactly the positive-ordinate zeros of the repository's canonical xi reading. Each distinct zero is repeated by its concrete analytic vanishing order in the phase-density measure.

For omega at least one half and nonnegative eta, both public conjuncts state the same concrete measure identity: the density at omega plus eta is convolution of the eta Poisson kernel with the density at omega. The first leaf carries formula (347.7); the second carries the separately boxed smoothing conclusion.

The Poisson kernel is the scaled half-Cauchy probability measure, and convolution is Mathlib measure convolution. Characteristic-function uniqueness proves its additive semigroup law.

The named shiftedPhaseFourier carrier evaluates the characteristic function at minus t, exactly matching the source convention. Its factorization is exp(-omega times abs(t)) times the independently defined finite zero sum Q_T; Q_T contains the delta and ordinate factors and has no omega parameter. The main equality is proved through this certificate.

The canonicalShiftedZeroWindow constructor takes the finite set of all canonical xi zeros with ordinates in (0,T], and analytic order provides multiplicity. Theorem 347.1 is unconditional: it fixes no window-nonemptiness hypothesis, and the empty window is a legitimate instance under which both sides reduce to the zero measure and the identity still holds. The source defines the ordinate window without asserting that it is nonempty, so no such condition is claimed here. The retained certificates are the poissonKernel nondegeneracy and the shiftedPhaseFourier factorization through Q_T. No Riemann-hypothesis or inverse-positivity premise occurs in either public equality leaf.

## References

- Truth anchor: `D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.shifted_poisson_semigroup`
- Dependency: [D5/S3/Zeros/Endpoints/XiEndpointValues](../../Zeros/Endpoints/XiEndpointValues.md)
