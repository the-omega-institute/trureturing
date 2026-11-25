# Signed Mellin cancellation by inversion

## Abstract

Inversion across the unit scale pairs the real signed Mellin kernel and gives a fixed linear gain above the critical exponent.

**Definition 1.1 (Signed power kernel).**

$$K_{\beta}(y)=\left(\left\lvert y\right\rvert^{-\beta}-1\right)\cdot \left\lvert 1-y\right\rvert^{-\frac{3}{2}}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.signedKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponent beta and position y are real. The powers are real powers. Values on the singular points do not affect Lebesgue integration.

**Definition 1.2 (Whole-line Mellin integral).**

$$J(\beta)=\int_{\mathbb{R}}K_{\beta}(y)\,dy$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integration is over the entire real line with Lebesgue measure, not just its positive half. The theorem below proves integrability on the stated exponent range.

**Definition 1.3 (Fixed coefficient of the lower bound).**

$$c=\frac{\left(1-\exp\left(-\frac{\log 2}{2}\right)\right)\cdot \log 2}{4}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.gapCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is independent of beta. The factor one quarter is the length of the compact interval used for the lower estimate.

**Theorem 1.4 (Exact cancellation and a positive linear gap).**

$$\begin{gathered}(\forall \beta\in \mathbb{R},\quad0\le\beta<1\longrightarrow \operatorname{Integrable}\left(K_{\beta}\right)) \land\\{}J(\frac{1}{2})=0\quad\land\quad0<c \land\\{}(\forall \beta\in \mathbb{R},\quad\frac{1}{2}\le\beta<1\longrightarrow c\cdot \left(\beta-\frac{1}{2}\right)\le J(\beta))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.signed_mellin_cancellation_and_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrable means absolutely integrable with respect to Lebesgue measure. Near zero the bound is a multiple of the absolute position to the power minus beta. Near one the numerator vanishes linearly, leaving an integrable power minus one half. Both tails are controlled by the power minus three halves.

Substituting the reciprocal where the absolute position exceeds one contributes the absolute Jacobian. After factoring the paired kernel, its numerator at absolute position t is the product of one minus t to the beta and t to the minus beta minus t to the minus one half. This vanishes at the critical exponent and is nonnegative throughout the supercritical range. A positive lower estimate on the interval from one quarter to one half gives the displayed uniform linear bound.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.J`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.gapCoefficient`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.signedKernel`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin.signed_mellin_cancellation_and_gap`
