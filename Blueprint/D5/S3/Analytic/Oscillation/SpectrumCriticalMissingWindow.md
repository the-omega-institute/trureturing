# Missing Windows at the Critical Mass Fraction

## Abstract

A shifted critical cutoff gives a strict missing window at the endpoint mass fraction.

For a locally finite positive spectrum S and weights w, use the same inclusive cutoff for the mass and the sine score. In each formula, Eventually means that the indicated real variable is sufficiently large. `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff`

**Definition 1.1 (Squared-logarithmic mass with a linear logarithmic error).**

$$\forall S \in Spectrum,\; \forall w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \operatorname{HasLogSquaredMass}\left(S, w\right) \Leftrightarrow \left(\exists a \in \mathbb{R},\; \exists C \in \mathbb{R},\; 0 < a \land \left(0 \le C \land \operatorname{Eventually}\left((Y \mapsto \left|\operatorname{mass}\left(S, w, Y\right) - a \cdot \operatorname{log}\left(Y\right)^{2}\right| \le C \cdot (1 + \operatorname{log}\left(Y\right))), atTop\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow.HasLogSquaredMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is positive. The error constant is independent of the cutoff.

**Definition 1.2 (Uniform smallness of the square tail).**

$$\forall S \in Spectrum,\; \forall w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \operatorname{HasSmallSquareTail}\left(S, w\right) \Leftrightarrow \left(\forall eta \in \mathbb{R},\; 0 < eta \Rightarrow \operatorname{Eventually}\left((X \mapsto \forall T \in \mathbb{R},\; X \le T \Rightarrow \sum_{j \in \operatorname{cut}\left(S, T\right) \setminus \operatorname{cut}\left(S, X\right)} \operatorname{w}\left(j\right)^{2} \le \frac{eta \cdot \operatorname{log}\left(X\right)^{2}}{X}), atTop\right)\right)$$

*Formalization.* `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow.HasSmallSquareTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower cutoff may depend on η. The bound then holds uniformly over every upper cutoff and includes every ordinate in (X,T].

**Theorem 1.3 (Arbitrarily late closed windows below the critical mass fraction).**

$$\forall S \in Spectrum,\; \forall w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \forall r \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \left(\left(\forall j \in \operatorname{index}\left(S\right),\; 0 \le \operatorname{w}\left(j\right)\right) \land \left(\operatorname{LinearIndependent}\left(\mathbb{Q}, \operatorname{gamma}\left(S\right)\right) \land \left(\operatorname{HasLogSquaredMass}\left(S, w\right) \land \left(\operatorname{HasSmallSquareTail}\left(S, w\right) \land \left(0 < r \land \left(0 < beta \land beta < 1\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Eventually}\left((T \mapsto 0 < \operatorname{mass}\left(S, w, T\right) \land \left(\forall A \in \mathbb{R},\; \exists a \in \mathbb{R},\; A < a \land \left(\forall u \in [a,a + \operatorname{exp}\left(T^{beta}\right)],\; \operatorname{sine}\left(S, w, T, \frac{u}{r}\right) < beta^{2} \cdot \operatorname{mass}\left(S, w, T\right)\right)\right)), atTop\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow.eventual_critical_missing_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write W for the mass function, L = log T and X = exp(−K)T^β. Choose K = (C(β+β²)+4)/(2aβ), where a and C are the coefficient and error constant in the mass hypothesis. Expanding log X = βL − K gives β²W(T) − W(X) > 3L eventually. Nonnegative weights on the head then imply positive total mass.

In score time, use length exp(T^β)/r, threshold L and mesh h = 1/T². The tail slope is bounded by TW(T), so the mesh allowance is at most W(T)/T < L eventually. The grid has at most exp(2T^β) nodes because exp(T^β)/T² grows without bound.

Apply the uniform square-tail bound at that same X with η = exp(−K)/(8β²). Since 0 ≤ log X ≤ βL eventually, the variance bound V ≤ L²/(8T^β) follows. For V > 0, the product of the grid count and the one-node tail bound is at most exp(−2T^β) < 1. The finite theorem also handles V = 0. `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_arbitrarily_late_missing_window`

Restrict rational linear independence to the finite cutoff. The head mass, threshold and mesh allowance fit strictly below β²W(T), so the finite orbit theorem gives a closed score-time window starting above A/r. Multiplying the endpoints by r gives the asserted window starting above A.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow.HasLogSquaredMass`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow.HasSmallSquareTail`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow.eventual_critical_missing_window`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_arbitrarily_late_missing_window`
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff](SpectrumPhaseCutoff.md)
- Dependency: [D5/S3/Fourier/Concentration/FiniteSineMissingWindow](../../Fourier/Concentration/FiniteSineMissingWindow.md)
- Narrative reference: [D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff](SpectrumPhaseCutoff.md)
