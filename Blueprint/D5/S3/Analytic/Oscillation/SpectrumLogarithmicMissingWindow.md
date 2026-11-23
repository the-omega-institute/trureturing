# A Logarithmic Gain in Critical Missing Windows

## Abstract

A logarithmic square tail gives longer critical missing windows.

For a locally finite positive spectrum S and weights w, use the same inclusive cutoff for the mass and the sine score. In each formula, Eventually means that the indicated real variable is sufficiently large. `D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff`

**Definition 1.1 (A uniform logarithmic square-tail bound).**

$$\forall S \in Spectrum,\; \forall w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \operatorname{HasLogarithmicSquareTail}\left(S, w\right) \Leftrightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \operatorname{Eventually}\left((X \mapsto \forall T \in \mathbb{R},\; X \le T \Rightarrow \sum_{j \in \operatorname{cut}\left(S, T\right) \setminus \operatorname{cut}\left(S, X\right)} \operatorname{w}\left(j\right)^{2} \le \frac{C \cdot \operatorname{log}\left(X\right)}{X}), atTop\right)\right)$$

*Formalization.* `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow.HasLogarithmicSquareTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One positive constant bounds the squared weights on (X,T] for every finite upper cutoff T ≥ X once X is sufficiently large.

**Theorem 1.2 (A logarithmic gain in the waiting exponent).**

$$\forall S \in Spectrum,\; \forall w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \forall r \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \left(\left(\forall j \in \operatorname{index}\left(S\right),\; 0 \le \operatorname{w}\left(j\right)\right) \land \left(\operatorname{LinearIndependent}\left(\mathbb{Q}, \operatorname{gamma}\left(S\right)\right) \land \left(\operatorname{HasLogSquaredMass}\left(S, w\right) \land \left(\operatorname{HasLogarithmicSquareTail}\left(S, w\right) \land \left(0 < r \land \left(0 < beta \land beta < 1\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists c \in \mathbb{R},\; 0 < c \land \operatorname{Eventually}\left((T \mapsto 0 < \operatorname{mass}\left(S, w, T\right) \land \left(\forall A \in \mathbb{R},\; \exists a \in \mathbb{R},\; A < a \land \left(\forall u \in [a,a + \operatorname{exp}\left(c \cdot T^{beta} \cdot \operatorname{log}\left(T\right)\right)],\; \operatorname{sine}\left(S, w, T, \frac{u}{r}\right) < beta^{2} \cdot \operatorname{mass}\left(S, w, T\right) - \operatorname{log}\left(T\right)\right)\right)), atTop\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow.eventual_logarithmic_missing_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Siegfred Alan C. Baluyot; Daniel Alan Goldston; Ade Irma Suriajaya; Caroline L. Turnage-Butterbaugh (2024). *An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta-function*. DOI: [10.4064/aa230612-20-3](https://doi.org/10.4064/aa230612-20-3). URL: <https://arxiv.org/abs/2306.04799>.

*Commentary.*

Use the shifted cutoff X = exp(−K)T^β and write L = log T. The same head estimate gives β²W(T) − W(X) > 3L, and the mesh 1/T² costs less than L because the slope is at most TW(T). Nonnegative head mass gives W(T) > 0 eventually.

For the square-tail constant C, put D = Cβ exp(K). Using log X = βL − K gives V ≤ DL/T^β. When V is positive, the one-node tail bound at threshold L is at most exp(−T^βL/(2D)). Choose c = 1/(4D) and E = cT^βL.

In score time the interval has length exp(E)/r. The grid count is at most exp(E)(1 + 1/r)T² for T ≥ 1. Its logarithm is at most E + 2L + log(1 + 1/r) < 2E eventually. The grid count times the one-node bound is then strictly less than one. The finite theorem also allows zero variance. `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_arbitrarily_late_missing_window`

The head, threshold and mesh allowance fit below β²W(T) − L. Rational linear independence restricts to the finite cutoff. The orbit supplies a closed score-time interval starting above A/r, and scaling by r gives the stated interval.

For positive zeta ordinates, assume RH and rational linear independence of the distinct ordinates. The weight is mγ γ/(1/4+γ²), with analytic multiplicity mγ and inclusive cutoff γ ≤ T. The harmonic mass estimate gives coefficient 1/(4π). `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine`

The analytic input is the bounded average of the normalized Montgomery sum against 2(1−α) on 0 ≤ α ≤ 1. Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh (arXiv:2306.04799, Theorem 1) give this by integrating their uniform formula. Under RH, each ordinate difference contributes a nonnegative multiple of the triangular cosine transform. This transform is 1 at zero and 2(1−cos z)/z² elsewhere. The raw diagonal is the sum of squared multiplicities. In the normalized average the same sum is multiplied by 2π/(Y log Y). The other terms are nonnegative. `D5/S3/Analytic/Oscillation/MontgomeryWindow`

Thus the cumulative sum of squared multiplicities is O(Y log Y). On each band (2^k X, 2^(k+1) X], the squared harmonic weights are bounded by the squared multiplicities divided by (2^k X)². Summing the resulting geometric series with a linear factor in k gives O(log X/X) uniformly in T ≥ X. The application uses the analytic pair-correlation average as a literature input.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow.HasLogarithmicSquareTail`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow.eventual_logarithmic_missing_window`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_arbitrarily_late_missing_window`
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow](SpectrumCriticalMissingWindow.md)
- Narrative reference: [D5/S3/Analytic/Oscillation/MontgomeryWindow](MontgomeryWindow.md)
- Narrative reference: [D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff](SpectrumPhaseCutoff.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine](../../Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine.md)
