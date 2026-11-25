# Local averaging of a finite harmonic score

## Abstract

Local averaging gives a three-band lower bound for a finite weighted sine score.

Fix a finite set s of indices in a type J. Each j in s has a real angular frequency γⱼ and a real weight wⱼ. For a real cutoff Z, sum over the indices with γⱼ ≤ Z. The notation W and S suppresses the common set, frequencies and weights.

**Definition 1.1 (Mass through the cutoff).**

$$W_{Z} = \sum_{j\in s,\gamma_{j}\le Z}\,w_{j}$$

*Formalization.* `D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cutoff includes frequencies equal to Z. An empty cutoff has mass zero.

**Definition 1.2 (Sine score through the cutoff).**

$$S_{Z}(v) = \sum_{j\in s,\gamma_{j}\le Z}\,w_{j}\operatorname{sin}\left(\gamma_{j}v\right)$$

*Formalization.* `D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The argument v is the time in the score. The estimates evaluate the score at v = u/r as u runs through the window.

For the following estimates assume γⱼ > 0 and wⱼ ≥ 0 for every j in s. Take real cutoffs 0 < X ≤ Y ≤ T, a scale r > 0, a window length h > 0, and any real left endpoint b.

**Theorem 1.3 (Lower bound for the window mean).**

$$S_{X}(\frac{b}{r})-\frac{hX}{r}W_{X}-(W_{Y} - W_{X})-\frac{2r}{hY}(W_{T} - W_{Y})\le\frac{1}{h}\int_{b}^{b + h} S_{T}(\frac{u}{r})\,du$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffScore_average_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For γⱼ ≤ X, sine is one-Lipschitz and the argument moves by at most hX/r from its left-endpoint value. For X < γⱼ ≤ Y, the mean of each sine is at least −1. For Y < γⱼ ≤ T, integrating the sine at angular frequency γⱼ/r gives the difference of the endpoint cosines multiplied by r/γⱼ. After division by h the result is at least −2r/(hγⱼ), hence at least −2r/(hY). Nonnegative weights preserve each inequality. The two band masses are the respective differences of cumulative masses.

The endpoint estimate is the real sine version of the normalized finite character average in norm_avg_le, ExpSumCoeffEqZeroOfVanishing.lean, lines 32–62, from the Riemann hypothesis repository at b8864ecd5798c6030a03d756fab95f0b89a12754. Its frequencies are measured in cycles per unit.

**Theorem 1.4 (A score at least the bound in the same window).**

$$\exists u\in[b,b + h],\quad S_{X}(\frac{b}{r})-\frac{hX}{r}W_{X}-(W_{Y} - W_{X})-\frac{2r}{hY}(W_{T} - W_{Y})\le S_{T}(\frac{u}{r})$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HarmonicScoreLocalAverage.exists_cutoffScore_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite score is continuous. The first integral mean value theorem with weight one gives a point in the closed window where the score equals its window mean.

## References

- Truth anchor: `D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffMass`
- Truth anchor: `D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffScore`
- Truth anchor: `D5/S3/Fourier/HarmonicScoreLocalAverage.cutoffScore_average_lower`
- Truth anchor: `D5/S3/Fourier/HarmonicScoreLocalAverage.exists_cutoffScore_ge`
