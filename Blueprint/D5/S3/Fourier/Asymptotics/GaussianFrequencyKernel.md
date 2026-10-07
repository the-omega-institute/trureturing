# Gaussian frequency integration

## Abstract

The original Gaussian density controls the zero-frequency quotient and the logarithmic singular H in actual symmetric product L2.

**Definition 1.1 (Actual weighted measure).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \operatorname{spatialMeasure}\left(c, kappa\right) = \operatorname{withDensity}\left(volume, (x:Real\mapsto \operatorname{ofReal}\left(c \cdot \operatorname{exp}\left(\frac{-kappa \cdot x^{2}}{2}\right)\right))\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For arbitrary real c and kappa, spatialMeasure is the Lebesgue measure with density ofReal(c exp(-kappa x^2/2)). Positive kappa and nonnegative c are required only by the subsequent estimates.

**Definition 1.2 (Gaussian normalization constant).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \operatorname{spatialMass}\left(c, kappa\right) = c \cdot \operatorname{sqrt}\left(\frac{2 \cdot \operatorname{pi}\left(\right)}{kappa}\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The mass expression retains the unnormalized coefficient c.

**Theorem 1.3 (Density normalization).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{spatialMeasure}\left(c, kappa\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(\operatorname{spatialMass}\left(c, kappa\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\frac{1}{kappa}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMeasure_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For c nonnegative and kappa positive, the actual weighted measure is its mass times the centered Gaussian probability measure with variance 1/kappa. This is an equality of measures derived from their densities, including c=0.

**Theorem 1.4 (Original spatial mass).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{spatialMass}\left(c, kappa\right) = \operatorname{integral}\left((x:Real\mapsto c \cdot \operatorname{exp}\left(\frac{-kappa \cdot x^{2}}{2}\right)), volume\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMass_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The normalization constant equals the integral of the original real density. Thus gamma is the actual unnormalized mass, rather than an imposed probability normalization.

**Theorem 1.5 (Finite Gaussian weight).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{IsFiniteMeasure}\left(\operatorname{spatialMeasure}\left(c, kappa\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMeasure_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The density normalization supplies finiteness for every nonnegative c and positive kappa.

**Theorem 1.6 (Product-coordinate difference law).**

$$\forall v \in NNReal,\; \operatorname{map}\left(\operatorname{prod}\left(\operatorname{gaussianReal}\left(0, v\right), \operatorname{gaussianReal}\left(0, v\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto (\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right)))\right) = \operatorname{gaussianReal}\left(0, v+v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussian_difference_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Independent coordinates of the actual Gaussian product measure have centered difference law with variance 2v. The pinned Gaussian convolution and map theorems supply this statement, including v=0.

**Theorem 1.7 (Reused scalar fourth moment).**

$$\forall v \in NNReal,\; \operatorname{integral}\left((x:Real\mapsto x^{4}), \operatorname{gaussianReal}\left(0, v\right)\right) = 3 \cdot \operatorname{coe}\left(v\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussian_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The scalar fourth moment is 3v^2, using centralMoment_two_mul in its existing owner. Zero variance is included.

**Theorem 1.8 (Exact fourth spatial difference moment).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{integral}\left((z:\operatorname{Prod}\left(Real, Real\right)\mapsto (\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))^{4}), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right) = \frac{12 \cdot \operatorname{integral}\left((x:Real\mapsto c \cdot \operatorname{exp}\left(\frac{-kappa \cdot x^{2}}{2}\right)), volume\right)^{2}}{kappa^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatial_difference_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The actual product-measure integral of (x-y)^4 is 12 gamma^2/kappa^2. Density normalization, the product-coordinate difference law and the existing scalar moment determine every constant.

**Theorem 1.9 (Fourth difference integrability).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{Integrable}\left((z:\operatorname{Prod}\left(Real, Real\right)\mapsto (\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))^{4}), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatial_difference_fourth_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Gaussian finite-moment integrability transports through the actual difference map and finite scaling of each coordinate measure.

**Definition 1.10 (Actual square-difference class).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{HasType}\left(\operatorname{squareDifference}\left(c, kappa, hc, hkappa\right), \operatorname{Lp}\left(Real, 2, \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)\right) \land \operatorname{squareDifference}\left(c, kappa, hc, hkappa\right) = \operatorname{toLp}\left(\operatorname{memLpOfIntegrableSquare}\left(\operatorname{spatialDifferenceFourthIntegrable}\left(c, kappa, hc, hkappa\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto (\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))^{2})\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.squareDifference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

This is the toLp class of (x-y)^2, with its membership witness obtained from fourth difference integrability.

**Theorem 1.11 (Square-difference representative).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{squareDifference}\left(c, kappa, hc, hkappa\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto (\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))^{2}), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.squareDifference_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The L2 class has the displayed actual product-measure representative.

**Theorem 1.12 (Exact dominating class norm).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{norm}\left(\operatorname{squareDifference}\left(c, kappa, hc, hkappa\right)\right) = \frac{2 \cdot \operatorname{sqrt}\left(3\right) \cdot \operatorname{spatialMass}\left(c, kappa\right)}{kappa}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.squareDifference_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The fourth difference integral gives the norm 2 sqrt(3) gamma/kappa, with no positivity-of-mass assumption.

**Definition 1.13 (Original frequency kernel).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall v \in Real,\; \operatorname{gaussianFrequency}\left(c, kappa, hc, hkappa, v\right) = \operatorname{val}\left(\operatorname{frequencyKernel}\left(\operatorname{spatialMeasure}\left(c, kappa\right), v\right)\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussianFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

This is the existing frequencyKernel, viewed in the actual symmetric L2 subspace using the derived finite-measure instance. No kernel or noise is replaced.

**Theorem 1.14 (Cosine-difference representative).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall v \in Real,\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{val}\left(\operatorname{gaussianFrequency}\left(c, kappa, hc, hkappa, v\right)\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto \operatorname{cos}\left(\frac{\operatorname{pi}\left(\right)}{2} \cdot v \cdot (\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))\right)-1), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussianFrequency_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every real frequency v, the representative is cos((pi/2)v(x-y))-1.

**Theorem 1.15 (Quadratic zero-frequency bound).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall v \in Real,\; \operatorname{norm}\left(\operatorname{gaussianFrequency}\left(c, kappa, hc, hkappa, v\right)\right) \le \frac{\operatorname{sqrt}\left(3\right) \cdot \frac{\operatorname{pi}\left(\right)}{2}^{2} \cdot \operatorname{spatialMass}\left(c, kappa\right)}{kappa} \cdot v^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The global cosine remainder inequality and exact square-difference norm give ||D_v|| <= sqrt(3)(pi/2)^2 gamma v^2/kappa for every real v, including zero.

**Theorem 1.16 (Global frequency regularity).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \exists K \in NNReal,\; \operatorname{LipschitzWith}\left(K, (v:Real\mapsto \operatorname{gaussianFrequency}\left(c, kappa, hc, hkappa, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

There is a finite nonnegative Lipschitz constant for the actual Gaussian frequency kernel on the whole real line. The proof uses the same cosine bound and dominating L2 class 1+(x-y)^2 as frequency continuity, whose proof consumes this helper. The helper adds no mathematical content credit. Composition with the original second integral gives the regularity needed by the existing jointly measurable L2 version theorem, on the original probability space.

**Theorem 1.17 (Frequency L2 continuity).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{Continuous}\left((v:Real\mapsto \operatorname{gaussianFrequency}\left(c, kappa, hc, hkappa, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The consumed global Lipschitz helper supplies continuity in the actual symmetric product L2 space.

**Definition 1.18 (Zero-inclusive quotient).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall v \in Real,\; \operatorname{quotientFrequency}\left(c, kappa, hc, hkappa, v\right) = \operatorname{smul}\left(\operatorname{inv}\left(v\right), \operatorname{gaussianFrequency}\left(c, kappa, hc, hkappa, v\right)\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quotientFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Real inverse assigns zero at zero, so J_v=v^-1 D_v has J_0=0 and the original D_v/v representative elsewhere.

**Theorem 1.19 (Linear quotient bound).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall v \in Real,\; \operatorname{norm}\left(\operatorname{quotientFrequency}\left(c, kappa, hc, hkappa, v\right)\right) \le \frac{\operatorname{sqrt}\left(3\right) \cdot \frac{\operatorname{pi}\left(\right)}{2}^{2} \cdot \operatorname{spatialMass}\left(c, kappa\right)}{kappa} \cdot \operatorname{abs}\left(v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quotientFrequency_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Cancellation of one frequency factor gives ||J_v|| <= sqrt(3)(pi/2)^2 gamma |v|/kappa. The zero case is proved separately.

**Theorem 1.20 (Continuity at the boundary).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \operatorname{Continuous}\left((v:Real\mapsto \operatorname{quotientFrequency}\left(c, kappa, hc, hkappa, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quotientFrequency_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Away from zero, continuity follows from inverse and scalar multiplication. At zero, the linear norm bound squeezes J_v to J_0=0.

**Theorem 1.21 (Every original finite window).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall s \in Real,\; \operatorname{IntegrableOn}\left((v:Real\mapsto \operatorname{quotientFrequency}\left(c, kappa, hc, hkappa, v\right)), \operatorname{Icc}\left(0, \operatorname{exp}\left(s\right)\right), volume\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quotientFrequency_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Continuity on the compact closed interval [0,exp(s)] supplies Bochner integrability for every real s. The boundary is included.

**Theorem 1.22 (Actual spatial integral representative).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall s \in Real,\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{val}\left(\operatorname{setIntegral}\left((v:Real\mapsto \operatorname{quotientFrequency}\left(c, kappa, hc, hkappa, v\right)), \operatorname{Icc}\left(0, \operatorname{exp}\left(s\right)\right), volume\right)\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto \operatorname{intervalIntegral}\left((v:Real\mapsto \frac{\operatorname{cos}\left(\frac{\operatorname{pi}\left(\right)}{2} \cdot v \cdot (\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))\right)-1}{v}), 0, \operatorname{exp}\left(s\right), volume\right)), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_integral_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For each real s, the symmetric L2 Bochner integral on [0,exp(s)] has the almost-everywhere representative obtained by integrating the actual cosine quotient in frequency. The continuous L2 primitive and its jointly measurable spatial quotient supply product integrability and Fubini.

**Definition 1.23 (Original finite-frequency kernel).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall D \in Real,\; \forall s \in Real,\; \operatorname{regularKernel}\left(c, kappa, hc, hkappa, D, s\right) = \operatorname{smul}\left(1+2 \cdot \operatorname{eulerMascheroniConstant}\left(\right)+2 \cdot D+2 \cdot s, \operatorname{diagonalKernel}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{oneVector}\left(\operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)\right)+\operatorname{smul}\left(2, \operatorname{setIntegral}\left((v:Real\mapsto \operatorname{quotientFrequency}\left(c, kappa, hc, hkappa, v\right)), \operatorname{Icc}\left(0, \operatorname{exp}\left(s\right)\right), volume\right)\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.regularKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The original H_s is constructed in the actual symmetric product L2 space. Its constant coefficient is b_*+2s, where b_*=1+2 Euler+2D, and its frequency integral includes the zero endpoint.

**Theorem 1.24 (Off-diagonal Ci identity).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall D \in Real,\; \forall s \in Real,\; \forall H \in \operatorname{symmetricKernel}\left(\operatorname{spatialMeasure}\left(c, kappa\right)\right),\; \forall hH \in \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{val}\left(H\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto 1+2 \cdot D-2 \cdot \operatorname{log}\left(\frac{\operatorname{pi}\left(\right)}{2} \cdot \operatorname{abs}\left((\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))\right)\right)), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{val}\left(\operatorname{regularKernel}\left(c, kappa, hc, hkappa, D, s\right)-H\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto 2 \cdot \operatorname{cosineIntegral}\left(\frac{\operatorname{pi}\left(\right)}{2} \cdot \operatorname{exp}\left(s\right) \cdot \operatorname{abs}\left((\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))\right)\right)), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.regularKernel_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For any H with the original logarithmic representative, H_s-H has representative 2Ci((pi/2)exp(s)|x-y|). The actual Gaussian density gives a null spatial diagonal, including c=0. Cosine evenness, positive scaling and the positive Ci/Euler normalization identify the spatial primitive; the desired kernel identity is a conclusion.

**Definition 1.25 (Actual same-W quadratic frequency).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall Omega \in Type,\; \forall SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right),\; \forall P \in \operatorname{Measure}\left(Omega\right),\; \forall hprob \in \operatorname{IsProbabilityMeasure}\left(P\right),\; \forall W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, \operatorname{spatialMeasure}\left(c, kappa\right)\right), \operatorname{Lp}\left(Real, 2, P\right)\right),\; \forall hW \in \left(\forall f \in \operatorname{Lp}\left(Real, 2, \operatorname{spatialMeasure}\left(c, kappa\right)\right),\; \operatorname{HasLaw}\left(\operatorname{coeFn}\left(\operatorname{apply}\left(W, f\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right),\; \forall v \in Real,\; \operatorname{quadraticFrequency}\left(c, kappa, hc, hkappa, P, W, hW, v\right) = \operatorname{centeredSquare}\left(\operatorname{spatialMeasure}\left(c, kappa\right), P, W, hW, \operatorname{cosineVector}\left(\operatorname{spatialMeasure}\left(c, kappa\right), v\right)\right)+\operatorname{centeredSquare}\left(\operatorname{spatialMeasure}\left(c, kappa\right), P, W, hW, \operatorname{sineVector}\left(\operatorname{spatialMeasure}\left(c, kappa\right), v\right)\right)-\operatorname{centeredSquare}\left(\operatorname{spatialMeasure}\left(c, kappa\right), P, W, hW, \operatorname{oneVector}\left(\operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quadraticFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For one fixed original isometry W and its centered Gaussian marginal laws on P, the quadratic class is the sum of the centered cosine and sine squares minus the centered constant square.

**Theorem 1.26 (Exact same-noise identification).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall Omega \in Type,\; \forall SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right),\; \forall P \in \operatorname{Measure}\left(Omega\right),\; \forall hprob \in \operatorname{IsProbabilityMeasure}\left(P\right),\; \forall W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, \operatorname{spatialMeasure}\left(c, kappa\right)\right), \operatorname{Lp}\left(Real, 2, P\right)\right),\; \forall hW \in \left(\forall f \in \operatorname{Lp}\left(Real, 2, \operatorname{spatialMeasure}\left(c, kappa\right)\right),\; \operatorname{HasLaw}\left(\operatorname{coeFn}\left(\operatorname{apply}\left(W, f\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right),\; \forall v \in Real,\; \operatorname{apply}\left(\operatorname{secondIntegral}\left(\operatorname{spatialMeasure}\left(c, kappa\right), P, W, hW\right), \operatorname{gaussianFrequency}\left(c, kappa, hc, hkappa, v\right)\right) = \operatorname{quadraticFrequency}\left(c, kappa, hc, hkappa, P, W, hW, v\right) \land \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{quadraticFrequency}\left(c, kappa, hc, hkappa, P, W, hW, v\right)\right), (omega:Omega\mapsto \operatorname{evaluation}\left(\operatorname{apply}\left(W, \operatorname{cosineVector}\left(\operatorname{spatialMeasure}\left(c, kappa\right), v\right)\right), omega\right)^{2}+\operatorname{evaluation}\left(\operatorname{apply}\left(W, \operatorname{sineVector}\left(\operatorname{spatialMeasure}\left(c, kappa\right), v\right)\right), omega\right)^{2}-\operatorname{evaluation}\left(\operatorname{apply}\left(W, \operatorname{oneVector}\left(\operatorname{spatialMeasure}\left(c, kappa\right)\right)\right), omega\right)^{2}), P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quadraticFrequency_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The continuous second integral agrees with the finite construction. Trigonometric energy cancels the centering terms, so the displayed representative is |F(v)|^2-Y^2 for the same W and P.

**Theorem 1.27 (Bochner commutation and centered remainder).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall Omega \in Type,\; \forall SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right),\; \forall P \in \operatorname{Measure}\left(Omega\right),\; \forall hprob \in \operatorname{IsProbabilityMeasure}\left(P\right),\; \forall W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, \operatorname{spatialMeasure}\left(c, kappa\right)\right), \operatorname{Lp}\left(Real, 2, P\right)\right),\; \forall hW \in \left(\forall f \in \operatorname{Lp}\left(Real, 2, \operatorname{spatialMeasure}\left(c, kappa\right)\right),\; \operatorname{HasLaw}\left(\operatorname{coeFn}\left(\operatorname{apply}\left(W, f\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right),\; \forall s \in Real,\; \operatorname{IntegrableOn}\left((v:Real\mapsto \operatorname{smul}\left(\operatorname{inv}\left(v\right), \operatorname{quadraticFrequency}\left(c, kappa, hc, hkappa, P, W, hW, v\right)\right)), \operatorname{Icc}\left(0, \operatorname{exp}\left(s\right)\right), volume\right) \land \left(\operatorname{apply}\left(\operatorname{secondIntegral}\left(\operatorname{spatialMeasure}\left(c, kappa\right), P, W, hW\right), \operatorname{setIntegral}\left((v:Real\mapsto \operatorname{quotientFrequency}\left(c, kappa, hc, hkappa, v\right)), \operatorname{Icc}\left(0, \operatorname{exp}\left(s\right)\right), volume\right)\right) = \operatorname{setIntegral}\left((v:Real\mapsto \operatorname{smul}\left(\operatorname{inv}\left(v\right), \operatorname{quadraticFrequency}\left(c, kappa, hc, hkappa, P, W, hW, v\right)\right)), \operatorname{Icc}\left(0, \operatorname{exp}\left(s\right)\right), volume\right) \land \left(\forall D \in Real,\; \forall H \in \operatorname{symmetricKernel}\left(\operatorname{spatialMeasure}\left(c, kappa\right)\right),\; \operatorname{apply}\left(\operatorname{secondIntegral}\left(\operatorname{spatialMeasure}\left(c, kappa\right), P, W, hW\right), \operatorname{regularKernel}\left(c, kappa, hc, hkappa, D, s\right)-H\right) = \operatorname{smul}\left(1+2 \cdot \operatorname{eulerMascheroniConstant}\left(\right)+2 \cdot D+2 \cdot s, \operatorname{centeredSquare}\left(\operatorname{spatialMeasure}\left(c, kappa\right), P, W, hW, \operatorname{oneVector}\left(\operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)\right)+\operatorname{smul}\left(2, \operatorname{setIntegral}\left((v:Real\mapsto \operatorname{smul}\left(\operatorname{inv}\left(v\right), \operatorname{quadraticFrequency}\left(c, kappa, hc, hkappa, P, W, hW, v\right)\right)), \operatorname{Icc}\left(0, \operatorname{exp}\left(s\right)\right), volume\right)\right)-\operatorname{apply}\left(\operatorname{secondIntegral}\left(\operatorname{spatialMeasure}\left(c, kappa\right), P, W, hW\right), H\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_integral_sameNoise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The original second integral commutes with the integrable frequency quotient on every finite window. For every D and symmetric H, its image of H_s-H is (b_*+2s) times the centered original Y square, plus twice the same-W quadratic quotient integral, minus I2(H). This is an equality of actual L2(P) classes. Identifying the selected original R and E processes and their common paths requires the corresponding process version identification.

**Theorem 1.28 (Two-sided logarithmic control).**

$$\forall x \in Real,\; \forall hx \in 0 < x,\; \operatorname{log}\left(x\right)^{2} \le 16 \cdot \operatorname{rpow}\left(x, \frac{-1}{2}\right)+x^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.log_square_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every positive x, log(x)^2 <= 16 x^(-1/2)+x^2. Below one, the reciprocal power bound controls the logarithmic singularity; above one, log(x) <= x controls the tail. This estimate is consumed by Gaussian logarithmic integrability.

**Theorem 1.29 (Gaussian integrability at the singularity).**

$$\forall b \in Real,\; \forall hb \in 0 < b,\; \operatorname{Integrable}\left((x:Real\mapsto \operatorname{log}\left(\operatorname{abs}\left(x\right)\right)^{2} \cdot \operatorname{exp}\left(-b \cdot x^{2}\right)), volume\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.log_square_gaussian_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The actual function log(|x|)^2 exp(-b x^2) is Lebesgue integrable for every b>0. The previous bound is dominated by the pinned Gaussian power integrals with exponents -1/2 and 2 on the positive half-line; reflection covers the negative half-line. The assigned value at zero has no integral effect.

**Theorem 1.30 (Logarithmic moment of the actual Gaussian law).**

$$\forall v \in NNReal,\; \forall hv \in \operatorname{Not}\left(v = 0\right),\; \operatorname{Integrable}\left((x:Real\mapsto \operatorname{log}\left(\operatorname{abs}\left(x\right)\right)^{2}), \operatorname{gaussianReal}\left(0, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussian_log_square_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every nonzero nonnegative variance v, log(|x|)^2 is integrable under gaussianReal(0,v). The Gaussian density identity directly consumes the proved weighted Lebesgue integrability. No logarithmic moment premise is supplied.

**Theorem 1.31 (Singular H and its actual Ci remainder).**

$$\forall c \in Real,\; \forall kappa \in Real,\; \forall hc \in 0 \le c,\; \forall hkappa \in 0 < kappa,\; \forall D \in Real,\; \exists H \in \operatorname{symmetricKernel}\left(\operatorname{spatialMeasure}\left(c, kappa\right)\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{val}\left(H\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto 1+2 \cdot D-2 \cdot \operatorname{log}\left(\frac{\operatorname{pi}\left(\right)}{2} \cdot \operatorname{abs}\left((\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))\right)\right)), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right) \land \left(\forall s \in Real,\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{val}\left(\operatorname{regularKernel}\left(c, kappa, hc, hkappa, D, s\right)-H\right)\right), (z:\operatorname{Prod}\left(Real, Real\right)\mapsto 2 \cdot \operatorname{cosineIntegral}\left(\frac{\operatorname{pi}\left(\right)}{2} \cdot \operatorname{exp}\left(s\right) \cdot \operatorname{abs}\left((\operatorname{fst}\left(z\right)-\operatorname{snd}\left(z\right))\right)\right)), \operatorname{prod}\left(\operatorname{spatialMeasure}\left(c, kappa\right), \operatorname{spatialMeasure}\left(c, kappa\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.singularKernel_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every real D, nonnegative c and positive kappa, one H in the actual symmetric product L2 space has representative 1+2D-2 log((pi/2)|x-y|), and for every real s its difference from the constructed H_s has the Ci representative. Apply D=D_w for the original kernel. The Gaussian logarithmic moment and unnormalized mass include c=0; the spatial diagonal is null. This assertion gives the spatial kernel and all its fixed-time differences. It does not assert a common pointwise W version or a process limit.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_continuous`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_integral_coe`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_integral_sameNoise`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_lipschitz`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.frequency_norm_bound`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussianFrequency`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussianFrequency_coe`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussian_difference_law`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussian_fourth`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.gaussian_log_square_integrable`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.log_square_bound`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.log_square_gaussian_integrable`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quadraticFrequency`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quadraticFrequency_representation`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quotientFrequency`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quotientFrequency_continuous`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quotientFrequency_integrable`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.quotientFrequency_norm`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.regularKernel`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.regularKernel_difference`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.singularKernel_exists`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMass`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMass_eq_integral`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMeasure`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMeasure_finite`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatialMeasure_normalized`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatial_difference_fourth`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.spatial_difference_fourth_integrable`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.squareDifference`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.squareDifference_coe`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.squareDifference_norm`
- Dependency: [D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder](CosineNormalizedRemainder.md)
- Dependency: [D5/S3/Fourier/Asymptotics/L2ContinuousPrimitive](L2ContinuousPrimitive.md)
- Dependency: [D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos](SameNoiseSecondChaos.md)
