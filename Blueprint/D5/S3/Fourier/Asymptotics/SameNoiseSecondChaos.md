# Finite same-noise second integral

## Abstract

Finite symmetric kernel sums have a well-defined centered-square integral on the same Gaussian noise.

**Theorem 1.1 (Exact finite Gram identity).**

$$\forall X \in Type, SigmaX \in \operatorname{MeasurableSpace}\left(X\right), mu \in \operatorname{Measure}\left(X\right), Omega \in Type, SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega\right), W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, mu\right), \operatorname{Lp}\left(Real, 2, P\right)\right),\; \left(\operatorname{IsFiniteMeasure}\left(mu\right) \land \left(\operatorname{IsProbabilityMeasure}\left(P\right) \land \left(\forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{HasLaw}\left(\operatorname{evaluation}\left(W, f\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right)\right)\right) \Rightarrow \left(\forall c \in \operatorname{Finsupp}\left(\operatorname{Lp}\left(Real, 2, mu\right), Real\right),\; \forall b \in \operatorname{Finsupp}\left(\operatorname{Lp}\left(Real, 2, mu\right), Real\right),\; \operatorname{inner}\left(\operatorname{finiteNoiseMap}\left(mu, P, W, hW, c\right), \operatorname{finiteNoiseMap}\left(mu, P, W, hW, b\right)\right) = 2 \cdot \operatorname{inner}\left(\operatorname{finiteKernelMap}\left(mu, c\right), \operatorname{finiteKernelMap}\left(mu, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Let mu be any finite measure, P a probability law, and W a fixed real linear isometry from H=L2(mu) to L2(P). Assume every W(f) has Gaussian law N(0,||f||^2). Spatial measure is not normalized. The rank-one class r(f,g) is represented by f(x)g(y) in L2(mu times mu); the symmetric subspace is the kernel of flip minus identity.

For finite real coefficients c on H, let e(c) be the sum of c(h)r(h,h) and j(c) the sum of c(h)(W(h)^2-||h||^2). Exact scalar fourth moments and the sum-and-difference polarization give the centered-square covariance 2 inner(f,g)^2. Fubini gives the spatial rank-one inner products. Consequently inner(j(c),j(b))=2 inner(e(c),e(b)).

The identity implies ||j(c)||=sqrt(2)||e(c)|| and e(c)=0 implies j(c)=0. Quotienting by the kernel of e therefore defines a bounded real linear map on the actual finite-kernel range. This map uses the given W and P throughout.

**Theorem 1.2 (Actual trigonometric frequency).**

$$\forall X \in Real, SigmaX \in \operatorname{MeasurableSpace}\left(X\right), mu \in \operatorname{Measure}\left(X\right), Omega \in Type, SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega\right), W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, mu\right), \operatorname{Lp}\left(Real, 2, P\right)\right),\; \left(\operatorname{IsFiniteMeasure}\left(mu\right) \land \left(\operatorname{IsProbabilityMeasure}\left(P\right) \land \left(\forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{HasLaw}\left(\operatorname{evaluation}\left(W, f\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right)\right)\right) \Rightarrow \left(\forall v \in Real,\; \operatorname{AlmostEverywhere}\left(P, \forall omega \in Omega,\; \operatorname{evaluation}\left(\operatorname{finiteSecondIntegral}\left(mu, P, W, hW\right), \operatorname{frequencyKernel}\left(mu, v\right), omega\right) = \operatorname{evaluation}\left(W, \operatorname{cosineVector}\left(mu, v\right), omega\right)^{2}+\operatorname{evaluation}\left(W, \operatorname{sineVector}\left(mu, v\right), omega\right)^{2}-\operatorname{evaluation}\left(W, \operatorname{oneVector}\left(mu\right), omega\right)^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteFrequency_sameNoise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every real v, set c_v(x)=cos((pi/2)vx), s_v(x)=sin((pi/2)vx) and let 1 be the constant spatial vector. The finite coefficient vector consists of c_v and s_v with coefficient one and 1 with coefficient minus one. Its symmetric kernel has the actual representative cos((pi/2)v(x-y))-1.

The norm-square sum ||c_v||^2+||s_v||^2=||1||^2 equals the original spatial mass. Centering therefore cancels exactly. The finite second integral has the almost-everywhere representative W(c_v)^2+W(s_v)^2-W(1)^2, which is |F(v)|^2-Y^2 for F(v)=W(c_v)-iW(s_v) and Y=W(1).

The statements concern the actual finite-kernel range. Extension to all symmetric product-space kernels requires density of this range. Frequency integration and the singular logarithmic kernel require additional analytic statements.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteFrequency_sameNoise`
- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteGram`
- Dependency: [D5/S3/Fourier/Asymptotics/GaussianEvenMoment](GaussianEvenMoment.md)
