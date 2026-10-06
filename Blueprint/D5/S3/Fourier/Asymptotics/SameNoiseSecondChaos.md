# Same-noise second integral

## Abstract

Symmetric product-space kernels have a unique continuous centered-square integral on the same Gaussian noise.

**Theorem 1.1 (Original diagonal image).**

$$\forall X \in Type, SigmaX \in \operatorname{MeasurableSpace}\left(X\right), mu \in \operatorname{Measure}\left(X\right), hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right), Omega \in Type, SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega\right), hprob \in \operatorname{IsProbabilityMeasure}\left(P\right), W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, mu\right), \operatorname{Lp}\left(Real, 2, P\right)\right), hW \in \left(\forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{HasLaw}\left(\operatorname{representative}\left(\operatorname{apply}\left(W, f\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right),\; \forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{apply}\left(\operatorname{secondIntegral}\left(mu, P, W, hW\right), \operatorname{diagonalKernel}\left(mu, f\right)\right) = \operatorname{centeredSquare}\left(mu, P, W, hW, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.secondIntegral_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The continuous second integral sends each actual diagonal kernel to the centered square of the same original W. The constant vector supplies the centered Y square in the finite-frequency remainder.

**Theorem 1.2 (Constant vector representative).**

$$\forall mu \in \operatorname{Measure}\left(Real\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{oneVector}\left(mu\right)\right), (x:Real\mapsto 1), mu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.oneVector_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every finite measure on the real line, the constant L2 vector has representative one almost everywhere. Its diagonal product therefore represents the constant spatial kernel.

**Theorem 1.3 (Density in the actual symmetric space).**

$$\forall X \in Type, SigmaX \in \operatorname{MeasurableSpace}\left(X\right), mu \in \operatorname{Measure}\left(X\right), hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \operatorname{DenseRange}\left(\operatorname{finiteKernelMap}\left(mu\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteKernelMap_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every finite measure mu on any measurable space X, the range of the finite diagonal-kernel map is dense in the fixed subspace of coordinate swap in L2(mu times mu). No normalization, positive mass or finite-dimensional restriction is imposed.

A kernel orthogonal to every rank-one class has zero integral on every measurable rectangle. Rectangles generate the product sigma algebra; complements and disjoint countable unions preserve zero integrals. The kernel therefore vanishes almost everywhere. For a symmetric kernel, polarization of diagonal generators and invariance of inner products under swap reduce diagonal orthogonality to rank-one orthogonality. The symmetric subspace is closed and complete.

**Theorem 1.4 (Continuous extension and characterization).**

$$\forall X \in Type, SigmaX \in \operatorname{MeasurableSpace}\left(X\right), mu \in \operatorname{Measure}\left(X\right), hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right), Omega \in Type, SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega\right), hprob \in \operatorname{IsProbabilityMeasure}\left(P\right), W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, mu\right), \operatorname{Lp}\left(Real, 2, P\right)\right), hW \in \left(\forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{HasLaw}\left(\operatorname{representative}\left(\operatorname{apply}\left(W, f\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right),\; \left(\left(\left(\forall k \in \operatorname{symmetricKernel}\left(mu\right),\; \operatorname{Integral}\left(P, (omega:Omega\mapsto \operatorname{evaluation}\left(\operatorname{apply}\left(\operatorname{secondIntegral}\left(mu, P, W, hW\right), k\right), omega\right))\right) = 0\right) \land \left(\forall k \in \operatorname{symmetricKernel}\left(mu\right),\; \forall l \in \operatorname{symmetricKernel}\left(mu\right),\; \operatorname{inner}\left(\operatorname{apply}\left(\operatorname{secondIntegral}\left(mu, P, W, hW\right), k\right), \operatorname{apply}\left(\operatorname{secondIntegral}\left(mu, P, W, hW\right), l\right)\right) = 2 \cdot \operatorname{inner}\left(k, l\right)\right)\right) \land \left(\forall k \in \operatorname{symmetricKernel}\left(mu\right),\; \operatorname{norm}\left(\operatorname{apply}\left(\operatorname{secondIntegral}\left(mu, P, W, hW\right), k\right)\right) = \operatorname{sqrt}\left(2\right) \cdot \operatorname{norm}\left(k\right)\right)\right) \land \left(\forall J \in \operatorname{ContinuousLinearMap}\left(Real, \operatorname{symmetricKernel}\left(mu\right), \operatorname{Lp}\left(Real, 2, P\right)\right),\; \left(\forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{apply}\left(J, \operatorname{diagonalKernel}\left(mu, f\right)\right) = \operatorname{centeredSquare}\left(mu, P, W, hW, f\right)\right) \Rightarrow J = \operatorname{secondIntegral}\left(mu, P, W, hW\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.secondIntegral_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Let P be a probability measure and W a fixed real linear isometry from L2(mu) to L2(P), with each W(f) having centered Gaussian law of variance ||f||^2. The second integral extends the finite coefficient assignment continuously to the full actual symmetric product-space L2 subspace.

Every output has mean zero. For arbitrary symmetric kernels k and l its covariance is 2 inner(k,l), and its norm is sqrt(2)||k||. It is the unique continuous real linear map sending each diagonal kernel f(x)f(y) to the actual class W(f)^2-||f||^2. Density passes the finite Gram identity and mean to the full space. Every random variable uses the original W and P.

**Theorem 1.5 (Actual symmetrized products).**

$$\forall X \in Type, SigmaX \in \operatorname{MeasurableSpace}\left(X\right), mu \in \operatorname{Measure}\left(X\right), hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right), Omega \in Type, SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega\right), hprob \in \operatorname{IsProbabilityMeasure}\left(P\right), W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, mu\right), \operatorname{Lp}\left(Real, 2, P\right)\right), hW \in \left(\forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{HasLaw}\left(\operatorname{representative}\left(\operatorname{apply}\left(W, f\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right),\; \forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \forall g \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{AlmostEverywhere}\left(\operatorname{prod}\left(mu, mu\right), (z:\operatorname{Prod}\left(X, X\right)\mapsto \operatorname{evaluation}\left(\operatorname{val}\left(\operatorname{symmetrizedKernel}\left(mu, f, g\right)\right), z\right) = \frac{\operatorname{evaluation}\left(f, \operatorname{fst}\left(z\right)\right) \cdot \operatorname{evaluation}\left(g, \operatorname{snd}\left(z\right)\right)+\operatorname{evaluation}\left(g, \operatorname{fst}\left(z\right)\right) \cdot \operatorname{evaluation}\left(f, \operatorname{snd}\left(z\right)\right)}{2})\right) \land \operatorname{AlmostEverywhere}\left(P, (omega:Omega\mapsto \operatorname{evaluation}\left(\operatorname{apply}\left(\operatorname{secondIntegral}\left(mu, P, W, hW\right), \operatorname{symmetrizedKernel}\left(mu, f, g\right)\right), omega\right) = \operatorname{evaluation}\left(\operatorname{apply}\left(W, f\right), omega\right) \cdot \operatorname{evaluation}\left(\operatorname{apply}\left(W, g\right), omega\right)-\operatorname{inner}\left(f, g\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.secondIntegral_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For all f and g in L2(mu), symmetrizedKernel(f,g) has the product-measure representative (f(x)g(y)+g(x)f(y))/2. Its second integral has the almost-everywhere representative W(f)W(g)-inner(f,g) on the original probability space. Both conclusions include zero vectors, zero measure and linearly dependent vectors.

**Theorem 1.6 (Exact finite Gram identity).**

$$\forall X \in Type, SigmaX \in \operatorname{MeasurableSpace}\left(X\right), mu \in \operatorname{Measure}\left(X\right), hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right), Omega \in Type, SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega\right), hprob \in \operatorname{IsProbabilityMeasure}\left(P\right), W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, mu\right), \operatorname{Lp}\left(Real, 2, P\right)\right), hW \in \left(\forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{HasLaw}\left(\operatorname{representative}\left(\operatorname{apply}\left(W, f\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right),\; \forall c \in \operatorname{Finsupp}\left(\operatorname{Lp}\left(Real, 2, mu\right), Real\right),\; \forall b \in \operatorname{Finsupp}\left(\operatorname{Lp}\left(Real, 2, mu\right), Real\right),\; \operatorname{inner}\left(\operatorname{finiteNoiseMap}\left(mu, P, W, hW, c\right), \operatorname{finiteNoiseMap}\left(mu, P, W, hW, b\right)\right) = 2 \cdot \operatorname{inner}\left(\operatorname{finiteKernelMap}\left(mu, c\right), \operatorname{finiteKernelMap}\left(mu, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Let mu be any finite measure, P a probability law, and W a fixed real linear isometry from H=L2(mu) to L2(P). Assume every W(f) has Gaussian law N(0,||f||^2). Spatial measure is not normalized. The rank-one class r(f,g) is represented by f(x)g(y) in L2(mu times mu); the symmetric subspace is the kernel of flip minus identity.

For finite real coefficients c on H, let e(c) be the sum of c(h)r(h,h) and j(c) the sum of c(h)(W(h)^2-||h||^2). Exact scalar fourth moments and the sum-and-difference polarization give the centered-square covariance 2 inner(f,g)^2. Fubini gives the spatial rank-one inner products. Consequently inner(j(c),j(b))=2 inner(e(c),e(b)).

The identity implies ||j(c)||=sqrt(2)||e(c)|| and e(c)=0 implies j(c)=0. Quotienting by the kernel of e therefore defines a bounded real linear map on the actual finite-kernel range. This map uses the given W and P throughout.

**Theorem 1.7 (Actual trigonometric frequency).**

$$\forall mu \in \operatorname{Measure}\left(Real\right), hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right), Omega \in Type, SigmaOmega \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega\right), hprob \in \operatorname{IsProbabilityMeasure}\left(P\right), W \in \operatorname{LinearIsometry}\left(Real, \operatorname{Lp}\left(Real, 2, mu\right), \operatorname{Lp}\left(Real, 2, P\right)\right), hW \in \left(\forall f \in \operatorname{Lp}\left(Real, 2, mu\right),\; \operatorname{HasLaw}\left(\operatorname{representative}\left(\operatorname{apply}\left(W, f\right)\right), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(f\right)^{2}\right)\right), P\right)\right),\; \forall v \in Real,\; \operatorname{AlmostEverywhere}\left(P, (omega:Omega\mapsto \operatorname{evaluation}\left(\operatorname{finiteSecondIntegral}\left(mu, P, W, hW\right), \operatorname{frequencyKernel}\left(mu, v\right), omega\right) = \operatorname{evaluation}\left(W, \operatorname{cosineVector}\left(mu, v\right), omega\right)^{2}+\operatorname{evaluation}\left(W, \operatorname{sineVector}\left(mu, v\right), omega\right)^{2}-\operatorname{evaluation}\left(W, \operatorname{oneVector}\left(mu\right), omega\right)^{2})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteFrequency_sameNoise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every real v, set c_v(x)=cos((pi/2)vx), s_v(x)=sin((pi/2)vx) and let 1 be the constant spatial vector. The finite coefficient vector consists of c_v and s_v with coefficient one and 1 with coefficient minus one. Its symmetric kernel has the actual representative cos((pi/2)v(x-y))-1.

The norm-square sum ||c_v||^2+||s_v||^2=||1||^2 equals the original spatial mass. Centering therefore cancels exactly. The finite second integral has the almost-everywhere representative W(c_v)^2+W(s_v)^2-W(1)^2, which is |F(v)|^2-Y^2 for F(v)=W(c_v)-iW(s_v) and Y=W(1).

The finite frequency identity agrees with the continuous extension on its actual finite-kernel input. Frequency integration and the singular logarithmic kernel require additional analytic statements; common continuous paths and process convergence require separate probability results.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteFrequency_sameNoise`
- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteGram`
- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.finiteKernelMap_dense`
- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.oneVector_coe`
- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.secondIntegral_characterization`
- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.secondIntegral_diagonal`
- Truth anchor: `D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos.secondIntegral_product`
- Dependency: [D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment](CountableGaussianQuadraticFourthMoment.md)
