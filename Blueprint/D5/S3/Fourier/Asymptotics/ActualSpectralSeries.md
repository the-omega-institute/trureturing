# Actual kernel spectral construction

## Abstract

Actual integral kernels have complete same-noise spectral series, including nullspace and zero variance.

**Theorem 1.1 (Actual kernel pairing).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right), \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right)\right),\; \forall hT \in \left(\forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{AEEq}\left((x:X\mapsto\operatorname{T}\left(K, f, x\right)), (x:X\mapsto\operatorname{integral}\left((y:X\mapsto\operatorname{mul}\left(\operatorname{K}\left(\operatorname{pair}\left(x, y\right)\right), \operatorname{f}\left(y\right)\right)), mu\right)), mu\right)\right),\; \forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \forall g \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{Eq}\left(\operatorname{inner}\left(\operatorname{Real}\left(\right), \operatorname{T}\left(K, f\right), g\right), \operatorname{inner}\left(\operatorname{Real}\left(\right), \operatorname{rankOne}\left(mu, g, f\right), K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every finite measure and every continuous kernel factory with the actual a.e. integral representation, Fubini identifies the operator pairing with the product-space rank-one pairing. Integrability follows from the two actual L2 classes.

**Theorem 1.2 (Kernel identification).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right), \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right)\right),\; \forall hT \in \left(\forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{AEEq}\left((x:X\mapsto\operatorname{T}\left(K, f, x\right)), (x:X\mapsto\operatorname{integral}\left((y:X\mapsto\operatorname{mul}\left(\operatorname{K}\left(\operatorname{pair}\left(x, y\right)\right), \operatorname{f}\left(y\right)\right)), mu\right)), mu\right)\right),\; \operatorname{Injective}\left(T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Equality of actual integral operators implies equality of their L2 kernels. The proof consumes the pairing identity and the original rank-one totality supplier; it introduces no identification premise.

**Theorem 1.3 (Actual rank-one operator).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right), \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right)\right),\; \forall hT \in \left(\forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{AEEq}\left((x:X\mapsto\operatorname{T}\left(K, f, x\right)), (x:X\mapsto\operatorname{integral}\left((y:X\mapsto\operatorname{mul}\left(\operatorname{K}\left(\operatorname{pair}\left(x, y\right)\right), \operatorname{f}\left(y\right)\right)), mu\right)), mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \forall g \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{Eq}\left(\operatorname{T}\left(\operatorname{rankOne}\left(mu, f, f\right), g\right), \operatorname{smul}\left(\operatorname{inner}\left(\operatorname{Real}\left(\right), f, g\right), f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

A diagonal kernel acts by f times inner(f,g) on the original spatial Hilbert space. This consumed helper identifies every finite approximation used to prove compactness.

**Theorem 1.4 (Kernel symmetry).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right), \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right)\right),\; \forall hT \in \left(\forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{AEEq}\left((x:X\mapsto\operatorname{T}\left(K, f, x\right)), (x:X\mapsto\operatorname{integral}\left((y:X\mapsto\operatorname{mul}\left(\operatorname{K}\left(\operatorname{pair}\left(x, y\right)\right), \operatorname{f}\left(y\right)\right)), mu\right)), mu\right)\right),\; \forall K \in \operatorname{symmetricKernel}\left(mu\right),\; \operatorname{IsSymmetric}\left(\operatorname{T}\left(\operatorname{val}\left(K\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The fixed subspace of coordinate swap gives a symmetric actual operator. Swap is an isometry on the same product measure, and the rank-one swap supplier is consumed in the proof.

**Theorem 1.5 (Compactness from actual kernels).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right), \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right)\right),\; \forall hT \in \left(\forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{AEEq}\left((x:X\mapsto\operatorname{T}\left(K, f, x\right)), (x:X\mapsto\operatorname{integral}\left((y:X\mapsto\operatorname{mul}\left(\operatorname{K}\left(\operatorname{pair}\left(x, y\right)\right), \operatorname{f}\left(y\right)\right)), mu\right)), mu\right)\right),\; \forall K \in \operatorname{symmetricKernel}\left(mu\right),\; \operatorname{IsCompactOperator}\left(\operatorname{T}\left(\operatorname{val}\left(K\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Dense finite diagonal-kernel sums map to genuine finite-rank operators. Continuity of the kernel factory and the closedness of compact operators pass compactness to every actual symmetric L2 kernel. Compactness is constructed, not assumed.

**Theorem 1.6 (Complete countable eigenfamily).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right), \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right)\right),\; \forall hT \in \left(\forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{AEEq}\left((x:X\mapsto\operatorname{T}\left(K, f, x\right)), (x:X\mapsto\operatorname{integral}\left((y:X\mapsto\operatorname{mul}\left(\operatorname{K}\left(\operatorname{pair}\left(x, y\right)\right), \operatorname{f}\left(y\right)\right)), mu\right)), mu\right)\right),\; \forall hgenerated \in \operatorname{CountablyGenerated}\left(X\right),\; \forall K \in \operatorname{symmetricKernel}\left(mu\right),\; \exists index \in Type,\; \exists hcount \in \operatorname{Countable}\left(index\right),\; \exists b \in \operatorname{HilbertBasis}\left(index, \operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \exists c \in \operatorname{Function}\left(index, \operatorname{Real}\left(\right)\right),\; \forall i \in index,\; \operatorname{Eq}\left(\operatorname{apply}\left(\operatorname{T}\left(\operatorname{val}\left(K\right)\right), \operatorname{b}\left(i\right)\right), \operatorname{smul}\left(\operatorname{c}\left(i\right), \operatorname{b}\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_eigenbasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Nonzero eigenspaces use the pinned finite-dimensional eigenspace theorem and finite orthonormal bases. Their Hilbert bases and the zero-eigenspace Hilbert basis are assembled using the pinned compact spectral totality theorem. The zero eigenspace is retained. Orthonormality and separability make the resulting family countable, including empty and zero-operator cases.

**Theorem 1.7 (Diagonal orthonormality).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall index \in Type,\; \forall e \in \operatorname{Function}\left(index, \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \operatorname{Orthonormal}\left(\operatorname{Real}\left(\right), e\right) \Rightarrow \operatorname{Orthonormal}\left(\operatorname{Real}\left(\right), (i:index\mapsto\operatorname{diagonalKernel}\left(mu, \operatorname{e}\left(i\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.diagonal_orthonormal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

An orthonormal spatial family gives an orthonormal family of diagonal kernels under the product-measure inner product.

**Theorem 1.8 (Complete actual kernel series).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right), \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right)\right),\; \forall hT \in \left(\forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{AEEq}\left((x:X\mapsto\operatorname{T}\left(K, f, x\right)), (x:X\mapsto\operatorname{integral}\left((y:X\mapsto\operatorname{mul}\left(\operatorname{K}\left(\operatorname{pair}\left(x, y\right)\right), \operatorname{f}\left(y\right)\right)), mu\right)), mu\right)\right),\; \forall K \in \operatorname{symmetricKernel}\left(mu\right),\; \forall index \in Type,\; \forall hcount \in \operatorname{Countable}\left(index\right),\; \forall b \in \operatorname{HilbertBasis}\left(index, \operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \forall c \in \operatorname{Function}\left(index, \operatorname{Real}\left(\right)\right),\; \left(\forall i \in index,\; \operatorname{Eq}\left(\operatorname{apply}\left(\operatorname{T}\left(\operatorname{val}\left(K\right)\right), \operatorname{b}\left(i\right)\right), \operatorname{smul}\left(\operatorname{c}\left(i\right), \operatorname{b}\left(i\right)\right)\right)\right) \Rightarrow \operatorname{HasSum}\left((i:index\mapsto\operatorname{smul}\left(\operatorname{c}\left(i\right), \operatorname{diagonalKernel}\left(mu, \operatorname{b}\left(i\right)\right)\right)), K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.kernel_hasSum_of_eigenbasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Bessel gives square summability of actual diagonal-kernel coefficients. Its convergent kernel series has the same action on every eigenbasis vector as the original operator. Completeness and kernel-to-operator injectivity identify the limit with the original K. No kernel HasSum is supplied as a premise.

**Theorem 1.9 (Consumed same-noise transport).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall Omega \in Type,\; \forall mOmega \in \operatorname{MeasurableSpace}\left(Omega\right),\; \forall P \in \operatorname{Measure}\left(Omega\right),\; \forall hprob \in \operatorname{IsProbabilityMeasure}\left(P\right),\; \forall W \in \operatorname{LinearIsometry}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, P\right)\right),\; \forall hW \in \left(\forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{HasLaw}\left((omega:Omega\mapsto\operatorname{W}\left(f, omega\right)), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{pow}\left(\operatorname{norm}\left(f\right), 2\right)\right)\right), P\right)\right),\; \forall K \in \operatorname{symmetricKernel}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \forall index \in Type,\; \forall hcount \in \operatorname{Countable}\left(index\right),\; \forall e \in \operatorname{Function}\left(index, \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \forall coeff \in \operatorname{Function}\left(index, \operatorname{Real}\left(\right)\right),\; \left(\operatorname{Orthonormal}\left(\operatorname{Real}\left(\right), e\right) \land \left(\left(\forall i \in index,\; \operatorname{Eq}\left(\operatorname{T}\left(\operatorname{e}\left(i\right)\right), \operatorname{smul}\left(\operatorname{coeff}\left(i\right), \operatorname{e}\left(i\right)\right)\right)\right) \land \operatorname{HasSum}\left((i:index\mapsto\operatorname{smul}\left(\operatorname{coeff}\left(i\right), \operatorname{diagonalKernel}\left(mu, \operatorname{e}\left(i\right)\right)\right)), K\right)\right)\right) \Rightarrow \left(\operatorname{Summable}\left((i:index\mapsto\operatorname{pow}\left(\operatorname{coeff}\left(i\right), 2\right))\right) \land \left(\operatorname{Eq}\left(\operatorname{tsum}\left((i:index\mapsto\operatorname{pow}\left(\operatorname{coeff}\left(i\right), 2\right))\right), \operatorname{pow}\left(\operatorname{norm}\left(K\right), 2\right)\right) \land \left(\operatorname{Eq}\left(\operatorname{pow}\left(\operatorname{norm}\left(K\right), 2\right), \operatorname{div}\left(\operatorname{variance}\left(\operatorname{secondIntegral}\left(mu, P, W, hW, K\right), P\right), 2\right)\right) \land \left(\left(\forall i \in index,\; \operatorname{Le}\left(\operatorname{abs}\left(\operatorname{coeff}\left(i\right)\right), \operatorname{norm}\left(T\right)\right)\right) \land \left(\operatorname{Le}\left(\operatorname{iSup}\left((i:index\mapsto\operatorname{abs}\left(\operatorname{coeff}\left(i\right)\right))\right), \operatorname{norm}\left(T\right)\right) \land \operatorname{HasSum}\left((i:index\mapsto\operatorname{smul}\left(\operatorname{coeff}\left(i\right), \operatorname{centeredSquare}\left(mu, P, W, hW, \operatorname{e}\left(i\right)\right)\right)), \operatorname{secondIntegral}\left(mu, P, W, hW, K\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.same_noise_series_of_kernel_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

This conditional transport helper is consumed by actual_same_noise_spectral after kernel HasSum is constructed. It maps the kernel series through the original secondIntegral and derives exact square sum, variance and operator-norm bounds. It receives zero independent content credit.

**Theorem 1.10 (Joint laws of the original W).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall Omega \in Type,\; \forall mOmega \in \operatorname{MeasurableSpace}\left(Omega\right),\; \forall P \in \operatorname{Measure}\left(Omega\right),\; \forall hprob \in \operatorname{IsProbabilityMeasure}\left(P\right),\; \forall W \in \operatorname{LinearIsometry}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, P\right)\right),\; \forall hW \in \left(\forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{HasLaw}\left((omega:Omega\mapsto\operatorname{W}\left(f, omega\right)), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{pow}\left(\operatorname{norm}\left(f\right), 2\right)\right)\right), P\right)\right),\; \forall index \in Type,\; \forall hfiniteIndex \in \operatorname{Finite}\left(index\right),\; \forall f \in \operatorname{Function}\left(index, \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \operatorname{HasGaussianLaw}\left((omega:Omega\mapsto(i:index\mapsto\operatorname{W}\left(\operatorname{f}\left(i\right), omega\right))), P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.same_noise_finite_joint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Every scalar linear combination of the finite coordinates is an evaluation of the same W, almost everywhere. The pinned Gaussian linear-functional characterization yields the finite joint Gaussian law on the same P. No product noise or joint-Gaussian premise is introduced. Empty families and arbitrary old fixed vectors remain in scope.

**Theorem 1.11 (Finite row independence).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall Omega \in Type,\; \forall mOmega \in \operatorname{MeasurableSpace}\left(Omega\right),\; \forall P \in \operatorname{Measure}\left(Omega\right),\; \forall hprob \in \operatorname{IsProbabilityMeasure}\left(P\right),\; \forall W \in \operatorname{LinearIsometry}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, P\right)\right),\; \forall hW \in \left(\forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{HasLaw}\left((omega:Omega\mapsto\operatorname{W}\left(f, omega\right)), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{pow}\left(\operatorname{norm}\left(f\right), 2\right)\right)\right), P\right)\right),\; \forall index \in Type,\; \forall hfiniteIndex \in \operatorname{Finite}\left(index\right),\; \forall e \in \operatorname{Function}\left(index, \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \operatorname{Orthonormal}\left(\operatorname{Real}\left(\right), e\right) \Rightarrow \operatorname{iIndepFun}\left((i:index\mapsto(omega:Omega\mapsto\operatorname{W}\left(\operatorname{e}\left(i\right), omega\right))), P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.same_noise_finite_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

The constructed finite joint law and orthonormal covariance identity give independence on the original P. This consumed helper extends to the countable spectral row by finite restrictions; no independence from old vectors or between rows is claimed.

**Theorem 1.12 (Actual same-noise spectral representation).**

$$\forall X \in Type,\; \forall mX \in \operatorname{MeasurableSpace}\left(X\right),\; \forall mu \in \operatorname{Measure}\left(X\right),\; \forall hfinite \in \operatorname{IsFiniteMeasure}\left(mu\right),\; \forall T \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right), \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right)\right),\; \forall hT \in \left(\forall K \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, \operatorname{prod}\left(mu, mu\right)\right),\; \forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{AEEq}\left((x:X\mapsto\operatorname{T}\left(K, f, x\right)), (x:X\mapsto\operatorname{integral}\left((y:X\mapsto\operatorname{mul}\left(\operatorname{K}\left(\operatorname{pair}\left(x, y\right)\right), \operatorname{f}\left(y\right)\right)), mu\right)), mu\right)\right),\; \forall Omega \in Type,\; \forall mOmega \in \operatorname{MeasurableSpace}\left(Omega\right),\; \forall P \in \operatorname{Measure}\left(Omega\right),\; \forall hprob \in \operatorname{IsProbabilityMeasure}\left(P\right),\; \forall W \in \operatorname{LinearIsometry}\left(\operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, P\right)\right),\; \forall hW \in \left(\forall f \in \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right),\; \operatorname{HasLaw}\left((omega:Omega\mapsto\operatorname{W}\left(f, omega\right)), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{pow}\left(\operatorname{norm}\left(f\right), 2\right)\right)\right), P\right)\right),\; \forall hgenerated \in \operatorname{CountablyGenerated}\left(X\right),\; \forall K \in \operatorname{symmetricKernel}\left(mu\right),\; \exists index \in Type,\; \exists hcount \in \operatorname{Countable}\left(index\right),\; \exists b \in \operatorname{HilbertBasis}\left(index, \operatorname{Real}\left(\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \exists c \in \operatorname{Function}\left(index, \operatorname{Real}\left(\right)\right),\; \left(\forall i \in index,\; \operatorname{Eq}\left(\operatorname{apply}\left(\operatorname{T}\left(\operatorname{val}\left(K\right)\right), \operatorname{b}\left(i\right)\right), \operatorname{smul}\left(\operatorname{c}\left(i\right), \operatorname{b}\left(i\right)\right)\right)\right) \land \left(\operatorname{HasSum}\left((i:index\mapsto\operatorname{smul}\left(\operatorname{c}\left(i\right), \operatorname{diagonalKernel}\left(mu, \operatorname{b}\left(i\right)\right)\right)), K\right) \land \left(\left(\operatorname{Summable}\left((i:index\mapsto\operatorname{pow}\left(\operatorname{c}\left(i\right), 2\right))\right) \land \left(\operatorname{Eq}\left(\operatorname{tsum}\left((i:index\mapsto\operatorname{pow}\left(\operatorname{c}\left(i\right), 2\right))\right), \operatorname{pow}\left(\operatorname{norm}\left(K\right), 2\right)\right) \land \left(\operatorname{Eq}\left(\operatorname{pow}\left(\operatorname{norm}\left(K\right), 2\right), \operatorname{div}\left(\operatorname{variance}\left(\operatorname{secondIntegral}\left(mu, P, W, hW, K\right), P\right), 2\right)\right) \land \left(\left(\forall i \in index,\; \operatorname{Le}\left(\operatorname{abs}\left(\operatorname{c}\left(i\right)\right), \operatorname{norm}\left(\operatorname{T}\left(\operatorname{val}\left(K\right)\right)\right)\right)\right) \land \left(\operatorname{Le}\left(\operatorname{iSup}\left((i:index\mapsto\operatorname{abs}\left(\operatorname{c}\left(i\right)\right))\right), \operatorname{norm}\left(\operatorname{T}\left(\operatorname{val}\left(K\right)\right)\right)\right) \land \operatorname{HasSum}\left((i:index\mapsto\operatorname{smul}\left(\operatorname{c}\left(i\right), \operatorname{centeredSquare}\left(mu, P, W, hW, \operatorname{b}\left(i\right)\right)\right)), \operatorname{secondIntegral}\left(mu, P, W, hW, K\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{iIndepFun}\left((i:index\mapsto(omega:Omega\mapsto\operatorname{W}\left(\operatorname{b}\left(i\right), omega\right))), P\right) \land \left(\left(\forall i \in index,\; \operatorname{HasLaw}\left((omega:Omega\mapsto\operatorname{W}\left(\operatorname{b}\left(i\right), omega\right)), \operatorname{gaussianReal}\left(0, 1\right), P\right)\right) \land \left(\forall s \in \operatorname{Finset}\left(index\right),\; \forall n \in \operatorname{Nat}\left(\right),\; \forall old \in \operatorname{Function}\left(\operatorname{Fin}\left(n\right), \operatorname{Lp}\left(\operatorname{Real}\left(\right), 2, mu\right)\right),\; \operatorname{HasGaussianLaw}\left((omega:Omega\mapsto(j:\operatorname{Sum}\left(s, \operatorname{Fin}\left(n\right)\right)\mapsto\operatorname{W}\left(\operatorname{sumElim}\left((i:s\mapsto\operatorname{b}\left(\operatorname{val}\left(i\right)\right)), old, j\right), omega\right))), P\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.actual_same_noise_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every actual symmetric kernel, the construction returns a complete countable orthonormal eigenbasis, the complete kernel HasSum, exact coefficient square sum equal to the kernel norm squared and variance divided by two, coefficient and supremum operator bounds, and the actual infinite L2(P) second-integral series. Its standard Gaussian coordinates are independent within the row and jointly Gaussian with every finite old-vector append under the original W and P. Zero coefficients, nullspace and zero variance are included. Each row may have its own eigenbasis. This result does not assert the original covariance asymptotics, real-filter limit, increment estimates, path tightness, completed-field mixing or full original process goal.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.actual_same_noise_spectral`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.diagonal_orthonormal`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_compact`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_diagonal`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_eigenbasis`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_injective`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_pairing`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.integral_operator_symmetric`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.kernel_hasSum_of_eigenbasis`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.same_noise_finite_independence`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.same_noise_finite_joint`
- Truth anchor: `D5/S3/Fourier/Asymptotics/ActualSpectralSeries.same_noise_series_of_kernel_hasSum`
- Dependency: [D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos](SameNoiseSecondChaos.md)
