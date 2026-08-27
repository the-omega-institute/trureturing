# Least-Squares Reconstruction Noise Bound

## Abstract

Full-column-rank least-squares reconstruction is stable under additive noise.

**Theorem 1.1 (A lower frame bound controls reconstruction error).**

$$\begin{aligned}\forall State, Observation: \operatorname{Type},\\{}[\operatorname{NormedAddCommGroup}(State)], [\operatorname{InnerProductSpace}(\mathbb{R}, State)], [\operatorname{FiniteDimensional}(\mathbb{R}, State)],\\{}[\operatorname{NormedAddCommGroup}(Observation)], [\operatorname{InnerProductSpace}(\mathbb{R}, Observation)], [\operatorname{FiniteDimensional}(\mathbb{R}, Observation)],\\\forall measurement: \operatorname{LinearMap}(\mathbb{R}, State, Observation), \alpha: \mathbb{R},\\{}0 < \alpha \Rightarrow\\{}\forall difference: State, \alpha \left\lVert difference \right\rVert^{2} \leq \left\lVert \operatorname{measurement}(difference) \right\rVert^{2} \Rightarrow\\{}\forall trueState, reconstructed: State, data, noise: Observation,\\{}data = \operatorname{measurement}(trueState) + noise \Rightarrow\\{}\operatorname{adjoint}(measurement)(\operatorname{measurement}(reconstructed) - data) = 0 \Rightarrow\\{}\left\lVert reconstructed - trueState \right\rVert \leq \frac{\left\lVert noise \right\rVert}{\sqrt{\alpha}}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/LeastSquaresReconstructionNoiseBound.least_squares_reconstruction_noise_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measurement operator is defined on arbitrary finite-dimensional real inner-product spaces. A positive lower frame bound makes it injective and supplies the smallest-singular-value scale.

The reconstructed state is characterized publicly by the exact least-squares normal equation. Under the lower frame premise this is the full-column-rank Moore--Penrose reconstruction.

Normal-equation orthogonality bounds the measured reconstruction error by the noise norm. The lower frame inequality then gives the sharp inverse-square-root stability factor.

## References

- Truth anchor: `D5/S3/Observer/Linear/LeastSquaresReconstructionNoiseBound.least_squares_reconstruction_noise_bound`
