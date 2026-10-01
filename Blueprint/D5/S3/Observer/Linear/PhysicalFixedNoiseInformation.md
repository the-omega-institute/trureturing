# Fixed-noise exponential-Gramian information expansion

## Abstract

Fixed-noise exponential-Gramian information expansion

**Theorem 1.1 (Fixed-noise exponential-Gramian information expansion).**

$$\begin{gathered}\forall V, W, B, C, \beta, \mathit{eta},\\{}\operatorname{InnerProductSpace}(\mathbb{R}, V) \land \operatorname{FiniteDimensional}(\mathbb{R}, V) \land \operatorname{InnerProductSpace}(\mathbb{R}, W) \land \operatorname{CompleteSpace}(W),\\{}B: V \to V, C: V \to W, \beta>0 \land \mathit{eta}>0,\\{}H=C^{*} C, \operatorname{A}(t)=C \exp(t B), \operatorname{G}(T)=\int_{0}^{T} \operatorname{A}(t)^{*} \operatorname{A}(t) dt,\\{}\exists K, \delta: K\ge0 \land \delta>0 \land \forall T, 0<T\le\delta \Rightarrow \left|\frac{1}{2} \log(\operatorname{det}(\operatorname{id}(V)+(\beta \mathit{eta})^{-1} \operatorname{G}(T)))-\frac{T}{2 \beta \mathit{eta}} \operatorname{tr}(H)\right|\le K T^{2}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/PhysicalFixedNoiseInformation.physical_fixed_noise_information` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a finite-dimensional real inner-product space, W a complete real inner-product space, and B:V→V and C:V→W bounded linear maps. Zero-dimensional spaces and unobserved directions are allowed. Fix a positive prior precision beta and a positive coordinate-noise variance eta.

Define H as the adjoint of C composed with C. Define G(T) as the actual Bochner integral from zero to T of the adjoint of C exp(t B) composed with C exp(t B). The determinant and trace are those of the finite-dimensional state operator, and the norm is the induced Hilbert operator norm.

There are K at least zero and delta greater than zero such that for every positive T at most delta, the absolute difference between one half log det(id+(beta eta)^(-1)G(T)) and T trace(H)/(2 beta eta) is at most K T squared.

Differentiability of the exponential integrand yields a uniform bound for G(T)-T H of order T squared. Positivity of G(T), its actual orthonormal eigenbasis, and a scalar logarithmic remainder bound control the determinant. An orthonormal trace estimate combines these errors.

The result concerns the actual exponential-Gramian log determinant. In a finite-coordinate linear Gaussian observation model with state covariance beta^(-1)I, independent isotropic coordinate noise covariance eta I, and observation-coordinate Gramian G(T), this expression is mutual information in nats. Polynomial moment compression requires its own finite-time estimate.

## References

- Truth anchor: `D5/S3/Observer/Linear/PhysicalFixedNoiseInformation.physical_fixed_noise_information`
