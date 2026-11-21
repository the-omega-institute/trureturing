# Chebyshev interpolation at the reflecting heat rates

## Abstract

Chebyshev interpolation at the reflecting heat rates

The rates qⱼ and weights bⱼ are those of the finite strip lower bound. For j in Fin(n−1), the angle θⱼ is π(j+1)/n. Write Qₙ for the full nodal polynomial and Qₙⱼ for the one with the j-th node omitted. The signed product of gaps is Dⱼ. The reflecting-path critical crossover proof uses these quantities in equations (11)–(12) and (35)–(38).

**Theorem 1.1 (Monic Chebyshev nodal polynomial).**

$$Q_{n}\left(w\right)=\prod_{k\in Fin\left(n-1\right)} (w-q_{k})=U_{n-1}\left(\frac{w-2}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatInterpolation.nodalPolynomial_eq_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine change of variables takes the Chebyshev roots to the reflecting rates. The leading coefficient becomes one.

**Theorem 1.2 (Exact normalization at each node).**

$$\left|D_{j}\right|=\frac{n}{2 (\sin\left(\theta_{j}\right))^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatInterpolation.abs_nodalDerivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate the Chebyshev sine identity on the reflecting grid. The omitted node factor gives the derivative of the full polynomial at that node.

**Theorem 1.3 (Uniform bounds through both edge modes).**

$$\frac{n}{2}\le \left|D_{j}\right|\le \frac{n^{3}}{8} \land \frac{4}{n^{2}}\le q_{j} \land \frac{4}{n^{2}}\le 4-q_{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatInterpolation.uniform_nodal_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sine chord bound controls the smallest sine and the distances to both endpoints of the spectral interval.

**Theorem 1.4 (Normalization with the physical endpoint weight).**

$$\frac{n}{b_{j} \left|D_{j}\right|}=q_{j} b_{j} \land \frac{4}{n^{2}}\le q_{j} b_{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatInterpolation.endpoint_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relation between the squared sine and the physical squared weight cancels the nodal derivative as in equation (12). The endpoint estimates bound the resulting factor below uniformly.

**Theorem 1.5 (Growth of the omitted polynomial on the imaginary axis).**

$$\zeta\neq 0 \land \zeta+\zeta^{-1}=i \omega-2 \land 1\le \left|\zeta\right| \Rightarrow \left|Q_{n,j}\left(i \omega\right)\right|\le \frac{n \left|\zeta\right|^{n-1}}{\sqrt{q_{j}^{2}+\omega^{2}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatInterpolation.norm_omittedPolynomial_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second-kind polynomial expands as a finite geometric sum in the outer Joukowski root. Removing a node supplies the exact distance in the denominator, including at zero frequency.

The Fourier-side interpolant is $\psi_{n,j}\left(z\right)=Q_{n,j}\left(i z\right) M\left(z\right)$. At −iqₖ the omitted polynomial is evaluated at qₖ. Mathlib’s Lagrange.eval_nodal gives the product of gaps on the diagonal, and Lagrange.eval_nodal_at_node gives zero off the diagonal.

$\psi_{n,j}\left(-i q_{j}\right)=D_{j} M\left(-i q_{j}\right)$ and $k\neq j \Rightarrow \psi_{n,j}\left(-i q_{k}\right)=0$.

**Theorem 1.6 (Square-integrable envelope for the moment interpolant).**

$$\operatorname{Measurable}\left(M\rvert_{\mathbb{R}}\right) \land (\forall \omega, \exists \zeta, \zeta\neq 0 \land \zeta+\zeta^{-1}=i \omega-2 \land 1\le \left|\zeta\right| \land \left|M\left(\omega\right)\right|\le \frac{A(1+B \left|\omega\right|)}{\left|\zeta\right|^{n}})\\\Rightarrow \psi_{n,j}\in \left(L^{2}\right)\left(\mathbb{R}\right) \land \int_{\mathbb{R}} \left|\psi_{n,j}\left(\omega\right)\right|^{2} d \omega\le 2(nA)^{2} \pi(\frac{n^{2}}{4}+2B^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatInterpolation.momentInterpolant_L2_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplier envelope has inverse radius to power n, while the omitted polynomial has radius to power n−1. The remaining inverse radius controls the linear factor in frequency. Squaring gives two integrable Cauchy kernels. Their integrals and the lower bound on qⱼ give the uniform squared-norm estimate.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatInterpolation.abs_nodalDerivative`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatInterpolation.endpoint_normalization`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatInterpolation.momentInterpolant_L2_bound`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatInterpolation.nodalPolynomial_eq_chebyshev`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatInterpolation.norm_omittedPolynomial_eval`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatInterpolation.uniform_nodal_factors`
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatStripBound](ReflectingHeatStripBound.md)
