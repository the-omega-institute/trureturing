# Center-Fiber Moment Representation

## Abstract

Even difference moments are Fourier transforms of nonnegative center-fiber densities.

**Theorem 1.1 (The center-fiber density represents the even moment).**

$$\begin{gathered}\forall \varphi: \mathbb{R} \to \mathbb{R}, m\in \mathbb{N}, t\in \mathbb{R},\\{}\operatorname{Continuous}\left(\varphi\right) \land (\forall x\in \mathbb{R}, 0 \leq \varphi\left(x\right)) \land\\{}\operatorname{Integrable}\left(((u, v) \mapsto v^{2m}\varphi\left(\frac{u+v}{2}\right)\varphi\left(\frac{u-v}{2}\right))\right) \Rightarrow\\{}\left(C_{m}\right)\left(u\right) = \frac{1}{2\operatorname{factorial}\left(2m\right)} \int_{\mathbb{R}} v^{2m}\varphi\left(\frac{u+v}{2}\right)\varphi\left(\frac{u-v}{2}\right) dv,\\{}\left(\mathcal{J}_{m}\right)\left(t\right) = \frac{1}{\operatorname{factorial}\left(2m\right)} \int_{\mathbb{R}} \int_{\mathbb{R}} \varphi\left(x\right)\varphi\left(y\right){x-y}^{2m}\operatorname{exp}\left(i t {x+y}\right) dy dx,\\{}\left(\mathcal{J}_{m}\right)\left(t\right) = \int_{\mathbb{R}} \left(C_{m}\right)\left(u\right)\operatorname{exp}\left(i t u\right) du \land \forall u\in \mathbb{R}, 0 \leq \left(C_{m}\right)\left(u\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CenterFiberMomentRepresentation.center_fiber_moment_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let phi be a continuous nonnegative real function. The source did not state the positivity assumption needed for the claimed pointwise nonnegativity of C_m, so it is explicit here.

We also require absolute integrability of the real center-fiber moment kernel. This supplies the missing analytic hypothesis for Fubini and for both displayed Lebesgue integrals.

The proof applies the real linear map (x,y) maps to (x+y,x-y). Its determinant is minus two, so the inverse Jacobian contributes the factor one half in C_m.

Pinned Mathlib supplies Haar-measure transport for an invertible linear map and Fubini's theorem. Evenness of the exponent and nonnegativity of phi give C_m(u) nonnegative for every real u.

## References

- Truth anchor: `D5/S3/Fourier/CenterFiberMomentRepresentation.center_fiber_moment_representation`
