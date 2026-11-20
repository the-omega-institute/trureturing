# Exact Schur pivot for derivative layers

## Abstract

Exact Schur pivot for derivative layers

**Theorem 1.1 (Attained minimum for filtered vector polynomials).**

$$\begin{gathered}\forall W, [\operatorname{RealInnerProductSpace}\left(W\right)], \forall X: \mathbb{N} \to Type, [\operatorname{RealModuleFamily}\left(X\right)],\\\forall D: \prod_{i: \mathbb{N}} \operatorname{RealLinear}\left(X\left(i\right), W\right), \forall k: \mathbb{N}, \forall v: W,\\(\forall i\in \operatorname{Fin}\left(k\right), v\in \operatorname{range}\left(D\left(i\right)\right)) \Rightarrow\\\operatorname{IsLeast}\left(\{\int_{0}^{1} \left\lVert s^{k}\cdot v-\sum_{i\in \operatorname{Fin}\left(k\right)} s^{i}\cdot D\left(i\right)\left(a\left(i\right)\right) \right\rVert^{2} \mathrm{d}s \mid a: \prod_{i: \operatorname{Fin}\left(k\right)} X\left(i\right)\}, \frac{1}{(2k+1)\operatorname{choose}\left(2k, k\right)^{2}} \left\lVert v \right\rVert^{2}\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DerivativeLayerExactPivot.filtered_polynomial_pivot_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be a real inner-product space, X(i) any family of real modules, and D(i) : X(i) → W linear. If v belongs to the range of every D(i) with i < k, the squared L² distance on [0,1] from sᵏv to the polynomials with those lower-degree coefficients has an attained minimum of ‖v‖² divided by the product of (2k+1) and the square of the binomial coefficient (2k choose k).

The scalar pairing uses PolynomialL2Derivative.moment_legendreC_top and PolynomialL2Derivative.integral_rod directly. The beta integral contributes (k!)²/(2k+1)!, the reciprocal of the product of 2k+1 and the central binomial coefficient. Making the polynomial monic cancels the Rodrigues sign and divides by the central binomial coefficient once more. The pairing with any polynomial of degree at most k is its degree-k coefficient times the stated scalar factor.

The monic shifted Legendre polynomial p of degree k is thus orthogonal to every scalar monomial of degree below k. The residual p(s)v is therefore orthogonal to every allowed vector polynomial of lower degree. Its squared norm is the stated minimum. The coefficient of degree i in the projection is −coeff(p,i)v. Each such coefficient has a preimage in X(i), and these preimages attain the minimum.

At k=0 the family of trial coefficients is empty and the minimum is ‖v‖². If v=0 the minimum is zero. Neither finite dimension nor completeness of W is required.

**Theorem 1.2 (Exact minimum for the factorially normalized derivative layer).**

$$\begin{gathered}\forall V, W, [\operatorname{RealInnerProductSpace}\left(V\right)] [\operatorname{FiniteDimensional}\left(V\right)] [\operatorname{RealInnerProductSpace}\left(W\right)],\\\forall B: \operatorname{RealLinear}\left(V, V\right), \forall C: \operatorname{RealLinear}\left(V, W\right), \forall k: \mathbb{N}, \forall x: E\left(B, C\right)\left(k\right),\\\operatorname{IsLeast}\left(\{\int_{0}^{1} \left\lVert s^{k}\cdot D\left(B, C\right)\left(k, x\right)-\sum_{i\in \operatorname{Fin}\left(k\right)} s^{i}\cdot D\left(B, C\right)\left(i, a\left(i\right)\right) \right\rVert^{2} \mathrm{d}s \mid a: \prod_{i: \operatorname{Fin}\left(k\right)} E\left(B, C\right)\left(i\right)\}, \frac{1}{(2k+1)\operatorname{choose}\left(2k, k\right)^{2}} \left\lVert D\left(B, C\right)\left(k, x\right) \right\rVert^{2}\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DerivativeLayerExactPivot.derivative_layer_pivot_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite-dimensional real inner-product state space V, arbitrary real inner-product output space W, and linear maps B : V → V and C : V → W, let N(k) be the intersection of the kernels of CBʲ for j < k and E(k) = N(k) ∩ N(k+1)⊥. The actual degree-k output map D(k) on E(k) is CBᵏ divided by k!. Its range equals CBᵏ(N(k)). Applying B takes N(k+1) into N(k), so these output ranges are nested.

For any x in E(k), take v = D(k)x in the attained polynomial minimum. Every trial coefficient of degree i comes from an independent state in E(i) through CBⁱ divided by i!. The result retains zero-dimensional spaces, zero layers and repeated output ranges. With the unnormalized vector CBᵏx, the minimum includes the additional factor 1/(k!)².

In the normalized polynomial Gramian this minimum gives the quadratic form of the degree-k Schur complement after eliminating the earlier layers. On the observable state space, the ordinary spectral proof passes the O(T) error in the positive normalized Gramian through block elimination to the Schur blocks. When the block triangular factor is conjugated by the time scaling, a strict lower block in row j and column i acquires the factor T^(j−i). The resulting factor is I+O(T). Min–max comparison gives dim E(k) decreasing eigenvalues at the scale T^(2k+1), with leading coefficients from that limiting Schur block, counted with multiplicity and with relative O(T) error for fixed B and C. This transfer to the sorted spectrum is a separate ordinary proof.

## References

- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerExactPivot.derivative_layer_pivot_isLeast`
- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerExactPivot.filtered_polynomial_pivot_isLeast`
- Dependency: [D5/S3/Analytic/PolynomialL2Derivative](../../Analytic/PolynomialL2Derivative.md)
