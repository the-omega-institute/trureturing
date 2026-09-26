# Integral Operators from Square-Integrable Kernels

## Abstract

Every square-integrable complex kernel on a product of sigma-finite measure spaces defines a bounded integral operator, contractively and linearly in the kernel.

**Theorem 1.1 (The actual operator and its almost-everywhere integral formula).**

$$\forall X \in Type, Y \in Type, mx \in \operatorname{MeasurableSpace}\left(X\right), my \in \operatorname{MeasurableSpace}\left(Y\right), mu \in \operatorname{Measure}\left(X, mx\right), nu \in \operatorname{Measure}\left(Y, my\right),\; \left(\operatorname{SigmaFinite}\left(mu\right) \land \operatorname{SigmaFinite}\left(nu\right)\right) \Rightarrow \left(\exists A \in \operatorname{CLM}\left(\mathbb{C}, \operatorname{Lp}\left(\mathbb{C}, 2, \operatorname{prod}\left(mu, nu\right)\right), \operatorname{CLM}\left(\mathbb{C}, \operatorname{Lp}\left(\mathbb{C}, 2, nu\right), \operatorname{Lp}\left(\mathbb{C}, 2, mu\right)\right)\right),\; \operatorname{norm}\left(A\right) \le 1 \land \left(\forall k \in \operatorname{Lp}\left(\mathbb{C}, 2, \operatorname{prod}\left(mu, nu\right)\right),\; \forall f \in \operatorname{Lp}\left(\mathbb{C}, 2, nu\right),\; \operatorname{AE}\left(mu, (x:X\mapsto \operatorname{Integrable}\left((y:Y\mapsto k((x,y)) \cdot f(y)), nu\right))\right) \land \left(\operatorname{AE}\left(mu, (x:X\mapsto A(k)(f)(x) = \int_{nu} k((x,y)) \cdot f(y) dy)\right) \land \operatorname{norm}\left(A(k)(f)\right) \le \operatorname{norm}\left(k\right) \cdot \operatorname{norm}\left(f\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/L2KernelIntegralOperator.result` (`✓ std3`). ∎

*Citation.* B. M. Bredikhin (2020). *Hilbert-Schmidt integral operator*. URL: <https://encyclopediaofmath.org/index.php?title=Hilbert-Schmidt_integral_operator&oldid=47226>.

*Commentary.*

Let X and Y be arbitrary measurable spaces, with sigma-finite measures mu and nu. L2 denotes complex-valued square-integrable functions modulo almost-everywhere equality. CLM(C,E,F) denotes continuous complex linear maps from E to F, equipped with the operator norm.

There exists a continuous complex linear map A from L2(mu product nu) to CLM(C,L2(nu),L2(mu)), with norm at most one. For every kernel k and every input f, almost every x has an integrable section y mapped to k(x,y)f(y). The actual representative of A(k)(f) equals the Bochner integral of that section almost everywhere. The output norm is at most the kernel norm times the input norm.

The product is complex bilinear: neither k nor f is conjugated. A acts on equivalence classes, and replacing either function by an almost-everywhere equal representative preserves both the section integrability assertion and the output formula almost everywhere. Zero measures, infinite total measure and infinitely supported kernels and inputs are included.

Square integrability of k makes its squared norm integrable on the product. Fubini gives square-integrable sections almost everywhere and an integrable function of their squared norms. Cauchy--Schwarz on each section bounds the squared integral output by this function times the squared norm of f. The section integral is almost-everywhere strongly measurable; the bound proves its square integrability without assuming it.

Taking the resulting L2 equivalence class constructs the output. Almost-everywhere identities for addition and complex scalar multiplication, together with section integrability, give linearity in both arguments. The norm estimate makes this bilinear operation continuous and bounds the norm of the curried map by one. The construction is the classical square-integrable-kernel mechanism described by Bredikhin.

This theorem supplies an integral operator and the bound by the L2 norm of its kernel. It does not prove compactness, a spectral representation, or the sharper cosine-integral multiplier bound involving the inverse cutoff scale.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/L2KernelIntegralOperator.result`
