# The Product Absorption Logarithmic Kernel

## Abstract

The exact five-term logarithmic kernel for binary product absorption has at most one positive sign change, from positive to negative.

Let u and v belong to the closed unit interval. Put A=u+v, B=uv, L=A-B, and Mplus=A-2B+2sqrt(B(1-A+B)), Mminus=A-2B-2sqrt(B(1-A+B)). Both roots are nonnegative, their sum is 2(A-2B), and their product is (u-v)^2. In particular u=v is permitted and gives Mminus=0. Every logarithm in the kernel has a strictly positive argument when s>0.

**Definition 1.1 (The exact logarithmic kernel).**

$$\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \forall (s: \mathbb{R}), \operatorname{productLogKernel}\left(u, v, s\right) = \operatorname{log}\left(1 + \frac{u}{s}\right) + \operatorname{log}\left(1 + \frac{v}{s}\right) - 2 \cdot \operatorname{log}\left(1 + \frac{u + v - u \cdot v}{s}\right) + \frac{\operatorname{log}\left(1 + \frac{u + v - 2 \cdot u \cdot v + 2 \cdot \operatorname{sqrt}\left(u \cdot v \cdot \left(1 - \left(u + v\right) + u \cdot v\right)\right)}{s}\right) + \operatorname{log}\left(1 + \frac{u + v - 2 \cdot u \cdot v - 2 \cdot \operatorname{sqrt}\left(u \cdot v \cdot \left(1 - \left(u + v\right) + u \cdot v\right)\right)}{s}\right)}{2}$$

*Formalization.* `D5/S3/Entropy/ProductAbsorptionLogKernel.productLogKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Task-supplied local unpublished mathematical inputs (2026). *The scalar product absorption inequality for binary qubit entropy; A sharp physical record bound for complex product seeds*. URL: <https://github.com/the-omega-institute/trureturing/blob/a5f1b8485c7373d7943fc33aab7d6abb5f1819f7/Library/Entropy/local2026productabsorption.md>.

*Commentary.*

The definition is a total real function. Its single-crossing theorem concerns 0<=u,v<=1 and s>0. The logarithm is the natural logarithm. A zero quadratic root contributes log(1)=0.

**Theorem 1.2 (One positive sign change).**

$$\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), ((0 \le u) \land (u \le 1)) \Rightarrow \left(((0 \le v) \land (v \le 1)) \Rightarrow \left((\forall (s: \mathbb{R}), (0 < s) \Rightarrow 0 \le \operatorname{productLogKernel}\left(u, v, s\right)) \lor (\exists (r: \mathbb{R}), (0 < r) \land ((\operatorname{productLogKernel}\left(u, v, r\right) = 0) \land ((\forall (s: \mathbb{R}), ((0 < s) \land (s < r)) \Rightarrow 0 < \operatorname{productLogKernel}\left(u, v, s\right)) \land (\forall (s: \mathbb{R}), (r < s) \Rightarrow \operatorname{productLogKernel}\left(u, v, s\right) < 0))))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/ProductAbsorptionLogKernel.product_log_kernel_single_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Task-supplied local unpublished mathematical inputs (2026). *The scalar product absorption inequality for binary qubit entropy; A sharp physical record bound for complex product seeds*. URL: <https://github.com/the-omega-institute/trureturing/blob/a5f1b8485c7373d7943fc33aab7d6abb5f1819f7/Library/Entropy/local2026productabsorption.md>.

*Commentary.*

Either K is nonnegative for every positive s, or there exists a positive r with K(r)=0, K(s)>0 for every 0<s<r, and K(s)<0 for every s>r. The strict signs make the zero unique in the second case. There is no assumption that u and v are unequal, and all parameter endpoints are included.

Twice the kernel is log(N)-log(D), where N=(s^2+As+B)^2(s^2+2(A-2B)s+A^2-4B) and D=s^2(s+A-B)^4. Both N and D are positive. Their difference is the quartic P(s)=aFour*s^4+aThree*s^3+aTwo*s^2+aOne*s+aZero. The coefficients are aFour=2B(2A-3B-1), aThree=2B(4A^2-6AB-A+2B^2-4B), aTwo=B(4A^3-6A^2B+2A^2+4AB^2-8AB-B^3-7B), aOne=2B(A^3-3AB-2B^2), and aZero=B^2(A^2-4B).

For 0<u,v<1 the coefficient estimates give aZero>=0, aOne>0, aTwo>0, and aFour>=0 implies aThree>=0. In the latter case P is nonnegative. When aFour<0 and aThree>=0, P(s)/s^4 is strictly decreasing. When both aFour and aThree are negative, P(s)/s^3 is strictly decreasing. Continuity and the signs at small and large positive arguments give the unique crossing. The strict monotonicity of log transfers its signs to the original five-term kernel.

At u=0 the kernel vanishes identically. At u=1 it is log(1+v/s)+log(1+(1-v)/s)-log(1+1/s), which is nonnegative because (1+v/s)(1+(1-v)/s)-(1+1/s)=v(1-v)/s^2>=0. Symmetry supplies the two remaining boundary faces. Thus no strict positivity of u, v, or a quadratic root is required.

This is the kernel crossing component of the scalar binary-entropy absorption argument. The entropy integral representation, absolute integrability, the nonnegative first moment, the decreasing-weight integral argument, and the closed-domain entropy inequality are separate mathematical statements. No spectral-entropy, quantum-channel, or all-product-seed absorption conclusion is asserted by this theorem. The ordinary mathematical source is the local unpublished proof identified in the source note; no publication-priority claim is made.

## References

- Truth anchor: `D5/S3/Entropy/ProductAbsorptionLogKernel.productLogKernel`
- Truth anchor: `D5/S3/Entropy/ProductAbsorptionLogKernel.product_log_kernel_single_crossing`
