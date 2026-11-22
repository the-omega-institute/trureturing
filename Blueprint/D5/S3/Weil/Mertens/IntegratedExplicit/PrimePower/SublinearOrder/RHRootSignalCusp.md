# The logarithmic cusp of the centered root spectrum

## Abstract

The logarithmic cusp of the centered root spectrum

**Theorem 1.1 (The symmetric difference at the origin).**

$$\mathit{RH} \Rightarrow \left(\forall r \in \mathbb{R},\; 1 < r \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall h \in \mathbb{R},\; \left(0 < h \land h \le \frac{r}{2}\right) \Rightarrow \left|\operatorname{S}\left(r, h\right) + \operatorname{S}\left(r, -h\right) - 2 \cdot \operatorname{S}\left(r, 0\right) - \frac{h}{\operatorname{s}\left(r\right)} \cdot \left(\operatorname{log}\left(\frac{1}{h}\right) + \operatorname{log}\left(r\right) - 2 \cdot c\right)\right| \le C \cdot h \cdot h\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootSignalCusp.root_signal_symmetric_cusp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r greater than one, put s(r)=1/2−1/(2r) and c=(Euler's constant−1+log(2π))/2. The centered signal S(r,u) is the real part of the root series divided by s(r), with each actual zero included according to its analytic multiplicity.

For a zero of ordinate γ, the symmetric difference multiplies the real coefficient by 2(cos(γh/r)−1). Subtract the reference coefficient −r/(1/4+γ²). The correction has another quadratic denominator in γ, so its second ordinate moment is bounded by the total reciprocal-square mass. This gives a quadratic bound for the correction series.

The reference series equals the actual cosine kernel difference at h/r, scaled by −2r/s(r). Substituting the kernel expansion gives both cusp coefficients. The estimate describes the symmetric difference about the origin. The sharp uniform modulus over arbitrary starting points is open.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootSignalCusp.root_signal_symmetric_cusp`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp](../../ActualKernelCusp.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelGlobalStrictPositivity](../../ActualKernelGlobalStrictPositivity.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingWidth](RHMobiusEvenCutoffShrinkingWidth.md)
