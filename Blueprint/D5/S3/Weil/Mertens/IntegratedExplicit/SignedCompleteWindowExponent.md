# The logarithmic exponent at the zeta zero abscissa

## Abstract

Exact signed power-window growth for the complete Mangoldt tail

**Definition 1.1 (Signed weighted window mass).**

$$\forall e \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall Y \in \mathbb{R},\; \operatorname{M}\left(e, b, Y\right) = \int_{Y}^{Y^{b}} \frac{\operatorname{max}\left(e \cdot -\operatorname{Q}\left(x\right), 0\right)}{\sqrt{x}} dx$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent.signedMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real e, b and Y, M(e,b,Y) is the oriented interval integral from Y to Y^b. The complete Chebyshev tail Q(x) is the integral of (ψ(t)−t)/t² from x to infinity, with every prime power counted in ψ. The signs e=1 and e=−1 select the positive and negative parts of −Q respectively.

**Theorem 1.2 (Exact exponent for either sign).**

$$\forall b \in \mathbb{R},\; \forall e \in \mathbb{R},\; 1 < b \Rightarrow \left(\left(e = 1 \lor e = -1\right) \Rightarrow \operatorname{Tendsto}\left((\lambda Y:\mathbb{R} \mapsto \frac{\operatorname{log}\left(1 + \operatorname{M}\left(e, b, Y\right)\right)}{\operatorname{log}\left(Y\right)}), atTop, \operatorname{nhds}\left(b \cdot (Theta - \frac{1}{2})\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent.tendsto_log_one_add_signedMass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Θ be zeroAbscissa, the supremum of the real parts of the nontrivial zeta zeros. Reflection gives Θ≥1/2. Fix any real b>1 and either sign e=1 or e=−1. Set p=b(Θ−1/2). The logarithmic growth of 1+M(e,b,Y) has limit p as the real window start Y tends to infinity.

Absolute summability of the actual zero coefficients and the bounded remainder in RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le give |U(x)|≤C x^Θ for x≥1, even when Θ is unattained. The identity ZeroAbscissaPower.primitive_eq_negative_tail gives −Q(x)=U(x)/x for x≥2. On [Y,Y^b] the density is therefore at most C Y^p/x. Integration yields M(e,b,Y)≤C(b−1)Y^p log Y for both signs with the same constant and threshold.

For Θ>1/2 and any real a<p, choose a nontrivial zero with real part β>1/2 and b(β−1/2)>a by the defining supremum. PrimeWindowPoleGrowth.off_line_zero_forces_signed_complete_window_mass applied with ε=b(β−1/2)−a gives Y^a≤M(e,b,Y) on every sufficiently late window, simultaneously for both signs.

The upper bound contributes only a logarithmic factor beyond Y^p, and log(log Y)/log Y tends to zero. The lower bound holds for every exponent strictly below p when p>0. At p=0, nonnegativity of the mass supplies the lower limit. Together these estimates give the exact limit.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent.signedMass`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent.tendsto_log_one_add_signedMass`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/KappaGap](../../../Arith/Robin/ForwardKernel/KappaGap.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth](PrimeWindowPoleGrowth.md)
- Dependency: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../ZeroAbscissaPower.md)
