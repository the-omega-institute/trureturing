# The local Laurent expansion of the Mangoldt transform

## Abstract

The principal part of the complete Mangoldt transform at each zeta zero

**Definition 1.1 (The explicit transform).**

$$\forall s \in \mathbb{C},\; \operatorname{transform}\left(s\right) = \frac{\frac{-\zeta'\left(s\right)}{\zeta\left(s\right)}}{s \cdot \left(s - 1\right)} - \frac{1}{(s - 1)^{2}} + \frac{1 + \gamma}{s - 1}$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent.transform` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction terms come from the logarithmic and linear terms of the inclusive remainder U.

**Theorem 1.2 (The transform on the half-plane and its zero germs).**

$$\left(\forall s \in \mathbb{C},\; 1 < \operatorname{Re}\left(s\right) \Rightarrow \left(\operatorname{IntegrableOn}\left((\lambda y \mapsto \operatorname{exp}\left(-\left(s \cdot y\right)\right) \cdot \operatorname{U}\left(\operatorname{exp}\left(y\right)\right)), \operatorname{Ioi}\left(0\right)\right) \land \int_{0}^{\infty} \operatorname{exp}\left(-\left(s \cdot y\right)\right) \cdot \operatorname{U}\left(\operatorname{exp}\left(y\right)\right) dy = \operatorname{transform}\left(s\right)\right)\right) \land \left(\forall z \in \mathbb{C},\; \zeta\left(z\right) = 0 \Rightarrow \left(\operatorname{analyticOrderNatAt}\left(\zeta, z\right) \ne 0 \land \left(\frac{\operatorname{analyticOrderNatAt}\left(\zeta, z\right)}{z \cdot \left(1 - z\right)} \ne 0 \land \left(\exists H \in \mathbb{C} \to \mathbb{C},\; \operatorname{AnalyticAt}\left(\mathbb{C}, H, z\right) \land \left(\exists r \in \mathbb{R},\; 0 < r \land \left(\forall s \in \mathbb{C},\; \left(\left|s - z\right| \ne 0 \land \left|s - z\right| < r\right) \Rightarrow \operatorname{transform}\left(s\right) = \frac{\frac{\operatorname{analyticOrderNatAt}\left(\zeta, z\right)}{z \cdot \left(1 - z\right)}}{s - z} + \operatorname{H}\left(s\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent.transform_integral_and_zero_germs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re(s)>1 the complete half-plane transform theorem gives the absolutely convergent integral. At a zero z, the expansion concerns the explicit transform function. Since ζ(0)=−1/2, zero is excluded. Classically ζ has a pole at 1. Lean assigns ζ(1) a nonzero value, so the zero hypothesis excludes 1 as well.

Write ζ(s)=(s−z)ᵐu(s) near z, where u is analytic and u(z) is nonzero. Its logarithmic derivative splits as m/(s−z)+u′(s)/u(s). With d(s)=s(1−s), the identity d(z)−d(s)=(s−z)(s+z−1) absorbs exactly the varying denominator. The analytic remainder is m(s+z−1)/(d(s)d(z))+(u′(s)/u(s))/d(s) −1/(s−1)²+(1+γ)/(s−1). The residue m/d(z) is nonzero even at a multiple zero.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent.transform`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent.transform_integral_and_zero_germs`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Residues](../Cryptids/WeightedStieltjes/Residues.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane](CompleteMangoldtHalfPlane.md)
