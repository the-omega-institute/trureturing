# Discriminant Determinant Product

## Abstract

Conditional Lerch data identify the two mod-five holonomy determinants.

**Theorem 1.1 (The mod-five sector determinants recover the golden constants).**

$$\left(\operatorname{HasReflectedHurwitzDerivativeAtZeroFormula}(\frac{1}{5}) \land \operatorname{HasReflectedHurwitzDerivativeAtZeroFormula}(\frac{2}{5})\right) \Rightarrow \left({\operatorname{masslessHolonomyDeterminant}(\frac{1}{5})} \times {\operatorname{masslessHolonomyDeterminant}(\frac{2}{5})} = \operatorname{sqrt}(5) \land \frac{\operatorname{masslessHolonomyDeterminant}(\frac{2}{5})}{\operatorname{masslessHolonomyDeterminant}(\frac{1}{5})} = goldenRatio\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct.discriminant_determinant_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assuming the reflected Hurwitz derivative formula at both source-fixed mod-five representatives, the frozen determinant bridge evaluates the two zeta-regularized massless holonomy determinants.

Their product is the square root of five, while ordering the second sector over the first gives the golden ratio.

## References

- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct.discriminant_determinant_product`
- Dependency: [D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant](MasslessHolonomyDeterminant.md)
