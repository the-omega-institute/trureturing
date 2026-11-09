# Odd Four-Dissection of the Three-Core Euler Quotient

## Abstract

The odd coefficients of the integral three-core Euler quotient form an exact four-dissection.

For integer x and y, put Q(x,y)=x^2+x*y+y^2 and C(x,y)=3*Q(x,y)-2*x-y. The finite set CoreFiber(n) consists of all integer pairs with C(x,y)=n. Write E for the integral pentagonal Euler series, so E(q) is the product of 1-q^m over positive integers m. Its constant coefficient is one.

**Definition 1.1 (coreOddEquiv).**

$$\forall n \in \mathrm{Nat},\; \operatorname{coreOddEquiv}\left(n\right) \in \operatorname{Equiv}\left(\operatorname{CoreFiber}\left(n\right), \operatorname{CoreFiber}\left(4 \cdot n + 1\right)\right)$$

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaOddParity.coreOddEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Hirschhorn, Frank Garvan and Jon Borwein (1993). *Cubic Analogues of the Jacobian Theta Function theta(z, q)*. DOI: [10.4153/CJM-1993-038-2](https://doi.org/10.4153/CJM-1993-038-2). URL: <https://doi.org/10.4153/CJM-1993-038-2>.

*Commentary.*

For every natural n, the map (x,y) -> (1-2*x,-2*y) is an equivalence from CoreFiber(n) to CoreFiber(4*n+1). It sends C to 4*C+1. Conversely, C(x,y) congruent to one modulo four forces x odd and y even, giving the integer inverse ((1-x)/2,-y/2). No integer pair has C congruent to three modulo four.

**Definition 1.2 (integralT).**

$$\mathrm{integralT} \in \operatorname{PowerSeries}\left(\mathbb{Z}\right) \land \mathrm{integralT} = \operatorname{expand}\left(3, \operatorname{pentagonalSeries}\left(\mathbb{Z}\right)\right)^{3} \cdot \operatorname{invOfUnit}\left(\operatorname{pentagonalSeries}\left(\mathbb{Z}\right), 1\right)$$

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Hirschhorn, Frank Garvan and Jon Borwein (1993). *Cubic Analogues of the Jacobian Theta Function theta(z, q)*. DOI: [10.4153/CJM-1993-038-2](https://doi.org/10.4153/CJM-1993-038-2). URL: <https://doi.org/10.4153/CJM-1993-038-2>.

*Commentary.*

The series integralT lies in the ring of formal power series over the integers. Here expand(3,E) substitutes q^3 for q, and invOfUnit(E,1) is the inverse determined by the unit constant coefficient. Thus integralT(q)=E(q^3)^3/E(q). The rational three-core product theorem identifies each coefficient with the cardinality of CoreFiber(n). Mapping the integral inverse to the rationals preserves that inverse, so the same interpretation applies to integralT.

**Theorem 1.3 (integralT_coeff_mod_four).**

$$\forall n \in \mathrm{Nat},\; \operatorname{coeff}\left(4 \cdot n + 1, \mathrm{integralT}\right) = \operatorname{coeff}\left(n, \mathrm{integralT}\right) \land \operatorname{coeff}\left(4 \cdot n + 3, \mathrm{integralT}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four` (`✓ std3`). ∎

*Citation.* Michael Hirschhorn, Frank Garvan and Jon Borwein (1993). *Cubic Analogues of the Jacobian Theta Function theta(z, q)*. DOI: [10.4153/CJM-1993-038-2](https://doi.org/10.4153/CJM-1993-038-2). URL: <https://doi.org/10.4153/CJM-1993-038-2>.

*Commentary.*

For every natural n, including zero, the coefficient at 4*n+1 equals the coefficient at n, and the coefficient at 4*n+3 vanishes. The fibre equivalence proves the first equality, and the empty residue-three fibres prove the second. The rational coefficient equalities descend to the integers by injectivity of the integer embedding.

Hirschhorn, Garvan and Borwein state the classical four-dissections in identities (1.35) and (1.36), page 676, and prove them in (9.7)-(9.13), pages 689-691. Their normalization is c(q)=3*integralT(q). Identity (1.36) writes c(q) as q*c(q^4) plus a series in q^2, yielding exactly the two odd coefficient equalities above. The even coefficients and the companion b(q) dissection are outside these statements.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.coreOddEquiv`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four`
- Dependency: [D5/S1/Recurrence/Residue/ContinuedFractionOddSquare](../../../S1/Recurrence/Residue/ContinuedFractionOddSquare.md)
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaCoreProduct](CubicThetaCoreProduct.md)
