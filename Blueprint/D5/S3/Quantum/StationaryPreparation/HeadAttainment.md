# Stationary Occupation Attainment

## Abstract

One fixed complex linear isometry exactly prepares every finite occupation state with minimum memory.

**Theorem 1.1 (Exact preparation at the minimum dimension).**

$$\forall a: sigma \to Nat,\ \exists h: sigma, \exists P: PhysicalPreparation\left(H\left(a, h\right), a\right),\ finrank\left(Complex, H\left(a, h\right)\right) = product\left(aPlusOne\left(a\right)\right) - max\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/HeadAttainment.stationary_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sirui Lu and TNLean contributors (2026). *Gram equality and unitary extension for rectangular matrices*. URL: <https://github.com/LionSR/QICLean/blob/cdaa636d1f41560f7caca7077c11068229cb9727/QICLean/Algebra/MatrixGramUnitary.lean>.

*Commentary.*

For every finite nonempty alphabet sigma and every natural capacity function a, choose a head h attaining max(i,a(i)). The memory H is the span of the explicit head Gram vectors chi(r). There exists a PhysicalPreparation on H, and its complex dimension is product(i,a(i)+1)-max(i,a(i)). The lower bound applies to every PhysicalPreparation in this model, so this dimension is the least admissible one.

For each nonzero r, prescribe the emission image whose letter i component is chi(r-e(i)) when r(i)>0 and zero otherwise. The head Gram recurrence proves equality of the source and image Gram matrices. Embed the source into one letter coordinate of the output space and apply the equal-Gram unitary extension. The resulting V is one total complex linear isometry from H to EuclideanSpace(Complex,sigma) tensor H. It preserves every linear relation among the residual vectors and is reused unchanged at every emission.

Normalize by phi(r)=chi(r)/sqrt(M(r)). The Gram diagonal proves unit norm. The identity |r| M(r-e(i))=r(i) M(r) converts the raw transition into Step: the letter i component of V phi(r) is sqrt(r(i)/|r|) phi(r-e(i)) for r(i)>0 and zero otherwise. The word evolution formula then gives every allowed length-|a| word the same positive amplitude 1/sqrt(M(a)), and every other word amplitude zero. The initial vector is phi(a), and every allowed word has the common unit final vector phi(0). Hence emitted(V,|a|,phi(a)) equals sector(a) tensor phi(0) exactly.

When all capacities vanish, the span has dimension one, the initial and final vectors agree, and there are zero emissions. A singleton alphabet, zero coordinates, and tied maxima are included. No clock, varying gate, postselection, or extra memory is part of the construction. The final vector is freely chosen by the construction and is not required to equal a prescribed reset vector.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/HeadAttainment.stationary_attainment`
- Dependency: [D5/S3/Quantum/Algebra/GramUnitaryExtension](../Algebra/GramUnitaryExtension.md)
- Dependency: [D5/S3/Quantum/StationaryPreparation/HeadGram](HeadGram.md)
