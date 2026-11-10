# Detecting an integral homology class of order two

## Abstract

A mod-two functional detects a nonzero order-two class in integral ModuleCat homology.

**Definition 1.1 (The class map into actual categorical homology).**

$$\forall S: \operatorname{ShortComplex}\left(\operatorname{ModuleCat}\left(\mathbb{Z}\right)\right), \operatorname{cycleClassMap}\left(S\right): \operatorname{integerLinearMap}\left(\operatorname{ker}\left(\operatorname{g}\left(S\right)\right), \operatorname{homology}\left(S\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology.cycleClassMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every short complex S of integer modules, cycleClassMap S is the integer-linear map from the concrete kernel of S.g to S.homology. It first takes the quotient by the range of S.moduleCatToCycles and then applies the inverse of Mathlib's moduleCatHomologyIso. Thus its codomain is the existing ShortComplex homology object, not an unrelated quotient.

**Theorem 1.2 (A class vanishes exactly when it bounds).**

$$\forall S: \operatorname{ShortComplex}\left(\operatorname{ModuleCat}\left(\mathbb{Z}\right)\right), \forall z: \operatorname{ker}\left(\operatorname{g}\left(S\right)\right), \operatorname{cycleClassMap}\left(S, z\right)=0 \iff \exists c: \operatorname{sourceModule}\left(S\right), \operatorname{f}\left(S, c\right)=z$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology.cycleClassMap_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every S : ShortComplex (ModuleCat Z) and z in LinearMap.ker S.g.hom, cycleClassMap S z = 0 if and only if there exists c in S.X1 with S.f c = z. The proof uses the exact ModuleCat homology isomorphism and quotient-zero criterion.

**Theorem 1.3 (A detected cycle whose double bounds).**

$$\forall S: \operatorname{ShortComplex}\left(\operatorname{ModuleCat}\left(\mathbb{Z}\right)\right), \forall z: \operatorname{ker}\left(\operatorname{g}\left(S\right)\right), \forall c: \operatorname{sourceModule}\left(S\right), \forall phi: \operatorname{integerLinearMap}\left(\operatorname{middleModule}\left(S\right), \operatorname{ZMod}\left(2\right)\right), \operatorname{f}\left(S, c\right)=2\cdot z \Rightarrow (\forall b: \operatorname{sourceModule}\left(S\right), \operatorname{apply}\left(phi, \operatorname{f}\left(S, b\right)\right)=0) \Rightarrow \operatorname{apply}\left(phi, z\right) \neq 0 \Rightarrow \operatorname{cycleClassMap}\left(S, z\right) \neq 0 \land 2\cdot \operatorname{cycleClassMap}\left(S, z\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology.detected_order_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every short complex S of integer modules, every z in the kernel of S.g, every c in S.X1 with S.f c = 2 times z, and every integer-linear map phi from S.X2 to ZMod 2 which is zero on S.f b for all b in S.X1 and is nonzero on z, the actual class cycleClassMap S z is nonzero and its double is zero. These hypotheses impose no finiteness or exactness assumptions on the other classes. The eleven-vertex independence-complex seed consumes this construction; no singular-homology comparison is part of this theorem.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology.cycleClassMap`
- Truth anchor: `D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology.cycleClassMap_eq_zero_iff`
- Truth anchor: `D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology.detected_order_two`
