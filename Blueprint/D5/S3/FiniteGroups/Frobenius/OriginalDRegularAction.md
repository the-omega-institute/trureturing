# Descent with the original division ring

## Abstract

Normal-basis coordinates for covariant field operators over an independent division ring.

**Theorem 1.1 (normalMap bijective).**

$$\forall K \in Type*,\; \forall F \in Type*,\; \forall D \in Type*,\; \forall U \in Type*,\; [Field\left(K\right)], [Field\left(F\right)], [Algebra\left(K, F\right)], [\operatorname{Module}.\operatorname{Finite}\left(K, F\right)], [IsGalois\left(K, F\right)], [DivisionRing\left(D\right)], [AddCommGroup\left(U\right)], [Module\left(D, U\right)], \forall a \in RingHom\left(F, \operatorname{Module}.\operatorname{End}\left(D, U\right)\right),\; \forall tau \in MonoidHom\left(AlgEquiv\left(K, F, F\right), \operatorname{Module}.\operatorname{End}\left(D, U\right)\right),\; \forall cov \in \left(\forall g \in AlgEquiv\left(K, F, F\right),\; \forall x \in F,\; tau\left(g\right) \cdot a\left(x\right) = a\left(g\left(x\right)\right) \cdot tau\left(g\right)\right),\; \operatorname{Function}.\operatorname{Bijective}\left(\operatorname{FrobeniusOriginalD}.\operatorname{RegularAction}.\operatorname{normalMap}\left(a, tau\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction.normalMap_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F/K be a finite Galois extension, D an arbitrary division ring, and U a left D-module. Let a : F -> End_D(U) be a unital ring map and tau : Gal(F/K) -> End_D(U) a monoid map satisfying tau(g)a(x) = a(g(x))tau(g). The common fixed vectors form a D-submodule S. For a normal basis b of F/K, the D-linear map f -> sum_g a(b(g))f(g) from Gal(F/K) -> S to U is bijective.

The field operators install the F-module structure on U, while covariance gives semilinearity of the Galois action. Galois vector descent identifies U with F tensor_K S. The tensor-basis equivalence for a normal basis identifies that tensor product with the function space. Comparing the composite with the displayed sum proves bijectivity. Its D-linearity follows from the D-linearity of the actual operators a(x). The descent supplier is GaloisVectorDescent, attributed to Qiuzhen-CFSG/CFSG, revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7, under Apache-2.0; normal bases and tensor-basis equivalences are from Mathlib.

**Definition 1.2 (regularEquiv).**

$$\forall K \in Type*,\; \forall F \in Type*,\; \forall D \in Type*,\; \forall U \in Type*,\; [Field\left(K\right)], [Field\left(F\right)], [Algebra\left(K, F\right)], [\operatorname{Module}.\operatorname{Finite}\left(K, F\right)], [IsGalois\left(K, F\right)], [DivisionRing\left(D\right)], [AddCommGroup\left(U\right)], [Module\left(D, U\right)], \forall a \in RingHom\left(F, \operatorname{Module}.\operatorname{End}\left(D, U\right)\right),\; \forall tau \in MonoidHom\left(AlgEquiv\left(K, F, F\right), \operatorname{Module}.\operatorname{End}\left(D, U\right)\right),\; \forall cov \in \left(\forall g \in AlgEquiv\left(K, F, F\right),\; \forall x \in F,\; tau\left(g\right) \cdot a\left(x\right) = a\left(g\left(x\right)\right) \cdot tau\left(g\right)\right),\; LinearEquiv\left(\operatorname{RingHom}.\operatorname{id}\left(D\right), U, AlgEquiv\left(K, F, F\right) \to \operatorname{FrobeniusOriginalD}.\operatorname{RegularAction}.\operatorname{fixed}\left(tau\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction.regularEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse of the normal-basis sum map gives a D-linear equivalence from U to Gal(F/K) -> S. The division ring D has no required embedding of K or F and is not required to be commutative. The universes of K, F, D and U are independent.

**Theorem 1.3 (regularEquiv apply action).**

$$\forall K \in Type*,\; \forall F \in Type*,\; \forall D \in Type*,\; \forall U \in Type*,\; [Field\left(K\right)], [Field\left(F\right)], [Algebra\left(K, F\right)], [\operatorname{Module}.\operatorname{Finite}\left(K, F\right)], [IsGalois\left(K, F\right)], [DivisionRing\left(D\right)], [AddCommGroup\left(U\right)], [Module\left(D, U\right)], \forall a \in RingHom\left(F, \operatorname{Module}.\operatorname{End}\left(D, U\right)\right),\; \forall tau \in MonoidHom\left(AlgEquiv\left(K, F, F\right), \operatorname{Module}.\operatorname{End}\left(D, U\right)\right),\; \forall cov \in \left(\forall g \in AlgEquiv\left(K, F, F\right),\; \forall x \in F,\; tau\left(g\right) \cdot a\left(x\right) = a\left(g\left(x\right)\right) \cdot tau\left(g\right)\right),\; \forall h \in AlgEquiv\left(K, F, F\right),\; \forall u \in U,\; \forall g \in AlgEquiv\left(K, F, F\right),\; \operatorname{FrobeniusOriginalD}.\operatorname{RegularAction}.\operatorname{regularEquiv}\left(a, tau, cov\right)\left(tau\left(h, u\right), g\right) = \operatorname{FrobeniusOriginalD}.\operatorname{RegularAction}.\operatorname{regularEquiv}\left(a, tau, cov\right)\left(u, \operatorname{Inv}.\operatorname{inv}\left(h\right) \cdot g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction.regularEquiv_apply_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These coordinates intertwine the actual operators tau(h) with left translation: E(tau(h)u)(g) = E(u)(h^(-1)g). Covariance sends the normal-basis vector indexed by g to the one indexed by hg, and every coordinate value is fixed by tau. Reindexing the sum by left multiplication proves the law; inverting the bijective sum map gives the stated formula.

## References

- Truth anchor: `D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction.normalMap_bijective`
- Truth anchor: `D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction.regularEquiv`
- Truth anchor: `D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction.regularEquiv_apply_action`
- Dependency: [D5/S3/Factorization/Galois/GaloisVectorDescent](../../Factorization/Galois/GaloisVectorDescent.md)
