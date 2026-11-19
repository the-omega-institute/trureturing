# Simplicity of the actual image on an isotypic semisimple module.

## Abstract

Simplicity of the actual image on an isotypic semisimple module.

The matrix and double-centralizer theorems are reused from Mathlib. The constructed range identification supplies simplicity of the actual restricted group-algebra image used by the normalizer center action. The field, acting algebra and carrier universes are independent.

**Theorem 1.1 (isSimpleRing actionRange).**

$$\forall k \in Type*,\; \forall R \in Type*,\; \forall U \in Type*,\; [Field\left(k\right)], [Ring\left(R\right)], [Algebra\left(k, R\right)], [AddCommGroup\left(U\right)], [Module\left(k, U\right)], [Module\left(R, U\right)], [IsScalarTower\left(k, R, U\right)], [\operatorname{Module}.\operatorname{Finite}\left(k, U\right)], [Nontrivial\left(U\right)], [IsSemisimpleModule\left(R, U\right)], \forall hU \in IsIsotypic\left(R, U\right),\; IsSimpleRing\left(\operatorname{AlgHom}.\operatorname{range}\left(\operatorname{Algebra}.\operatorname{lsmul}\left(k, k, U\right)(\operatorname{A}:=R)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/FiniteIsotypicImageSimple.isSimpleRing_actionRange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero finite-dimensional semisimple isotypic module, its endomorphism algebra is a matrix algebra over a division ring. The same holds for the bicommutant. The finite double-centralizer surjectivity theorem identifies that bicommutant with the actual action range by an explicitly bijective ring map. Thus the image itself is simple; simplicity is not an extra assumption.

## References

- Truth anchor: `D5/S3/FiniteGroups/Frobenius/FiniteIsotypicImageSimple.isSimpleRing_actionRange`
