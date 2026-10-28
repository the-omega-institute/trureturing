# PrimitivePencil

## Abstract

Every full row rank integer matrix admits one perturbation with primitive maximal minors for all integer parameters.

**Theorem 1.1 (primitive pencil perturbation).**

$$\forall \{d : \mathbb{N}\}, \forall (A : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), (\operatorname{Function} . \operatorname{Injective} (\operatorname{fun} x : \operatorname{Fin} d \to \mathbb{Z} \mapsto A . \operatorname{transpose} *_{v} x)) \to \exists B : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z} , \forall t : \mathbb{Z} , \operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} (t \cdot A + B)) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/PrimitivePencil.primitive_pencil_perturbation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every full row rank integer matrix admits one perturbation with primitive maximal minors for all integer parameters.

## References

- Truth anchor: `D5/S3/Arith/Lattices/PrimitivePencil.primitive_pencil_perturbation`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](CofactorKernel.md)
