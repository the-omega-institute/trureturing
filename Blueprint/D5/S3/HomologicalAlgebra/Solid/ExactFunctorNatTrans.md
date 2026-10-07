# Derived natural transformations

## Abstract

Natural transformations of exact additive functors descend to the unbounded derived localization and commute with integer shifts.

**Definition 1.1 (Descend an exact natural transformation).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapDerivedCategory`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapDerivedCategory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This supplier ports Joel Riou's proved Mathlib natural-transformation construction from commit 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22 to the native pin. The source retains the original Apache-2.0 notices. Shift compatibility is proved componentwise and transported through localization; no derived-existence hypothesis is introduced.

**Theorem 1.2 (The formula on every unbounded representative).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapDerivedCategory_app_Q_obj`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapDerivedCategory_app_Q_obj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer-indexed complex, the localized transformation is the degreewise map conjugated by the two exact-functor localization comparisons. This literal formula supplies the mate and defining-cell compatibility in the constructor.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapDerivedCategory`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapDerivedCategory_app_Q_obj`
