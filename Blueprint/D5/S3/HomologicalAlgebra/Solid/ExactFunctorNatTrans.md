# Derived natural transformations

## Abstract

Natural transformations of exact additive functors descend to the unbounded derived localization and commute with integer shifts.

**Definition 1.1 (Degreewise composition under preservation of zero morphisms).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapHomologicalComplexCompIsoZero`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapHomologicalComplexCompIsoZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For functors F, G and H preserving zero morphisms and an isomorphism e from F composed with G to H, mapHomologicalComplexCompIsoZero is NatIso.mapHomologicalComplex e c for any complex shape c. Its hom and inverse act in degree i by e.hom.app and e.inv.app on the degree-i object. This retains the zero-morphism interface used by the solidification construction.

**Theorem 1.2 (Degreewise shift compatibility).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.instCommShiftHomologicalComplexIntUpMapHomologicalComplex_d5`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.instCommShiftHomologicalComplexIntUpMapHomologicalComplex_d5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural transformation of additive functors between preadditive categories commutes with integer shifts after degreewise extension to cochain complexes. The componentwise proof and the localization identity-comparison instance are retained locally.

For abelian categories with the stated HasDerivedCategory instances, and additive functors F and G preserving finite limits and finite colimits, Mathlib's CategoryTheory.NatTrans.mapDerivedCategory sends a natural transformation tau to Localization.liftNatTrans of its degreewise extension whiskered with DerivedCategory.Q. This is the same localization operation, with no additional derived-existence hypothesis. CategoryTheory.NatTrans.CommShift.liftNatTrans supplies shift compatibility, and the induced transformation commutes with every integer shift.

For every unbounded integer-indexed complex X, CategoryTheory.NatTrans.mapDerivedCategory_app_Q_obj states that tau.mapDerivedCategory.app(Q.obj X) equals F.mapDerivedCategoryFactors.hom.app X followed by Q.map((tau.mapHomologicalComplex (.up Z)).app X) followed by G.mapDerivedCategoryFactors.inv.app X. Its reassociated form is mapDerivedCategory_app_Q_obj_assoc. This formula supplies the mate and defining-cell compatibility in the constructor. These declarations are owned by the imported Mathlib module, rather than by this source.

Sources: Joel Riou, Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean, namespace CategoryTheory.NatTrans; Mathlib/CategoryTheory/Shift/Localization.lean, namespace CategoryTheory.NatTrans.CommShift; Mathlib/Algebra/Homology/HomotopyCategory/Shift.lean. The Lean source retains the original Apache-2.0 notices and immutable source citation.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.instCommShiftHomologicalComplexIntUpMapHomologicalComplex_d5`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapHomologicalComplexCompIsoZero`
