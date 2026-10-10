/- GID: D5/S3/HomologicalAlgebra/Solid/ConeColimit
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/ConeColimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.ComplexColimit
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Tactic

/-! Coproducts of the actual mapping cones used by the unbounded cellular
construction. New proofs, released under the Apache 2.0 license. -/

noncomputable section
open CategoryTheory Limits HomologicalComplex

namespace CWSolid

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Transposing the existing complex-to-diagram construction returns the
original unbounded complex, with its original differentials. -/
def complexDiagramAsFunctorIso {J : Type*} [Category* J]
    (M : CochainComplex (J ⥤ C) ℤ) : complexDiagram M.asFunctor ≅ M :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by intros; ext j; simp [complexDiagram, HomologicalComplex.asFunctor])

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Arbitrary coproducts of mapping cones are the mapping cone of the
actual coproduct map. The complexes need not be bounded. -/
def mappingConeCoproductIso {I : Type} [HasColimitsOfShape (Discrete I) C]
    (K : I → CochainComplex C ℤ) (f : ∀ i, K i ⟶ K i) :
    (∐ fun i => CochainComplex.mappingCone (f i)) ≅
      CochainComplex.mappingCone (Limits.Sigma.map f) := by
  letI : (Functor.const (Discrete I) : C ⥤ Discrete I ⥤ C).Additive :=
    { map_add := by intros; ext j; rfl }
  letI : (colim (J := Discrete I) (C := C)).Additive :=
    colimConstAdj.left_adjoint_additive
  let D := Discrete.functor K
  let τ : D ⟶ D := Discrete.natTrans (fun j => f j.as)
  let φ := complexDiagramMap τ
  let M := CochainComplex.mappingCone φ
  let E : M.asFunctor ≅ Discrete.functor (fun i => CochainComplex.mappingCone (f i)) :=
    Discrete.natIso (fun i => CochainComplex.mappingCone.mapHomologicalComplexIso φ
      ((evaluation (Discrete I) C).obj i))
  let G := (colim (J := Discrete I) (C := C)).mapHomologicalComplex (.up ℤ)
  let e : G.obj (complexDiagram D) ≅ colimit D := complexDiagramColimitIso D
  let eφ : Arrow.mk (G.map φ) ≅ Arrow.mk (Limits.Sigma.map f) :=
    Arrow.isoMk e e (complexDiagramColimitIso_naturality τ).symm
  exact (HasColimit.isoOfNatIso E).symm ≪≫
    (complexDiagramColimitIso M.asFunctor).symm ≪≫
    G.mapIso (complexDiagramAsFunctorIso M) ≪≫
    CochainComplex.mappingCone.mapHomologicalComplexIso φ (colim (J := Discrete I) (C := C)) ≪≫
    homotopyCofiber.mapArrowIso _ _
      (fun n => ⟨n - 1, by change n - 1 + 1 = n; omega⟩) eφ

end CWSolid
