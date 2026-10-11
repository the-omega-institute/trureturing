/- GID: D5/S3/HomologicalAlgebra/Solid/ComplexColimit
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/ComplexColimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! Exact colimits of arbitrary unbounded complexes. These new proofs are
used to assemble weak equivalences in the cellular localization argument.
Released under the Apache 2.0 license. -/

noncomputable section
open CategoryTheory Limits HomologicalComplex

namespace CWSolid

variable {C : Type*} [Category* C] [Abelian C]
  {J : Type*} [Category* J]

/-- Transpose a diagram of complexes to a complex of diagrams. -/
def complexDiagram (K : J ⥤ CochainComplex C ℤ) : CochainComplex (J ⥤ C) ℤ where
  X n := K ⋙ eval C (.up ℤ) n
  d n m :=
    { app j := (K.obj j).d n m
      naturality j j' f := (K.map f).comm n m }
  shape n m h := by ext j; exact (K.obj j).shape n m h
  d_comp_d' n m k _ _ := by ext j; exact (K.obj j).d_comp_d n m k

/-- Transposition on actual natural transformations. -/
def complexDiagramMap {K L : J ⥤ CochainComplex C ℤ} (f : K ⟶ L) :
    complexDiagram K ⟶ complexDiagram L where
  f n := Functor.whiskerRight f (eval C (.up ℤ) n)
  comm' n m _ := by ext j; exact (f.app j).comm n m

variable [HasColimitsOfShape J C]

local instance constantFunctor_additive : (Functor.const J : C ⥤ J ⥤ C).Additive where
  map_add := by intros; ext j; rfl

local instance colimitFunctor_additive : (colim (J := J) (C := C)).Additive :=
  colimConstAdj.left_adjoint_additive

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual degreewise colimit is the colimit functor applied to the
transposed unbounded complex. -/
def complexDiagramColimitIso (K : J ⥤ CochainComplex C ℤ) :
    ((colim (J := J) (C := C)).mapHomologicalComplex (.up ℤ)).obj (complexDiagram K) ≅
      colimit K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (preservesColimitIso (eval C (.up ℤ) n) K).symm)
    (by
      intro n m h
      apply colimit.hom_ext
      intro j
      change colimit.ι (K ⋙ eval C (.up ℤ) n) j ≫
        (preservesColimitIso (eval C (.up ℤ) n) K).inv ≫ (colimit K).d n m =
          colimit.ι (K ⋙ eval C (.up ℤ) n) j ≫
            colim.map ((complexDiagram K).d n m) ≫
              (preservesColimitIso (eval C (.up ℤ) m) K).inv
      have hm : colimit.ι ((complexDiagram K).X m) j ≫
          (preservesColimitIso (eval C (.up ℤ) m) K).inv = (colimit.ι K j).f m :=
        ι_preservesColimitIso_inv (eval C (.up ℤ) m) K j
      rw [colimit.ι_map_assoc, ι_preservesColimitIso_inv_assoc, hm]
      change (colimit.ι K j).f n ≫ (colimit K).d n m =
        (K.obj j).d n m ≫ (colimit.ι K j).f m
      exact (colimit.ι K j).comm n m)

set_option backward.isDefEq.respectTransparency false in
theorem complexDiagramColimitIso_naturality {K L : J ⥤ CochainComplex C ℤ}
    (f : K ⟶ L) :
    ((colim (J := J) (C := C)).mapHomologicalComplex (.up ℤ)).map (complexDiagramMap f) ≫
        (complexDiagramColimitIso L).hom =
      (complexDiagramColimitIso K).hom ≫ colim.map f := by
  ext n
  apply colimit.hom_ext
  intro j
  dsimp only [comp_f, complexDiagramMap, Functor.mapHomologicalComplex_map_f,
    complexDiagramColimitIso, Hom.isoOfComponents, Iso.symm_hom]
  have hK : colimit.ι ((complexDiagram K).X n) j ≫
      (preservesColimitIso (eval C (.up ℤ) n) K).inv = (colimit.ι K j).f n :=
    ι_preservesColimitIso_inv (eval C (.up ℤ) n) K j
  have hL : colimit.ι ((complexDiagram L).X n) j ≫
      (preservesColimitIso (eval C (.up ℤ) n) L).inv = (colimit.ι L j).f n :=
    ι_preservesColimitIso_inv (eval C (.up ℤ) n) L j
  change colimit.ι (K ⋙ eval C (.up ℤ) n) j ≫
      colim.map (Functor.whiskerRight f (eval C (.up ℤ) n)) ≫
        (preservesColimitIso (eval C (.up ℤ) n) L).inv =
    colimit.ι (K ⋙ eval C (.up ℤ) n) j ≫
      (preservesColimitIso (eval C (.up ℤ) n) K).inv ≫ (colim.map f).f n
  erw [colimit.ι_map_assoc, hL, ← Category.assoc, hK]
  change (f.app j).f n ≫ (colimit.ι L j).f n = (colimit.ι K j).f n ≫ (colim.map f).f n
  have h := congrArg (fun z => z.f n) (colimit.ι_map f j)
  exact h.symm

section Exact

variable [HasExactColimitsOfShape J C]

/-- Exact colimits preserve all quasi-isomorphisms of arbitrary unbounded
diagrams. In particular, this covers filtered colimits and arbitrary sums
in the protected light condensed category. -/
theorem quasiIso_colimitMap {K L : J ⥤ CochainComplex C ℤ}
    (f : K ⟶ L) [∀ j, QuasiIso (f.app j)] : QuasiIso (colim.map f) := by
  have : QuasiIso (complexDiagramMap f) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro j
    change QuasiIso (f.app j)
    infer_instance
  have : QuasiIso (((colim (J := J) (C := C)).mapHomologicalComplex (.up ℤ)).map
      (complexDiagramMap f)) := by infer_instance
  have h : colim.map f = (complexDiagramColimitIso K).inv ≫
      ((colim (J := J) (C := C)).mapHomologicalComplex (.up ℤ)).map
        (complexDiagramMap f) ≫ (complexDiagramColimitIso L).hom := by
    rw [← cancel_epi (complexDiagramColimitIso K).hom, Iso.hom_inv_id_assoc]
    exact (complexDiagramColimitIso_naturality f).symm
  rw [h]
  infer_instance

end Exact

end CWSolid
