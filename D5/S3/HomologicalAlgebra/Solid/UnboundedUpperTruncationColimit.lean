/- GID: D5/S3/HomologicalAlgebra/Solid/UnboundedUpperTruncationColimit
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/UnboundedUpperTruncationColimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedCoproduct
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Category.Preorder

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
The actual increasing good upper truncations have every unrestricted
cochain complex as their colimit. Together with the accepted lower
truncation construction, this is the concrete double truncation step
in unbounded generation. No realization equivalence or completeness
premise is asserted. Research: Rodríguez Camargo, Notes on Solid Geometry,
Theorem 3.3.1, unbounded extension by truncations and telescopes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex

namespace CWSolid

variable {C : Type*} [Category* C] [Abelian C]

local instance upperTruncationι_mono (K : CochainComplex C ℤ) (n : ℤ) :
    Mono (K.ιTruncLE n) := by
  dsimp only [CochainComplex.ιTruncLE]
  infer_instance

/-- The transition is induced by the genuine truncation and its inclusion. -/
def upperTruncationMap (K : CochainComplex C ℤ) (m n : ℕ) (hmn : m ≤ n) :
    K.truncLE (m : ℤ) ⟶ K.truncLE (n : ℤ) := by
  haveI : (K.truncLE (m : ℤ)).IsStrictlyLE (n : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ (m : ℤ) (n : ℤ) (by omega)
  exact inv ((K.truncLE (m : ℤ)).ιTruncLE (n : ℤ)) ≫
    CochainComplex.truncLEMap (K.ιTruncLE (m : ℤ)) (n : ℤ)

@[reassoc (attr := simp)]
theorem upperTruncationMap_ι (K : CochainComplex C ℤ) (m n : ℕ) (hmn : m ≤ n) :
    upperTruncationMap K m n hmn ≫ K.ιTruncLE (n : ℤ) = K.ιTruncLE (m : ℤ) := by
  haveI : (K.truncLE (m : ℤ)).IsStrictlyLE (n : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ (m : ℤ) (n : ℤ) (by omega)
  dsimp only [upperTruncationMap]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

@[simp] theorem upperTruncationMap_id (K : CochainComplex C ℤ) (m : ℕ) :
    upperTruncationMap K m m le_rfl = 𝟙 _ := by
  apply (cancel_mono (K.ιTruncLE (m : ℤ))).1
  simp

@[reassoc] theorem upperTruncationMap_comp (K : CochainComplex C ℤ)
    (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) :
    upperTruncationMap K l m hlm ≫ upperTruncationMap K m n hmn =
      upperTruncationMap K l n (hlm.trans hmn) := by
  apply (cancel_mono (K.ιTruncLE (n : ℤ))).1
  simp [Category.assoc]

def upperTruncationDiagram (K : CochainComplex C ℤ) : ℕ ⥤ CochainComplex C ℤ where
  obj m := K.truncLE (m : ℤ)
  map f := upperTruncationMap K _ _ (leOfHom f)
  map_id m := upperTruncationMap_id K m
  map_comp f g := (upperTruncationMap_comp K _ _ _ _ _).symm

def upperTruncationCocone (K : CochainComplex C ℤ) : Cocone (upperTruncationDiagram K) where
  pt := K
  ι := { app m := K.ιTruncLE (m : ℤ)
         naturality m n f := by
           change upperTruncationMap K m n (leOfHom f) ≫ K.ιTruncLE (n : ℤ) =
             K.ιTruncLE (m : ℤ) ≫ 𝟙 K
           simp }

/-- Below the genuine truncation boundary, its actual inclusion is invertible. -/
theorem upperTruncationι_f_isIso (K : CochainComplex C ℤ) (n i : ℤ) (hi : i < n) :
    IsIso ((K.ιTruncLE n).f i) := by
  let e := (ComplexShape.embeddingUpIntLE n).op
  have hi' : e.f (n - i).natAbs = i := by
    change n - ((n - i).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hn : ¬ (ComplexShape.embeddingUpIntLE n).BoundaryLE (n - i).natAbs := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff, Int.natAbs_eq_zero]
    omega
  have hn' : ¬ e.BoundaryGE (n - i).natAbs := by simpa [e] using hn
  haveI : IsIso ((K.op.πTruncGE e).f i) := by
    dsimp only [HomologicalComplex.πTruncGE]
    rw [e.isIso_liftExtend_f_iff _ _ hi']
    exact K.op.isIso_restrictionToTruncGE' e _ hn'
  change IsIso (((K.op.πTruncGE e).f i).unop)
  infer_instance

theorem upperTruncationDiagram_eventuallyConstant (K : CochainComplex C ℤ) (i : ℤ) :
    (upperTruncationDiagram K ⋙ eval C (.up ℤ) i).IsEventuallyConstantFrom
      (i.toNat + 1) := by
  intro n f
  have hm : i < ((i.toNat + 1 : ℕ) : ℤ) := by omega
  have hn : i < (n : ℤ) := by
    have hmn := leOfHom f
    omega
  haveI := upperTruncationι_f_isIso K ((i.toNat + 1 : ℕ) : ℤ) i hm
  haveI := upperTruncationι_f_isIso K n i hn
  change IsIso ((upperTruncationMap K (i.toNat + 1) n (leOfHom f)).f i)
  haveI : IsIso ((upperTruncationMap K (i.toNat + 1) n (leOfHom f)).f i ≫
      (K.ιTruncLE (n : ℤ)).f i) := by
    rw [← HomologicalComplex.comp_f, upperTruncationMap_ι]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((upperTruncationMap K (i.toNat + 1) n (leOfHom f)).f i)
    ((K.ιTruncLE (n : ℤ)).f i)

/-- This is an actual colimit for every unbounded K, in particular in Solid. -/
def upperTruncationCocone_isColimit (K : CochainComplex C ℤ) :
    IsColimit (upperTruncationCocone K) := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  haveI := upperTruncationι_f_isIso K ((i.toNat + 1 : ℕ) : ℤ) i (by omega)
  haveI : IsIso (((eval C (.up ℤ) i).mapCocone
      (upperTruncationCocone K)).ι.app (i.toNat + 1)) := by
    change IsIso ((K.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i)
    infer_instance
  exact (upperTruncationDiagram_eventuallyConstant K i).isColimitOfIsIso
    ((eval C (.up ℤ) i).mapCocone (upperTruncationCocone K))

end CWSolid

#print axioms CWSolid.upperTruncationMap
#print axioms CWSolid.upperTruncationMap_ι
#print axioms CWSolid.upperTruncationMap_id
#print axioms CWSolid.upperTruncationMap_comp
#print axioms CWSolid.upperTruncationDiagram
#print axioms CWSolid.upperTruncationCocone
#print axioms CWSolid.upperTruncationι_f_isIso
#print axioms CWSolid.upperTruncationDiagram_eventuallyConstant
#print axioms CWSolid.upperTruncationCocone_isColimit
