/- GID: D5/S3/HomologicalAlgebra/Solid/UnboundedTruncationColimit
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/UnboundedTruncationColimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedCoproduct
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Category.Preorder

/-!
Copyright (c) 2026. Released under Apache 2.0.
The actual increasing brutal lower truncations of every unbounded cochain
complex have that complex as their colimit. Each fixed coefficient is
eventually the original coefficient with identity transition. This is the
concrete first telescope input for unbounded realization, not a hypothesis
postulating generation or a realization equivalence.
Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry,
Theorem 3.3.1, unbounded extension by truncations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex
open scoped ZeroObject

namespace CWSolid

variable {C : Type*} [Category* C] [Abelian C]

/-- The actual lower truncation, retaining every degree at least -m. -/
def lowerTruncation (K : CochainComplex C ℤ) (m : ℕ) : CochainComplex C ℤ where
  X i := if -(m : ℤ) ≤ i then K.X i else 0
  d i j := if hi : -(m : ℤ) ≤ i then
    if hj : -(m : ℤ) ≤ j then
      eqToHom (by simp [hi]) ≫ K.d i j ≫ eqToHom (by simp [hj])
    else 0
    else 0
  shape i j hij := by
    split_ifs <;> simp [K.shape i j hij]
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hjk' : j + 1 = k := hjk
    by_cases hi : -(m : ℤ) ≤ i
    · have hj : -(m : ℤ) ≤ j := by omega
      have hk : -(m : ℤ) ≤ k := by omega
      simp [hi, hj, hk, Category.assoc, K.d_comp_d i j k]
    · simp [hi]

/-- The transition between two actual lower truncations. -/
def lowerTruncationMap (K : CochainComplex C ℤ) (m n : ℕ) (hmn : m ≤ n) :
    lowerTruncation K m ⟶ lowerTruncation K n where
  f i := if hi : -(m : ℤ) ≤ i then
    eqToHom (by
      have hn : -(n : ℤ) ≤ i := by omega
      simp only [lowerTruncation, if_pos hi, if_pos hn])
    else 0
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases hi : -(m : ℤ) ≤ i
    · have hj : -(m : ℤ) ≤ j := by omega
      have hni : -(n : ℤ) ≤ i := by omega
      have hnj : -(n : ℤ) ≤ j := by omega
      simp [lowerTruncation, hi, hj, hni, hnj]
    · simp [lowerTruncation, hi]

/-- The canonical chain map into the unrestricted original complex. -/
def lowerTruncationι (K : CochainComplex C ℤ) (m : ℕ) : lowerTruncation K m ⟶ K where
  f i := if hi : -(m : ℤ) ≤ i then
    eqToHom (by simp only [lowerTruncation, if_pos hi]) else 0
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases hi : -(m : ℤ) ≤ i
    · have hj : -(m : ℤ) ≤ j := by omega
      simp [lowerTruncation, hi, hj]
    · simp [lowerTruncation, hi]

@[simp] theorem lowerTruncationMap_id (K : CochainComplex C ℤ) (m : ℕ) :
    lowerTruncationMap K m m le_rfl = 𝟙 _ := by
  ext i
  by_cases hi : -(m : ℤ) ≤ i
  · simp [lowerTruncationMap, hi]
  · have hz : IsZero ((lowerTruncation K m).X i) := by
      simp only [lowerTruncation, if_neg hi]
      exact isZero_zero C
    exact hz.eq_of_src _ _

@[reassoc] theorem lowerTruncationMap_comp (K : CochainComplex C ℤ)
    (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) :
    lowerTruncationMap K l m hlm ≫ lowerTruncationMap K m n hmn =
      lowerTruncationMap K l n (hlm.trans hmn) := by
  ext i
  by_cases hi : -(l : ℤ) ≤ i
  · have hm : -(m : ℤ) ≤ i := by omega
    have hn : -(n : ℤ) ≤ i := by omega
    simp [lowerTruncationMap, hi, hm, hn]
  · simp [lowerTruncationMap, hi]

@[reassoc] theorem lowerTruncationMap_ι (K : CochainComplex C ℤ)
    (m n : ℕ) (hmn : m ≤ n) :
    lowerTruncationMap K m n hmn ≫ lowerTruncationι K n = lowerTruncationι K m := by
  ext i
  by_cases hi : -(m : ℤ) ≤ i
  · have hn : -(n : ℤ) ≤ i := by omega
    simp [lowerTruncationMap, lowerTruncationι, hi, hn]
  · simp [lowerTruncationMap, lowerTruncationι, hi]

theorem lowerTruncationι_f_isIso (K : CochainComplex C ℤ) (m : ℕ)
    (i : ℤ) (hi : -(m : ℤ) ≤ i) : IsIso ((lowerTruncationι K m).f i) := by
  simp only [lowerTruncationι, dif_pos hi]
  infer_instance

instance lowerTruncation_isStrictlyGE (K : CochainComplex C ℤ) (m : ℕ) :
    (lowerTruncation K m).IsStrictlyGE (-(m : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  simp only [lowerTruncation, if_neg (show ¬ -(m : ℤ) ≤ i by omega)]
  exact isZero_zero C

def lowerTruncationDiagram (K : CochainComplex C ℤ) : ℕ ⥤ CochainComplex C ℤ where
  obj m := lowerTruncation K m
  map f := lowerTruncationMap K _ _ (leOfHom f)
  map_id m := lowerTruncationMap_id K m
  map_comp f g := (lowerTruncationMap_comp K _ _ _ _ _).symm

def lowerTruncationCocone (K : CochainComplex C ℤ) : Cocone (lowerTruncationDiagram K) where
  pt := K
  ι := { app := lowerTruncationι K
         naturality m n f := by
           change lowerTruncationMap K m n (leOfHom f) ≫ lowerTruncationι K n =
             lowerTruncationι K m ≫ 𝟙 K
           simpa only [Category.comp_id] using lowerTruncationMap_ι K m n (leOfHom f) }

/-- Each coefficient of this specific unbounded diagram stabilizes. -/
theorem lowerTruncationDiagram_eventuallyConstant (K : CochainComplex C ℤ) (i : ℤ) :
    (lowerTruncationDiagram K ⋙ eval C (.up ℤ) i).IsEventuallyConstantFrom
      ((-i).toNat) := by
  intro n f
  have hm : -(((-i).toNat : ℕ) : ℤ) ≤ i := by omega
  have hn : -(n : ℤ) ≤ i := by
    have hmn := leOfHom f
    omega
  haveI := lowerTruncationι_f_isIso K ((-i).toNat) i hm
  haveI := lowerTruncationι_f_isIso K n i hn
  have heq := congrArg (fun z => z.f i)
    (lowerTruncationMap_ι K ((-i).toNat) n (leOfHom f))
  change IsIso ((lowerTruncationMap K ((-i).toNat) n (leOfHom f)).f i)
  haveI : IsIso ((lowerTruncationMap K ((-i).toNat) n (leOfHom f)).f i ≫
      (lowerTruncationι K n).f i) := by
    rw [← HomologicalComplex.comp_f, lowerTruncationMap_ι]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((lowerTruncationMap K ((-i).toNat) n (leOfHom f)).f i)
    ((lowerTruncationι K n).f i)

/-- Every arbitrary unbounded complex is the actual colimit of its
bounded-below lower truncations. No completeness premise is used. -/
def lowerTruncationCocone_isColimit (K : CochainComplex C ℤ) :
    IsColimit (lowerTruncationCocone K) := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  haveI := lowerTruncationι_f_isIso K ((-i).toNat) i (by omega)
  haveI : IsIso (((eval C (.up ℤ) i).mapCocone
      (lowerTruncationCocone K)).ι.app ((-i).toNat)) := by
    change IsIso ((lowerTruncationι K ((-i).toNat)).f i)
    infer_instance
  exact (lowerTruncationDiagram_eventuallyConstant K i).isColimitOfIsIso
    ((eval C (.up ℤ) i).mapCocone (lowerTruncationCocone K))

end CWSolid

#print axioms CWSolid.lowerTruncation
#print axioms CWSolid.lowerTruncationMap
#print axioms CWSolid.lowerTruncationι
#print axioms CWSolid.lowerTruncationMap_id
#print axioms CWSolid.lowerTruncationMap_comp
#print axioms CWSolid.lowerTruncationMap_ι
#print axioms CWSolid.lowerTruncationι_f_isIso
#print axioms CWSolid.lowerTruncation_isStrictlyGE
#print axioms CWSolid.lowerTruncationDiagram
#print axioms CWSolid.lowerTruncationCocone
#print axioms CWSolid.lowerTruncationDiagram_eventuallyConstant
#print axioms CWSolid.lowerTruncationCocone_isColimit
