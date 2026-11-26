module
import all Init.Data.Int.Package
import all Init.Data.Fin.Package
import all Init.Data.Order.LemmasExtra
import all Init.Data.Order.Factories

/-! Construct the order-package proofs directly from the concrete numeric orders. -/

open Std

namespace OmegaChecks.InitPort.Alternatives

public theorem Int.instLinearOrderPackage._proof_2 :
    type_of% @_root_.Int.instLinearOrderPackage._proof_2 := by
  dsimp only
  intro a b
  change decide (a = b) = true ↔ a ≤ b ∧ b ≤ a
  constructor
  · intro h
    cases of_decide_eq_true h
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  · intro ⟨h, h'⟩
    exact decide_eq_true (Int.le_antisymm h h')

public theorem Int.instLinearOrderPackage._proof_7 :
    type_of% @_root_.Int.instLinearOrderPackage._proof_7 :=
  fun _ _ => Int.le_antisymm

public theorem Fin.instLinearOrderPackage._proof_5 :
    type_of% @_root_.Fin.instLinearOrderPackage._proof_5 := by
  intro n a b
  rw [← Fin.compare_val]
  exact (Std.isLE_compare (a := a.val) (b := b.val)).trans Fin.le_def.symm

public theorem Fin.instLinearOrderPackage._proof_6 :
    type_of% @_root_.Fin.instLinearOrderPackage._proof_6 := by
  intro n a b
  rw [← Fin.compare_val]
  exact (Std.isGE_compare (a := a.val) (b := b.val)).trans Fin.le_def.symm

public theorem Fin.instLinearOrderPackage._proof_7 :
    type_of% @_root_.Fin.instLinearOrderPackage._proof_7 :=
  fun {_} _ _ => Fin.le_antisymm

public theorem Std.LawfulOrderBEq.of_le : type_of% @_root_.Std.LawfulOrderBEq.of_le :=
  fun {_} _ _ h => ⟨h⟩

public theorem Std.LawfulOrderInf.of_lt : type_of% @_root_.Std.LawfulOrderInf.of_lt := by
  intro α op lt h
  letI := LE.ofLT α
  refine ⟨fun a b c => ?_⟩
  change (¬ min b c < a) ↔ (¬ b < a) ∧ (¬ c < a)
  exact (not_congr (h a b c)).trans not_or

public theorem Std.LawfulOrderSup.of_lt : type_of% @_root_.Std.LawfulOrderSup.of_lt := by
  intro α op lt h
  letI := LE.ofLT α
  refine ⟨fun a b c => ?_⟩
  change (¬ c < max a b) ↔ (¬ c < a) ∧ (¬ c < b)
  exact (not_congr (h a b c)).trans not_or

private theorem compareEqual {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] (a b : α) :
    compare a b = .eq ↔ a ≤ b ∧ b ≤ a :=
  Ordering.eq_eq_iff_isLE_and_isGE.trans
    (and_congr (LawfulOrderOrd.isLE_compare a b) (LawfulOrderOrd.isGE_compare a b))

public theorem Std.LawfulOrderBEq.of_ord : type_of% @_root_.Std.LawfulOrderBEq.of_ord :=
  fun _ _ _ _ _ h => ⟨fun a b => (h a b).trans (compareEqual a b)⟩

public theorem Std.instLawfulOrderBEqOfLawfulBEqOrdOfLawfulOrderOrd :
    type_of% @_root_.Std.instLawfulOrderBEqOfLawfulBEqOrdOfLawfulOrderOrd := by
  intro α eq ord le law order
  exact ⟨fun a b => (LawfulBEqOrd.compare_eq_iff_beq (a := a) (b := b)).symm.trans (compareEqual a b)⟩

public theorem Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe :
    type_of% @_root_.Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe := by
  intro α ord le law antisymm
  exact {
    compare_self := fun {a} =>
      have h : a ≤ a := (_root_.Std.instTotalLeOfLawfulOrderOrd (α := α)).total a a |>.elim id id
      (compareEqual a a).mpr ⟨h,h⟩
    eq_of_compare := fun {a b} h => ((compareEqual a b).mp h).elim (Antisymm.antisymm a b) }

public theorem Std.instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder :
    type_of% @_root_.Std.instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder := by
  intro α ord le law order
  exact {
    compare_self := fun {a} => (compareEqual a a).mpr ⟨Std.le_refl _, Std.le_refl _⟩
    eq_of_compare := fun {a b} h => ((compareEqual a b).mp h).elim (fun f r => Std.le_antisymm f r) }

public theorem Std.instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd :
    type_of% @_root_.Std.instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd := by
  intro α ord le order law
  exact ⟨fun a b f r => LawfulEqOrd.eq_of_compare ((compareEqual a b).mpr ⟨f,r⟩)⟩

public theorem Std.min_eq_ite_isLE_compare : type_of% @_root_.Std.min_eq_ite_isLE_compare := by
  intro α ord le min order law a b
  split
  · next h => exact LawfulOrderLeftLeaningMin.min_eq_left _ _ (isLE_compare.mp h)
  · next h => exact LawfulOrderLeftLeaningMin.min_eq_right _ _ (fun he => h (isLE_compare.mpr he))

public theorem Std.max_eq_ite_isGE_compare : type_of% @_root_.Std.max_eq_ite_isGE_compare := by
  intro α ord le max order law a b
  split
  · next h => exact LawfulOrderLeftLeaningMax.max_eq_left _ _ (isGE_compare.mp h)
  · next h => exact LawfulOrderLeftLeaningMax.max_eq_right _ _ (fun he => h (isGE_compare.mpr he))

private theorem comparisonLT {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] (a b : α) :
    compare a b = .lt ↔ a ≤ b ∧ ¬ b ≤ a := by
  have bits (o : Ordering) : o = .lt ↔ o.isLE = true ∧ ¬ o.isGE = true := by
    cases o <;> decide
  exact (bits _).trans (and_congr (isLE_compare (a := a)) (not_congr (isGE_compare (a := a))))

private theorem comparisonGT {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] (a b : α) :
    compare a b = .gt ↔ b ≤ a ∧ ¬ a ≤ b := by
  have bits (o : Ordering) : o = .gt ↔ o.isGE = true ∧ ¬ o.isLE = true := by
    cases o <;> decide
  exact (bits _).trans (and_congr (isGE_compare (a := a)) (not_congr (isLE_compare (a := a))))

public theorem Std.LawfulOrderLT.of_ord : type_of% @_root_.Std.LawfulOrderLT.of_ord :=
  fun _ _ _ _ _ h => ⟨fun a b => (h a b).trans (comparisonLT a b)⟩

public theorem Std.compare_eq_lt : type_of% @_root_.Std.compare_eq_lt :=
  fun {_} _ _ _ _ _ {a b} => (comparisonLT a b).trans (LawfulOrderLT.lt_iff a b).symm

public theorem Std.compare_eq_gt : type_of% @_root_.Std.compare_eq_gt :=
  fun {_} _ _ _ _ _ {a b} => (comparisonGT a b).trans (LawfulOrderLT.lt_iff b a).symm

public theorem Std.instLawfulOrderLT_ofOrd : type_of% @_root_.Std.instLawfulOrderLT_ofOrd := by
  intro α ord le law
  letI := LT.ofOrd α
  exact ⟨comparisonLT⟩

public theorem Std.instLawfulOrderBEq_ofOrd : type_of% @_root_.Std.instLawfulOrderBEq_ofOrd := by
  intro α ord le law
  letI := BEq.ofOrd α
  refine ⟨fun a b => ?_⟩
  change decide (compare a b = .eq) = true ↔ a ≤ b ∧ b ≤ a
  exact (Iff.intro of_decide_eq_true decide_eq_true).trans (compareEqual a b)

@[instance_reducible] public def DecidableLT.ofOrd : type_of% @_root_.DecidableLT.ofOrd :=
  fun _ _ _ _ _ _ a b => if h : compare a b = .lt then
    isTrue (Std.compare_eq_lt.mp h)
  else
    isFalse fun lt => h (Std.compare_eq_lt.mpr lt)

private theorem swapOfBits (x y : Ordering) (f : x.isLE = y.isGE) (r : x.isGE = y.isLE) :
    x = y.swap := by
  cases x <;> cases y <;> first | rfl | contradiction

public theorem Std.instOrientedOrdOfLawfulOrderOrd : type_of% @_root_.Std.instOrientedOrdOfLawfulOrderOrd := by
  intro α le ord law
  refine ⟨fun {a b} => swapOfBits _ _ ?_ ?_⟩
  · exact Bool.eq_iff_iff.mpr ((LawfulOrderOrd.isLE_compare a b).trans (LawfulOrderOrd.isGE_compare b a).symm)
  · exact Bool.eq_iff_iff.mpr ((LawfulOrderOrd.isGE_compare a b).trans (LawfulOrderOrd.isLE_compare b a).symm)

public theorem Std.instTransOrdOfLawfulOrderOrdOfIsPreorder :
    type_of% @_root_.Std.instTransOrdOfLawfulOrderOrdOfIsPreorder := by
  intro α ord le law order
  exact { isLE_trans := fun h₁ h₂ => isLE_compare.mpr (Std.le_trans (isLE_compare.mp h₁) (isLE_compare.mp h₂)) }

end OmegaChecks.InitPort.Alternatives
