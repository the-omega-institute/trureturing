/- GID: D5/S3/ConceptDynamics/Attribution/CoordinateFlagCoupling
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/CoordinateFlagCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every two-row Boolean-profile coupling lifts to an invariant coupling with exact coordinate-subgroup fixed masses. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Defs

/-! Realize Boolean coupling profiles by fixed points of coordinate subgroups. -/

set_option autoImplicit false

open Finset
open scoped Classical

noncomputable section

namespace D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling

abbrev Acting (I : Type*) := Multiplicative (I → ZMod 2)

structure Output (I : Type*) where
  profile : I → Bool
  colour : ZMod 2

variable {I : Type*} [Fintype I]

def shift (profile : I → Bool) (v : I → ZMod 2) : ZMod 2 :=
  ∑ i, if profile i then 0 else v i

private theorem shift_add (profile : I → Bool) (v w : I → ZMod 2) :
    shift profile (v + w) = shift profile v + shift profile w := by
  rw [shift, shift, shift, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  cases profile i <;> simp

instance : MulAction (Acting I) (Output I) where
  smul g y := ⟨y.profile, shift y.profile g.toAdd + y.colour⟩
  one_smul y := by
    have zeroShift : shift y.profile 0 = 0 := by
      unfold shift
      apply sum_eq_zero
      intro i _
      cases y.profile i <;> rfl
    change Output.mk _ (shift y.profile 0 + _) = y
    cases y
    simp [zeroShift]
  mul_smul g h y := by
    change Output.mk _ (shift y.profile (g.toAdd + h.toAdd) + _) = _
    rw [shift_add, add_assoc]
    rfl

def generator (i : I) : Acting I := Multiplicative.ofAdd (Pi.single i 1)

def coordinate (i : I) : Subgroup (Acting I) := Subgroup.zpowers (generator i)

private theorem coordinate_fixed_iff (y : Output I) (i : I) :
    (∀ g ∈ coordinate i, g • y = y) ↔ y.profile i = true := by
  have generatorFix : generator i • y = y ↔ y.profile i = true := by
    have eval : shift y.profile (Pi.single i 1) = if y.profile i then 0 else 1 := by
      unfold shift
      rw [sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · exact fun h => (h (mem_univ i)).elim
    change Output.mk y.profile (shift y.profile (Pi.single i 1) + y.colour) = y ↔ _
    have result : Output.mk y.profile (shift y.profile (Pi.single i 1) + y.colour) = y ↔
        shift y.profile (Pi.single i 1) + y.colour = y.colour := by cases y; simp
    rw [result, eval]
    cases y.profile i <;> simp
  change coordinate i ≤ MulAction.stabilizer (Acting I) y ↔ _
  rw [coordinate, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
  exact generatorFix


private def outputEquiv : Output I ≃ (I → Bool) × ZMod 2 where
  toFun y := (y.profile, y.colour)
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (Output I) :=
  Fintype.ofEquiv ((I → Bool) × ZMod 2) outputEquiv.symm

private theorem sum_outputs (f : Output I → ℝ) :
    ∑ y, f y = ∑ p : I → Bool, ∑ c : ZMod 2, f ⟨p, c⟩ := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv outputEquiv _ _ (fun _ => rfl)

private theorem sum_colours_constant (r : ℝ) : ∑ _ : ZMod 2, r = 2 * r := by
  rw [sum_const, card_univ, ZMod.card]
  norm_num [two_nsmul, two_mul]

abbrev Coupling {A : Type*} [Fintype A] (left right : A → ℝ) (w : A → A → ℝ) : Prop :=
  (∀ x y, 0 ≤ w x y) ∧ (∀ x, ∑ y, w x y = left x) ∧ (∀ y, ∑ x, w x y = right y)

noncomputable def commonTrue (w : (I → Bool) → (I → Bool) → ℝ) (i : I) : ℝ :=
  ∑ p, ∑ q, if p i && q i then w p q else 0

noncomputable def commonFixed (w : Output I → Output I → ℝ) (i : I) : ℝ := by
  classical
  exact ∑ x, ∑ y, if (∀ g ∈ coordinate i, g • x = x ∧ g • y = y) then w x y else 0

private theorem fixed_pair_iff (x y : Output I) (i : I) :
    (∀ g ∈ coordinate i, g • x = x ∧ g • y = y) ↔ (x.profile i && y.profile i) = true := by
  simp only [forall_and, coordinate_fixed_iff, Bool.and_eq_true]

noncomputable def forgetColours (w : Output I → Output I → ℝ) (p q : I → Bool) : ℝ :=
  ∑ c : ZMod 2, ∑ d : ZMod 2, w ⟨p, c⟩ ⟨q, d⟩

private noncomputable def lift (w : (I → Bool) → (I → Bool) → ℝ) (x y : Output I) : ℝ :=
  w x.profile y.profile / 4

private theorem push_common (w : Output I → Output I → ℝ) (i : I) :
    commonFixed w i = commonTrue (forgetColours w) i := by
  classical
  unfold commonFixed commonTrue forgetColours
  simp_rw [fixed_pair_iff, sum_outputs]
  apply sum_congr rfl
  intro p _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  by_cases h : (p i && q i) = true <;> simp [h]

omit [Fintype I] in
private theorem push_lift (w : (I → Bool) → (I → Bool) → ℝ) :
    forgetColours (lift w) = w := by
  funext p q
  simp only [forgetColours, lift, sum_colours_constant]
  ring

-- Each matrix entry is preserved by projecting the invariant lift.
theorem invariant_coupling_iff (left right : (I → Bool) → ℝ)
    (w : (I → Bool) → (I → Bool) → ℝ) :
    Coupling left right w ↔
      ∃ W : Output I → Output I → ℝ,
        Coupling (fun x => left x.profile / 2) (fun y => right y.profile / 2) W ∧
        (∀ (g : Acting I) x y, W (g • x) (g • y) = W x y) ∧
        forgetColours W = w ∧ ∀ i, commonFixed W i = commonTrue w i := by
  constructor
  · rintro ⟨nonneg, row, column⟩
    refine ⟨lift w, ⟨fun x y => div_nonneg (nonneg _ _) (by norm_num), fun x => ?_, fun y => ?_⟩,
      fun _ _ _ => rfl, push_lift w, fun i => ?_⟩
    · rw [sum_outputs]
      simp_rw [lift, sum_colours_constant, ← mul_div_assoc, ← sum_div, ← mul_sum, row]
      ring
    · rw [sum_outputs]
      simp_rw [lift, sum_colours_constant, ← mul_div_assoc, ← sum_div, ← mul_sum, column]
      ring
    · rw [push_common, push_lift]
  · rintro ⟨W, ⟨nonneg, row, column⟩, _, same, _⟩
    rw [← same]
    refine ⟨fun p q => ?_, fun p => ?_, fun q => ?_⟩
    · exact sum_nonneg fun c _ => sum_nonneg fun d _ => nonneg ⟨p, c⟩ ⟨q, d⟩
    · unfold forgetColours
      rw [sum_comm]
      simp_rw [← sum_outputs, row, sum_colours_constant]
      ring
    · unfold forgetColours
      calc
        (∑ p : I → Bool, ∑ c : ZMod 2, ∑ d : ZMod 2, W ⟨p, c⟩ ⟨q, d⟩) =
            ∑ p : I → Bool, ∑ d : ZMod 2, ∑ c : ZMod 2, W ⟨p, c⟩ ⟨q, d⟩ := by
          exact sum_congr rfl (fun _ _ => sum_comm)
        _ = ∑ d : ZMod 2, ∑ p : I → Bool, ∑ c : ZMod 2, W ⟨p, c⟩ ⟨q, d⟩ := sum_comm
        _ = right q := by
          have collapse (d : ZMod 2) :
              (∑ p : I → Bool, ∑ c : ZMod 2, W ⟨p, c⟩ ⟨q, d⟩) = right q / 2 :=
            (sum_outputs (fun x => W x ⟨q, d⟩)).symm.trans (column ⟨q, d⟩)
          simp only [collapse, sum_colours_constant]
          ring

end D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
