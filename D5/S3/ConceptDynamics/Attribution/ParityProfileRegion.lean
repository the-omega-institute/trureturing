/- GID: D5/S3/ConceptDynamics/Attribution/ParityProfileRegion
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityProfileRegion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite three-bit parity rows have an exact tetrahedron of common-flag masses under all couplings. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact coupling region for two rows supported on opposite Boolean parities. -/

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.ParityProfileRegion

abbrev Profile := Bool × Bool × Bool

private def bit (x : Profile) (i : Fin 3) : Bool :=
  if i = 0 then x.1 else if i = 1 then x.2.1 else x.2.2

private def odd (x : Profile) : Bool := (x.1 ^^ x.2.1) ^^ x.2.2

noncomputable def rowMass (p : Bool) (x : Profile) : ℝ := if odd x = p then 1 / 4 else 0

private def difference (x y : Profile) : Profile := (x.1 ^^ y.1, x.2.1 ^^ y.2.1, x.2.2 ^^ y.2.2)

noncomputable def commonMass (w : Profile → Profile → ℝ) (i : Fin 3) : ℝ :=
  ∑ x, ∑ y, if bit x i && bit y i then w x y else 0

abbrev Feasible (w : Profile → Profile → ℝ) : Prop :=
  (∀ x y, 0 ≤ w x y) ∧ (∀ x, ∑ y, w x y = rowMass false x) ∧
    (∀ y, ∑ x, w x y = rowMass true y)

private theorem off_parity (w : Profile → Profile → ℝ) (hw : Feasible w) (x y : Profile)
    (h : odd x = true ∨ odd y = false) : w x y = 0 := by
  apply le_antisymm _ (hw.1 x y)
  rcases h with h | h
  · calc
      w x y ≤ ∑ z, w x z := single_le_sum (fun z _ => hw.1 x z) (mem_univ y)
      _ = 0 := by rw [hw.2.1]; simp [rowMass, h]
  · calc
      w x y ≤ ∑ z, w z y := single_le_sum (fun z _ => hw.1 z y) (mem_univ x)
      _ = 0 := by rw [hw.2.2]; simp [rowMass, h]

private theorem total_row (p : Bool) : ∑ x, rowMass p x = 1 := by
  cases p <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool, rowMass, odd]

private theorem flag_row (p : Bool) (i : Fin 3) :
    (∑ x, if bit x i then rowMass p x else 0) = 1 / 2 := by
  cases p <;> fin_cases i <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, rowMass, odd, bit]

private def evenDifference (x y : Profile) : Bool := !(odd (difference x y))

private theorem support (w : Profile → Profile → ℝ) (hw : Feasible w) :
    ∀ x y, evenDifference x y = true → w x y = 0 := by
  intro x y h
  apply off_parity w hw
  revert h
  rcases x with ⟨a,b,c⟩
  rcases y with ⟨d,e,f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

private noncomputable def agreements (w : Profile → Profile → ℝ) (i : Fin 3) : ℝ :=
  ∑ x, ∑ y, if bit x i = bit y i then w x y else 0

private theorem twice_common (w : Profile → Profile → ℝ) (hw : Feasible w) (i : Fin 3) :
    2 * commonMass w i = agreements w i := by
  have first : (∑ x, ∑ y, if bit x i then w x y else 0) = 1 / 2 := by
    calc
      _ = ∑ x, if bit x i then rowMass false x else 0 := by
        apply sum_congr rfl
        intro x _
        cases bit x i <;> simp [hw.2.1]
      _ = _ := flag_row false i
  have second : (∑ x, ∑ y, if bit y i then w x y else 0) = 1 / 2 := by
    rw [sum_comm]
    calc
      _ = ∑ y, if bit y i then rowMass true y else 0 := by
        apply sum_congr rfl
        intro y _
        cases bit y i <;> simp [hw.2.2]
      _ = _ := flag_row true i
  have tot : (∑ x, ∑ y, w x y) = 1 := by simp only [hw.2.1, total_row]
  have identity : (∑ x, ∑ y,
      (2 * (if bit x i && bit y i then w x y else 0) + w x y)) =
      ∑ x, ∑ y, ((if bit x i = bit y i then w x y else 0) +
        (if bit x i then w x y else 0) + (if bit y i then w x y else 0)) := by
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    cases bit x i <;> cases bit y i <;> simp [two_mul]
  simp only [sum_add_distrib, ← mul_sum, commonMass, agreements] at identity ⊢
  linarith

private def singletonMask (i : Fin 3) : Profile :=
  if i = 0 then (true,false,false) else
  if i = 1 then (false,true,false) else (false,false,true)

private theorem allowed_mask (d : Profile) (h : odd d = true) :
    (d = singletonMask 0 ∨ d = singletonMask 1 ∨ d = singletonMask 2 ∨ d = (true,true,true)) := by
  revert h
  rcases d with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

private noncomputable def maskMass (w : Profile → Profile → ℝ) (d : Profile) : ℝ :=
  ∑ x, ∑ y, if difference x y = d then w x y else 0

private theorem mask_nonneg (w : Profile → Profile → ℝ) (hw : Feasible w) (d : Profile) :
    0 ≤ maskMass w d := by
  unfold maskMass
  apply sum_nonneg
  intro x _
  apply sum_nonneg
  intro y _
  split
  · exact hw.1 x y
  · exact le_rfl

private theorem agreement_eq (x y : Profile) (i : Fin 3) :
    (bit x i = bit y i) ↔
      (difference x y = singletonMask (i + 1) ∨ difference x y = singletonMask (i + 2))
      ∨ evenDifference x y = true ∧ bit x i = bit y i := by
  rcases x with ⟨a,b,c⟩
  rcases y with ⟨d,e,f⟩
  fin_cases i <;> cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

private theorem agreement_mass (w : Profile → Profile → ℝ) (hw : Feasible w) (i : Fin 3) :
    agreements w i = maskMass w (singletonMask (i + 1)) + maskMass w (singletonMask (i + 2)) := by
  have distinct : singletonMask (i + 1) ≠ singletonMask (i + 2) := by fin_cases i <;> decide
  unfold agreements maskMass
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases h : evenDifference x y = true
  · simp [support w hw x y h]
  have agree : bit x i = bit y i ↔
      difference x y = singletonMask (i + 1) ∨ difference x y = singletonMask (i + 2) := by
    exact (agreement_eq x y i).trans (by simp [h])
  simp only [agree]
  by_cases h₁ : difference x y = singletonMask (i + 1)
  · simp [h₁, distinct]
  · simp [h₁]

private theorem masks_take_total (w : Profile → Profile → ℝ) (hw : Feasible w) :
    maskMass w (singletonMask 0) + maskMass w (singletonMask 1) +
      maskMass w (singletonMask 2) + maskMass w (true,true,true) = 1 := by
  have tot : (∑ x, ∑ y, w x y) = 1 := by simp only [hw.2.1, total_row]
  rw [← tot]
  unfold maskMass
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases h : evenDifference x y = true
  · simp [support w hw x y h]
  have hd : odd (difference x y) = true := by simpa [evenDifference] using h
  rcases allowed_mask _ hd with h0 | h1 | h2 | h3
  all_goals first | rw [h0] | rw [h1] | rw [h2] | rw [h3]
  all_goals simp [singletonMask]

private theorem difference_eq (x y d : Profile) :
    difference x y = d ↔ y = difference x d := by
  rcases x with ⟨a,b,c⟩
  rcases y with ⟨e,f,g⟩
  rcases d with ⟨i,j,k⟩
  simp only [difference, Prod.mk.injEq]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;>
    exact ⟨by cases a <;> simpa using h₁, by cases b <;> simpa using h₂,
      by cases c <;> simpa using h₃⟩

private theorem difference_symm (x y : Profile) : difference x y = difference y x := by
  simp [difference, Bool.xor_comm]

private theorem row_translate (d y : Profile) (hd : odd d = true) :
    rowMass false (difference y d) = rowMass true y := by
  have parity : odd (difference y d) = !odd y := by
    revert hd
    rcases d with ⟨a,b,c⟩
    rcases y with ⟨e,f,g⟩
    cases a <;> cases b <;> cases c <;> cases e <;> cases f <;> cases g <;> decide
  cases h : odd y <;> simp [rowMass, parity, h]

private noncomputable def translateCoupling (d x y : Profile) : ℝ :=
  if difference x y = d then rowMass false x else 0

private theorem translate_feasible (d : Profile) (hd : odd d = true) :
    Feasible (translateCoupling d) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
  · unfold translateCoupling rowMass
    split_ifs <;> norm_num
  · simp [translateCoupling, difference_eq, Finset.sum_ite_eq']
  · simp_rw [translateCoupling, difference_symm _ y, difference_eq]
    rw [Finset.sum_ite_eq', ite_eq_left (mem_univ _), row_translate d y hd]

private theorem translate_mask (d e : Profile) (hd : odd d = true) :
    maskMass (translateCoupling d) e = if d = e then 1 else 0 := by
  by_cases eq : d = e
  · subst e
    have drop (x y : Profile) :
        (if difference x y = d then translateCoupling d x y else 0) =
          translateCoupling d x y := by
      by_cases h : difference x y = d <;> simp [h, translateCoupling]
    simp only [eq_self, ite_true, maskMass, drop, (translate_feasible d hd).2.1, total_row]
  · rw [ite_eq_right eq]
    unfold maskMass translateCoupling
    apply sum_eq_zero
    intro x _
    apply sum_eq_zero
    intro y _
    by_cases h : difference x y = e
    · simp [h, Ne.symm eq]
    · simp [h]

private def mask (i : Fin 4) : Profile :=
  if i = 3 then (true,true,true) else singletonMask (Fin.ofNat 3 i.val)

private theorem mask_odd (i : Fin 4) : odd (mask i) = true := by
  fin_cases i <;> decide

private theorem mask_injective : Function.Injective mask := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private noncomputable def mixture (c : Fin 4 → ℝ) (x y : Profile) : ℝ :=
  ∑ i, c i * translateCoupling (mask i) x y

private theorem mixture_feasible (c : Fin 4 → ℝ) (nn : ∀ i, 0 ≤ c i) (tot : ∑ i, c i = 1) :
    Feasible (mixture c) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
  · exact sum_nonneg fun i _ => mul_nonneg (nn i) ((translate_feasible _ (mask_odd i)).1 x y)
  · unfold mixture
    rw [sum_comm]
    simp_rw [← mul_sum, fun i => (translate_feasible (mask i) (mask_odd i)).2.1 x]
    rw [← sum_mul, tot, one_mul]
  · unfold mixture
    rw [sum_comm]
    simp_rw [← mul_sum, fun i => (translate_feasible (mask i) (mask_odd i)).2.2 y]
    rw [← sum_mul, tot, one_mul]

private theorem mixture_mask (c : Fin 4 → ℝ) (i : Fin 4) :
    maskMass (mixture c) (mask i) = c i := by
  unfold maskMass
  have move (x y : Profile) :
      (if difference x y = mask i then mixture c x y else 0) =
        ∑ j, c j * (if difference x y = mask i then translateCoupling (mask j) x y else 0) := by
    by_cases h : difference x y = mask i <;> simp [h, mixture]
  simp only [move]
  rw [sum_comm]
  conv_lhs =>
    enter [2, x]
    rw [sum_comm]
  rw [sum_comm]
  simp_rw [← mul_sum]
  conv_lhs =>
    enter [2, j, 2]
    rw [sum_comm]
  change (∑ j, c j * maskMass (translateCoupling (mask j)) (mask i)) = c i
  simp_rw [fun j => translate_mask (mask j) (mask i) (mask_odd j), mask_injective.eq_iff]
  simp [Finset.sum_ite_eq', mul_ite]

/-- Exact simultaneous common-flag masses for uniform opposite-parity rows. -/
theorem attainable_iff (a : Fin 3 → ℝ) :
    (∃ w : Profile → Profile → ℝ, Feasible w ∧ ∀ i, commonMass w i = a i) ↔
      (∀ i, a i ≤ a (i+1) + a (i+2)) ∧
        a 0 + a 1 + a 2 ≤ 1 := by
  constructor
  · rintro ⟨w, hw, masses⟩
    have read (i : Fin 3) :
        2 * a i = maskMass w (singletonMask (i + 1)) + maskMass w (singletonMask (i + 2)) := by
      rw [← masses, twice_common w hw, agreement_mass w hw]
    have read₀ := read 0
    have read₁ := read 1
    have read₂ := read 2
    change 2 * a 0 = maskMass w (singletonMask 1) + maskMass w (singletonMask 2) at read₀
    change 2 * a 1 = maskMass w (singletonMask 2) + maskMass w (singletonMask 0) at read₁
    change 2 * a 2 = maskMass w (singletonMask 0) + maskMass w (singletonMask 1) at read₂
    have n₀ := mask_nonneg w hw (singletonMask 0)
    have n₁ := mask_nonneg w hw (singletonMask 1)
    have n₂ := mask_nonneg w hw (singletonMask 2)
    have n₃ := mask_nonneg w hw (true,true,true)
    have total := masks_take_total w hw
    refine ⟨fun i => ?_, by linarith⟩
    · fin_cases i
      · change a 0 ≤ a 1 + a 2
        linarith
      · change a 1 ≤ a 2 + a 0
        linarith
      · change a 2 ≤ a 0 + a 1
        linarith
  · rintro ⟨triangle, total⟩
    let c (i : Fin 4) : ℝ :=
      if i = 0 then a 1 + a 2 - a 0
      else if i = 1 then a 2 + a 0 - a 1
      else if i = 2 then a 0 + a 1 - a 2
      else 1 - (a 0 + a 1 + a 2)
    have ctr₀ := triangle 0
    have ctr₁ := triangle 1
    have ctr₂ := triangle 2
    change a 0 ≤ a 1 + a 2 at ctr₀
    change a 1 ≤ a 2 + a 0 at ctr₁
    change a 2 ≤ a 0 + a 1 at ctr₂
    have nn (i : Fin 4) : 0 ≤ c i := by
      fin_cases i <;> norm_num [c] <;> linarith
    have ct : ∑ i, c i = 1 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      norm_num [c]
      linarith
    have hw := mixture_feasible c nn ct
    refine ⟨mixture c, hw, fun i => ?_⟩
    have read (j : Fin 3) :
        2 * commonMass (mixture c) j =
          maskMass (mixture c) (singletonMask (j+1)) + maskMass (mixture c) (singletonMask (j+2)) := by
      rw [twice_common _ hw, agreement_mass _ hw]
    have h0 := mixture_mask c 0
    have h1 := mixture_mask c 1
    have h2 := mixture_mask c 2
    change maskMass (mixture c) (singletonMask 0) = a 1 + a 2 - a 0 at h0
    change maskMass (mixture c) (singletonMask 1) = a 2 + a 0 - a 1 at h1
    change maskMass (mixture c) (singletonMask 2) = a 0 + a 1 - a 2 at h2
    fin_cases i
    · have h := read 0
      change 2 * commonMass (mixture c) 0 =
        maskMass (mixture c) (singletonMask 1) + maskMass (mixture c) (singletonMask 2) at h
      change commonMass (mixture c) 0 = a 0
      linarith
    · have h := read 1
      change 2 * commonMass (mixture c) 1 =
        maskMass (mixture c) (singletonMask 2) + maskMass (mixture c) (singletonMask 0) at h
      change commonMass (mixture c) 1 = a 1
      linarith
    · have h := read 2
      change 2 * commonMass (mixture c) 2 =
        maskMass (mixture c) (singletonMask 0) + maskMass (mixture c) (singletonMask 1) at h
      change commonMass (mixture c) 2 = a 2
      linarith

#print axioms attainable_iff

end D5.S3.ConceptDynamics.Attribution.ParityProfileRegion
