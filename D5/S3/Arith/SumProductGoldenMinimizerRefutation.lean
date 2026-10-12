/- GID: D5/S3/Arith/SumProductGoldenMinimizerRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/SumProductGoldenMinimizerRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/SumProductGoldenMinimizerRefutation.claim; result=D5/S3/Arith/SumProductGoldenMinimizerRefutation.result; claim=D5/S3/Arith/SumProductGoldenMinimizerRefutation.claim
   digest: The plastic-number seven-point set has at most twenty-two sums and at most seventeen products, while the golden seven-point set has at least twenty-four sums. -/

import D5.S3.Arith.SumProductSevenPointCell
import Mathlib.Analysis.Polynomial.Order
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Pointwise
namespace D5.S3.Arith.SumProductGoldenMinimizerRefutation
noncomputable section

def goldenSet (n : ℕ) : Finset ℝ :=
  (Finset.Icc 1 n).image (fun i => Real.goldenRatio ^ i)

def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ A : Finset ℝ,
    (∀ a ∈ A, 0 < a) → A.card = n →
      (A * A).card ≤ 3 * n - 4 →
        (goldenSet n + goldenSet n).card ≤ (A + A).card

private def E : Finset ℕ := {0, 3, 5, 6, 7, 8, 9}
private def A (r : ℝ) : Finset ℝ := E.image (fun e => r ^ e)
private def P (r : ℝ) : Finset ℝ :=
  (E + E).image (fun e => r ^ e)

private abbrev V := ℤ × ℤ × ℤ
private def ev (r : ℝ) (v : V) : ℝ := v.1 + v.2.1 * r + v.2.2 * r^2
private def D : Finset V :=
  {(1, 0, 0), (1, 1, 0), (1, 1, 1), (1, 2, 1),
   (1, 2, 2), (2, 3, 2), (2, 4, 3)}
private def C : Finset V := D + D

private theorem plastic_root : ∃ r : ℝ, 1 < r ∧ r < 2 ∧ r ^ 3 = r + 1 := by
  let f : ℝ → ℝ := fun x => x ^ 3 - x - 1
  have hcont : Continuous f := by fun_prop
  have hz : (0 : ℝ) ∈ Set.Icc (f 1) (f 2) := by norm_num [f]
  obtain ⟨r, hr, hfr⟩ :=
    ((intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num) hcont.continuousOn) hz)
  refine ⟨r, ?_, ?_, ?_⟩
  · have : r ≠ 1 := by intro h; subst h; norm_num [f] at hfr
    exact lt_of_le_of_ne hr.1 (Ne.symm this)
  · have : r ≠ 2 := by intro h; subst h; norm_num [f] at hfr
    exact lt_of_le_of_ne hr.2 this
  · dsimp [f] at hfr
    linarith

private theorem A_card (r : ℝ) (hr : 1 < r) : (A r).card = 7 := by
  classical
  apply Finset.card_image_of_injective
  intro i j h
  apply (pow_right_strictMono₀ hr).injective
  exact h

private theorem A_pos (r : ℝ) (hr : 1 < r) : ∀ a ∈ A r, 0 < a := by
  classical
  intro a ha
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  exact pow_pos (lt_trans zero_lt_one hr) _

private theorem product_subset (r : ℝ) (hr : 1 < r) : A r * A r ⊆ P r := by
  classical
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  refine Finset.mem_image.mpr ⟨i + j, ?_, ?_⟩
  · exact Finset.mem_add.mpr ⟨i, hi, j, hj, rfl⟩
  · rw [pow_add]

private theorem product_card (r : ℝ) (hr : 1 < r) : (A r * A r).card ≤ 17 := by
  have hsub := Finset.card_le_card (product_subset r hr)
  have hp : (P r).card ≤ (E + E).card := Finset.card_image_le
  have he : (E + E).card = 16 := by decide
  rw [he] at hp
  omega

private theorem power_coeff (r : ℝ) (hroot : r ^ 3 = r + 1) :
    r ^ 0 = ev r (1,0,0) ∧ r ^ 3 = ev r (1,1,0) ∧
    r ^ 5 = ev r (1,1,1) ∧ r ^ 6 = ev r (1,2,1) ∧
    r ^ 7 = ev r (1,2,2) ∧ r ^ 8 = ev r (2,3,2) ∧
    r ^ 9 = ev r (2,4,3) := by
  have hp4 : r ^ 4 = r ^ 2 + r := by
    calc r ^ 4 = r * r ^ 3 := by ring
      _ = r ^ 2 + r := by rw [hroot]; ring
  have hp5 : r ^ 5 = r ^ 2 + r + 1 := by
    calc r ^ 5 = r ^ 2 * r ^ 3 := by ring
      _ = r ^ 2 + r + 1 := by linear_combination (r^2 + 1) * hroot
  have hp6 : r ^ 6 = r ^ 2 + 2*r + 1 := by
    calc r ^ 6 = r ^ 3 * r ^ 3 := by ring
      _ = r ^ 2 + 2*r + 1 := by linear_combination (r^3 + r + 1) * hroot
  have hp7 : r ^ 7 = 2*r^2 + 2*r + 1 := by
    calc r ^ 7 = r ^ 4 * r ^ 3 := by ring
      _ = 2*r^2 + 2*r + 1 := by linear_combination (r^4 + r^2 + r + 1) * hroot
  have hp8 : r ^ 8 = 2*r^2 + 3*r + 2 := by
    calc r ^ 8 = r ^ 5 * r ^ 3 := by ring
      _ = 2*r^2 + 3*r + 2 := by linear_combination (r^5 + r^3 + r^2 + r + 2) * hroot
  have hp9 : r ^ 9 = 3*r^2 + 4*r + 2 := by
    calc r ^ 9 = r ^ 6 * r ^ 3 := by ring
      _ = 3*r^2 + 4*r + 2 := by linear_combination (r^6 + r^4 + r^3 + r^2 + 2*r + 2) * hroot
  simp only [ev, hp5, hp6, hp7, hp8, hp9, hroot, pow_zero, Int.cast_ofNat]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · constructor <;> ring

private theorem sum_card (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1) :
    (A r + A r).card ≤ 22 := by
  classical
  have hpow := power_coeff r hroot
  have hA : A r = D.image (ev r) := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [D, hpow, ev, hroot]
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      simp only [D, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [A, E, hpow, ev, hroot]
  rw [hA]
  have hs : D.image (ev r) + D.image (ev r) ⊆ C.image (ev r) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨u + v,
      Finset.mem_add.mpr ⟨u, hu, v, hv, rfl⟩, ?_⟩
    dsimp [ev]
    push_cast
    ring
  calc
    (D.image (ev r) + D.image (ev r)).card ≤ (C.image (ev r)).card :=
      Finset.card_le_card hs
    _ ≤ C.card := Finset.card_image_le
    _ = 22 := by decide

theorem result : ¬ claim := by
  obtain ⟨r, hr1, hr2, hroot⟩ := plastic_root
  intro hclaim
  have hApos := A_pos r hr1
  have hAcard := A_card r hr1
  have hprod := product_card r hr1
  have hsum := sum_card r hr1 hroot
  have hgold : 24 ≤ (goldenSet 7 + goldenSet 7).card := by
    have hi : Finset.Icc 1 7 = (Finset.range 7).image Nat.succ := by decide
    rw [goldenSet, hi, Finset.image_image]
    have hfun : (fun i : ℕ => Real.goldenRatio ^ i) ∘ Nat.succ =
        (fun i : ℕ => Real.goldenRatio * Real.goldenRatio ^ i) := by
      funext i
      simp [Function.comp_apply, pow_succ, mul_comm]
    rw [hfun]
    simpa [mul_comm] using
      (D5.S3.Arith.SumProductSevenPointCell.geometric_sum_card_lower_bound Real.goldenRatio Real.goldenRatio
        Real.goldenRatio_pos Real.one_lt_goldenRatio)
  have hc := hclaim 7 (by norm_num) (A r) hApos hAcard hprod
  omega

end
end D5.S3.Arith.SumProductGoldenMinimizerRefutation
