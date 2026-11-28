/- GID: D5/S3/Fourier/Asymptotics/PlanarFourierTail
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/PlanarFourierTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sixth-power decay bounds the absolute tail of planar integer frequencies. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-! Absolute Fourier tails from counting square lattice shells. -/

compile_only_with_mathlib

namespace D5.S3.Fourier.Asymptotics.PlanarFourierTail

open Finset
open scoped BigOperators

private theorem inverseFifth_le_quarter_difference (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ 5 ≤ (1 / x ^ 4 - 1 / (x + 1) ^ 4) / 4 := by
  apply (div_le_div_iff₀ (by positivity : 0 < (x + 1) ^ 5) (by norm_num : (0 : ℝ) < 4)).2
  rw [div_sub_div _ _ (by positivity : x ^ 4 ≠ 0) (by positivity : (x + 1) ^ 4 ≠ 0)]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < x ^ 4 * (x + 1) ^ 4)).2
  have hpoly : 0 ≤ (x + 1) ^ 4 * (10 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1) := by
    positivity
  nlinarith only [hpoly]

private theorem inverseFifth_partial (J : ℝ) (hJ : 0 < J) (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / (J + (k : ℝ) + 1) ^ 5 ≤
      (1 / J ^ 4 - 1 / (J + (n : ℝ)) ^ 4) / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc]
      have hstep := inverseFifth_le_quarter_difference (J + (n : ℝ)) (by positivity)
      linarith only [ih, hstep]

private theorem inverseFifth_tail (J : ℝ) (hJ : 0 < J) (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / (J + (k : ℝ) + 1) ^ 5 ≤ 1 / (4 * J ^ 4) := by
  refine (inverseFifth_partial J hJ n).trans ?_
  have hend : (0 : ℝ) ≤ 1 / (J + (n : ℝ)) ^ 4 := by positivity
  rw [mul_comm, ← div_div]
  linarith only [hend]

/-- The maximum of the two absolute integer frequencies. -/
def modeRadius (m : ℤ × ℤ) : ℕ :=
  max m.1.natAbs m.2.natAbs

private def modeBox (n : ℕ) : Finset (ℤ × ℤ) :=
  Icc (-n : ℤ × ℤ) n

private theorem mem_modeBox {n : ℕ} {m : ℤ × ℤ} :
    m ∈ modeBox n ↔ modeRadius m ≤ n := by
  have hcoord (z : ℤ) : z ∈ Icc (-(n : ℤ)) n ↔ z.natAbs ≤ n := by
    rw [mem_Icc, ← abs_le, Int.abs_eq_natAbs, Int.ofNat_le]
  change m ∈ Icc (-(n : ℤ), -(n : ℤ)) ((n : ℤ), (n : ℤ)) ↔ _
  rw [Icc_prod_def, mem_product, hcoord, hcoord, modeRadius, max_le_iff]

private theorem modeBox_mono : Monotone modeBox :=
  fun _ _ h _ hm => mem_modeBox.mpr ((mem_modeBox.mp hm).trans h)

/-- A scaled sixth-power coefficient bound controls the absolute high-frequency tail. -/
theorem lattice_fourier_tail (s : Finset (ℤ × ℤ)) (a : ℤ × ℤ → ℂ) (J : ℕ) (ε K : ℝ)
    (hJ : 0 < J) (hε : 0 < ε) (hK : 0 ≤ K)
    (hcut : ∀ m ∈ s, J < modeRadius m)
    (hdecay : ∀ m ∈ s, ‖a m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 6) :
    ∑ m ∈ s, ‖a m‖ ≤ 2 * K / (ε ^ 4 * (J : ℝ) ^ 4) := by
  let weight (m : ℤ × ℤ) : ℝ := if m ∈ s then ‖a m‖ else 0
  have hweight_nonneg (m : ℤ × ℤ) : 0 ≤ weight m := by
    unfold weight
    split_ifs <;> positivity
  have hweight (m : ℤ × ℤ) : weight m ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 6 := by
    by_cases hm : m ∈ s
    · simpa [weight, hm] using hdecay m hm
    · simpa [weight, hm] using
        (show 0 ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 6 by positivity)
  have hsum : ∑ m ∈ s, ‖a m‖ = ∑ m ∈ s, weight m := by
    exact sum_congr rfl (fun m hm => by simp [weight, hm])
  rw [hsum]
  let n := s.sup modeRadius
  let b : ℕ → Finset (ℤ × ℤ) := fun k => modeBox (J + k)
  have hb : Monotone b := fun _ _ h => modeBox_mono (Nat.add_le_add_left h J)
  have hs : s ⊆ b n \ b 0 := by
    intro m hm
    change m ∈ modeBox (J + n) \ modeBox J
    rw [mem_sdiff, mem_modeBox, mem_modeBox]
    exact ⟨(Finset.le_sup hm).trans (Nat.le_add_left n J), not_le.mpr (hcut m hm)⟩
  have hsplit : ∑ m ∈ b n \ b 0, weight m =
      ∑ k ∈ range n, ∑ m ∈ b (k + 1) \ b k, weight m := by
    have h₁ := sum_eq_sum_range_sdiff b hb (fun m => weight m) n
    have h₂ := sum_sdiff (f := fun m => weight m) (hb (Nat.zero_le n))
    linarith only [h₁, h₂]
  have hrow (k : ℕ) :
      ∑ m ∈ b (k + 1) \ b k, weight m ≤
        (8 * K / ε ^ 4) * (1 / ((J : ℝ) + (k : ℝ) + 1) ^ 5) := by
    let p : ℝ := (J : ℝ) + (k : ℝ) + 1
    have hp : 0 < p := by dsimp [p]; positivity
    have hshell : b (k + 1) \ b k = (box (J + k + 1) : Finset (ℤ × ℤ)) := by
      rw [box_succ_eq_sdiff]
      simp only [b, modeBox, Nat.succ_eq_add_one, Nat.add_assoc]
    have hcard : (b (k + 1) \ b k).card = 8 * (J + k + 1) := by
      rw [hshell, Int.card_box (Nat.succ_ne_zero (J + k))]
    have hbnd (m : ℤ × ℤ) (hm : m ∈ b (k + 1) \ b k) :
        weight m ≤ K / (ε ^ 4 * p ^ 6) := by
      have hr : modeRadius m = J + k + 1 := Int.mem_box.mp (hshell ▸ hm)
      have hcast : (modeRadius m : ℝ) = p := by
        rw [hr]
        simp [p]
      calc
        weight m ≤ K * ε ^ 2 / (1 + ε * p) ^ 6 := hcast ▸ hweight m
        _ ≤ K * ε ^ 2 / (ε * p) ^ 6 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          gcongr
          linarith
        _ = K / (ε ^ 4 * p ^ 6) := by field_simp
    calc
      _ ≤ ∑ _m ∈ b (k + 1) \ b k, K / (ε ^ 4 * p ^ 6) := sum_le_sum hbnd
      _ = _ := by
        rw [sum_const, nsmul_eq_mul, hcard]
        push_cast
        change 8 * p * (K / (ε ^ 4 * p ^ 6)) = (8 * K / ε ^ 4) * (1 / p ^ 5)
        field_simp
  calc
    _ ≤ ∑ m ∈ b n \ b 0, weight m := sum_le_sum_of_subset_of_nonneg hs
      (fun m _ _ => hweight_nonneg m)
    _ = ∑ k ∈ range n, ∑ m ∈ b (k + 1) \ b k, weight m := hsplit
    _ ≤ ∑ k ∈ range n, (8 * K / ε ^ 4) * (1 / ((J : ℝ) + (k : ℝ) + 1) ^ 5) :=
      sum_le_sum (fun k _ => hrow k)
    _ = (8 * K / ε ^ 4) * ∑ k ∈ range n, 1 / ((J : ℝ) + (k : ℝ) + 1) ^ 5 :=
      (mul_sum _ _ _).symm
    _ ≤ (8 * K / ε ^ 4) * (1 / (4 * (J : ℝ) ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact inverseFifth_tail J (by exact_mod_cast hJ) n
    _ = _ := by field_simp; ring

end D5.S3.Fourier.Asymptotics.PlanarFourierTail
