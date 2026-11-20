/- GID: D5/S3/Combinatorics/SubsetSpectrum/DigitPeriodCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/DigitPeriodCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common multiple of short digit periods bounds integer levels on arbitrary weighted grids. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Integer-level capacity from a missing short period in one weight. -/

namespace D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity

open Finset

set_option autoImplicit false

private theorem short_period_missing {r B M : ℕ} (w : Fin r → ℝ)
    (common : ∀ d : ℕ, 0 < d → d < B → d ∣ M)
    (nonintegral : ¬ ∃ z : ℤ, (M : ℝ) * (∑ j, w j) = z) :
    ∃ j, ∀ d : ℕ, 0 < d → d < B → ¬ ∃ z : ℤ, (d : ℝ) * w j = z := by
  classical
  by_contra h
  push Not at h
  choose d hpos hlt z hz using h
  have ints (j : Fin r) : ∃ c : ℤ, (M : ℝ) * w j = c := by
    obtain ⟨n, eq⟩ := common (d j) (hpos j) (hlt j)
    refine ⟨(n : ℤ) * z j, ?_⟩
    rw [eq, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← hz]
    ring
  choose c hc using ints
  apply nonintegral
  exact ⟨∑ j, c j, by rw [Finset.mul_sum, Int.cast_sum]; exact Finset.sum_congr rfl fun j _ => hc j⟩

/-- A nonintegral multiple of the total weight forces a gap between consecutive admissible
digits in at least one coordinate. -/
theorem integral_range_le_period_blocks {r k n B M : ℕ} (positive : 0 < B)
    (w : Fin (r + 1) → ℝ)
    (common : ∀ d : ℕ, 0 < d → d < B → d ∣ M)
    (nonintegral : ¬ ∃ z : ℤ, (M : ℝ) * (∑ j, w j) = z)
    (level : Fin n → ℤ) (distinct : Function.Injective level)
    (cover : ∀ x : Fin n, ∃ d : Fin (r + 1) → Fin (k + 1),
      (∑ j, ((d j).val : ℝ) * w j) = (level x : ℝ)) :
    n ≤ (k / B + 1) * (k + 1) ^ r := by
  classical
  obtain ⟨i, gap⟩ := short_period_missing w common nonintegral
  choose digits mass using cover
  let code (x : Fin n) : Fin (k / B + 1) × (Fin r → Fin (k + 1)) :=
    (⟨(digits x i).val / B, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ (digits x i).isLt))⟩,
      i.removeNth (digits x))
  have identify (x y : Fin n) (q : (digits x i).val / B = (digits y i).val / B)
      (same : i.removeNth (digits x) = i.removeNth (digits y))
      (ord : (digits x i).val ≤ (digits y i).val) :
      (digits x i).val = (digits y i).val := by
    let u := (digits x i).val
    let v := (digits y i).val
    have qeq : u / B = v / B := q
    change u ≤ v at ord
    change u = v
    by_contra ne
    have udec := Nat.mod_add_div u B
    have vdec := Nat.mod_add_div v B
    rw [qeq] at udec
    have ru := Nat.mod_lt u positive
    have rv := Nat.mod_lt v positive
    have gap_lt : v - u < B := by omega
    have gap_pos : 0 < v - u := by omega
    have hx := mass x
    have hy := mass y
    rw [Fin.sum_univ_succAbove _ i] at hx hy
    have rest :
        (∑ j : Fin r, ((digits x (i.succAbove j)).val : ℝ) * w (i.succAbove j)) =
          ∑ j : Fin r, ((digits y (i.succAbove j)).val : ℝ) * w (i.succAbove j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show digits x (i.succAbove j) = digits y (i.succAbove j) from congrFun same j]
    rw [rest] at hx
    apply gap (v - u) gap_pos gap_lt
    refine ⟨level y - level x, ?_⟩
    rw [Int.cast_sub, Nat.cast_sub ord]
    change ((v : ℝ) - (u : ℝ)) * w i = (level y : ℝ) - level x
    linarith only [hx, hy]
  have inj : Function.Injective code := by
    intro x y h
    have q := congrArg (fun p : Fin (k / B + 1) × (Fin r → Fin (k + 1)) => p.1.val) h
    have tail := congrArg Prod.snd h
    have head : (digits x i).val = (digits y i).val := by
      rcases le_total (digits x i).val (digits y i).val with le | le
      · exact identify x y q tail le
      · exact (identify y x q.symm tail.symm le).symm
    have same : digits x = digits y := by
      funext j
      revert j
      rw [Fin.forall_iff_succAbove i]
      exact ⟨Fin.ext head, congrFun tail⟩
    apply distinct
    exact_mod_cast ((mass x).symm.trans (same ▸ mass y))
  simpa only [Fintype.card_fin, Fintype.card_fun, Fintype.card_prod] using
    Fintype.card_le_of_injective code inj


end D5.S3.Combinatorics.SubsetSpectrum.DigitPeriodCapacity
