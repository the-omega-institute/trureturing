/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/BinSquareTail
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/BinSquareTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summable symmetric power tails over frequency bins. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.MoebiusPrefixes

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open MeasureTheory Real Set
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

private theorem one_sided_tail (H : ℕ) (hH : 0 < H) {s : ℝ} (hs : s < -1) :
    (∑' n : ℕ, ((n + H + 1 : ℕ) : ℝ) ^ s) ≤
      (H : ℝ) ^ (s+1) / (-(s+1)) := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have anti : AntitoneOn (fun x : ℝ => x ^ s) (Ici (H : ℝ)) := by
    intro x hx y _ hxy
    exact rpow_le_rpow_of_nonpos (hH'.trans_le hx) hxy (by linarith)
  have h := AntitoneOn.tsum_comp_add_le_integral H anti
    (integrableOn_Ioi_rpow_of_lt hs hH')
    (fun x hx => rpow_nonneg (hH'.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt hs hH'] at h
  simpa only [div_neg, neg_div] using h

open Finset

/-- The square tail outside the symmetric interval of frequency bins. -/
theorem signed_bin_tail_rpow (H : ℕ) (hH : 0 < H) {s : ℝ} (hs : s < -1) :
    (∑' k : ℤ, if k.natAbs ≤ H then 0 else (|(k : ℝ)| + 1) ^ s) ≤
      2 * ((H : ℝ) ^ (s+1) / (-(s+1))) := by
  let f (k : ℤ) : ℝ := if k.natAbs ≤ H then 0 else (|(k : ℝ)| + 1) ^ s
  let e := Equiv.intEquivNatSumNat.symm
  let g (n : ℕ) : ℝ := if n ≤ H then 0 else ((n + 1 : ℕ) : ℝ) ^ s
  have hn : Summable (fun n : ℕ => (n : ℝ) ^ s) :=
    Real.summable_nat_rpow.mpr hs
  have hg : Summable g := Summable.of_nonneg_of_le (fun n => by
    dsimp [g]
    split <;> positivity) (fun n => by
    dsimp [g]
    split
    · positivity
    · exact le_rfl) ((summable_nat_add_iff 1).2 hn)
  have gh0 : g 0 = 0 := by simp [g]
  have epos (n : ℕ) : f (e (Sum.inl n)) = g n := by
    change f (n : ℤ) = _
    simp [f, g, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  have eneg (n : ℕ) : f (e (Sum.inr n)) = g (n + 1) := by
    change f (Int.negSucc n) = _
    have habs : |(Int.negSucc n : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
      rw [Int.cast_negSucc, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [f, g]
    rw [Int.natAbs_negSucc, Nat.succ_eq_add_one, habs, Nat.cast_add_one (n + 1)]
  have hs₁ : Summable ((f ∘ e) ∘ Sum.inl) := hg.congr (fun n => (epos n).symm)
  have hs₂ : Summable ((f ∘ e) ∘ Sum.inr) :=
    ((summable_nat_add_iff 1).2 hg).congr (fun n => (eneg n).symm)
  have hsplit := hg.sum_add_tsum_nat_add 1
  simp only [sum_range_one, gh0, zero_add] at hsplit
  have hmain := hg.sum_add_tsum_nat_add (H + 1)
  have hz : ∑ i ∈ range (H + 1), g i = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [g, Nat.lt_succ_iff.mp (mem_range.mp hi)]
  rw [hz, zero_add] at hmain
  have htail : (∑' i : ℕ, g (i + (H + 1))) ≤
      ∑' i : ℕ, ((i + H + 1 : ℕ) : ℝ) ^ s := by
    apply Summable.tsum_le_tsum _ ((summable_nat_add_iff (H + 1)).2 hg)
    · simpa only [Nat.add_assoc] using (summable_nat_add_iff (H + 1)).2 hn
    · intro i
      have hi : ¬i + (H + 1) ≤ H := by omega
      simp only [g, hi, ite_false]
      apply rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast (show i + H + 1 ≤ i + (H + 1) + 1 by omega)
      · linarith
  change ∑' k, f k ≤ _
  rw [← e.tsum_eq f]
  change ∑' k, (f ∘ e) k ≤ _
  rw [hs₁.tsum_sum hs₂]
  simp only [Function.comp_apply, tsum_congr epos, tsum_congr eneg, hsplit]
  rw [← hmain]
  linarith only [htail, one_sided_tail H hH hs]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
