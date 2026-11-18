/- GID: D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ExceptionCount/Counting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relaxed distinct-prime thresholds and dyadic counting transfer. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting
open OmegaTailUpper OmegaTail

/-- The sharp rate survives a sufficiently small fixed decrease of the
second-order distinct-prime threshold. -/
lemma relaxed_tail_upper {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ x : ℝ in atTop,
      (tailCount (-eta) x : ℝ) ≤ exp ((C0 + epsilon) * scale x) := by
  have hs := saddle_characterization.1.1
  have hs0 : 0 < saddle := zero_lt_one.trans hs
  let eta : ℝ := epsilon / (2 * saddle)
  have heta : 0 < eta := div_pos hepsilon (by positivity)
  refine ⟨eta, heta, ?_⟩
  have hrate : rate (-eta) saddle + epsilon / 2 = C0 + epsilon := by
    rw [saddle_characterization.2.2.2.2.1]
    dsimp [rate, eta]
    field_simp
    <;> ring
  simpa only [hrate] using
    upper_bound (-eta) (by linarith) hs (show 0 < epsilon / 2 by positivity)

/-- A predicate excluded below the distinct-prime threshold on every large
dyadic interval is covered by a fixed initial segment and the corresponding
distinct-prime tails. -/
lemma dyadic_cover_count (E : ℕ → Prop) [DecidablePred E]
    (N J : ℕ) (lambda : ℝ)
    (hlocal : ∀ j : ℕ, J < j → j ≤ Nat.clog 2 N →
      ∀ n : ℕ, (2 : ℝ) ^ j / 2 < n → (n : ℝ) ≤ (2 : ℝ) ^ j → E n →
        threshold lambda ((2 : ℝ) ^ j) <
          (ArithmeticFunction.cardDistinctFactors n : ℝ)) :
    ((Icc 1 N).filter E).card ≤ 2 ^ J +
      ∑ j ∈ Icc (J + 1) (Nat.clog 2 N), tailCount lambda ((2 : ℝ) ^ j) := by
  let T : ℕ → Finset ℕ := fun j =>
    (Icc 1 ⌊(2 : ℝ) ^ j⌋₊).filter (fun n =>
      threshold lambda ((2 : ℝ) ^ j) <
        (ArithmeticFunction.cardDistinctFactors n : ℝ))
  have hcover : (Icc 1 N).filter E ⊆
      Icc 1 (2 ^ J) ∪ (Icc (J + 1) (Nat.clog 2 N)).biUnion T := by
    intro n hn
    obtain ⟨hn, hE⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    by_cases hsmall : n ≤ 2 ^ J
    · exact mem_union_left _ (mem_Icc.mpr ⟨hn1, hsmall⟩)
    · have hJn : J < Nat.clog 2 n :=
        (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (lt_of_not_ge hsmall)
      have hjN : Nat.clog 2 n ≤ Nat.clog 2 N := Nat.clog_mono_right 2 hnN
      have hj0 : 0 < Nat.clog 2 n := lt_of_le_of_lt (Nat.zero_le J) hJn
      have hu : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 n := by
        exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) n
      have hl : (2 : ℝ) ^ Nat.clog 2 n / 2 < n := by
        have hp := Nat.pow_lt_of_lt_clog
          (show Nat.clog 2 n - 1 < Nat.clog 2 n by omega)
        have hp' : (2 : ℝ) ^ (Nat.clog 2 n - 1) < n := by exact_mod_cast hp
        have he : Nat.clog 2 n = Nat.clog 2 n - 1 + 1 := by omega
        rw [he, pow_succ]
        nlinarith
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨Nat.clog 2 n, mem_Icc.mpr ⟨by omega, hjN⟩, ?_⟩
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨hn1, ?_⟩, hlocal _ hJn hjN n hl hu hE⟩
      exact (Nat.le_floor_iff (by positivity)).mpr hu
  calc
    _ ≤ (Icc 1 (2 ^ J) ∪ (Icc (J + 1) (Nat.clog 2 N)).biUnion T).card :=
      card_le_card hcover
    _ ≤ (Icc 1 (2 ^ J)).card + ((Icc (J + 1) (Nat.clog 2 N)).biUnion T).card :=
      card_union_le _ _
    _ ≤ 2 ^ J + ∑ j ∈ Icc (J + 1) (Nat.clog 2 N), (T j).card := by
      simpa using Nat.add_le_add_left (card_biUnion_le (s := Icc (J + 1) (Nat.clog 2 N))
        (t := T)) (2 ^ J)
    _ = _ := rfl

end D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting
