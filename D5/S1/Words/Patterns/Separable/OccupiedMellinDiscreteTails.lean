/- GID: D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteTails
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedMellinDiscreteTails
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SumIntegralComparisons]
   utility: none
   digest: Exact discrete origin and far tails of the occupation Mellin mesh. -/

import D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs
import Mathlib.Analysis.SumIntegralComparisons

/-! The two tails of the normalized Mellin mesh have explicit bounds at
integer cutoffs. The far comparison uses the decreasing power majorant. -/

open MeasureTheory
open scoped BigOperators

namespace D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails

open OccupiedMellinInterior OccupiedMellinCutoffs

private theorem origin_cutoff {β a : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 3 / 4) (ha : 0 ≤ a)
    (n K : ℕ) (hn : 0 < n) (hK : (K : ℝ) / n ≤ 1 / 2) :
    (∑ i ∈ Finset.range K, |sample β a ((i + 1 : ℕ) / (n : ℝ))|) / n ≤
      32 * ((K : ℝ) / n) ^ (3 / 2 : ℝ) := by
  let δ : ℝ := (K : ℝ) / n
  have hδ₀ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ 1 / 2 := hK
  rw [← one_div_mul_eq_div]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ i ∈ Finset.range K,
      |sample β a ((i+1 : ℕ) / (n : ℝ))| ≤ 32 * δ ^ (1 / 2 : ℝ) := by
    intro i hi
    have h₁ : (i+1 : ℕ) ≤ K := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hle : ((i+1 : ℕ) : ℝ) / n ≤ δ :=
      div_le_div_of_nonneg_right (by exact_mod_cast h₁) hn0.le
    have hpos : 0 < ((i+1 : ℕ) : ℝ) / n := div_pos (by positivity) hn0
    exact (mellin_cutoff_bounds.2.2.2.1 β a _ hβ₀ hβ₁ ha hpos (hle.trans hδ₁)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hpos.le hle (by norm_num)) (by norm_num))
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hnon : (0 : ℝ) ≤ 1/n := by positivity
  calc
    _ ≤ (1/(n:ℝ)) * ((K:ℝ) * (32*δ^(1 / 2:ℝ))) := mul_le_mul_of_nonneg_left hsum hnon
    _ = δ * (32 * δ ^ (1 / 2 : ℝ)) := by dsimp [δ]; ring
    _ = _ := by
      change δ * (32 * δ ^ (1 / 2 : ℝ)) = 32 * δ ^ (3 / 2 : ℝ)
      by_cases h : δ = 0
      · simp [h, Real.zero_rpow]
      · have hp : 0 < δ := lt_of_le_of_ne hδ₀ (Ne.symm h)
        have heq : δ * δ^(1 / 2:ℝ) = δ^(3 / 2:ℝ) := by
          rw [← show (1+(1 / 2:ℝ)) = 3 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one]
        linear_combination 32 * heq

private theorem far_scale {n M : ℝ} (hn : 0 < n) (hM : 0 ≤ M) :
    (n^(3 / 2:ℝ) * M^(-(1 / 2:ℝ)))/n = (M/n)^(-(1 / 2:ℝ)) := by
  rw [mul_comm, mul_div_assoc, Real.div_rpow hM hn.le, div_eq_mul_inv (M^(-(1 / 2:ℝ))),
    ← Real.rpow_neg hn.le, neg_neg]
  congr 1
  rw [div_eq_mul_inv, ← Real.rpow_neg_one n, ← Real.rpow_add hn]
  congr 1
  norm_num

private theorem far_cutoff {β a : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (n M : ℕ) (hn : 0 < n) (hcut : 2 ≤ (M : ℝ) / n) :
    Summable (fun i : ℕ => |sample β a ((M + i + 1 : ℕ) / (n : ℝ))|) ∧
      (∑' i : ℕ, |sample β a ((M + i + 1 : ℕ) / (n : ℝ))|) / n ≤
        4 * ((M : ℝ) / n) ^ (-(1 / 2 : ℝ)) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hM0 : 0 < (M : ℝ) :=
    (div_pos_iff_of_pos_right hn0).mp ((by norm_num : (0 : ℝ) < 2).trans_le hcut)
  let f : ℝ → ℝ := fun x => x ^ (-(3 / 2 : ℝ))
  let w : ℕ → ℝ := fun i => f (↑(M + i + 1 : ℕ))
  let g : ℕ → ℝ := fun i => |sample β a ((M + i + 1 : ℕ) / (n : ℝ))|
  have hanti : AntitoneOn f (Set.Ici (M : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hM0.trans_le hx) hxy (by norm_num)
  have hnon : ∀ x ∈ Set.Ioi (M : ℝ), 0 ≤ f x :=
    fun x hx => Real.rpow_nonneg (hM0.trans (Set.mem_Ioi.mp hx)).le _
  have hfi : IntegrableOn f (Set.Ioi (M : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hM0
  have hws : Summable w := by
    have hs := (summable_nat_add_iff (M + 1)).2
      (hanti.summable_of_integrableOn_Ioi hfi hnon)
    convert hs using 1
    funext i
    change f (↑(M + i + 1 : ℕ)) = f (↑(i + (M + 1) : ℕ))
    rw [Nat.add_comm M i, Nat.add_assoc]
  have hwb : ∑' i : ℕ, w i ≤ 2 * (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hi := hanti.tsum_comp_add_le_integral M hfi hnon
    change (∑' i : ℕ, f (↑(i + M + 1 : ℕ))) ≤ _ at hi
    have hIntegral : (∫ x in Set.Ioi (M : ℝ), f x) =
        2 * (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
      dsimp [f]
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3 / 2 : ℝ)) < -1) hM0,
        show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num]
      ring
    rw [hIntegral] at hi
    simpa only [w, Nat.add_comm M] using hi
  let c : ℝ := 2 * (n : ℝ) ^ (3 / 2 : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hterm (i : ℕ) : g i ≤ c * w i := by
    have hmi : (M : ℝ) ≤ (↑(M + i + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hcut' := hcut.trans (div_le_div_of_nonneg_right hmi hn0.le)
    have h := mellin_cutoff_bounds.2.2.2.2 β a _ hβ ha hcut'
    rw [Real.div_rpow (by positivity) hn0.le,
      div_eq_mul_inv ((↑(M + i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))),
      ← Real.rpow_neg hn0.le, neg_neg] at h
    dsimp [g, w, f, c]
    convert h using 1
    ring
  have hcs : Summable (fun i : ℕ => c * w i) := hws.mul_left c
  have hgs : Summable g := hcs.of_nonneg_of_le (fun _ => abs_nonneg _) hterm
  refine ⟨hgs, (div_le_div_of_nonneg_right (hgs.tsum_le_tsum hterm hcs) hn0.le).trans ?_⟩
  rw [tsum_mul_left]
  have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwb hc) hn0.le
  have heq : c * (2 * (M : ℝ) ^ (-(1 / 2 : ℝ))) / (n : ℝ) =
      4 * ((M : ℝ) / n) ^ (-(1 / 2 : ℝ)) := by
    dsimp [c]
    linear_combination 4 * (far_scale hn0 hM0.le)
  exact hb.trans_eq heq

/-- Discarding the mesh prefix through K or the tail strictly after M incurs
the displayed absolute error. Both parts use the same nonnegative shift. -/
theorem discrete_mellin_tail_bounds :
    (∀ (β a : ℝ) (n K : ℕ), 0 ≤ β → β ≤ 3 / 4 → 0 ≤ a → 0 < n →
      (K : ℝ) / n ≤ 1 / 2 →
      (∑ i ∈ Finset.range K, |sample β a ((i + 1 : ℕ) / (n : ℝ))|) / n ≤
        32 * ((K : ℝ) / n) ^ (3 / 2 : ℝ)) ∧
    (∀ (β a : ℝ) (n M : ℕ), 0 ≤ β → 0 ≤ a → 0 < n → 2 ≤ (M : ℝ) / n →
      Summable (fun i : ℕ => |sample β a ((M + i + 1 : ℕ) / (n : ℝ))|) ∧
        (∑' i : ℕ, |sample β a ((M + i + 1 : ℕ) / (n : ℝ))|) / n ≤
          4 * ((M : ℝ) / n) ^ (-(1 / 2 : ℝ))) :=
  ⟨fun _ _ n K hβ hb ha hn hK => origin_cutoff hβ hb ha n K hn hK,
    fun _ _ n M hβ ha hn hM => far_cutoff hβ ha n M hn hM⟩

end D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails
