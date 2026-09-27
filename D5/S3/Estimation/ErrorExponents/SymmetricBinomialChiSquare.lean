/- GID: D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact symmetric-binomial chi-square defect and root-fidelity bound. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic
import D5.S3.TotalVariation.Hellinger

open scoped BigOperators

namespace D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare

open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger

noncomputable def p_z (B : ℕ) (z : ℝ) (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (B.choose k : ℝ) *
    (((1 + z) / 2) ^ k * ((1 - z) / 2) ^ (B - k) +
      ((1 - z) / 2) ^ k * ((1 + z) / 2) ^ (B - k))

noncomputable def p_0 (B : ℕ) (k : ℕ) : ℝ :=
  (B.choose k : ℝ) / (2 : ℝ) ^ B

noncomputable def chiSquare (B : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (B + 1), (p_z B z k) ^ 2 / p_0 B k - 1

theorem symmetric_binomial_chi_square
    (B : ℕ) (z : ℝ) (hz : |z| ≤ 1) :
    (∀ k ∈ Finset.range (B + 1), 0 ≤ p_z B z k) ∧
    (∑ k ∈ Finset.range (B + 1), p_z B z k) = 1 ∧
    (∀ k ≤ B, p_z B z k / p_0 B k =
      ((1 + z) ^ k * (1 - z) ^ (B - k) +
        (1 - z) ^ k * (1 + z) ^ (B - k)) / 2) ∧
    chiSquare B z = ((1 + z ^ 2) ^ B + (1 - z ^ 2) ^ B) / 2 - 1 ∧
      chiSquare B z = ∑ j ∈ Finset.Icc 1 (B / 2), (B.choose (2 * j) : ℝ) * z ^ (4 * j) ∧
    chiSquare B z ≤ Real.cosh (B * z ^ 2) - 1 ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → (B : ℝ) * δ ≤ 1 →
      z ^ 2 = 2 * δ - δ ^ 2 → chiSquare B z ≤ 3 * ((B : ℝ) * δ) ^ 2) ∧
    (|z| < 1 →
      (∀ k ∈ Finset.range (B + 1), 0 < p_z B z k) ∧
      0 < bhattacharyya
        (fun k : Fin (B + 1) => p_0 B k)
        (fun k : Fin (B + 1) => p_z B z k)) ∧
    1 - bhattacharyya
      (fun k : Fin (B + 1) => p_0 B k)
      (fun k : Fin (B + 1) => p_z B z k) ^ 2 ≤ chiSquare B z := by
  classical
  have ha : 0 ≤ (1 + z) / 2 := by linarith [(abs_le.mp hz).1]
  have hb : 0 ≤ (1 - z) / 2 := by linarith [(abs_le.mp hz).2]
  have hpz_nonneg : ∀ k ∈ Finset.range (B + 1), 0 ≤ p_z B z k := by
    intro k hk
    dsimp [p_z]
    positivity
  have hpz_sum : (∑ k ∈ Finset.range (B + 1), p_z B z k) = 1 := by
    dsimp [p_z]
    have h₁ := add_pow ((1 + z) / 2) ((1 - z) / 2) B
    have h₂ := add_pow ((1 - z) / 2) ((1 + z) / 2) B
    rw [show ((1 + z) / 2 + (1 - z) / 2) = 1 by ring] at h₁
    rw [show ((1 - z) / 2 + (1 + z) / 2) = 1 by ring] at h₂
    simp_rw [mul_add]
    calc
      (∑ x ∈ Finset.range (B + 1), (
          (1 / 2 : ℝ) * (B.choose x : ℝ) *
            (((1 + z) / 2) ^ x * ((1 - z) / 2) ^ (B - x)) +
          (1 / 2 : ℝ) * (B.choose x : ℝ) *
            (((1 - z) / 2) ^ x * ((1 + z) / 2) ^ (B - x)))) =
          (1 / 2 : ℝ) *
            (∑ x ∈ Finset.range (B + 1),
              ((1 + z) / 2) ^ x * ((1 - z) / 2) ^ (B - x) *
                (B.choose x : ℝ)) +
            (1 / 2 : ℝ) *
            (∑ x ∈ Finset.range (B + 1),
              ((1 - z) / 2) ^ x * ((1 + z) / 2) ^ (B - x) *
                (B.choose x : ℝ)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
              apply congrArg₂ (· + ·) <;>
                apply Finset.sum_congr rfl <;> intro x hx <;> ring
      _ = 1 := by rw [← h₁, ← h₂]; norm_num
  have hp0_sum : (∑ k ∈ Finset.range (B + 1), p_0 B k) = 1 := by
    dsimp [p_0]
    have h := add_pow (1 : ℝ) 1 B
    norm_num [one_pow] at h
    calc
      ∑ x ∈ Finset.range (B + 1), (B.choose x : ℝ) / (2 : ℝ) ^ B =
          (∑ x ∈ Finset.range (B + 1), (B.choose x : ℝ)) / (2 : ℝ) ^ B := by
            rw [Finset.sum_div]
      _ = 1 := by
        rw [← h]
        norm_num
  let L : ℕ → ℝ := fun k => (1 / 2 : ℝ) *
    ((1 + z) ^ k * (1 - z) ^ (B - k) +
      (1 - z) ^ k * (1 + z) ^ (B - k))
  let A : ℕ → ℝ := fun k => (1 + z) ^ k * (1 - z) ^ (B - k)
  let C : ℕ → ℝ := fun k => (1 - z) ^ k * (1 + z) ^ (B - k)
  have hp0_pos (k : ℕ) (hk : k ∈ Finset.range (B + 1)) : 0 < p_0 B k := by
    have hkB : k ≤ B := by simpa [Finset.mem_range] using hk
    dsimp [p_0]
    exact div_pos (by exact_mod_cast Nat.choose_pos hkB) (pow_pos (by norm_num) _)
  have hpz_likelihood (k : ℕ) (hk : k ∈ Finset.range (B + 1)) :
      p_z B z k = p_0 B k * L k := by
    have hkB : k ≤ B := by simpa [Finset.mem_range] using hk
    have hpow : (2 : ℝ) ^ k * (2 : ℝ) ^ (B - k) = (2 : ℝ) ^ B := by
      rw [← pow_add, Nat.add_sub_of_le hkB]
    dsimp [p_z, p_0, L]
    rw [div_pow, div_pow, div_pow, div_pow]
    field_simp [hpow]
    rw [← hpow]
    ring
  have hlikelihood_ratio (k : ℕ) (hk : k ≤ B) :
      p_z B z k / p_0 B k =
        ((1 + z) ^ k * (1 - z) ^ (B - k) +
          (1 - z) ^ k * (1 + z) ^ (B - k)) / 2 := by
    have hkrange : k ∈ Finset.range (B + 1) := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    rw [hpz_likelihood k hkrange]
    field_simp [(hp0_pos k hkrange).ne']
    dsimp [L]
    ring
  have hsecond :
      (∑ k ∈ Finset.range (B + 1), p_0 B k * L k ^ 2) =
        ((1 + z ^ 2) ^ B + (1 - z ^ 2) ^ B) / 2 := by
    have hAA :
        (∑ k ∈ Finset.range (B + 1), p_0 B k * A k ^ 2) =
          (1 + z ^ 2) ^ B := by
      have h := add_pow (((1 + z) ^ 2) / 2) (((1 - z) ^ 2) / 2) B
      rw [show (1 + z) ^ 2 / 2 + (1 - z) ^ 2 / 2 = 1 + z ^ 2 by ring] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro k hk
      have hkB : k ≤ B := by simpa [Finset.mem_range] using hk
      have hpow : (2 : ℝ) ^ k * (2 : ℝ) ^ (B - k) = (2 : ℝ) ^ B := by
        rw [← pow_add, Nat.add_sub_of_le hkB]
      dsimp [p_0, A]
      rw [div_pow, div_pow]
      field_simp [hpow]
      rw [← hpow]
      simp only [pow_two, mul_pow]
      ring
    have hCC :
        (∑ k ∈ Finset.range (B + 1), p_0 B k * C k ^ 2) =
          (1 + z ^ 2) ^ B := by
      have h := add_pow (((1 - z) ^ 2) / 2) (((1 + z) ^ 2) / 2) B
      rw [show (1 - z) ^ 2 / 2 + (1 + z) ^ 2 / 2 = 1 + z ^ 2 by ring] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro k hk
      have hkB : k ≤ B := by simpa [Finset.mem_range] using hk
      have hpow : (2 : ℝ) ^ k * (2 : ℝ) ^ (B - k) = (2 : ℝ) ^ B := by
        rw [← pow_add, Nat.add_sub_of_le hkB]
      dsimp [p_0, C]
      rw [div_pow, div_pow]
      field_simp [hpow]
      rw [← hpow]
      simp only [pow_two, mul_pow]
      ring
    have hAC (k : ℕ) (hk : k ∈ Finset.range (B + 1)) :
        A k * C k = (1 - z ^ 2) ^ B := by
      have hkB : k ≤ B := by simpa [Finset.mem_range] using hk
      dsimp [A, C]
      rw [show (1 - z ^ 2) = (1 + z) * (1 - z) by ring, mul_pow]
      rw [show (1 + z) ^ k * (1 - z) ^ (B - k) *
          ((1 - z) ^ k * (1 + z) ^ (B - k)) =
          ((1 + z) ^ k * (1 + z) ^ (B - k)) *
            ((1 - z) ^ k * (1 - z) ^ (B - k)) by ring]
      rw [← pow_add, ← pow_add, Nat.add_sub_of_le hkB]
    have hcross :
        (∑ k ∈ Finset.range (B + 1), p_0 B k * (A k * C k)) =
          (1 - z ^ 2) ^ B := by
      calc
        (∑ k ∈ Finset.range (B + 1), p_0 B k * (A k * C k)) =
            ∑ k ∈ Finset.range (B + 1), p_0 B k * (1 - z ^ 2) ^ B := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hAC k hk]
        _ = (∑ k ∈ Finset.range (B + 1), p_0 B k) * (1 - z ^ 2) ^ B := by
              rw [Finset.sum_mul]
        _ = (1 - z ^ 2) ^ B := by rw [hp0_sum, one_mul]
    calc
      (∑ k ∈ Finset.range (B + 1), p_0 B k * L k ^ 2) =
          ∑ k ∈ Finset.range (B + 1), (1 / 4 : ℝ) *
            (p_0 B k * A k ^ 2 + p_0 B k * C k ^ 2 +
              2 * (p_0 B k * (A k * C k))) := by
                apply Finset.sum_congr rfl
                intro k hk
                dsimp [L, A, C]
                ring
      _ = (1 / 4 : ℝ) *
            (∑ k ∈ Finset.range (B + 1), p_0 B k * A k ^ 2) +
          (1 / 4 : ℝ) *
            (∑ k ∈ Finset.range (B + 1), p_0 B k * C k ^ 2) +
          (1 / 2 : ℝ) *
            (∑ k ∈ Finset.range (B + 1), p_0 B k * (A k * C k)) := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
                ← Finset.mul_sum]
              ring
      _ = ((1 + z ^ 2) ^ B + (1 - z ^ 2) ^ B) / 2 := by
            rw [hAA, hCC, hcross]
            ring
  have hchi_exact :
      chiSquare B z = ((1 + z ^ 2) ^ B + (1 - z ^ 2) ^ B) / 2 - 1 := by
    rw [chiSquare]
    congr 1
    calc
      (∑ k ∈ Finset.range (B + 1), p_z B z k ^ 2 / p_0 B k) =
          ∑ k ∈ Finset.range (B + 1), p_0 B k * L k ^ 2 := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hpz_likelihood k hk]
            field_simp [(ne_of_gt (hp0_pos k hk))]
      _ = _ := hsecond
  have heven_expansion :
      ((1 + z ^ 2) ^ B + (1 - z ^ 2) ^ B) / 2 - 1 =
        ∑ j ∈ Finset.Icc 1 (B / 2), (B.choose (2 * j) : ℝ) * z ^ (4 * j) := by
    let x : ℝ := z ^ 2
    have hplus := add_pow x 1 B
    have hminus := add_pow (-x) 1 B
    rw [show x + 1 = 1 + x by ring] at hplus
    rw [show -x + 1 = 1 - x by ring] at hminus
    simp only [one_pow, mul_one] at hplus hminus
    have havg :
        ((1 + x) ^ B + (1 - x) ^ B) / 2 =
          ∑ k ∈ Finset.range (B + 1),
            if Even k then (B.choose k : ℝ) * x ^ k else 0 := by
      rw [hplus, hminus, ← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rcases k.even_or_odd with heven | hodd
      · rw [if_pos heven, heven.neg_pow]
        ring
      · rw [if_neg (Nat.not_even_iff_odd.mpr hodd), hodd.neg_pow]
        ring
    have hreindex :
        (∑ j ∈ Finset.Icc 0 (B / 2), (B.choose (2 * j) : ℝ) * x ^ (2 * j)) =
          ∑ k ∈ (Finset.range (B + 1)).filter Even,
            (B.choose k : ℝ) * x ^ k := by
      apply Finset.sum_bij (fun j _ => 2 * j)
      · intro j hj
        simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hj ⊢
        constructor
        · omega
        · exact ⟨j, by omega⟩
      · intro j hj l hl heq
        omega
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        rcases hk.2 with ⟨j, hj⟩
        refine ⟨j, ?_, by omega⟩
        simp only [Finset.mem_Icc]
        omega
      · intro j hj
        rfl
    have hzero_split :
        (∑ j ∈ Finset.Icc 0 (B / 2), (B.choose (2 * j) : ℝ) * x ^ (2 * j)) =
          1 + ∑ j ∈ Finset.Icc 1 (B / 2),
            (B.choose (2 * j) : ℝ) * x ^ (2 * j) := by
      have hsets : Finset.Ioc 0 (B / 2) = Finset.Icc 1 (B / 2) := by
        rfl
      rw [Finset.Icc_eq_cons_Ioc (by omega : 0 ≤ B / 2), Finset.sum_cons]
      rw [hsets]
      norm_num
    rw [show z ^ 2 = x by rfl]
    rw [havg, ← Finset.sum_filter, ← hreindex, hzero_split]
    dsimp [x]
    simp_rw [← pow_mul]
    have hcancel : (1 : ℝ) +
        (∑ j ∈ Finset.Icc 1 (B / 2),
          (B.choose (2 * j) : ℝ) * z ^ (2 * (2 * j))) - 1 =
        ∑ j ∈ Finset.Icc 1 (B / 2),
          (B.choose (2 * j) : ℝ) * z ^ (2 * (2 * j)) := by ring
    rw [hcancel]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hchi_even :
      chiSquare B z =
        ∑ j ∈ Finset.Icc 1 (B / 2), (B.choose (2 * j) : ℝ) * z ^ (4 * j) :=
    hchi_exact.trans heven_expansion
  let u : ℝ := (B : ℝ) * z ^ 2
  have hterm (j : ℕ) :
      (B.choose (2 * j) : ℝ) * z ^ (4 * j) ≤
        u ^ (2 * j) / (2 * j).factorial := by
    calc
      (B.choose (2 * j) : ℝ) * z ^ (4 * j) ≤
          ((B : ℝ) ^ (2 * j) / (2 * j).factorial) * z ^ (4 * j) :=
        mul_le_mul_of_nonneg_right
          (Nat.choose_le_pow_div (α := ℝ) (2 * j) B)
          (Even.pow_nonneg ⟨2 * j, by omega⟩ z)
      _ = u ^ (2 * j) / (2 * j).factorial := by
        dsimp [u]
        rw [mul_pow]
        simp only [← pow_mul]
        ring
  have hfinite_series :
      (∑ j ∈ Finset.Icc 1 (B / 2), (B.choose (2 * j) : ℝ) * z ^ (4 * j)) ≤
        ∑ j ∈ Finset.Icc 1 (B / 2), u ^ (2 * j) / (2 * j).factorial := by
    exact Finset.sum_le_sum fun j _ => hterm j
  have hseries_tail :
      (∑ j ∈ Finset.Icc 1 (B / 2), u ^ (2 * j) / (2 * j).factorial) ≤
        Real.cosh u - 1 := by
    have hsummable := (Real.hasSum_cosh u).summable
    have hpartial :
        (∑ j ∈ insert 0 (Finset.Icc 1 (B / 2)),
          u ^ (2 * j) / (2 * j).factorial) ≤
          ∑' j : ℕ, u ^ (2 * j) / (2 * j).factorial :=
      hsummable.sum_le_tsum _ (fun j hj => by positivity)
    rw [Finset.sum_insert (by simp)] at hpartial
    norm_num at hpartial
    rw [(Real.hasSum_cosh u).tsum_eq] at hpartial
    linarith
  have hchi_cosh : chiSquare B z ≤ Real.cosh ((B : ℝ) * z ^ 2) - 1 := by
    rw [hchi_even]
    dsimp [u] at hfinite_series hseries_tail ⊢
    exact hfinite_series.trans hseries_tail
  have hcosh_small (v : ℝ) (hv0 : 0 ≤ v) (hv2 : v ≤ 2) :
      Real.cosh v - 1 ≤ (v ^ 2 / 4) * (Real.cosh 2 - 1) := by
    let av : ℕ → ℝ := fun n => v ^ (2 * n) / (2 * n).factorial
    let a2 : ℕ → ℝ := fun n => (2 : ℝ) ^ (2 * n) / (2 * n).factorial
    have hav_sum : Summable av := by
      dsimp [av]
      exact (Real.hasSum_cosh v).summable
    have ha2_sum : Summable a2 := by
      dsimp [a2]
      exact (Real.hasSum_cosh 2).summable
    have htail_v : (∑' n : ℕ, av (n + 1)) = Real.cosh v - 1 := by
      have hsplit := hav_sum.sum_add_tsum_nat_add 1
      rw [(Real.hasSum_cosh v).tsum_eq] at hsplit
      simp only [Finset.sum_range_one, av, mul_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one] at hsplit
      linarith
    have htail_2 : (∑' n : ℕ, a2 (n + 1)) = Real.cosh 2 - 1 := by
      have hsplit := ha2_sum.sum_add_tsum_nat_add 1
      rw [(Real.hasSum_cosh 2).tsum_eq] at hsplit
      simp only [Finset.sum_range_one, a2, mul_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one] at hsplit
      linarith
    have hpoint (n : ℕ) : av (n + 1) ≤ (v ^ 2 / 4) * a2 (n + 1) := by
      have hq0 : 0 ≤ v / 2 := by linarith
      have hq1 : v / 2 ≤ 1 := by linarith
      have hpow : (v / 2) ^ (2 * (n + 1)) ≤ (v / 2) ^ 2 :=
        pow_le_pow_of_le_one hq0 hq1 (by omega)
      have hscale : 0 ≤ (2 : ℝ) ^ (2 * (n + 1)) /
          (2 * (n + 1)).factorial := by positivity
      calc
        av (n + 1) = ((2 : ℝ) ^ (2 * (n + 1)) /
            (2 * (n + 1)).factorial) * (v / 2) ^ (2 * (n + 1)) := by
              dsimp [av]
              rw [div_mul_eq_mul_div, ← mul_pow]
              congr 1
              ring
        _ ≤ ((2 : ℝ) ^ (2 * (n + 1)) /
            (2 * (n + 1)).factorial) * (v / 2) ^ 2 :=
              mul_le_mul_of_nonneg_left hpow hscale
        _ = (v ^ 2 / 4) * a2 (n + 1) := by
              dsimp [a2]
              ring
    have htail_le : (∑' n : ℕ, av (n + 1)) ≤
        ∑' n : ℕ, (v ^ 2 / 4) * a2 (n + 1) := by
      exact ((summable_nat_add_iff 1).2 hav_sum).tsum_le_tsum hpoint
        (((summable_nat_add_iff 1).2 ha2_sum).mul_left _)
    rw [htail_v, tsum_mul_left, htail_2] at htail_le
    exact htail_le
  have hcosh_two : Real.cosh 2 - 1 < 3 := by
    have he1u := Real.exp_one_lt_d9
    have he1l := Real.exp_one_gt_two
    have he2u : Real.exp 2 < (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have he2l : (4 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have heneg2 : Real.exp (-2) < (1 / 4 : ℝ) := by
      rw [Real.exp_neg]
      simpa [one_div] using
        (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) he2l)
    rw [Real.cosh_eq]
    nlinarith
  have hdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → (B : ℝ) * δ ≤ 1 →
      z ^ 2 = 2 * δ - δ ^ 2 → chiSquare B z ≤ 3 * ((B : ℝ) * δ) ^ 2 := by
    intro δ _ _ hBδ hzδ
    have hB0 : 0 ≤ (B : ℝ) := by positivity
    have hzsqupper : z ^ 2 ≤ 2 * δ := by rw [hzδ]; nlinarith [sq_nonneg δ]
    have hu0 : 0 ≤ (B : ℝ) * z ^ 2 := mul_nonneg hB0 (sq_nonneg z)
    have hu2 : (B : ℝ) * z ^ 2 ≤ 2 := by
      calc
        (B : ℝ) * z ^ 2 ≤ (B : ℝ) * (2 * δ) :=
          mul_le_mul_of_nonneg_left hzsqupper hB0
        _ ≤ 2 := by nlinarith
    have hsmall := hcosh_small ((B : ℝ) * z ^ 2) hu0 hu2
    have hchain := hchi_cosh.trans hsmall
    have huBδ : (B : ℝ) * z ^ 2 ≤ 2 * ((B : ℝ) * δ) := by
      calc
        (B : ℝ) * z ^ 2 ≤ (B : ℝ) * (2 * δ) :=
          mul_le_mul_of_nonneg_left hzsqupper hB0
        _ = 2 * ((B : ℝ) * δ) := by ring
    have husq : ((B : ℝ) * z ^ 2) ^ 2 ≤ (2 * ((B : ℝ) * δ)) ^ 2 := by
      nlinarith
    have hprod : (((B : ℝ) * z ^ 2) ^ 2 / 4) * (Real.cosh 2 - 1) ≤
        (((B : ℝ) * z ^ 2) ^ 2 / 4) * 3 :=
      mul_le_mul_of_nonneg_left hcosh_two.le (by positivity)
    nlinarith
  have hL_nonneg (k : ℕ) (hk : k ∈ Finset.range (B + 1)) : 0 ≤ L k := by
    have hp := hpz_nonneg k hk
    rw [hpz_likelihood k hk] at hp
    exact nonneg_of_mul_nonneg_right hp (hp0_pos k hk)
  have hp0L_sum :
      (∑ k ∈ Finset.range (B + 1), p_0 B k * L k) = 1 := by
    calc
      (∑ k ∈ Finset.range (B + 1), p_0 B k * L k) =
          ∑ k ∈ Finset.range (B + 1), p_z B z k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact (hpz_likelihood k hk).symm
      _ = 1 := hpz_sum
  have hp0_fin :
      (∀ k : Fin (B + 1), 0 ≤ p_0 B k) ∧
        ∑ k : Fin (B + 1), p_0 B k = 1 := by
    constructor
    · intro k
      exact (hp0_pos k (Finset.mem_range.mpr k.isLt)).le
    · rw [Fin.sum_univ_eq_sum_range]
      exact hp0_sum
  have hpz_fin :
      (∀ k : Fin (B + 1), 0 ≤ p_z B z k) ∧
        ∑ k : Fin (B + 1), p_z B z k = 1 := by
    constructor
    · intro k
      exact hpz_nonneg k (Finset.mem_range.mpr k.isLt)
    · rw [Fin.sum_univ_eq_sum_range]
      exact hpz_sum
  have hroot_variance :
      (∑ k ∈ Finset.range (B + 1),
          p_0 B k * (Real.sqrt (L k) - 1) ^ 2) =
        2 * (1 - bhattacharyya
          (fun k : Fin (B + 1) => p_0 B k)
          (fun k : Fin (B + 1) => p_z B z k)) := by
    calc
      (∑ k ∈ Finset.range (B + 1),
          p_0 B k * (Real.sqrt (L k) - 1) ^ 2) =
          ∑ k : Fin (B + 1),
            p_0 B k * (Real.sqrt (L k) - 1) ^ 2 := by
        exact (Fin.sum_univ_eq_sum_range
          (fun k : ℕ => p_0 B k * (Real.sqrt (L k) - 1) ^ 2) (B + 1)).symm
      _ =
          hellingerSq
            (fun k : Fin (B + 1) => p_0 B k)
            (fun k : Fin (B + 1) => p_z B z k) := by
        rw [hellingerSq]
        apply Finset.sum_congr rfl
        intro k _
        have hk : (k : ℕ) ∈ Finset.range (B + 1) := Finset.mem_range.mpr k.isLt
        rw [hpz_likelihood k hk]
        calc
          p_0 B k * (Real.sqrt (L k) - 1) ^ 2 =
              Real.sqrt (p_0 B k) ^ 2 * (Real.sqrt (L k) - 1) ^ 2 := by
                rw [Real.sq_sqrt (hp0_pos k hk).le]
          _ = (Real.sqrt (p_0 B k) -
              Real.sqrt (p_0 B k * L k)) ^ 2 := by
                rw [Real.sqrt_mul (hp0_pos k hk).le]
                ring
      _ = 2 * (1 - bhattacharyya
          (fun k : Fin (B + 1) => p_0 B k)
          (fun k : Fin (B + 1) => p_z B z k)) :=
        hellinger_sq_eq_two_sub _ _ hp0_fin hpz_fin
  have hchi_variance : chiSquare B z =
      ∑ k ∈ Finset.range (B + 1), p_0 B k * (L k - 1) ^ 2 := by
    have hchi_L : chiSquare B z =
        (∑ k ∈ Finset.range (B + 1), p_0 B k * L k ^ 2) - 1 := by
      rw [chiSquare]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [hpz_likelihood k hk]
      field_simp [(ne_of_gt (hp0_pos k hk))]
    rw [hchi_L]
    have hone : (1 : ℝ) = 2 *
        (∑ k ∈ Finset.range (B + 1), p_0 B k * L k) -
        (∑ k ∈ Finset.range (B + 1), p_0 B k) := by
      rw [hp0L_sum, hp0_sum]
      ring
    conv_lhs => rw [hone]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hroot_point (k : ℕ) (hk : k ∈ Finset.range (B + 1)) :
      (Real.sqrt (L k) - 1) ^ 2 ≤ (L k - 1) ^ 2 := by
    have hs := Real.sq_sqrt (hL_nonneg k hk)
    have hprod : 0 ≤ (Real.sqrt (L k) - 1) ^ 2 * Real.sqrt (L k) *
        (Real.sqrt (L k) + 2) := by positivity
    calc
      (Real.sqrt (L k) - 1) ^ 2 ≤
          (Real.sqrt (L k) - 1) ^ 2 +
            (Real.sqrt (L k) - 1) ^ 2 * Real.sqrt (L k) *
              (Real.sqrt (L k) + 2) := le_add_of_nonneg_right hprod
      _ = (Real.sqrt (L k) ^ 2 - 1) ^ 2 := by ring
      _ = (L k - 1) ^ 2 := by rw [hs]
  have hstrict : |z| < 1 →
      (∀ k ∈ Finset.range (B + 1), 0 < p_z B z k) ∧
      0 < bhattacharyya
        (fun k : Fin (B + 1) => p_0 B k)
        (fun k : Fin (B + 1) => p_z B z k) := by
    intro hzlt
    have ha_pos : 0 < (1 + z) / 2 := by linarith [(abs_lt.mp hzlt).1]
    have hb_pos : 0 < (1 - z) / 2 := by linarith [(abs_lt.mp hzlt).2]
    have hpz_pos (k : ℕ) (hk : k ∈ Finset.range (B + 1)) : 0 < p_z B z k := by
      have hkB : k ≤ B := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
      have hchoose : 0 < (B.choose k : ℝ) := by
        exact_mod_cast Nat.choose_pos hkB
      rw [p_z]
      positivity
    refine ⟨hpz_pos, ?_⟩
    rw [bhattacharyya]
    apply Finset.sum_pos'
    · intro k _
      exact (Real.sqrt_pos.2 (mul_pos
        (hp0_pos k (Finset.mem_range.mpr k.isLt))
        (hpz_pos k (Finset.mem_range.mpr k.isLt)))).le
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      exact Real.sqrt_pos.2 (mul_pos
        (hp0_pos 0 (by simp))
        (hpz_pos 0 (by simp)))
  exact ⟨hpz_nonneg, hpz_sum, hlikelihood_ratio, hchi_exact, hchi_even, hchi_cosh,
    hdelta, hstrict, by
    have hroot_le_chi :
        (∑ k ∈ Finset.range (B + 1),
            p_0 B k * (Real.sqrt (L k) - 1) ^ 2) ≤ chiSquare B z := by
      rw [hchi_variance]
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hroot_point k hk) (hp0_pos k hk).le
    calc
      1 - bhattacharyya
          (fun k : Fin (B + 1) => p_0 B k)
          (fun k : Fin (B + 1) => p_z B z k) ^ 2 ≤
          2 * (1 - bhattacharyya
            (fun k : Fin (B + 1) => p_0 B k)
            (fun k : Fin (B + 1) => p_z B z k)) := by
        nlinarith [sq_nonneg (1 - bhattacharyya
          (fun k : Fin (B + 1) => p_0 B k)
          (fun k : Fin (B + 1) => p_z B z k))]
      _ ≤ chiSquare B z := hroot_variance.symm.trans_le hroot_le_chi⟩
#print axioms symmetric_binomial_chi_square

end D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare
