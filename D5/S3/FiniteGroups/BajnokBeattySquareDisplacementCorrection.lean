/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCorrection
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementCorrection
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: All-q square-displacement coefficient signs and exact Perron cancellation. -/

import D5.S0.Tower.DBonacci.PerronRoot
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
import Mathlib.Tactic

/-! The logarithm lower bound reuses the fixed order-nine Perron instance.
The additional quantitative ingredient is the finite degree-four exponential
certificate for positivity of beta - q^4 exp (-q^2 sigma). -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection

open D5.S0.Tower.DBonacci.PerronRoot
open D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot

private theorem exp_two_mul_nat_div_three_gt {n : ℕ} (hn : 9 ≤ n) :
    (10 / 9 : ℝ) * (n : ℝ)^2 < Real.exp (2 * (n : ℝ) / 3) := by
  have h := Real.sum_le_exp_of_nonneg (x := 2 * (n : ℝ) / 3)
    (by positivity : 0 ≤ 2 * (n : ℝ) / 3) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hnR : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbr : (10 / 9 : ℝ) ≤
      4 * (n : ℝ) / 81 + 2 * (n : ℝ)^2 / 243 := by
    nlinarith [sq_nonneg ((n : ℝ) - 9)]
  have htail : (10 / 9 : ℝ) * (n : ℝ)^2 ≤
      (2 * (n : ℝ) / 3)^3 / 6 + (2 * (n : ℝ) / 3)^4 / 24 := by
    calc
      (10 / 9 : ℝ) * (n : ℝ)^2 ≤
          (n : ℝ)^2 * (4 * (n : ℝ) / 81 + 2 * (n : ℝ)^2 / 243) := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hbr (sq_nonneg (n : ℝ))
      _ = (2 * (n : ℝ) / 3)^3 / 6 + (2 * (n : ℝ) / 3)^4 / 24 := by ring
  have hpoly : (10 / 9 : ℝ) * (n : ℝ)^2 <
      1 + 2 * (n : ℝ) / 3 + (2 * (n : ℝ) / 3)^2 / 2 +
        (2 * (n : ℝ) / 3)^3 / 6 + (2 * (n : ℝ) / 3)^4 / 24 := by
    have hpos : 0 < 1 + 2 * (n : ℝ) / 3 + (2 * (n : ℝ) / 3)^2 / 2 := by
      positivity
    linarith only [htail, hpos]
  linarith only [h, hpoly]

/-!
The theorem is stated with local lets so that the public parameter surface is
exactly the requested coefficient formula.  No count extension, rounding
statement, or integer threshold is included.
-/
theorem square_displacement_correction (q : ℕ) (hq : 3 ≤ q) :
    let Q : ℝ := (q : ℝ)
    let nu : ℕ := q^2
    let beta : ℝ := dbonacciPerronRoot nu
    let sigma : ℝ := Real.log beta
    let c : ℝ := (Q^2 - 1) / (4 * Q)
    let alpha : ℝ := c / sigma
    let g : ℝ := Real.exp sigma - Q^2 * Real.exp (-Q^2 * sigma)
    let C : ℝ := 2 * (Q^2 + 1) / (3 * (Q^2 - 1)^2)
    let H : ℝ := C * sigma^3 *
      (Real.exp sigma - Q^4 * Real.exp (-Q^2 * sigma))
    let d : ℝ := ((Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1))) *
      (((Q^4 + 1) * beta - 2 * Q^4) /
        ((Q^2 + 1) * beta - 2 * Q^2))
    let b : ℝ := d - 1 / (2 * Q)
    0 < g ∧ 0 < d ∧ d < 5 * Real.log 2 / (24 * Q) ∧
      -1 / (2 * Q) < b ∧ b < 0 ∧ g * (sigma * d / alpha) = H := by
  let Q : ℝ := (q : ℝ)
  let nu : ℕ := q^2
  let beta : ℝ := dbonacciPerronRoot nu
  let sigma : ℝ := Real.log beta
  let c : ℝ := (Q^2 - 1) / (4 * Q)
  let alpha : ℝ := c / sigma
  let g : ℝ := Real.exp sigma - Q^2 * Real.exp (-Q^2 * sigma)
  let C : ℝ := 2 * (Q^2 + 1) / (3 * (Q^2 - 1)^2)
  let H : ℝ := C * sigma^3 *
    (Real.exp sigma - Q^4 * Real.exp (-Q^2 * sigma))
  let d : ℝ := ((Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1))) *
    (((Q^4 + 1) * beta - 2 * Q^4) /
      ((Q^2 + 1) * beta - 2 * Q^2))
  let b : ℝ := d - 1 / (2 * Q)
  have hqR : (3 : ℝ) ≤ Q := by
    dsimp [Q]
    exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le (by norm_num) hqR
  have hnu : 9 ≤ nu := by
    dsimp [nu]
    simpa only [pow_two] using (Nat.mul_le_mul hq hq)
  have hnuR : (9 : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hnu
  have hnuQ : (nu : ℝ) = Q^2 := by
    dsimp [nu, Q]
    push_cast
    ring
  have hnuQ4 : (nu : ℝ)^2 = Q^4 := by rw [hnuQ]; ring
  have hbeta_pos : 0 < beta := by
    dsimp [beta]
    exact lt_trans zero_lt_one (one_lt_dbonacciPerronRoot nu (by omega))
  have hbeta_gt_one : 1 < beta := by
    dsimp [beta]
    exact one_lt_dbonacciPerronRoot nu (by omega)
  have hbeta_lt_two : beta < 2 := by
    dsimp [beta]
    exact dbonacciPerronRoot_lt_two nu (by omega)
  have hroot_order : dbonacciPerronRoot 9 ≤ beta := by
    change dbonacciPerronRoot 9 ≤ dbonacciPerronRoot nu
    exact dbonacciPerronRoot_strictMonoOn.monotoneOn
      (by norm_num) (show 2 ≤ nu by omega) hnu
  have hsigma_lower : (2 / 3 : ℝ) < sigma := by
    have hlog9 : (2 / 3 : ℝ) < Real.log (dbonacciPerronRoot 9) := by
      simpa [s_star] using two_thirds_lt_s_star
    have hlogmono : Real.log (dbonacciPerronRoot 9) ≤ Real.log beta :=
      Real.strictMonoOn_log.monotoneOn
        (lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 9 (by norm_num)))
        hbeta_pos hroot_order
    exact lt_of_lt_of_le hlog9 (by simpa [sigma] using hlogmono)
  have hsigma_upper : sigma < Real.log 2 := by
    dsimp [sigma]
    exact Real.strictMonoOn_log hbeta_pos (by norm_num) hbeta_lt_two
  have hsigma_pos : 0 < sigma := lt_trans (by norm_num) hsigma_lower
  have hmul : Real.exp ((nu : ℝ) * sigma) = beta ^ nu := by
    dsimp [sigma]
    simpa only [Real.exp_log hbeta_pos] using
      (Real.exp_nat_mul (Real.log beta) nu)
  have hexp_order : Real.exp (2 * (nu : ℝ) / 3) <
      Real.exp ((nu : ℝ) * sigma) := by
    apply Real.exp_lt_exp.mpr
    nlinarith only [hsigma_lower, hnuR]
  have hexp_lower : (10 / 9 : ℝ) * (nu : ℝ)^2 <
      Real.exp (2 * (nu : ℝ) / 3) := exp_two_mul_nat_div_three_gt hnu
  have hexp_total : (10 / 9 : ℝ) * (nu : ℝ)^2 <
      Real.exp ((nu : ℝ) * sigma) := hexp_lower.trans hexp_order
  have hquot : (nu : ℝ)^2 / Real.exp ((nu : ℝ) * sigma) <
      (9 / 10 : ℝ) := by
    apply (div_lt_iff₀ (Real.exp_pos _)).2
    nlinarith only [hexp_total]
  have hsmall : (nu : ℝ)^2 * Real.exp (-((nu : ℝ) * sigma)) <
      (9 / 10 : ℝ) := by
    calc
      (nu : ℝ)^2 * Real.exp (-((nu : ℝ) * sigma)) =
          (nu : ℝ)^2 / Real.exp ((nu : ℝ) * sigma) := by
            rw [Real.exp_neg]
            simp only [div_eq_mul_inv]
      _ < (9 / 10 : ℝ) := hquot
  have hroot_exp : Real.exp (-Q^2 * sigma) = 2 - beta := by
    have hinv : Real.exp (-((nu : ℝ) * sigma)) = beta⁻¹ ^ nu := by
      rw [Real.exp_neg, hmul, inv_pow]
    rw [show -Q^2 * sigma = -((nu : ℝ) * sigma) by rw [hnuQ]; ring, hinv]
    symm
    exact two_sub_dbonacciPerronRoot_eq_inv_pow nu (by omega)
  have hexp_sigma : Real.exp sigma = beta := by
    dsimp [sigma]
    exact Real.exp_log hbeta_pos
  have hsmallQ : Q^4 * Real.exp (-Q^2 * sigma) < (9 / 10 : ℝ) := by
    rw [← hnuQ4, show -Q^2 * sigma = -((nu : ℝ) * sigma) by rw [hnuQ]; ring]
    exact hsmall
  have hN : 0 < beta - Q^4 * Real.exp (-Q^2 * sigma) := by
    nlinarith only [hsmallQ, hbeta_gt_one]
  have hwpos : 0 < Real.exp (-Q^2 * sigma) := Real.exp_pos _
  have hdiff : 0 < (Q^4 - Q^2) * Real.exp (-Q^2 * sigma) := by
    apply mul_pos _ hwpos
    rw [show Q^4 - Q^2 = Q^2 * (Q^2 - 1) by ring]
    exact mul_pos (pow_pos hQ 2) (by nlinarith only [hqR])
  have hNless : beta - Q^4 * Real.exp (-Q^2 * sigma) <
      beta - Q^2 * Real.exp (-Q^2 * sigma) := by
    nlinarith only [hdiff]
  have hg : 0 < beta - Q^2 * Real.exp (-Q^2 * sigma) := by
    nlinarith only [hN, hdiff]
  have hratio_pos : 0 <
      (beta - Q^4 * Real.exp (-Q^2 * sigma)) /
        (beta - Q^2 * Real.exp (-Q^2 * sigma)) :=
    div_pos hN hg
  have hratio_lt_one :
      (beta - Q^4 * Real.exp (-Q^2 * sigma)) /
        (beta - Q^2 * Real.exp (-Q^2 * sigma)) < 1 :=
    (div_lt_one hg).2 hNless
  have hden : (Q^2 + 1) * beta - 2 * Q^2 =
      beta - Q^2 * Real.exp (-Q^2 * sigma) := by
    rw [hroot_exp]
    ring
  have hnum : (Q^4 + 1) * beta - 2 * Q^4 =
      beta - Q^4 * Real.exp (-Q^2 * sigma) := by
    rw [hroot_exp]
    ring
  have hden_pos : 0 < (Q^2 + 1) * beta - 2 * Q^2 := by
    rw [hden]
    exact hg
  have hpref_pos : 0 < (Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1)) := by
    have hQminus : 0 < Q^2 - 1 := by nlinarith only [hqR]
    apply div_pos
    · positivity
    · positivity
  have hd_pos : 0 < d := by
    dsimp [d]
    rw [hnum, hden]
    exact mul_pos hpref_pos hratio_pos
  have hqratio : (Q^2 + 1) / (Q^2 - 1) ≤ (5 / 4 : ℝ) := by
    apply (div_le_iff₀ (show 0 < Q^2 - 1 by nlinarith only [hqR])).2
    nlinarith [sq_nonneg (Q - 3)]
  have hpref_bound : (Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1)) ≤
      5 * sigma / (24 * Q) := by
    calc
      (Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1)) =
          (sigma / (6 * Q)) * ((Q^2 + 1) / (Q^2 - 1)) := by
            field_simp [ne_of_gt hQ, show Q^2 - 1 ≠ 0 by nlinarith only [hqR]] <;> ring
      _ ≤ (sigma / (6 * Q)) * (5 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hqratio (by positivity)
      _ = 5 * sigma / (24 * Q) := by
        field_simp [ne_of_gt hQ]
        ring
  have hd_upper : d < 5 * Real.log 2 / (24 * Q) := by
    dsimp [d]
    rw [hnum, hden]
    calc
      (Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1)) *
          ((beta - Q^4 * Real.exp (-Q^2 * sigma)) /
            (beta - Q^2 * Real.exp (-Q^2 * sigma))) <
          (Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1)) * 1 := by
            exact mul_lt_mul_of_pos_left hratio_lt_one hpref_pos
      _ = (Q^2 + 1) * sigma / (6 * Q * (Q^2 - 1)) := by ring
      _ ≤ 5 * sigma / (24 * Q) := hpref_bound
      _ < 5 * Real.log 2 / (24 * Q) := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left hsigma_upper (by norm_num)) (by positivity)
  have hlog2 : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hd_half : d < 1 / (2 * Q) := by
    calc
      d < 5 * Real.log 2 / (24 * Q) := hd_upper
      _ < 12 / (24 * Q) := by
        apply div_lt_div_of_pos_right
        · nlinarith only [hlog2]
        · positivity
      _ = 1 / (2 * Q) := by
        field_simp [ne_of_gt hQ]
        ring
  have hb_lower : -1 / (2 * Q) < b := by
    change -1 / (2 * Q) < d - 1 / (2 * Q)
    calc
      -1 / (2 * Q) = (0 : ℝ) - 1 / (2 * Q) := by ring
      _ < d - 1 / (2 * Q) := sub_lt_sub_right hd_pos _
  have hb_upper : b < 0 := by
    dsimp [b]
    linarith only [hd_half]
  have halpha : 0 < alpha := by
    dsimp [alpha, c]
    exact div_pos (div_pos (by nlinarith only [hqR]) (by positivity)) hsigma_pos
  have hcancel : g * (sigma * d / alpha) = H := by
    have hg_norm : beta - Q^2 * Real.exp (-(Q^2 * sigma)) ≠ 0 := by
      simpa only [neg_mul] using hg.ne'
    dsimp [g, d, alpha, H, C, c]
    rw [hexp_sigma, hnum, hden]
    simp only [neg_mul]
    field_simp [ne_of_gt hQ, show Q^2 - 1 ≠ 0 by nlinarith only [hqR],
      hsigma_pos.ne', hg_norm] <;> ring
  change 0 < g ∧ 0 < d ∧ d < 5 * Real.log 2 / (24 * Q) ∧
    -1 / (2 * Q) < b ∧ b < 0 ∧ g * (sigma * d / alpha) = H
  refine ⟨?_, hd_pos, hd_upper, hb_lower, hb_upper, hcancel⟩
  dsimp [g]
  simpa [hexp_sigma] using hg

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCorrection
