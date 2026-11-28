/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The three finite sign failure bounds at the admissible dimensions. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.SignMatrixNetBounds
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking
open Real
private lemma seventeen_lt_exp_three : (17 : ℝ) < Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add] at *
  nlinarith [sq_nonneg (Real.exp 1 - (2.7182818283 : ℝ)),
    mul_self_nonneg (Real.exp 1), Real.exp_pos 1]
private lemma schmidt_exponent_gap {k d : ℕ} (hk : 2 ≤ k) (hdim : 524288 * k ^ 3 ≤ d) :
    24 * (d : ℝ) * k + 4 ≤ ((d : ℝ) / (64 * k)) ^ 2 / (4 * (18 / 25 : ℝ)) := by
  have hkN : 0 < k := lt_of_lt_of_le (by decide) hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hkN
  have hdN : 0 < d := lt_of_lt_of_le (by positivity) hdim
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hdN
  have hk2 : (0 : ℝ) < (k : ℝ)^2 := sq_pos_of_pos hk0
  have hdk : (524288 : ℝ) * (k : ℝ)^3 ≤ d := by exact_mod_cast hdim
  have hprod : (0 : ℝ) ≤ d * (d - (524288 : ℝ) * k^3) := by
    have : 0 ≤ d - (524288 : ℝ) * k^3 := sub_nonneg.mpr hdk
    positivity
  have hmain : 24 * d * k^3 ≤ (24 / 524288 : ℝ) * d^2 := by
    nlinarith [hprod]
  have hsq0 := (sq_le_sq₀ (show (0 : ℝ) ≤ 524288 * k^3 by positivity) (show (0 : ℝ) ≤ d by positivity)).2 hdk
  have hsq : (524288 : ℝ)^2 * k^6 ≤ d^2 := by
    nlinarith [hsq0]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkpow : (k : ℝ)^2 ≤ k^6 := pow_le_pow_right₀ hk1 (by decide)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (18 / 25))).2
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < 64 * k))).2
  field_simp
  ring_nf at hmain hsq ⊢
  nlinarith [hmain, hsq, hkpow, sq_nonneg (d - 1)]
private lemma operator_exponent_gap {d : ℕ} (hd : 4 ≤ d) :
    4 ≤ (3 * (d : ℝ)) ^ 2 / (2 * (18 / 25 : ℝ)) - 6 * (d : ℝ)^2 := by
  have hd0 : (4 : ℝ) ≤ d := by exact_mod_cast (hd)
  norm_num
  nlinarith [sq_nonneg ((d : ℝ) - 4)]
private lemma seventeen_pow_le_exp (n : ℕ) : (17 : ℝ)^n ≤ Real.exp (3 * n) := by
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 17 by norm_num) seventeen_lt_exp_three.le n
  rw [← Real.exp_nat_mul] at hp
  simpa [mul_comm] using hp
private lemma four_mul_exp_neg_four_lt_quarter : 4 * Real.exp (-4) < (1 : ℝ) / 4 := by
  have h34 : Real.exp 3 < Real.exp 4 := (Real.exp_lt_exp).2 (by norm_num)
  have he4 : (16 : ℝ) < Real.exp 4 := by linarith [seventeen_lt_exp_three, h34]
  have hp : Real.exp (-4) * Real.exp 4 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpos : 0 < Real.exp (-4) := Real.exp_pos _
  nlinarith
lemma schmidt_failure_bound_lt_quarter {k d : ℕ} (hk : 2 ≤ k) (hdim : 524288 * k ^ 3 ≤ d) :
    (17 : ℝ) ^ (8 * d * k) *
      (4 * Real.exp (-((d : ℝ) / (64 * (k : ℝ))) ^ 2 / (4 * (18 / 25 : ℝ)))) < 1 / 4 := by
  have he := schmidt_exponent_gap hk hdim
  have hp0 := seventeen_pow_le_exp (8 * d * k)
  have hp : (17 : ℝ) ^ (8 * d * k) ≤ Real.exp (3 * (8 * (d : ℝ) * (k : ℝ))) := by
    convert hp0 using 1 <;> norm_num <;> ring
  have harg : (3 : ℝ) * (8 * d * k) + 4 ≤
      ((d : ℝ) / (64 * (k : ℝ))) ^ 2 / (4 * (18 / 25 : ℝ)) := by
    convert he using 1 <;> norm_num <;> ring
  calc
    _ ≤ Real.exp (3 * (8 * d * k)) * (4 * Real.exp (-((d : ℝ) / (64 * (k : ℝ))) ^ 2 / (4 * (18 / 25 : ℝ)))) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 4 * (Real.exp (3 * (8 * (d : ℝ) * (k : ℝ))) *
        Real.exp (-((d : ℝ) / (64 * (k : ℝ))) ^ 2 / (4 * (18 / 25 : ℝ)))) := by ring
    _ = 4 * Real.exp (3 * (8 * (d : ℝ) * (k : ℝ)) -
        ((d : ℝ) / (64 * (k : ℝ))) ^ 2 / (4 * (18 / 25 : ℝ))) := by
      rw [← Real.exp_add]
      ring
    _ ≤ 4 * Real.exp (-4) := by
      gcongr
      linarith
    _ < 1 / 4 := four_mul_exp_neg_four_lt_quarter
lemma operator_failure_bound_lt_quarter {d : ℕ} (hd : 4 ≤ d) :
    (17 : ℝ) ^ (2 * d ^ 2) *
      (2 * Real.exp (-((3 * (d : ℝ)) ^ 2) / (2 * (18 / 25 : ℝ)))) < 1 / 4 := by
  have he := operator_exponent_gap hd
  have hp0 := seventeen_pow_le_exp (2 * d ^ 2)
  have hp : (17 : ℝ) ^ (2 * d ^ 2) ≤ Real.exp (3 * (2 * (d : ℝ)^2)) := by
    convert hp0 using 1 <;> norm_num <;> ring
  calc
    _ ≤ Real.exp (3 * (2 * (d : ℝ)^2)) *
        (2 * Real.exp (-((3 * (d : ℝ)) ^ 2) / (2 * (18 / 25 : ℝ)))) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 2 * (Real.exp (3 * (2 * (d : ℝ)^2)) *
        Real.exp (-((3 * (d : ℝ)) ^ 2) / (2 * (18 / 25 : ℝ)))) := by ring
    _ = 2 * Real.exp (3 * (2 * (d : ℝ)^2) -
        ((3 * (d : ℝ)) ^ 2) / (2 * (18 / 25 : ℝ))) := by
      rw [← Real.exp_add]
      ring
    _ ≤ 2 * Real.exp (-4) := by
      gcongr
      linarith
    _ < 1 / 4 := by
      have := four_mul_exp_neg_four_lt_quarter
      linarith

end D5.S3.Quantum.Entanglement.EntanglementBreaking
