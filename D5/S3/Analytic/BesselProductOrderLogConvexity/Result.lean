/- GID: D5/S3/Analytic/BesselProductOrderLogConvexity/Result
   generality: I
   mirror-B: D5/B/S3/Analytic/BesselProductOrderLogConvexity/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Series, mathlib/module/Mathlib.Analysis.Complex.ExponentialBounds]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/BesselProductOrderLogConvexity/Result.claim; result=D5/S3/Analytic/BesselProductOrderLogConvexity/Result.result; claim=D5/S3/Analytic/BesselProductOrderLogConvexity/Result.claim
   digest: Half-integer Bessel products refute log-convexity in the order. -/

/-
admission_basis: open-problem-resolution (Baricz-Ponnusamy final Conjecture; Refuted).
Per-declaration judgment: all rows have escape_witness: none.
After expanding same-delivery helpers, the proof uses the reused first-kind
series and its summability, Mathlib Gamma duplication and recurrence, the
hyperbolic series, tsum identities, exponential bounds, and normalization.
Every theorem row is bind-only; the settling conclusion supplies the
open-problem-resolution admission basis.
Current declaration identities from the scoped Lean report:
  B: GID D5/S3/Analytic/BesselRatioLogConcavity/Result.besselI
     Lean name: D5.S3.Analytic.BesselRatioLogConcavity.Result.besselI
     statement_id: sha256:b2c7dbd6b47657b5e857da424f6a6c4634758f039c6c82466b824b24e46d79be
  S: GID D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_summable
     Lean name: D5.S3.Analytic.BesselRatioLogConcavity.Result.bessel_summable
     statement_id: sha256:644a8c30490609feaef0b2cef77ba07a09379e4a19585cb2a496d3db75505920
B and S are declarations of BesselRatioLogConcavity.Result; S supplies
the convergence hypotheses used in the recurrence.
Compiler-generated proof constants are internal details, not extra source rows.
Per declaration: name | proof_shape | direct consumers | frozen owner dependencies.
  besselK | bind-only (definition) | P | B
  P | bind-only (definition) | claim, product_values, result, witness | B
  claim | bind-only (definition) | result | B
  a | bind-only (definition) | a_eq_sqrt, half_values, minus_term, plus_term | none
  gamma_factorial | bind-only | minus_term | none
  minus_term | bind-only | half_values, plus_term | none
  plus_term | bind-only | half_values | none
  a_eq_sqrt | bind-only | half_values | none
  half_values | bind-only | product_values | B
  summand | bind-only (definition) | lower, recurrence, shift, step | none
  lower | bind-only | recurrence, step | none
  shift | bind-only | step | none
  step | bind-only | recurrence | none
  recurrence | bind-only | recurrence_minus, recurrence_plus | B, S
  recurrence_minus | bind-only | product_values | B, S
  recurrence_plus | bind-only | product_values | B, S
  product_values | bind-only | witness | B, S
  exp_bound | bind-only | witness | none
  witness | bind-only | result | B, S
  half_noninteger | bind-only | result | none
  result | bind-only | settling result | B, S
The utility is certified-instance with basis refutes. The public theorems are
result, whose conclusion is exactly the negation of claim, and half_noninteger.
-/

import D5.S3.Analytic.BesselRatioLogConcavity.Result
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
open scoped BigOperators
open D5.S3.Analytic.BesselRatioLogConcavity.Result (besselI bessel_summable)
noncomputable section
namespace D5.S3.Analytic.BesselProductOrderLogConvexity.Result

def besselK (ν u : ℝ) : ℝ :=
  (Real.pi/2) * (besselI (-ν) u - besselI ν u) / Real.sin (ν*Real.pi)

def P (u ν : ℝ) : ℝ := besselI ν u * besselK ν u

def claim : Prop :=
  ∀ u : ℝ, 0 < u → ∀ ν h : ℝ, -1 < ν → 0 < h →
    (∀ n : ℤ, ν ≠ (n:ℝ)) → (∀ n : ℤ, ν+h ≠ (n:ℝ)) →
    (∀ n : ℤ, ν+2*h ≠ (n:ℝ)) → P u ν * P u (ν+2*h) ≥ P u (ν+h)^2

private def a : ℝ := (1/2:ℝ)^((-1/2:ℝ)) / Real.sqrt Real.pi

private lemma gamma_factorial (k : ℕ) :
    (k.factorial:ℝ) * Real.Gamma (k+1/2) * (4:ℝ)^k =
      ((2*k).factorial:ℝ) * Real.sqrt Real.pi := by
  have h := Real.Gamma_mul_Gamma_add_half ((k:ℝ)+1/2)
  rw [show (k:ℝ)+1/2+1/2 = k+1 by ring, Real.Gamma_nat_eq_factorial,
    show 2*((k:ℝ)+1/2) = ((2*k:ℕ):ℝ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial,
    show 1-(((2*k:ℕ):ℝ)+1) = -((2*k:ℕ):ℝ) by ring,
    Real.rpow_neg, Real.rpow_natCast] at h
  · have hp : (2:ℝ)^(2*k) = (4:ℝ)^k := by rw [pow_mul]; norm_num
    rw [hp] at h
    have h4 : (4:ℝ)^k ≠ 0 := by positivity
    field_simp at h
    rw [show ((k:ℝ)*2+1)/2 = k+1/2 by ring] at h
    linear_combination h
  · norm_num


private lemma minus_term (k : ℕ) :
    (1/2:ℝ)^((2*k:ℕ)+((-1/2:ℝ))) /
      ((k.factorial:ℝ)*Real.Gamma (k+((-1/2:ℝ))+1)) = a / ((2*k).factorial:ℝ) := by
  rw [show (k:ℝ)+((-1/2:ℝ))+1 = k+1/2 by ring,
    Real.rpow_add (by norm_num), Real.rpow_natCast]
  have hp : (1/2:ℝ)^(2*k) = 1/(4:ℝ)^k := by
    rw [pow_mul, show (1/2:ℝ)^2 = 1/4 by norm_num, one_div_pow]
  rw [hp]
  have h := gamma_factorial k
  have hg := (Real.Gamma_pos_of_pos (show 0 < (k:ℝ)+1/2 by positivity)).ne'
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  have hf2 : ((2*k).factorial:ℝ) ≠ 0 := by positivity
  have hs := (Real.sqrt_pos.2 Real.pi_pos).ne'
  dsimp [a]
  field_simp [hf, hg, hf2, hs, pow_ne_zero _ (by norm_num : (4:ℝ) ≠ 0)]
  rw [show (2*(k:ℝ)+1)/2 = k+1/2 by ring]
  linear_combination -h

private lemma plus_term (k : ℕ) :
    (1/2:ℝ)^((2*k:ℕ)+(1/2:ℝ)) /
      ((k.factorial:ℝ)*Real.Gamma (k+(1/2:ℝ)+1)) = a / ((2*k+1).factorial:ℝ) := by
  have he : (1/2:ℝ)^((2*k:ℕ)+(1/2:ℝ)) =
      (1/2:ℝ)^((2*k:ℕ)+((-1/2:ℝ))) * (1/2) := by
    calc
      _ = (1/2:ℝ)^(((2*k:ℕ):ℝ)+((-1/2:ℝ))+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
  rw [he, Real.Gamma_add_one (by positivity)]
  have h := minus_term k
  rw [show (k:ℝ)+((-1/2:ℝ))+1 = k+1/2 by ring] at h
  rw [Nat.factorial_succ]
  push_cast
  have hg := (Real.Gamma_pos_of_pos (show 0 < (k:ℝ)+1/2 by positivity)).ne'
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  have hf2 : ((2*k).factorial:ℝ) ≠ 0 := by positivity
  have hk : 2*(k:ℝ)+1 ≠ 0 := by positivity
  push_cast at h
  field_simp [hf, hg, hf2, hk] at h ⊢
  rw [show (2*(k:ℝ)+1)/2 = k+1/2 by ring]
  convert h using 1; ring

private lemma a_eq_sqrt : a = Real.sqrt (2/Real.pi) := by
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hpow : ((1/2:ℝ)^((-1/2:ℝ)))^2 = 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num), Nat.cast_ofNat, show ((-1/2:ℝ))*2 = -1 by norm_num,
      Real.rpow_neg_one]
    norm_num
  have ha : a^2 = 2/Real.pi := by
    dsimp [a]
    rw [div_pow, hpow, Real.sq_sqrt Real.pi_pos.le]
  apply (sq_eq_sq₀ (by dsimp [a]; positivity) (Real.sqrt_nonneg _)).mp
  rw [ha, Real.sq_sqrt (by positivity)]

private lemma half_values :
    besselI ((-1/2:ℝ)) 1 = Real.sqrt (2/Real.pi) * Real.cosh 1 ∧
    besselI (1/2) 1 = Real.sqrt (2/Real.pi) * Real.sinh 1 := by
  rw [← a_eq_sqrt]
  constructor
  · unfold besselI
    simp_rw [minus_term]
    rw [show (fun k : ℕ => a / ((2*k).factorial:ℝ)) = (fun k => a * (1^ (2*k) / ((2*k).factorial:ℝ))) by ext k; simp [div_eq_mul_inv], tsum_mul_left, ← Real.cosh_eq_tsum]
  · unfold besselI
    simp_rw [plus_term]
    rw [show (fun k : ℕ => a / ((2*k+1).factorial:ℝ)) = (fun k => a * (1^ (2*k+1) / ((2*k+1).factorial:ℝ))) by ext k; simp [div_eq_mul_inv], tsum_mul_left, ← Real.sinh_eq_tsum]

private def summand (ν : ℝ) (k : ℕ) : ℝ :=
  (1/2:ℝ)^((2*k:ℕ)+ν) / ((k.factorial:ℝ)*Real.Gamma (k+ν+1))
private lemma lower (ν : ℝ) (k : ℕ) (hs : (k:ℝ)+ν+1 ≠ 0) :
    summand ν k = 2*((k:ℝ)+ν+1)*summand (ν+1) k := by
  have hp : (1/2:ℝ)^((2*k:ℕ)+(ν+1)) =
      (1/2:ℝ)^((2*k:ℕ)+ν) * (1/2) := by
    rw [show ((2*k:ℕ):ℝ)+(ν+1) = (((2*k:ℕ):ℝ)+ν)+1 by ring,
      Real.rpow_add (by norm_num), Real.rpow_one]
  unfold summand
  rw [show (k:ℝ)+(ν+1)+1 = ((k:ℝ)+ν+1)+1 by ring,
    Real.Gamma_add_one hs, hp]
  by_cases hg : Real.Gamma ((k:ℝ)+ν+1) = 0
  · simp [hg]
  · field_simp [hs, hg]

private lemma shift (ν : ℝ) (k : ℕ) :
    summand (ν+2) k = 2*((k:ℝ)+1)*summand (ν+1) (k+1) := by
  have hp : (1/2:ℝ)^((2*(k+1):ℕ)+(ν+1)) =
      (1/2:ℝ)^((2*k:ℕ)+(ν+2)) * (1/2) := by
    rw [show ((2*(k+1):ℕ):ℝ)+(ν+1) = (((2*k:ℕ):ℝ)+(ν+2))+1 by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_one]
  unfold summand
  rw [hp, Nat.factorial_succ]
  push_cast
  rw [show (k:ℝ)+(ν+2)+1 = (k+1)+(ν+1)+1 by ring]
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  by_cases hg : Real.Gamma ((k+1:ℝ)+(ν+1)+1) = 0
  · simp [hg]
  · field_simp [hg, hf, hk]

private lemma step (ν : ℝ) (k : ℕ) (hs : (k+1:ℝ)+ν+1 ≠ 0) :
    summand ν (k+1) = summand (ν+2) k + 2*(ν+1)*summand (ν+1) (k+1) := by
  rw [lower ν (k+1) (by exact_mod_cast hs), shift]
  push_cast
  ring
private lemma recurrence (ν : ℝ) (hν : -2 < ν)
    (hn : ∀ k : ℕ, (k:ℝ)+ν+1 ≠ 0) :
    besselI ν 1 = besselI (ν+2) 1 + 2*(ν+1)*besselI (ν+1) 1 := by
  have hb : Summable (summand (ν+1)) := by
    exact bessel_summable (ν := ν+1) (z := 1) (by linarith) zero_lt_one
  have hc : Summable (summand (ν+2)) := by
    exact bessel_summable (ν := ν+2) (z := 1) (by linarith) zero_lt_one
  have hbt : Summable (fun k => summand (ν+1) (k+1)) := (summable_nat_add_iff 1).2 hb
  have he (k : ℕ) : summand ν (k+1) = summand (ν+2) k + 2*(ν+1)*summand (ν+1) (k+1) :=
    step ν k (by simpa only [Nat.cast_add, Nat.cast_one] using hn (k+1))
  have hat : Summable (fun k => summand ν (k+1)) := by
    simp_rw [he]
    exact hc.add (hbt.mul_left _)
  have ha : Summable (summand ν) := (summable_nat_add_iff 1).1 hat
  have ht : (∑' k, summand ν (k+1)) = (∑' k, summand (ν+2) k) +
      2*(ν+1)*(∑' k, summand (ν+1) (k+1)) := by
    simp_rw [he]
    rw [hc.tsum_add (hbt.mul_left _), tsum_mul_left]
  change (∑' k, summand ν k) = (∑' k, summand (ν+2) k) + 2*(ν+1)*(∑' k, summand (ν+1) k)
  rw [ha.tsum_eq_zero_add, hb.tsum_eq_zero_add, ht, lower ν 0 (hn 0)]
  norm_num only [Nat.cast_zero, zero_add]
  ring

private lemma recurrence_minus :
    besselI (-3/2) 1 = besselI (1/2) 1 - besselI (-1/2) 1 := by
  have h := recurrence (-3/2) (by norm_num) (fun k => by
    cases k with
    | zero => norm_num
    | succ k =>
      push_cast
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith)
  norm_num at h
  linarith

private lemma recurrence_plus :
    besselI (3/2) 1 = besselI (-1/2) 1 - besselI (1/2) 1 := by
  have h := recurrence (-1/2) (by norm_num) (fun k => by
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith)
  norm_num at h
  linarith

private lemma product_values :
    P 1 ((-1/2:ℝ)) = (1 + Real.exp (-2))/2 ∧
    P 1 (1/2) = (1 - Real.exp (-2))/2 ∧
    P 1 (3/2) = 2 * Real.exp (-2) := by
  obtain ⟨hm, hp⟩ := half_values
  have hmp := recurrence_minus
  have hpp := recurrence_plus
  rw [hm, hp] at hmp hpp
  have hs : (Real.sqrt (2/Real.pi))^2 * Real.pi = 2 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have ht : Real.exp (-2) = Real.exp (-1)^2 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num
  have sm : Real.sin ((-1/2:ℝ)*Real.pi) = -1 := by
    rw [show ((-1/2:ℝ))*Real.pi = -(Real.pi/2) by ring, Real.sin_neg,
      Real.sin_pi_div_two]
  have sp : Real.sin ((1/2:ℝ)*Real.pi) = 1 := by
    rw [show (1/2:ℝ)*Real.pi = Real.pi/2 by ring, Real.sin_pi_div_two]
  have spp : Real.sin ((3/2:ℝ)*Real.pi) = -1 := by
    rw [show (3/2:ℝ)*Real.pi = Real.pi/2+Real.pi by ring, Real.sin_add_pi,
      Real.sin_pi_div_two]
  dsimp [P, besselK]
  simp only [neg_div, neg_neg] at hm hp hmp hpp sm ⊢
  rw [hm, hp, hmp, hpp, sm, sp, spp]
  simp only [Real.cosh_eq, Real.sinh_eq]
  rw [ht]
  constructor
  · linear_combination (Real.exp 1 + Real.exp (-1))*Real.exp (-1)/4 * hs + he/2
  constructor
  · linear_combination (Real.exp 1 - Real.exp (-1))*Real.exp (-1)/4 * hs + he/2
  · linear_combination Real.exp (-1)^2 * hs

private lemma exp_bound : 0 < Real.exp (-2) ∧ Real.exp (-2) < 1/7 := by
  constructor
  · positivity
  have he : (8/3:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have ht : Real.exp (-2) = 1 / (Real.exp 1)^2 := by
    rw [show (-2:ℝ) = -(1+1) by norm_num, Real.exp_neg, Real.exp_add]
    simp [one_div, pow_two]
  rw [ht]
  apply (div_lt_iff₀ (by positivity : 0 < (Real.exp 1)^2)).2
  nlinarith [Real.exp_pos 1]

private lemma witness :
    P 1 ((-1/2:ℝ)) * P 1 (3/2) < P 1 (1/2)^2 := by
  obtain ⟨hm,hp,hpp⟩ := product_values
  rw [hm,hp,hpp]
  obtain ⟨ht0,ht1⟩ := exp_bound
  nlinarith [mul_nonneg ht0.le (show 0 ≤ 1/7 - Real.exp (-2) by linarith)]

lemma half_noninteger (k : ℤ) : ∀ n : ℤ, (k:ℝ)+1/2 ≠ (n:ℝ) := by
  intro n hn
  have hh : ((2*k+1:ℤ):ℝ) = ((2*n:ℤ):ℝ) := by push_cast; linarith
  have hi : 2*k+1 = 2*n := Int.cast_inj.mp hh
  omega

theorem result : ¬ claim := by
  intro hc
  have h := hc 1 (by norm_num) ((-1/2:ℝ)) 1 (by norm_num) (by norm_num)
    (by convert half_noninteger (-1) using 1 <;> norm_num)
    (by convert half_noninteger 0 using 1 <;> norm_num)
    (by convert half_noninteger 1 using 1 <;> norm_num)
  norm_num at h
  exact (not_lt_of_ge h) (by simpa only [neg_div] using witness)

end D5.S3.Analytic.BesselProductOrderLogConvexity.Result
