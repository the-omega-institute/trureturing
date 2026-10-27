import D5.S3.Weil.ZetaGamma.FormCore.ThetaFourthPerturbationCheck
import D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck
import Mathlib.Tactic
noncomputable section
/- Uncompiled continuation after the finite certificate, complete quadratic
   tail supplier, and fourth-numerator perturbation fragment.
   Add GaussianGammaDomainCheck to the import block for the final actual-jet
   bridge. The ordinary Phi-derivative corollary is restricted to x > 0. -/

namespace RhTransient.ThetaLogFourthCertificate

open Real
open D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open private tailJet_summable_ray from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private fullJet fullJet_eq_phi_derivative from
  D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck

def fullNormalizedJet (k : ℕ) (y : ℝ) : ℝ :=
  twoModeJet k y (exp (-3*y)) + normalizedTail k y

def fullNormalizedNumerator (y : ℝ) : ℝ :=
  fourthNumerator (fullNormalizedJet 0 y) (fullNormalizedJet 1 y)
    (fullNormalizedJet 2 y) (fullNormalizedJet 3 y) (fullNormalizedJet 4 y)

theorem twoModeJet_abs_le (k : ℕ) (hk : k ≤ 4) {y : ℝ} (hy : 3 ≤ y) :
    |twoModeJet k y (exp (-3*y))| ≤ frontBudget k*y^(k+2) := by
  have hy0 : 0 ≤ y := by linarith
  have h4y : 3 ≤ 4*y := by linarith
  have ht : exp (-3*y) ≤ 1/8000 :=
    (exp_le_exp.mpr (by linarith : -3*y ≤ (-9:ℝ))).trans exp_neg_nine_le
  calc
    _ ≤ |P k y|+|exp (-3*y)*P k (4*y)| := abs_add_le _ _
    _ = |P k y|+exp (-3*y)*|P k (4*y)| := by
      rw [abs_mul, abs_of_pos (exp_pos _)]
    _ ≤ (2:ℝ)^(k+2)*y^(k+2)+(1/8000)*((2:ℝ)^(k+2)*(4*y)^(k+2)) := by
      apply add_le_add (P_abs_le k hk hy)
      exact mul_le_mul ht (P_abs_le k hk h4y) (abs_nonneg _) (by norm_num)
    _ = _ := by dsimp [frontBudget]; rw [mul_pow]; ring

theorem tail_exp_le {y : ℝ} (hy : 3 ≤ y) :
    exp (-8*y) ≤ 1/tailExponentialDenominator := by
  have h3 : exp (-3:ℝ) ≤ 1/20 := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 20)
      exp_three_gt_twenty.le
  calc
    _ ≤ exp (-24:ℝ) := exp_le_exp.mpr (by linarith)
    _ = (exp (-3:ℝ))^8 := by rw [← exp_nat_mul]; norm_num
    _ ≤ (1/20:ℝ)^8 := pow_le_pow_left₀ (exp_nonneg _) h3 8
    _ = _ := by norm_num [tailExponentialDenominator]

theorem weighted_tail_exp_le {y : ℝ} (hy : 3 ≤ y) :
    y^3*exp (-8*y) ≤ 27/tailExponentialDenominator := by
  let z := y-3
  have hz : 0 ≤ z := sub_nonneg.mpr hy
  have hy0 : 0 ≤ y := by linarith
  have hyb : y ≤ 3*exp (z/3) := by
    have h := add_one_le_exp (z/3)
    dsimp [z] at h ⊢
    linarith
  have hy3 : y^3 ≤ 27*exp z := by
    calc
      _ ≤ (3*exp (z/3))^3 := pow_le_pow_left₀ hy0 hyb 3
      _ = _ := by
        have he : (exp (z/3))^3 = exp z := by
          rw [← exp_nat_mul]
          congr 1
          ring
        rw [mul_pow, he]
        norm_num
  have hdec : exp (z-8*y) ≤ exp (-24:ℝ) := by
    apply exp_le_exp.mpr
    dsimp [z]
    linarith
  calc
    _ ≤ (27*exp z)*exp (-8*y) :=
      mul_le_mul_of_nonneg_right hy3 (exp_nonneg _)
    _ = 27*exp (z-8*y) := by rw [mul_assoc, ← exp_add]; congr 1; ring
    _ ≤ 27*exp (-24:ℝ) := mul_le_mul_of_nonneg_left hdec (by norm_num)
    _ ≤ 27*(1/tailExponentialDenominator) :=
      mul_le_mul_of_nonneg_left (by convert tail_exp_le (y := 3) (by norm_num) using 1 <;> norm_num)
        (by norm_num)
    _ = _ := by ring

theorem firstModeReserve_ge {y : ℝ} (hy : 3 ≤ y) :
    256*y^9 ≤ firstModeReserve y := by
  have hy0 : 0 ≤ y := by linarith
  calc
    _ = 256*y^5*y^4 := by ring
    _ ≤ 256*y^5*Q0 y := mul_le_mul_of_nonneg_left (Q0_ge hy) (by positivity)
    _ = _ := rfl

/-- The complete infinite theta tail preserves strict negativity, uniformly
    throughout y >= 3. No frequency or mode is truncated in this statement. -/
theorem fullNormalizedNumerator_negative {y : ℝ} (hy : 3 ≤ y) :
    fullNormalizedNumerator y < 0 := by
  have hy0 : 0 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  let q := exp (-8*y)
  let C := tailExponentialDenominator
  have hC : 0 < C := by norm_num [C,tailExponentialDenominator]
  have hq : 0 ≤ q := exp_nonneg _
  have hqcap : q ≤ 1/C := tail_exp_le hy
  have hCs0 : 0 ≤ C*q := mul_nonneg hC.le hq
  have hCs1 : C*q ≤ 1 := by
    have hCn : C ≠ 0 := ne_of_gt hC
    calc
      _ ≤ C*(1/C) := mul_le_mul_of_nonneg_left hqcap hC.le
      _ = 1 := by field_simp [hCn]
  have ha (k : ℕ) (hk : k ≤ 4) := twoModeJet_abs_le k hk hy
  have hr (k : ℕ) (hk : k ≤ 4) := (normalizedTail_bound k hk hy).2
  have hp := fourthNumerator_perturbation
    (ha 0 (by omega)) (ha 1 (by omega)) (ha 2 (by omega))
    (ha 3 (by omega)) (ha 4 (by omega))
    (hr 0 (by omega)) (hr 1 (by omega)) (hr 2 (by omega))
    (hr 3 (by omega)) (hr 4 (by omega))
  let delta : ℝ :=
    absoluteFourth (frontBudget 0+tailBudget 0*q) (frontBudget 1+tailBudget 1*q)
      (frontBudget 2+tailBudget 2*q) (frontBudget 3+tailBudget 3*q)
      (frontBudget 4+tailBudget 4*q) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4)
  have hp' : |fullNormalizedNumerator y-twoModeNumerator y (exp (-3*y))| ≤
      y^12*delta := by
    calc
      _ ≤ _ := hp
      _ = _ := by
        dsimp [delta,q,absoluteFourth]
        ring
  have hdelta : delta ≤ C*q/2 := by
    have h := scaled_rational_perturbation hCs0 hCs1
    convert h using 1 <;>
      dsimp [delta,C,tailExponentialDenominator] <;> norm_num <;> ring
  have hweighted : y^3*q ≤ 27/C := weighted_tail_exp_le hy
  have herror : y^12*delta ≤ (27/512:ℝ)*firstModeReserve y := by
    calc
      _ ≤ y^12*(C*q/2) := mul_le_mul_of_nonneg_left hdelta (by positivity)
      _ = (y^9*C/2)*(y^3*q) := by ring
      _ ≤ (y^9*C/2)*(27/C) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ = (27/512:ℝ)*(256*y^9) := by
        dsimp [C,tailExponentialDenominator]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (firstModeReserve_ge hy) (by norm_num)
  have hreserve : 0 < firstModeReserve y :=
    (show 0 < 256*y^9 by positivity).trans_le (firstModeReserve_ge hy)
  have hfront := twoMode_actual_bound hy
  have hdiff := (le_abs_self
    (fullNormalizedNumerator y-twoModeNumerator y (exp (-3*y)))).trans hp'
  have hfull : fullNormalizedNumerator y ≤
      -(12623/64000:ℝ)*firstModeReserve y := by
    linarith
  exact hfull.trans_lt (mul_neg_of_neg_of_pos (by norm_num) hreserve)

/-- Exact normalization of an individual physical primal jet. -/
theorem actual_primalJet_normalized (k : ℕ) (hk : k ≤ 4) (n : ℕ) (x : ℝ) :
    let y : ℝ := Real.pi*exp (2*x)
    primalJet k n x = exp (x/2-y)*
      (P k ((n:ℝ)^2*y)*exp (-(((n:ℝ)^2-1)*y))) := by
  dsimp only
  rw [primalJet, ← P_eq_jetPolynomial k hk]
  dsimp [modeScale]
  have he : exp (x/2)*exp (-(Real.pi*(n:ℝ)^2)*exp (2*x)) =
      exp (x/2-Real.pi*exp (2*x))*
        exp (-(((n:ℝ)^2-1)*(Real.pi*exp (2*x)))) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have harg : Real.pi*(n:ℝ)^2*exp (2*x) =
      (n:ℝ)^2*(Real.pi*exp (2*x)) := by ring
  rw [he,harg]
  ring

theorem actual_fullJet_normalized (k : ℕ) (hk : k ≤ 4) {x : ℝ} (hx : 0 ≤ x) :
    let y : ℝ := Real.pi*exp (2*x)
    fullJet k x = exp (x/2-y)*fullNormalizedJet k y := by
  dsimp only
  have hs := tailJet_summable_ray k 1 (by omega) hx
  have hsplit : tailJet k 1 x = primalJet k 2 x+tailJet k 2 x := by
    calc
      _ = primalJet k (1+0+1) x+
          ∑' j : ℕ, primalJet k (1+(j+1)+1) x := hs.tsum_eq_zero_add
      _ = _ := by
        congr 1
        apply tsum_congr
        intro j
        congr 1
        omega
  rw [fullJet,hsplit,actual_tailJet_normalized k hk,
    actual_primalJet_normalized k hk 1,actual_primalJet_normalized k hk 2]
  norm_num only [Nat.cast_one,one_pow,one_mul,sub_self,zero_mul,neg_zero,
    exp_zero,mul_one,Nat.cast_ofNat,show (2:ℝ)^2=4 by norm_num]
  dsimp [fullNormalizedJet,twoModeJet]
  ring

/-- Strict negativity of the literal full-theta fourth-log numerator.
    These are actual jets, including every positive integer mode. -/
theorem actual_fullJet_fourthNumerator_negative {x : ℝ} (hx : 0 ≤ x) :
    fourthNumerator (fullJet 0 x) (fullJet 1 x) (fullJet 2 x)
      (fullJet 3 x) (fullJet 4 x) < 0 := by
  let y := Real.pi*exp (2*x)
  have hy : 3 ≤ y := by
    have he : 1 ≤ exp (2*x) := one_le_exp (by linarith)
    dsimp [y]
    nlinarith [Real.pi_gt_three]
  rw [actual_fullJet_normalized 0 (by omega) hx,
    actual_fullJet_normalized 1 (by omega) hx,
    actual_fullJet_normalized 2 (by omega) hx,
    actual_fullJet_normalized 3 (by omega) hx,
    actual_fullJet_normalized 4 (by omega) hx]
  have heq :
      fourthNumerator (exp (x/2-y)*fullNormalizedJet 0 y)
        (exp (x/2-y)*fullNormalizedJet 1 y)
        (exp (x/2-y)*fullNormalizedJet 2 y)
        (exp (x/2-y)*fullNormalizedJet 3 y)
        (exp (x/2-y)*fullNormalizedJet 4 y) =
      (exp (x/2-y))^4*fullNormalizedNumerator y := by
    dsimp [fourthNumerator,fullNormalizedNumerator]
    ring
  change fourthNumerator _ _ _ _ _ < 0
  rw [heq]
  exact mul_neg_of_pos_of_neg (pow_pos (exp_pos _) 4)
    (fullNormalizedNumerator_negative hy)

/-- The actual ordinary derivatives of Romik's original kernel, on the
    open positive ray where the accepted derivative-identity supplier applies. -/
theorem actual_phi_fourthNumerator_negative {x : ℝ} (hx : 0 < x) :
    fourthNumerator (romikPhi x) (iteratedDeriv 1 romikPhi x)
      (iteratedDeriv 2 romikPhi x) (iteratedDeriv 3 romikPhi x)
      (iteratedDeriv 4 romikPhi x) < 0 := by
  have h := actual_fullJet_fourthNumerator_negative hx.le
  rw [fullJet_eq_phi_derivative 0 hx,fullJet_eq_phi_derivative 1 hx,
    fullJet_eq_phi_derivative 2 hx,fullJet_eq_phi_derivative 3 hx,
    fullJet_eq_phi_derivative 4 hx] at h
  simpa only [iteratedDeriv_zero] using h

end RhTransient.ThetaLogFourthCertificate

#print axioms RhTransient.ThetaLogFourthCertificate.actual_phi_fourthNumerator_negative
