/- GID: D5/S3/Zeros/Jensen/OriginalPrimalTailProjection
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/OriginalPrimalTailProjection
   mirror-E: none(waiver:universal-infinite-analytic-estimate)
   anchors: []
   utility: none
   digest: Weighted endpoint estimates for the entire original moving primal theta tail. -/

import D5.S3.Analytic.Fourier.ThetaDifferentialKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open Real Set MeasureTheory Filter Polynomial
open scoped Topology
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel

/-- The scale of the actual positive integer mode. -/
def modeScale (m : ℕ) : ℝ := Real.pi * (m : ℝ)^2

/-- The smooth primal mode before its even extension. -/
def primalMode (m : ℕ) (x : ℝ) : ℝ :=
  exp (x / 2) * exp (-modeScale m * exp (2*x)) *
    (4 * (modeScale m)^2 * exp (4*x) - 6 * modeScale m * exp (2*x))

/-- Every omitted positive mode occurs exactly once. -/
def originalTail (N : ℕ) (x : ℝ) : ℝ := ∑' j : ℕ, primalMode (N+j+1) x

/-- The actual origin flux of the full omitted tail. -/
def originalFlux (N : ℕ) : ℝ :=
  ∑' j : ℕ, exp (-modeScale (N+j+1)) *
    (8 * (modeScale (N+j+1))^3 - 30 * (modeScale (N+j+1))^2 +
      15 * modeScale (N+j+1))

/-- Polynomial factors of the successive smooth primal derivatives. -/
def jetPolynomial : ℕ → ℝ[X]
  | 0 => C 4 * X^2 - C 6 * X
  | r+1 => (C (1/2) - C 2 * X) * jetPolynomial r +
      C 2 * X * (jetPolynomial r).derivative

def primalJet (r m : ℕ) (x : ℝ) : ℝ :=
  exp (x/2) * exp (-modeScale m * exp (2*x)) *
    (jetPolynomial r).eval (modeScale m * exp (2*x))

def tailJet (r N : ℕ) (x : ℝ) : ℝ := ∑' j : ℕ, primalJet r (N+j+1) x

private def jetSize (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (r+3), |(jetPolynomial r).coeff k|

private def endpointConstant (a : ℝ) (r p : ℕ) : ℝ :=
  let L : ℝ := 2*(r : ℝ)+9/2+(p : ℝ)
  exp (L + (a/2+L)^2/16)

private theorem jet_degree (r : ℕ) : (jetPolynomial r).natDegree ≤ r+2 := by
  induction r with
  | zero =>
    exact (natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le.trans (by simp))
      (natDegree_mul_le.trans (by simp)))
  | succ r ih =>
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have h : (C (1/2 : ℝ) - C 2 * X).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (max_le (by simp)
          (natDegree_mul_le.trans (by simp)))
      omega
    · apply natDegree_mul_le.trans
      have h : (C (2 : ℝ) * X).natDegree ≤ 1 :=
        natDegree_mul_le.trans (by simp)
      have hd := natDegree_derivative_le (jetPolynomial r)
      omega

private theorem jet_eval_bound (r : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    |(jetPolynomial r).eval y| ≤ jetSize r * y^(r+2) := by
  rw [eval_eq_sum_range' (show (jetPolynomial r).natDegree < r+3 by
    have := jet_degree r; omega)]
  calc
    _ ≤ ∑ k ∈ Finset.range (r+3), |(jetPolynomial r).coeff k * y^k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (r+3), |(jetPolynomial r).coeff k| * y^(r+2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (pow_nonneg (show 0 ≤ y by linarith) _)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy
        (by have := Finset.mem_range.mp hk; omega)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

private theorem primalJet_zero (m : ℕ) (x : ℝ) : primalJet 0 m x = primalMode m x := by
  simp only [primalJet, primalMode, jetPolynomial, eval_sub, eval_mul, eval_C,
    eval_pow, eval_X, mul_pow]
  rw [show exp (4*x) = exp (2*x)^2 by rw [← exp_nat_mul]; congr 1; ring]
  ring

private theorem primalJet_deriv (r m : ℕ) (x : ℝ) :
    HasDerivAt (primalJet r m) (primalJet (r+1) m x) x := by
  have he : HasDerivAt (fun x : ℝ => exp (2*x)) (2*exp (2*x)) x := by
    convert! ((hasDerivAt_id x).const_mul 2).exp using 1 <;> simp <;> ring
  have hy := he.const_mul (modeScale m)
  have hp := ((jetPolynomial r).hasDerivAt (modeScale m * exp (2*x))).comp x hy
  have hh : HasDerivAt (fun x : ℝ => exp (x/2)) (exp (x/2)/2) x := by
    convert! ((hasDerivAt_id x).div_const 2).exp using 1 <;> simp <;> ring
  convert! (hh.mul hy.neg.exp).mul hp using 1 <;>
    (try ext y) <;> simp [primalJet, jetPolynomial, Function.comp_def] <;> ring

private theorem scale_lower {m : ℕ} (hm : 2 ≤ m) : 12 ≤ modeScale m := by
  have hc : (2 : ℝ) ≤ m := by exact_mod_cast hm
  dsimp [modeScale]
  nlinarith [Real.pi_gt_three, mul_nonneg (by nlinarith : 0 ≤ (m : ℝ)^2-4) pi_pos.le]

private theorem quartic_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + (2/3 : ℝ)*x^4 ≤ exp (2*x) := by
  have h := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ 2*x) 5
  norm_num [Finset.sum_range_succ] at h
  nlinarith [pow_nonneg hx 3]

private theorem endpoint_exponent {a A L x : ℝ} (hA : 12 ≤ A)
    (hL : 0 ≤ L) (hx : 0 ≤ x) :
    a*x^2/2 + L*x - A*(exp (2*x)-1) ≤
      L+(a/2+L)^2/16-A*x := by
  have he := Real.add_one_le_exp (2*x)
  have hq := quartic_exp hx
  have hs : x ≤ 1+x^2 := by nlinarith [sq_nonneg (x-1/2)]
  have h1 : A*x + 6*(exp (2*x)-1) ≤ A*(exp (2*x)-1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ A-12)
      (by linarith : 0 ≤ exp (2*x)-1-x)]
  have h2 : L*x ≤ L*(1+x^2) := mul_le_mul_of_nonneg_left hs hL
  have h3 := sq_nonneg (2*x^2-(a/2+L)/4)
  nlinarith

private theorem primalJet_endpoint (a : ℝ) (r p m : ℕ) {x : ℝ}
    (hm : 2 ≤ m) (hx : 0 ≤ x) :
    exp (a*x^2/2)*(1+x)^p*|primalJet r m x| ≤
      jetSize r * endpointConstant a r p * (modeScale m)^(r+2) *
        exp (-modeScale m) * exp (-modeScale m*x) := by
  let A := modeScale m
  have hA : 12 ≤ A := scale_lower hm
  have he1 : 1 ≤ exp (2*x) := one_le_exp (by linarith)
  have hy : 1 ≤ A * exp (2*x) := by nlinarith
  have hp : (1+x)^p ≤ exp ((p : ℝ)*x) := by
    calc
      _ ≤ (exp x)^p := pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp x) p
      _ = _ := (Real.exp_nat_mul x p).symm
  have hsz : 0 ≤ jetSize r := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  rw [primalJet, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
  calc
    _ ≤ exp (a*x^2/2)*exp ((p : ℝ)*x) *
        (exp (x/2)*exp (-A*exp (2*x))*(jetSize r*(A*exp (2*x))^(r+2))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hp (exp_pos _).le
      · exact mul_le_mul_of_nonneg_left (jet_eval_bound r hy) (by positivity)
      · positivity
      · positivity
    _ = jetSize r*A^(r+2)*exp (-A)*
        exp (a*x^2/2+(2*(r : ℝ)+9/2+(p : ℝ))*x-A*(exp (2*x)-1)) := by
      rw [mul_pow]
      have he : exp (a*x^2/2)*exp ((p : ℝ)*x)*exp (x/2)*
          exp (-A*exp (2*x))*exp (2*x)^(r+2) =
          exp (-A)*exp (a*x^2/2+(2*(r : ℝ)+9/2+(p : ℝ))*x-A*(exp (2*x)-1)) := by
        rw [← exp_nat_mul]
        simp only [← exp_add]
        congr 1
        push_cast
        ring
      linear_combination (jetSize r*A^(r+2))*he
    _ ≤ jetSize r*A^(r+2)*exp (-A)*
        exp (2*(r : ℝ)+9/2+(p : ℝ)+(a/2+(2*(r : ℝ)+9/2+(p : ℝ)))^2/16-A*x) := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr
        (endpoint_exponent hA (by positivity) hx)) (by positivity)
    _ = _ := by
      have he : exp (2*(r : ℝ)+9/2+(p : ℝ)+
          (a/2+(2*(r : ℝ)+9/2+(p : ℝ)))^2/16-A*x) =
          endpointConstant a r p * exp (-A*x) := by
        dsimp [endpointConstant]
        rw [exp_sub, div_eq_mul_inv, ← exp_neg]
        congr 1
        ring
      rw [he]
      dsimp [A]
      ring

private def shiftedBudget (k : ℕ) : ℝ :=
  ∑' j : ℕ, ((j+1 : ℕ) : ℝ)^(2*k) * exp (-Real.pi*(j : ℝ))

private theorem shifted_summable (k : ℕ) :
    Summable (fun j : ℕ => ((j+1 : ℕ) : ℝ)^(2*k) * exp (-Real.pi*(j : ℝ))) := by
  have hs := (Real.summable_pow_mul_exp_neg_nat_mul (2*k) pi_pos).comp_injective
    Nat.succ_injective
  convert! hs.mul_left (exp Real.pi) using 1
  ext j
  simp only [Function.comp_def, Nat.succ_eq_add_one]
  rw [show exp (-Real.pi*(j : ℝ)) = exp Real.pi * exp (-Real.pi*((j+1 : ℕ) : ℝ)) by
    rw [← exp_add]; congr 1; push_cast; ring]
  ring

private theorem scale_summable (N k : ℕ) :
    Summable (fun j : ℕ => (modeScale (N+j+1))^k * exp (-modeScale (N+j+1))) := by
  have hs := (thetaSeries_summable (2*k) (show (0 : ℝ) < 1 by norm_num)).comp_injective
    (show Function.Injective (fun j : ℕ => N+j) from by intro i j hij; dsimp at hij; omega)
  convert! hs.mul_left (Real.pi^k) using 1
  ext j
  simp only [Function.comp_def, modeScale, Nat.cast_add, Nat.cast_one, mul_one, mul_pow,
    ← pow_mul]
  ring

private theorem shifted_comparison {N : ℕ} (hN : 1 ≤ N) (k j : ℕ) :
    (modeScale (N+j+1))^k * exp (-modeScale (N+j+1)) ≤
      (modeScale (N+1))^k * exp (-modeScale (N+1)) *
        (((j+1 : ℕ) : ℝ)^(2*k) * exp (-Real.pi*(j : ℝ))) := by
  let M : ℝ := ((N+1 : ℕ) : ℝ)
  let z : ℝ := (j : ℝ)
  have hM : 2 ≤ M := by dsimp [M]; exact_mod_cast (show 2 ≤ N+1 by omega)
  have hz : 0 ≤ z := Nat.cast_nonneg _
  have hm : ((N+j+1 : ℕ) : ℝ) = M+z := by dsimp [M,z]; push_cast; ring
  have hmle : M+z ≤ M*(z+1) := by nlinarith
  have hscale : modeScale (N+j+1) ≤ modeScale (N+1)*(z+1)^2 := by
    simp only [modeScale, hm]
    change Real.pi*(M+z)^2 ≤ Real.pi*M^2*(z+1)^2
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ M+z) hmle 2
    nlinarith [mul_le_mul_of_nonneg_left hh pi_pos.le]
  have hex : exp (-modeScale (N+j+1)) ≤ exp (-modeScale (N+1))*exp (-Real.pi*z) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    simp only [modeScale, hm]
    change -(Real.pi*(M+z)^2) ≤ -(Real.pi*M^2)+-Real.pi*z
    nlinarith [mul_nonneg pi_pos.le (sq_nonneg z),
      mul_nonneg pi_pos.le (mul_nonneg (by linarith : 0 ≤ 2*M-1) hz)]
  calc
    _ ≤ (modeScale (N+1)*(z+1)^2)^k *
        (exp (-modeScale (N+1))*exp (-Real.pi*z)) :=
      mul_le_mul (pow_le_pow_left₀ (by dsimp [modeScale]; positivity) hscale k)
        hex (exp_pos _).le (by dsimp [modeScale]; positivity)
    _ = _ := by simp only [mul_pow, ← pow_mul]; dsimp [z]; push_cast; ring

private theorem full_shifted_comparison {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    (∑' j : ℕ, (modeScale (N+j+1))^k * exp (-modeScale (N+j+1))) ≤
      (modeScale (N+1))^k * exp (-modeScale (N+1)) * shiftedBudget k := by
  rw [shiftedBudget, ← tsum_mul_left]
  exact (scale_summable N k).tsum_le_tsum (shifted_comparison hN k)
    ((shifted_summable k).mul_left _)

private theorem flux_term_lower {m : ℕ} (hm : 2 ≤ m) :
    5*(modeScale m)^3*exp (-modeScale m) ≤
      exp (-modeScale m)*(8*(modeScale m)^3-30*(modeScale m)^2+15*modeScale m) := by
  have h := scale_lower hm
  have hp : 0 ≤ (modeScale m)^2*(3*modeScale m-30)+15*modeScale m :=
    add_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
  nlinarith [mul_nonneg hp (exp_pos (-modeScale m)).le]

private theorem flux_summable (N : ℕ) : Summable (fun j : ℕ =>
    exp (-modeScale (N+j+1))*(8*(modeScale (N+j+1))^3-
      30*(modeScale (N+j+1))^2+15*modeScale (N+j+1))) := by
  convert! ((scale_summable N 3).mul_left 8).sub
    ((scale_summable N 2).mul_left 30) |>.add ((scale_summable N 1).mul_left 15) using 1
  ext j
  simp only [pow_one]
  ring

private theorem flux_lower {N : ℕ} (hN : 1 ≤ N) :
    5*(modeScale (N+1))^3*exp (-modeScale (N+1)) ≤ originalFlux N := by
  apply (flux_term_lower (show 2 ≤ N+1 by omega)).trans
  simpa only [Nat.add_zero, originalFlux] using (flux_summable N).le_tsum 0
    (fun j _ => (by
      have h := flux_term_lower (show 2 ≤ N+j+1 by omega)
      exact le_trans (show (0 : ℝ) ≤ 5*(modeScale (N+j+1))^3*
        exp (-modeScale (N+j+1)) by
          have := scale_lower (show 2 ≤ N+j+1 by omega); positivity) h))

private theorem tailJet_summable_ray (r N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun j : ℕ => primalJet r (N+j+1) x) := by
  apply ((scale_summable N (r+2)).mul_left
    (jetSize r * endpointConstant 0 r 0)).of_norm_bounded
  intro j
  have h := primalJet_endpoint 0 r 0 (N+j+1) (by omega) hx
  norm_num only [zero_mul, zero_div, exp_zero, pow_zero, mul_one, one_mul] at h
  have hex : exp (-modeScale (N+j+1)*x) ≤ 1 := exp_le_one_iff.mpr (by
    have := scale_lower (show 2 ≤ N+j+1 by omega); nlinarith)
  rw [Real.norm_eq_abs]
  apply h.trans
  calc
    _ ≤ jetSize r * endpointConstant 0 r 0 * (modeScale (N+j+1))^(r+2) *
        exp (-modeScale (N+j+1)) := mul_le_of_le_one_right (by
          dsimp [jetSize,endpointConstant,modeScale]; positivity) hex
    _ = _ := by ring

private theorem tailJet_endpoint (a : ℝ) (r p N : ℕ) (hN : 1 ≤ N) {x : ℝ}
    (hx : 0 ≤ x) :
    exp (a*x^2/2)*(1+x)^p*|tailJet r N x| ≤
      jetSize r * endpointConstant a r p *
        (modeScale (N+1))^(r+2) * exp (-modeScale (N+1)) *
          shiftedBudget (r+2) * exp (-modeScale (N+1)*x) := by
  let u := exp (a*x^2/2)*(1+x)^p
  have hu : 0 < u := by dsimp [u]; positivity
  have hs := tailJet_summable_ray r N hN hx
  have habs : Summable (fun j : ℕ => |primalJet r (N+j+1) x|) := hs.abs
  have hterm (j : ℕ) : u*|primalJet r (N+j+1) x| ≤
      (jetSize r * endpointConstant a r p * exp (-modeScale (N+1)*x)) *
        ((modeScale (N+j+1))^(r+2) * exp (-modeScale (N+j+1))) := by
    apply (primalJet_endpoint a r p (N+j+1) (by omega) hx).trans
    have hm : modeScale (N+1) ≤ modeScale (N+j+1) := by
      dsimp [modeScale]
      have hcast : ((N+1 : ℕ) : ℝ) ≤ ((N+j+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N+1 ≤ N+j+1)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcast 2) pi_pos.le
    have he : exp (-modeScale (N+j+1)*x) ≤ exp (-modeScale (N+1)*x) :=
      exp_le_exp.mpr (by nlinarith)
    calc
      _ ≤ jetSize r * endpointConstant a r p * (modeScale (N+j+1))^(r+2) *
          exp (-modeScale (N+j+1)) * exp (-modeScale (N+1)*x) :=
        mul_le_mul_of_nonneg_left he (by dsimp [jetSize,endpointConstant,modeScale]; positivity)
      _ = _ := by ring
  have hn : |tailJet r N x| ≤ ∑' j : ℕ, |primalJet r (N+j+1) x| := by
    simpa [tailJet, Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := fun j : ℕ => primalJet r (N+j+1) x)
        (by simpa only [Real.norm_eq_abs] using habs))
  calc
    _ ≤ u * ∑' j : ℕ, |primalJet r (N+j+1) x| :=
      mul_le_mul_of_nonneg_left hn hu.le
    _ ≤ (jetSize r * endpointConstant a r p * exp (-modeScale (N+1)*x)) *
        ∑' j : ℕ, (modeScale (N+j+1))^(r+2)*exp (-modeScale (N+j+1)) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact (habs.mul_left u).tsum_le_tsum hterm ((scale_summable N (r+2)).mul_left _)
    _ ≤ (jetSize r * endpointConstant a r p * exp (-modeScale (N+1)*x)) *
        ((modeScale (N+1))^(r+2)*exp (-modeScale (N+1))*shiftedBudget (r+2)) :=
      mul_le_mul_of_nonneg_left (full_shifted_comparison hN _) (by
        dsimp [jetSize,endpointConstant]; positivity)
    _ = _ := by ring

private theorem jet_eval_bound_upper (r : ℕ) {y z : ℝ}
    (hy : 0 ≤ y) (hyz : y ≤ z) (hz : 1 ≤ z) :
    |(jetPolynomial r).eval y| ≤ jetSize r * z^(r+2) := by
  rw [eval_eq_sum_range' (show (jetPolynomial r).natDegree < r+3 by
    have := jet_degree r; omega)]
  calc
    _ ≤ ∑ k ∈ Finset.range (r+3), |(jetPolynomial r).coeff k * y^k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (r+3), |(jetPolynomial r).coeff k| * z^(r+2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (pow_nonneg hy _)]
      exact mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ hy hyz k).trans (pow_le_pow_right₀ hz
          (by have := Finset.mem_range.mp hk; omega))) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

private theorem scale_parameter_summable (N k : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℕ => (modeScale (N+j+1))^k * exp (-modeScale (N+j+1)*t)) := by
  have hs := (thetaSeries_summable (2*k) ht).comp_injective
    (show Function.Injective (fun j : ℕ => N+j) from by
      intro i j hij; dsimp at hij; omega)
  convert! hs.mul_left (Real.pi^k) using 1
  ext j
  simp only [Function.comp_def, modeScale, Nat.cast_add, Nat.cast_one, mul_pow,
    ← pow_mul]
  ring

private theorem primalJet_compact_bound (r m : ℕ) (hm : 2 ≤ m) {R x : ℝ}
    (hR : 1 ≤ R) (hx : x ∈ Ioo (-R) R) :
    ‖primalJet r m x‖ ≤
      (exp (R/2)*jetSize r*exp (2*R)^(r+2)) *
        ((modeScale m)^(r+2)*exp (-modeScale m*exp (-2*R))) := by
  have hA := scale_lower hm
  have he := exp_le_exp.mpr (show 2*x ≤ 2*R by linarith [hx.2])
  have hyz : modeScale m*exp (2*x) ≤ modeScale m*exp (2*R) :=
    mul_le_mul_of_nonneg_left he (by linarith)
  have hz : 1 ≤ modeScale m*exp (2*R) := by
    have he1 := one_le_exp (show 0 ≤ 2*R by linarith)
    nlinarith
  have hf := jet_eval_bound_upper r (by positivity) hyz hz
  have hhalf : exp (x/2) ≤ exp (R/2) := exp_le_exp.mpr (by linarith [hx.2])
  have hdecay : exp (-modeScale m*exp (2*x)) ≤
      exp (-modeScale m*exp (-2*R)) := by
    apply exp_le_exp.mpr
    have hl := exp_le_exp.mpr (show -2*R ≤ 2*x by linarith [hx.1])
    nlinarith
  rw [Real.norm_eq_abs, primalJet, abs_mul, abs_mul,
    abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
  calc
    _ ≤ (exp (R/2)*exp (-modeScale m*exp (-2*R))) *
        (jetSize r*(modeScale m*exp (2*R))^(r+2)) :=
      mul_le_mul (mul_le_mul hhalf hdecay (exp_pos _).le (exp_pos _).le)
        hf (abs_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

private theorem tailJet_deriv (r N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    HasDerivAt (tailJet r N) (tailJet (r+1) N x) x := by
  let R := |x|+1
  let c := exp (R/2)*jetSize (r+1)*exp (2*R)^((r+1)+2)
  have hR : 1 ≤ R := by dsimp [R]; have := abs_nonneg x; linarith
  have hs := (scale_parameter_summable N ((r+1)+2) (exp_pos (-2*R))).mul_left c
  have hx : x ∈ Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := by constructor <;> linarith
  exact hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun j y _ => primalJet_deriv r (N+j+1) y)
    (fun j y hy => primalJet_compact_bound (r+1) (N+j+1) (by omega) hR hy)
    hzero (tailJet_summable_ray r N hN (le_refl 0)) hx

private theorem tailJet_continuous (r N : ℕ) (hN : 1 ≤ N) : Continuous (tailJet r N) :=
  continuous_iff_continuousAt.mpr (fun x => (tailJet_deriv r N hN x).continuousAt)

private theorem tailJet_eq_iterated (r N : ℕ) (hN : 1 ≤ N) :
    tailJet r N = iteratedDeriv r (originalTail N) := by
  induction r with
  | zero =>
    ext x
    simp only [iteratedDeriv_zero, originalTail, tailJet]
    exact tsum_congr (fun j => primalJet_zero (N+j+1) x)
  | succ r ih =>
    rw [iteratedDeriv_succ, ← ih]
    exact funext (fun x => (tailJet_deriv r N hN x).deriv.symm)

private theorem tail_smooth (N : ℕ) (hN : 1 ≤ N) : ContDiff ℝ 4 (originalTail N) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro r _
    rw [← tailJet_eq_iterated r N hN]
    exact tailJet_continuous r N hN
  · intro r _
    rw [← tailJet_eq_iterated r N hN]
    exact fun x => (tailJet_deriv r N hN x).differentiableAt

private def rayBudget (a : ℝ) (r p : ℕ) : ℝ :=
  jetSize r * endpointConstant a r p * shiftedBudget (r+2)

private theorem tailJet_integral (a : ℝ) (r p N : ℕ) (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => exp (a*x^2/2)*(1+x)^p*|tailJet r N x|) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), exp (a*x^2/2)*(1+x)^p*|tailJet r N x|) ≤
      rayBudget a r p * (modeScale (N+1))^(r+1) * exp (-modeScale (N+1)) := by
  let A := modeScale (N+1)
  let c := rayBudget a r p*A^(r+2)*exp (-A)
  have hA : 12 ≤ A := scale_lower (by omega)
  have hc : 0 ≤ c := by dsimp [c,rayBudget,jetSize,endpointConstant,shiftedBudget]; positivity
  have hi : IntegrableOn (fun x : ℝ => c*exp (-A*x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -A < 0 by linarith) 0).const_mul c
  have hcont : Continuous (fun x : ℝ => exp (a*x^2/2)*(1+x)^p*|tailJet r N x|) := by
    have hw : Continuous (fun x : ℝ => exp (a*x^2/2)*(1+x)^p) := by fun_prop
    exact hw.mul (tailJet_continuous r N hN).abs
  have hbound : ∀ x ∈ Ioi (0 : ℝ),
      exp (a*x^2/2)*(1+x)^p*|tailJet r N x| ≤ c*exp (-A*x) := by
    intro x hx
    simpa [c,A,rayBudget, mul_assoc, mul_left_comm, mul_comm] using
      tailJet_endpoint a r p N hN (le_of_lt hx)
  have hfi : IntegrableOn (fun x : ℝ => exp (a*x^2/2)*(1+x)^p*|tailJet r N x|)
      (Ioi 0) := by
    apply hi.mono' hcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound x hx
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), c*exp (-A*x) := integral_mono_ae hfi hi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hbound x hx)
    _ = c/A := by rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]; simp [div_eq_mul_inv]
    _ = _ := by
      change c/A = rayBudget a r p*A^(r+1)*exp (-A)
      dsimp [c]
      rw [show r+2=(r+1)+1 by omega, pow_succ]
      field_simp [show A ≠ 0 by linarith]

/-- The unchanged spatial density adjoint on a smooth primal function. -/
def densityAdjoint (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x + α*(f x+x*deriv f x)

private theorem adjoint_formula (N : ℕ) (hN : 1 ≤ N) (α x : ℝ) :
    densityAdjoint α (originalTail N) x =
      tailJet 2 N x+α*(tailJet 0 N x+x*tailJet 1 N x) := by
  have h0 : tailJet 0 N = originalTail N := by simpa using tailJet_eq_iterated 0 N hN
  have h1 : deriv (originalTail N) = tailJet 1 N := by
    rw [← h0]
    exact funext (fun y => (tailJet_deriv 0 N hN y).deriv)
  have h2 : deriv (deriv (originalTail N)) = tailJet 2 N := by
    rw [h1]
    exact funext (fun y => (tailJet_deriv 1 N hN y).deriv)
  rw [densityAdjoint, h2, h1, ← h0]

private theorem adjoint_deriv (N : ℕ) (hN : 1 ≤ N) (α x : ℝ) :
    HasDerivAt (densityAdjoint α (originalTail N))
      (tailJet 3 N x+α*(2*tailJet 1 N x+x*tailJet 2 N x)) x := by
  have h := (tailJet_deriv 2 N hN x).add
    (((tailJet_deriv 0 N hN x).add ((hasDerivAt_id x).mul
      (tailJet_deriv 1 N hN x))).const_mul α)
  convert! h using 1
  · ext y
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    exact adjoint_formula N hN α y
  · simp only [id_eq]
    ring

private theorem adjoint_second_deriv (N : ℕ) (hN : 1 ≤ N) (α x : ℝ) :
    HasDerivAt (deriv (densityAdjoint α (originalTail N)))
      (tailJet 4 N x+α*(3*tailJet 2 N x+x*tailJet 3 N x)) x := by
  have h := (tailJet_deriv 3 N hN x).add
    ((((tailJet_deriv 1 N hN x).const_mul 2).add
      ((hasDerivAt_id x).mul (tailJet_deriv 2 N hN x))).const_mul α)
  convert! h using 1
  · ext y
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    exact (adjoint_deriv N hN α y).deriv
  · simp only [id_eq]
    ring

private theorem adjoint_square (N : ℕ) (hN : 1 ≤ N) (α x : ℝ) :
    densityAdjoint α (densityAdjoint α (originalTail N)) x =
      tailJet 4 N x+2*α*x*tailJet 3 N x+(4*α+α^2*x^2)*tailJet 2 N x+
        3*α^2*x*tailJet 1 N x+α^2*tailJet 0 N x := by
  rw [densityAdjoint, (adjoint_second_deriv N hN α x).deriv,
    (adjoint_deriv N hN α x).deriv, adjoint_formula N hN α x]
  ring

private theorem flux_eq (N : ℕ) (hN : 1 ≤ N) :
    originalFlux N = -deriv (originalTail N) 0 := by
  have h0 : tailJet 0 N = originalTail N := by simpa using tailJet_eq_iterated 0 N hN
  rw [originalFlux, ← h0, (tailJet_deriv 0 N hN 0).deriv, tailJet, ← tsum_neg]
  apply tsum_congr
  intro j
  norm_num [primalJet, jetPolynomial]
  ring

private def adjointCoefficient (a : ℝ) : ℝ := 1+6*a+5*a^2

private theorem adjoint_bound (N : ℕ) (hN : 1 ≤ N) {a α x : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (hαa : α ≤ a) (hx : 0 ≤ x) :
    |densityAdjoint α (densityAdjoint α (originalTail N)) x| ≤
      adjointCoefficient a * ∑ r ∈ Finset.range 5, (1+x)^2*|tailJet r N x| := by
  rw [adjoint_square N hN α x]
  have ht : |tailJet 4 N x+2*α*x*tailJet 3 N x+(4*α+α^2*x^2)*tailJet 2 N x+
        3*α^2*x*tailJet 1 N x+α^2*tailJet 0 N x| ≤
      |tailJet 4 N x|+|2*α*x*tailJet 3 N x|+|(4*α+α^2*x^2)*tailJet 2 N x|+
        |3*α^2*x*tailJet 1 N x|+|α^2*tailJet 0 N x| := by
    have h1 := abs_add_le (tailJet 4 N x) (2*α*x*tailJet 3 N x)
    have h2 := abs_add_le (tailJet 4 N x+2*α*x*tailJet 3 N x)
      ((4*α+α^2*x^2)*tailJet 2 N x)
    have h3 := abs_add_le (tailJet 4 N x+2*α*x*tailJet 3 N x+
      (4*α+α^2*x^2)*tailJet 2 N x) (3*α^2*x*tailJet 1 N x)
    have h4 := abs_add_le (tailJet 4 N x+2*α*x*tailJet 3 N x+
      (4*α+α^2*x^2)*tailJet 2 N x+3*α^2*x*tailJet 1 N x) (α^2*tailJet 0 N x)
    linarith
  have hsq : α^2 ≤ a^2 := pow_le_pow_left₀ hα hαa 2
  have hw : 1 ≤ (1+x)^2 := by nlinarith
  have hxw : x ≤ (1+x)^2 := by nlinarith
  have hx2w : x^2 ≤ (1+x)^2 := by nlinarith
  have hD : 1 ≤ adjointCoefficient a := by dsimp [adjointCoefficient]; nlinarith [sq_nonneg a]
  have h3 : 2*α*x ≤ adjointCoefficient a*(1+x)^2 := by
    have h := mul_le_mul hαa hxw hx ha
    dsimp [adjointCoefficient]
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (1+x))]
  have h2 : 4*α+α^2*x^2 ≤ adjointCoefficient a*(1+x)^2 := by
    have h := mul_le_mul hsq hx2w (sq_nonneg x) (sq_nonneg a)
    have h' := mul_le_mul_of_nonneg_left hw ha
    dsimp [adjointCoefficient]
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (1+x))]
  have h1 : 3*α^2*x ≤ adjointCoefficient a*(1+x)^2 := by
    have h := mul_le_mul hsq hxw hx (sq_nonneg a)
    dsimp [adjointCoefficient]
    nlinarith [mul_nonneg ha (sq_nonneg (1+x))]
  have hzero : α^2 ≤ adjointCoefficient a*(1+x)^2 := by
    have h := mul_le_mul_of_nonneg_left hw (sq_nonneg a)
    dsimp [adjointCoefficient]
    nlinarith [mul_nonneg ha (sq_nonneg (1+x))]
  apply ht.trans
  simp only [abs_mul, abs_of_nonneg (show 0 ≤ 2*α*x by positivity),
    abs_of_nonneg (show 0 ≤ 4*α+α^2*x^2 by positivity),
    abs_of_nonneg (show 0 ≤ 3*α^2*x by positivity), abs_of_nonneg (sq_nonneg α)]
  have h4 := mul_le_mul_of_nonneg_right (le_trans hD (le_mul_of_one_le_right
    (by linarith : 0 ≤ adjointCoefficient a) hw)) (abs_nonneg (tailJet 4 N x))
  have h3' := mul_le_mul_of_nonneg_right h3 (abs_nonneg (tailJet 3 N x))
  have h2' := mul_le_mul_of_nonneg_right h2 (abs_nonneg (tailJet 2 N x))
  have h1' := mul_le_mul_of_nonneg_right h1 (abs_nonneg (tailJet 1 N x))
  have h0' := mul_le_mul_of_nonneg_right hzero (abs_nonneg (tailJet 0 N x))
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero] at *
  nlinarith

private def fullBudget (a : ℝ) : ℝ := 1+rayBudget a 3 0+2*a*rayBudget a 1 0+
  adjointCoefficient a*(∑ r ∈ Finset.range 5, rayBudget a r 2)

set_option maxHeartbeats 1600000 in
/-- The actual infinite-tail norm budget, including its origin flux and all four
smooth derivatives. The constant is chosen before the cutoff and adjoint parameter. -/
theorem original_primal_tail_budget (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ, 0 ≤ α → α ≤ a →
      ContDiff ℝ 4 (originalTail N) ∧
      originalFlux N = -deriv (originalTail N) 0 ∧ 0 < originalFlux N ∧
      IntegrableOn (fun x : ℝ => exp (a*x^2/2)*
        |densityAdjoint α (densityAdjoint α (originalTail N)) x|) (Ioi 0) ∧
      |deriv (densityAdjoint α (originalTail N)) 0|+
        (∫ x in Ioi (0 : ℝ), exp (a*x^2/2)*
          |densityAdjoint α (densityAdjoint α (originalTail N)) x|) ≤
            C*((N : ℝ)+1)^4*originalFlux N := by
  have hK : 0 < fullBudget a := by
    dsimp [fullBudget,rayBudget,jetSize,endpointConstant,shiftedBudget,adjointCoefficient]
    positivity
  refine ⟨Real.pi^2*fullBudget a/5, by positivity, ?_⟩
  intro N hN α hα hαa
  let A := modeScale (N+1)
  have hA : 12 ≤ A := scale_lower (by omega)
  have hflux := flux_lower hN
  have hfluxpos : 0 < originalFlux N := lt_of_lt_of_le (by
    have : 0 < A := by linarith
    change 0 < 5*A^3*exp (-A)
    positivity) hflux
  have hfi (r : ℕ) := (tailJet_integral a r 2 N hN).1
  let g := fun x : ℝ => ∑ r ∈ Finset.range 5, exp (a*x^2/2)*(1+x)^2*|tailJet r N x|
  have hgi : IntegrableOn g (Ioi 0) := integrable_finsetSum _ (fun r _ => hfi r)
  have hD : 0 ≤ adjointCoefficient a := by dsimp [adjointCoefficient]; positivity
  have hbound : ∀ x ∈ Ioi (0 : ℝ),
      exp (a*x^2/2)*|densityAdjoint α (densityAdjoint α (originalTail N)) x| ≤
        adjointCoefficient a*g x := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left (adjoint_bound N hN ha.le hα hαa (le_of_lt hx))
      (exp_pos (a*x^2/2)).le
    simpa [g, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
  have hcont : Continuous (fun x : ℝ => exp (a*x^2/2)*
      |densityAdjoint α (densityAdjoint α (originalTail N)) x|) := by
    simp_rw [adjoint_square N hN α]
    have h0 := tailJet_continuous 0 N hN
    have h1 := tailJet_continuous 1 N hN
    have h2 := tailJet_continuous 2 N hN
    have h3 := tailJet_continuous 3 N hN
    have h4 := tailJet_continuous 4 N hN
    have hc3 : Continuous (fun x : ℝ => 2*α*x*tailJet 3 N x) :=
      (continuous_const.mul continuous_id).mul h3
    have hc2 : Continuous (fun x : ℝ => (4*α+α^2*x^2)*tailJet 2 N x) :=
      (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).mul h2
    have hc1 : Continuous (fun x : ℝ => 3*α^2*x*tailJet 1 N x) :=
      (continuous_const.mul continuous_id).mul h1
    have hc0 : Continuous (fun x : ℝ => α^2*tailJet 0 N x) := continuous_const.mul h0
    have hw : Continuous (fun x : ℝ => exp (a*x^2/2)) := by fun_prop
    exact hw.mul ((((h4.add hc3).add hc2).add hc1).add hc0).abs
  have hi : IntegrableOn (fun x : ℝ => exp (a*x^2/2)*
      |densityAdjoint α (densityAdjoint α (originalTail N)) x|) (Ioi 0) := by
    apply (hgi.const_mul (adjointCoefficient a)).mono' hcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound x hx
  have hnorm : (∫ x in Ioi (0 : ℝ), exp (a*x^2/2)*
      |densityAdjoint α (densityAdjoint α (originalTail N)) x|) ≤
      adjointCoefficient a*(∑ r ∈ Finset.range 5, rayBudget a r 2)*A^5*exp (-A) := by
    calc
      _ ≤ ∫ x in Ioi (0 : ℝ), adjointCoefficient a*g x :=
        integral_mono_ae hi (hgi.const_mul _) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact hbound x hx)
      _ = adjointCoefficient a*∑ r ∈ Finset.range 5,
          ∫ x in Ioi (0 : ℝ), exp (a*x^2/2)*(1+x)^2*|tailJet r N x| := by
        rw [integral_const_mul, integral_finsetSum _ (fun r _ => hfi r)]
      _ ≤ adjointCoefficient a*∑ r ∈ Finset.range 5, rayBudget a r 2*A^5*exp (-A) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply Finset.sum_le_sum
        intro r hr
        apply (tailJet_integral a r 2 N hN).2.trans
        have hp := pow_le_pow_right₀ (show 1 ≤ A by linarith)
          (show r+1 ≤ 5 by have := Finset.mem_range.mp hr; omega)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
          (by dsimp [rayBudget,jetSize,endpointConstant,shiftedBudget]; positivity)) (exp_pos _).le
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
  have hpoint (r : ℕ) : |tailJet r N 0| ≤ rayBudget a r 0*A^(r+2)*exp (-A) := by
    simpa [rayBudget,A,mul_assoc,mul_left_comm,mul_comm] using
      tailJet_endpoint a r 0 N hN (le_refl 0)
  have hfirst : |deriv (densityAdjoint α (originalTail N)) 0| ≤
      (rayBudget a 3 0+2*a*rayBudget a 1 0)*A^5*exp (-A) := by
    rw [(adjoint_deriv N hN α 0).deriv]
    simp only [zero_mul, add_zero]
    have hp : A^3 ≤ A^5 := pow_le_pow_right₀ (by linarith) (by omega)
    have h1 := (hpoint 1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by
        dsimp [rayBudget,jetSize,endpointConstant,shiftedBudget]; positivity)) (exp_pos _).le)
    have ht := abs_add_le (tailJet 3 N 0) (α*(2*tailJet 1 N 0))
    rw [abs_mul, abs_of_nonneg hα, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at ht
    have hu := mul_le_mul hαa h1 (abs_nonneg _) ha.le
    calc
      _ ≤ |tailJet 3 N 0|+α*(2*|tailJet 1 N 0|) := ht
      _ ≤ rayBudget a 3 0*A^5*exp (-A)+
          2*(a*(rayBudget a 1 0*A^5*exp (-A))) := by
        apply add_le_add (by simpa using hpoint 3)
        simpa [mul_assoc,mul_left_comm,mul_comm] using
          mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 2 by norm_num)
      _ = _ := by ring
  refine ⟨tail_smooth N hN, flux_eq N hN, hfluxpos, hi, ?_⟩
  have htotal : |deriv (densityAdjoint α (originalTail N)) 0|+
      (∫ x in Ioi (0 : ℝ), exp (a*x^2/2)*
        |densityAdjoint α (densityAdjoint α (originalTail N)) x|) ≤
      fullBudget a*A^5*exp (-A) := by
    dsimp [fullBudget]
    nlinarith [mul_pos (pow_pos (show 0 < A by linarith) 5) (exp_pos (-A))]
  apply htotal.trans
  have h := mul_le_mul_of_nonneg_left hflux (show 0 ≤ fullBudget a*A^2/5 by positivity)
  have hscale : A^2 = Real.pi^2*((N : ℝ)+1)^4 := by
    dsimp [A,modeScale]
    push_cast
    ring
  calc
    fullBudget a*A^5*exp (-A) = (fullBudget a*A^2/5)*(5*A^3*exp (-A)) := by ring
    _ ≤ (fullBudget a*A^2/5)*originalFlux N := h
    _ = _ := by rw [hscale]; ring

#print axioms original_primal_tail_budget
end D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
