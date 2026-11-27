import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
import OmegaBuild.Commands

/-! The scalar charge-two product in the general-exponent extension of Wu v1 (3.54). -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.Quantum.Semigroups.WuPowerTwoChargeGap

open Filter Real
open scoped Topology
open D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
  (coth sinh_le_self_mul_cosh_of_nonneg)

noncomputable section

/-- The hyperbolic factor in Wu's scalar symbol at positive charge. -/
def B (p v : ℝ) : ℝ := sinh ((p - 1) * v / (2 * p)) / sinh (v / (2 * p))

/-- The response factor in Wu's scalar symbol at positive charge. -/
def g (p v : ℝ) : ℝ :=
  v / (2 * p ^ 2) * (coth ((p - 1) * v / (2 * p)) + coth (v / (2 * p)))

/-- The reduced charge-two product with independent positive arguments. -/
def chargeTwoGap (A T : ℝ) : ℝ := sinh A * cosh (A - T) / (sinh T * cosh T ^ 2)

private theorem coth_double {x : ℝ} (hx : 0 < x) :
    coth (2 * x) = (coth x + tanh x) / 2 := by
  unfold coth
  rw [cosh_two_mul, sinh_two_mul, tanh_eq_sinh_div_cosh]
  field_simp [(sinh_pos_iff.mpr hx).ne', (cosh_pos x).ne']

private theorem coth_pos {x : ℝ} (hx : 0 < x) : 0 < coth x :=
  div_pos (cosh_pos x) (sinh_pos_iff.mpr hx)

private theorem coth_double_ratio {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    2 * (coth (2 * A) + coth (2 * T)) / (coth A + coth T) =
      1 + tanh A * tanh T := by
  have hsum : 0 < coth A + coth T := add_pos (coth_pos hA) (coth_pos hT)
  have hcancel : (coth A + coth T) * (tanh A * tanh T) = tanh A + tanh T := by
    simp only [coth, tanh_eq_sinh_div_cosh]
    field_simp [(sinh_pos_iff.mpr hA).ne', (sinh_pos_iff.mpr hT).ne',
      (cosh_pos A).ne', (cosh_pos T).ne']
    ring
  apply (div_eq_iff hsum.ne').2
  rw [coth_double hA, coth_double hT]
  linear_combination -hcancel

/-- The doubled-charge product reduces to a single hyperbolic quotient. -/
theorem chargeTwoGap_eq_of_positive {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    sinh (2 * A) / sinh (2 * T) *
        (2 - 2 * (coth (2 * A) + coth (2 * T)) / (coth A + coth T)) =
      chargeTwoGap A T := by
  rw [coth_double_ratio hA hT, sinh_two_mul A, sinh_two_mul T,
    show (2 : ℝ) - (1 + tanh A * tanh T) = 1 - tanh A * tanh T by ring]
  have hcancel : cosh A * (1 - tanh A * tanh T) = cosh (A - T) / cosh T := by
    rw [cosh_sub, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
    field_simp [(cosh_pos A).ne', (cosh_pos T).ne']
  unfold chargeTwoGap
  rw [show (2 * sinh A * cosh A) / (2 * sinh T * cosh T) *
      (1 - tanh A * tanh T) =
        sinh A / (sinh T * cosh T) * (cosh A * (1 - tanh A * tanh T)) by
      field_simp [(sinh_pos_iff.mpr hT).ne', (cosh_pos T).ne'],
    hcancel]
  field_simp [(sinh_pos_iff.mpr hT).ne', (cosh_pos T).ne']

/-- The exact charge-two product at real exponent `p > 1` and positive cap `beta`. -/
theorem chargeTwo_product {p beta : ℝ} (hp : 1 < p) (hbeta : 0 < beta) :
    B p (2 * beta) * (2 - g p (2 * beta) / g p beta) =
      chargeTwoGap ((p - 1) * beta / (2 * p)) (beta / (2 * p)) := by
  have hp₀ : 0 < p := by linarith
  have hp₁ : 0 < p - 1 := sub_pos.mpr hp
  have hA : 0 < (p - 1) * beta / (2 * p) := by positivity
  have hT : 0 < beta / (2 * p) := by positivity
  let A := (p - 1) * beta / (2 * p)
  let T := beta / (2 * p)
  have hA₂ : (p - 1) * (2 * beta) / (2 * p) = 2 * A := by dsimp [A]; ring
  have hT₂ : 2 * beta / (2 * p) = 2 * T := by dsimp [T]; ring
  have hg : g p (2 * beta) / g p beta =
      2 * (coth (2 * A) + coth (2 * T)) / (coth A + coth T) := by
    rw [g, g, hA₂, hT₂]
    change (2 * beta / (2 * p ^ 2) * (coth (2 * A) + coth (2 * T))) /
      (beta / (2 * p ^ 2) * (coth A + coth T)) = _
    field_simp [(add_pos (coth_pos hA) (coth_pos hT)).ne', hp₀.ne', hbeta.ne']
  rw [B, hA₂, hT₂, hg]
  exact chargeTwoGap_eq_of_positive hA hT

private theorem sinh_div_monotoneOn : MonotoneOn (fun x : ℝ => sinh x / x) (Set.Ioi 0) := by
  have hderiv {x : ℝ} (hx : 0 < x) :
      HasDerivAt (fun y : ℝ => sinh y / y) ((cosh x * x - sinh x) / x ^ 2) x := by
    apply ((hasDerivAt_sinh x).div (hasDerivAt_id x) hx.ne').congr_deriv
    simp only [id_eq, mul_one]
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun x hx => (hderiv hx).continuousAt.continuousWithinAt)
    (fun x hx => (hderiv (interior_subset hx)).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  have hx₀ : 0 < x := interior_subset hx
  rw [(hderiv hx₀).deriv]
  exact div_nonneg (sub_nonneg.mpr (by
    simpa only [mul_comm] using sinh_le_self_mul_cosh_of_nonneg hx₀.le)) (sq_nonneg x)

/-- The sharp lower bound above the cubic threshold, with its equality condition. -/
theorem chargeTwoGap_sharp {A T : ℝ} (hT : 0 < T) (hA : 2 * T ≤ A) :
    A / T ≤ chargeTwoGap A T ∧ (chargeTwoGap A T = A / T ↔ A = 2 * T) := by
  have h2T : 0 < 2 * T := by positivity
  have hA₀ : 0 < A := h2T.trans_le hA
  have hsT := sinh_pos_iff.mpr hT
  have hs2T := sinh_pos_iff.mpr h2T
  have hcT := cosh_pos T
  have hfactor : chargeTwoGap A T =
      sinh A / sinh (2 * T) * (cosh (A - T) / cosh T) * 2 := by
    rw [chargeTwoGap, sinh_two_mul]
    field_simp [hsT.ne', hcT.ne']
  rcases hA.eq_or_lt with hEq | hlt
  · subst A
    have heq : chargeTwoGap (2 * T) T = 2 * T / T := by
      rw [hfactor, show 2 * T - T = T by ring, div_self hs2T.ne', div_self hcT.ne']
      field_simp
    simp [heq]
  have hsratio : A / (2 * T) ≤ sinh A / sinh (2 * T) := by
    have hmono := sinh_div_monotoneOn h2T hA₀ hlt.le
    have hcross := (div_le_div_iff₀ h2T hA₀).mp hmono
    exact (div_le_div_iff₀ h2T hs2T).2 (by simpa only [mul_comm] using hcross)
  have hcosh : 1 < cosh (A - T) / cosh T := by
    rw [lt_div_iff₀ hcT, one_mul, cosh_lt_cosh, abs_of_pos hT,
      abs_of_pos (show 0 < A - T by linarith)]
    linarith
  have hstrict : A / T < chargeTwoGap A T := by
    calc
      A / T = A / (2 * T) * 2 := by ring
      _ ≤ sinh A / sinh (2 * T) * 2 := mul_le_mul_of_nonneg_right hsratio (by norm_num)
      _ < chargeTwoGap A T := by
        rw [hfactor]
        apply mul_lt_mul_of_pos_right _ (by norm_num)
        simpa only [mul_one] using mul_lt_mul_of_pos_left hcosh
          (div_pos (sinh_pos_iff.mpr hA₀) hs2T)
  exact ⟨hstrict.le, iff_of_false hstrict.ne' hlt.ne'⟩

/-- The tracial endpoint value along the ray A = (p - 1) * T. -/
theorem tendsto_chargeTwoGap_tracial (p : ℝ) :
    Tendsto (fun T : ℝ => chargeTwoGap ((p - 1) * T) T) (𝓝[>] 0) (𝓝 (p - 1)) := by
  have hderiv : HasDerivAt (fun T : ℝ => sinh ((p - 1) * T)) (p - 1) 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_sinh ((p - 1) * (0 : ℝ))).comp 0 ((hasDerivAt_id 0).const_mul (p - 1))
  have hsA : Tendsto (fun T : ℝ => sinh ((p - 1) * T) / T) (𝓝[>] 0) (𝓝 (p - 1)) := by
    simpa [div_eq_mul_inv, mul_comm] using hderiv.tendsto_slope_zero_right
  have hsT : Tendsto (fun T : ℝ => sinh T / T) (𝓝[>] 0) (𝓝 1) := by
    simpa [div_eq_mul_inv, mul_comm] using (hasDerivAt_sinh 0).tendsto_slope_zero_right
  have hcontinuous : Continuous (fun T : ℝ => cosh ((p - 1) * T - T) / cosh T ^ 2) :=
    (continuous_cosh.comp ((continuous_const.mul continuous_id).sub continuous_id)).div
      (continuous_cosh.pow 2) (fun T => pow_ne_zero 2 (cosh_pos T).ne')
  have hc : Tendsto (fun T : ℝ => cosh ((p - 1) * T - T) / cosh T ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa [ContinuousWithinAt] using
      hcontinuous.continuousAt.continuousWithinAt (s := Set.Ioi 0) (x := (0 : ℝ))
  have hlim : Tendsto (fun T : ℝ => (sinh ((p - 1) * T) / T) / (sinh T / T) *
      (cosh ((p - 1) * T - T) / cosh T ^ 2)) (𝓝[>] 0) (𝓝 (p - 1)) := by
    simpa only [Pi.div_apply, div_one, mul_one] using (hsA.div hsT one_ne_zero).mul hc
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun T hT => ?_)
  have hT₀ : 0 < T := hT
  unfold chargeTwoGap
  field_simp [hT₀.ne', (sinh_pos_iff.mpr hT₀).ne', (cosh_pos T).ne']
  <;> ring

/-- An exponential majorant for the quotient at large cap. -/
theorem chargeTwoGap_exp_bound {A T : ℝ} (hT : 1 ≤ T) :
    chargeTwoGap A T ≤ 8 * exp (A + |A - T| - 3 * T) := by
  have hsA : sinh A ≤ exp A / 2 := by rw [sinh_eq]; linarith [exp_pos (-A)]
  have hcAT : cosh (A - T) ≤ exp (|A - T|) := by
    rw [← cosh_abs, cosh_eq]
    have h := exp_le_exp.mpr (show -|A - T| ≤ |A - T| by linarith [abs_nonneg (A - T)])
    linarith
  have hsT : exp T / 4 ≤ sinh T := by
    have htwo : 2 ≤ exp T := by linarith [add_one_le_exp T]
    have hneg : exp (-T) ≤ 1 := by
      rw [← exp_zero, exp_le_exp]
      linarith
    rw [sinh_eq]
    linarith
  have hcT : exp T / 2 ≤ cosh T := by rw [cosh_eq]; linarith [exp_pos (-T)]
  have hden : exp T / 4 * (exp T / 2) ^ 2 ≤ sinh T * cosh T ^ 2 :=
    mul_le_mul hsT (pow_le_pow_left₀ (by positivity) hcT 2) (by positivity)
      (sinh_pos_iff.mpr (by linarith : 0 < T)).le
  unfold chargeTwoGap
  calc
    _ ≤ (exp A / 2 * exp (|A - T|)) / (exp T / 4 * (exp T / 2) ^ 2) :=
      div_le_div₀ (by positivity)
        (mul_le_mul hsA hcAT (cosh_pos _).le (by positivity)) (by positivity) hden
    _ = _ := by
      rw [exp_sub, exp_add, show exp (3 * T) = exp T ^ 3 by
        simpa using exp_nat_mul T 3]
      field_simp [(exp_pos T).ne']
      ring

/-- Below the cubic threshold the scalar charge-two product tends to zero as
the cap tends to infinity. -/
theorem tendsto_chargeTwoGap_atTop {p : ℝ} (hp : 1 < p) (hp₃ : p < 3) :
    Tendsto (fun T : ℝ => chargeTwoGap ((p - 1) * T) T) atTop (𝓝 0) := by
  let c := 3 - (p - 1) - |p - 2|
  have habs : |p - 2| < 4 - p := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hc : 0 < c := by dsimp [c]; linarith
  have hscale : Tendsto (fun T : ℝ => c * T) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
  have hlim : Tendsto (fun T : ℝ => 8 * exp (-(c * T))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_exp_neg_atTop_nhds_zero.comp hscale).const_mul (8 : ℝ)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT₀ : 0 < T := by linarith
    have hA : 0 < (p - 1) * T := mul_pos (sub_pos.mpr hp) hT₀
    unfold chargeTwoGap
    exact div_nonneg (mul_nonneg (sinh_pos_iff.mpr hA).le (cosh_pos _).le)
      (mul_nonneg (sinh_pos_iff.mpr hT₀).le (sq_nonneg _))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hexponent : (p - 1) * T + |(p - 1) * T - T| - 3 * T = -(c * T) := by
      rw [show (p - 1) * T - T = (p - 2) * T by ring, abs_mul,
        abs_of_nonneg (show 0 ≤ T by linarith)]
      dsimp [c]
      ring
    simpa only [hexponent] using chargeTwoGap_exp_bound (A := (p - 1) * T) hT

#print axioms chargeTwo_product
#print axioms chargeTwoGap_sharp
#print axioms tendsto_chargeTwoGap_tracial
#print axioms tendsto_chargeTwoGap_atTop

end
end D5.S3.Quantum.Semigroups.WuPowerTwoChargeGap
