import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Fixed-ratio Mangoldt differences and one-sided power bounds. -/

namespace DyadicActualHingeProbe

open Filter Set D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.Mertens.IntegratedExplicit
open scoped Topology

/-- A nonnegative dyadic second difference forces the sequence to decrease
when its ratio to the geometric homogeneous solution tends to zero. -/
theorem sequence_maximum_principle (w : ℕ → ℝ)
    (hzero : Tendsto (fun n => w n / (2 : ℝ) ^ n) atTop (𝓝 0))
    (hhinge : ∀ n, 0 ≤ w (n + 2) - 3 * w (n + 1) + 2 * w n) :
    Antitone w := by
  let d (n : ℕ) := w (n + 1) / (2 : ℝ) ^ n - w n / (2 : ℝ) ^ n
  have hdmono : Monotone d := monotone_nat_of_le_succ fun n => by
    change w (n + 1) / (2 : ℝ) ^ n - w n / (2 : ℝ) ^ n ≤
      w (n + 2) / (2 : ℝ) ^ (n + 1) - w (n + 1) / (2 : ℝ) ^ (n + 1)
    rw [← sub_div, ← sub_div, pow_succ', ← div_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [hhinge n]
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have hshift := (hzero.comp (tendsto_add_atTop_nat 1)).const_mul (2 : ℝ)
    have hdiff : Tendsto
        (fun n : ℕ => 2 * (w (n + 1) / (2 : ℝ) ^ (n + 1)) - w n / (2 : ℝ) ^ n)
        atTop (𝓝 0) := by simpa only [Function.comp_apply, mul_zero, sub_zero] using hshift.sub hzero
    refine hdiff.congr fun n => ?_
    dsimp [d]
    rw [pow_succ', ← div_div, ← mul_div_assoc]
    ring
  refine antitone_nat_of_succ_le fun n => ?_
  have hn : d n ≤ 0 := hdmono.ge_of_tendsto hdlim n
  exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ n)).mp
    (sub_nonpos.mp hn)

/-- The fixed-ratio hinge, applied below only at positive real arguments. -/
def hinge (V : ℝ → ℝ) (x : ℝ) : ℝ := V (4 * x) - 3 * V (2 * x) + 2 * V x

/-- A point on the first dyadic interval dominates each point in the tail. -/
theorem exists_seed_ge_of_hinge_nonneg {W : ℝ → ℝ} {X : ℝ} (hX : 0 < X)
    (hzero : Tendsto (fun x => W x / x) atTop (𝓝 0))
    (hhinge : ∀ x ≥ X, 0 ≤ hinge W x) {x : ℝ} (hx : X ≤ x) :
    ∃ y ∈ Icc X (2 * X), W x ≤ W y := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near
    ((le_div_iff₀ hX).2 (by simpa using hx)) (show (1 : ℝ) < 2 by norm_num)
  let y := x / (2 : ℝ) ^ n
  have hyX : X ≤ y := (le_div_iff₀ (by positivity)).2 (by
    simpa only [mul_comm X] using (le_div_iff₀ hX).1 hn)
  have hy2X : y ≤ 2 * X := (div_le_iff₀ (by positivity)).2 (by
    have h := (div_lt_iff₀ hX).1 hn'
    rw [pow_succ] at h
    nlinarith only [h])
  have hy : 0 < y := hX.trans_le hyX
  let w (k : ℕ) := W ((2 : ℝ) ^ k * y)
  have hatTop : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * y) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).atTop_mul_const hy
  have hwzero : Tendsto (fun k => w k / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    have h := (hzero.comp hatTop).const_mul y
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    dsimp [w, Function.comp_def]
    field_simp [hy.ne']
  have hstep (k : ℕ) : (2 : ℝ) ^ (k + 1) * y = 2 * (2 ^ k * y) := by
    rw [pow_succ', mul_assoc]
  have hwmono : Antitone w := sequence_maximum_principle w hwzero fun k => by
    have hk : X ≤ (2 : ℝ) ^ k * y := hyX.trans (le_mul_of_one_le_left hy.le
      (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ k))
    have h := hhinge _ hk
    dsimp only [w, hinge] at *
    rw [hstep (k + 1), hstep k, ← mul_assoc]
    norm_num at h ⊢
    exact h
  refine ⟨y, ⟨hyX, hy2X⟩, ?_⟩
  have hxy : (2 : ℝ) ^ n * y = x := by
    dsimp [y]
    field_simp
  simpa only [w, hxy, pow_zero, one_mul] using hwmono (Nat.zero_le n)

/-- A one-sided hinge error of order `x ^ θ` bounds the ramp at the same power. -/
theorem upper_bound_of_hinge_lower_bound {V : ℝ → ℝ} {X θ A : ℝ}
    (hX : 0 < X) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 ≤ A)
    (hcont : ContinuousOn V (Icc X (2 * X)))
    (hzero : Tendsto (fun x => V x / x) atTop (𝓝 0))
    (hhinge : ∀ x ≥ X, -A * x ^ θ ≤ hinge V x) :
    ∃ B : ℝ, ∀ x ≥ X, V x ≤ B + A / ((2 ^ θ - 1) * (2 - 2 ^ θ)) * x ^ θ := by
  let D : ℝ := (2 ^ θ - 1) * (2 - 2 ^ θ)
  let K := A / D
  have hD : 0 < D := by
    have hlo : 1 < (2 : ℝ) ^ θ := Real.one_lt_rpow (by norm_num) hθ0
    have hhi : (2 : ℝ) ^ θ < 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) hθ1
    exact mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  have hK : K * D = A := div_mul_cancel₀ A hD.ne'
  have hKnonneg : 0 ≤ K := div_nonneg hA hD.le
  let W (x : ℝ) := V x - K * x ^ θ
  have hWzero : Tendsto (fun x => W x / x) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr hθ1)).const_mul K
    have hlim : Tendsto (fun x : ℝ => V x / x - K * x ^ (-(1 - θ))) atTop (𝓝 0) := by
      simpa only [mul_zero, sub_zero] using hzero.sub hpow
    refine hlim.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun x hx => ?_)
    rw [show -(1 - θ) = θ - 1 by ring, Real.rpow_sub_one (ne_of_gt hx),
      ← mul_div_assoc, ← sub_div]
  have hWhinge (x : ℝ) (hx : X ≤ x) : 0 ≤ hinge W x := by
    have hx0 : 0 ≤ x := hX.le.trans hx
    have hfour : (4 : ℝ) ^ θ = (2 : ℝ) ^ θ * (2 : ℝ) ^ θ := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
    have heq : hinge W x = hinge V x + A * x ^ θ := by
      rw [← hK]
      simp only [hinge, W, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hx0,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0, hfour, D]
      ring
    rw [heq]
    linarith [hhinge x hx]
  have hWcont : ContinuousOn W (Icc X (2 * X)) :=
    hcont.sub (((Real.continuous_rpow_const hθ0.le).const_mul K).continuousOn)
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by linarith : X ≤ 2 * X)) hWcont
  refine ⟨V y, fun x hx => ?_⟩
  obtain ⟨z, hz, hxz⟩ := exists_seed_ge_of_hinge_nonneg hX hWzero hWhinge hx
  have hxy : W x ≤ W y := hxz.trans (hmax hz)
  have hy0 : 0 ≤ y := hX.le.trans hy.1
  have hyV : W y ≤ V y := sub_le_self _ (mul_nonneg hKnonneg (Real.rpow_nonneg hy0 _))
  exact sub_le_iff_le_add.mp (hxy.trans hyV)

open MeasureTheory

private theorem ramp_eq_finite_sum {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : ⌊x⌋₊ ≤ N) :
    U x =
      (∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0) -
      x * Real.log x + (1 + Real.eulerMascheroniConstant) * x := by
  have hcut : x < (N : ℝ) + 1 := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast Nat.succ_le_succ hN)
  rw [U_eq_complete_ramps hx, mangoldtPart_eq_range hx (N := N + 1) (by exact_mod_cast hcut)]
  have hrange : Finset.range (N+1) = insert 0 (Finset.Ioc 0 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp [mangoldtRamp]

private theorem continuousOn_mangoldtRamp {X : ℝ} (hX : 0 < X) :
    ContinuousOn U (Icc X (2 * X)) := fun x hx =>
  (U_continuousAt_pos (hX.trans_le hx.1)).continuousWithinAt

private theorem tendsto_mangoldtRamp_div :
    Tendsto (fun x => U x / x) atTop (𝓝 0) := by
  let q (x : ℝ) := ∫ t in Ioi x, (Chebyshev.psi t - t) / t ^ 2
  have hq : Tendsto q atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  have hlim : Tendsto (fun x => -q x) atTop (𝓝 0) := by
    simpa only [neg_zero] using hq.neg
  refine hlim.congr' ((eventually_ge_atTop (2 : ℝ)).mono fun x hx => ?_)
  have hx0 : x ≠ 0 := by linarith
  have htail :=
    D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
      D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable hx
  change q x = _ at htail
  change -q x = U x / x
  rw [htail, U]
  field_simp [hx0]
  ring

/-- The weighted Mangoldt sum in the dyadic hinge. Its summand vanishes for
`n ≤ x`, and the finite cutoff includes `n = 4*x` when that is an integer. -/
noncomputable def mangoldtHingeSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊4 * x⌋₊, ArithmeticFunction.vonMangoldt n *
    (max (4 * x / (n : ℝ) - 1) 0 - 3 * max (2 * x / (n : ℝ) - 1) 0 +
      2 * max (x / (n : ℝ) - 1) 0)

/-- The linear term cancels, and the logarithmic term contributes `-2*x*log 2`. -/
theorem hinge_mangoldtRamp_eq {x : ℝ} (hx : 0 < x) :
    hinge U x = mangoldtHingeSum x - 2 * x * Real.log 2 := by
  have hx2 : 0 < 2 * x := by positivity
  have hx4 : 0 < 4 * x := by positivity
  rw [hinge, ramp_eq_finite_sum hx4.le le_rfl,
    ramp_eq_finite_sum hx2.le (Nat.floor_mono (by linarith : 2 * x ≤ 4 * x)),
    ramp_eq_finite_sum hx.le (Nat.floor_mono (by linarith : x ≤ 4 * x))]
  have hsum : mangoldtHingeSum x =
      (∑ n ∈ Finset.Ioc 0 ⌊4 * x⌋₊,
        ArithmeticFunction.vonMangoldt n * max (4 * x / (n : ℝ) - 1) 0) -
      3 * (∑ n ∈ Finset.Ioc 0 ⌊4 * x⌋₊,
        ArithmeticFunction.vonMangoldt n * max (2 * x / (n : ℝ) - 1) 0) +
      2 * (∑ n ∈ Finset.Ioc 0 ⌊4 * x⌋₊,
        ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0) := by
    rw [mangoldtHingeSum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hsum, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne', hlog4]
  ring

/-- For the actual complete Mangoldt ramp, only the one-sided hinge estimate
is needed in addition to the threshold and exponent conditions. -/
theorem mangoldt_ramp_upper_bound {X θ A : ℝ} (hX : 0 < X) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hA : 0 ≤ A)
    (hhinge : ∀ x ≥ X, -A * x ^ θ ≤ hinge U x) :
    ∃ B : ℝ, ∀ x ≥ X,
      U x ≤ B + A / ((2 ^ θ - 1) * (2 - 2 ^ θ)) * x ^ θ :=
  upper_bound_of_hinge_lower_bound hX hθ0 hθ1 hA (continuousOn_mangoldtRamp hX)
    tendsto_mangoldtRamp_div hhinge

/-- A lower bound on the finite weighted sum implies the same-power ramp bound. -/
theorem mangoldt_ramp_upper_bound_of_sum {X θ A : ℝ} (hX : 0 < X) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hA : 0 ≤ A)
    (hsum : ∀ x ≥ X, 2 * x * Real.log 2 - A * x ^ θ ≤ mangoldtHingeSum x) :
    ∃ B : ℝ, ∀ x ≥ X,
      U x ≤ B + A / ((2 ^ θ - 1) * (2 - 2 ^ θ)) * x ^ θ := by
  apply mangoldt_ramp_upper_bound hX hθ0 hθ1 hA
  intro x hx
  rw [hinge_mangoldtRamp_eq (hX.trans_le hx)]
  linarith only [hsum x hx]

end DyadicActualHingeProbe
