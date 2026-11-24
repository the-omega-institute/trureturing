/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeQuarterTriangle
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeQuarterTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An eventual square-root lower bound on ordinary prime triangles along the quarter grid is equivalent to RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows

/-! # An ordinary-prime criterion for the Riemann hypothesis -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle

open Filter Set D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.Mertens.IntegratedExplicit
open scoped Topology

/-- A nonnegative dyadic second difference forces the sequence to decrease
when its ratio to the geometric homogeneous solution tends to zero. -/
private theorem sequence_maximum_principle (w : ℕ → ℝ)
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
private theorem exists_seed_ge_of_hinge_nonneg {W : ℝ → ℝ} {X : ℝ} (hX : 0 < X)
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
private theorem upper_bound_of_hinge_lower_bound {V : ℝ → ℝ} {X θ A : ℝ}
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
private theorem hinge_mangoldtRamp_eq {x : ℝ} (hx : 0 < x) :
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
private theorem mangoldt_ramp_upper_bound {X θ A : ℝ} (hX : 0 < X) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hA : 0 ≤ A)
    (hhinge : ∀ x ≥ X, -A * x ^ θ ≤ hinge U x) :
    ∃ B : ℝ, ∀ x ≥ X,
      U x ≤ B + A / ((2 ^ θ - 1) * (2 - 2 ^ θ)) * x ^ θ :=
  upper_bound_of_hinge_lower_bound hX hθ0 hθ1 hA (continuousOn_mangoldtRamp hX)
    tendsto_mangoldtRamp_div hhinge

/-- A lower bound on the finite weighted sum implies the same-power ramp bound. -/
private theorem mangoldt_ramp_upper_bound_of_sum {X θ A : ℝ} (hX : 0 < X) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hA : 0 ≤ A)
    (hsum : ∀ x ≥ X, 2 * x * Real.log 2 - A * x ^ θ ≤ mangoldtHingeSum x) :
    ∃ B : ℝ, ∀ x ≥ X,
      U x ≤ B + A / ((2 ^ θ - 1) * (2 - 2 ^ θ)) * x ^ θ := by
  apply mangoldt_ramp_upper_bound hX hθ0 hθ1 hA
  intro x hx
  rw [hinge_mangoldtRamp_eq (hX.trans_le hx)]
  linarith only [hsum x hx]


open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass firstLiMass_lt_one)

private theorem ramp_unit_interpolation (n d k : ℕ) (hd : 0 < d)
    {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    mangoldtRamp n (((k : ℝ) + r) / d) =
      (1 - r) * mangoldtRamp n ((k : ℝ) / d) +
        r * mangoldtRamp n (((k : ℝ) + 1) / d) := by
  by_cases hn : n = 0
  · subst n
    simp [mangoldtRamp]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases h : n * d ≤ k
  · have hR : (n : ℝ) * d ≤ k := by exact_mod_cast h
    have hl : (n : ℝ) ≤ (k : ℝ) / d := (le_div_iff₀ hdR).mpr hR
    have hm : (n : ℝ) ≤ ((k : ℝ) + r) / d := (le_div_iff₀ hdR).mpr (by linarith)
    have hu : (n : ℝ) ≤ ((k : ℝ) + 1) / d := (le_div_iff₀ hdR).mpr (by linarith)
    rw [ramp_eq_affine (Nat.pos_of_ne_zero hn) hm,
      ramp_eq_affine (Nat.pos_of_ne_zero hn) hl, ramp_eq_affine (Nat.pos_of_ne_zero hn) hu]
    ring
  · have hN : k + 1 ≤ n * d := by omega
    have hR : (k : ℝ) + 1 ≤ (n : ℝ) * d := by exact_mod_cast hN
    have hu : ((k : ℝ) + 1) / d ≤ n := (div_le_iff₀ hdR).mpr hR
    have zeroBelow (t : ℝ) (ht : t ≤ n) : mangoldtRamp n t = 0 := by
      unfold mangoldtRamp
      rw [max_eq_right (show t / (n : ℝ) - 1 ≤ 0 by
        linarith [(div_le_one hnR).mpr ht]), mul_zero]
    rw [zeroBelow _ ((div_le_iff₀ hdR).mpr (by linarith)),
      zeroBelow _ ((div_le_iff₀ hdR).mpr (by linarith)), zeroBelow _ hu]
    ring

private theorem part_unit_interpolation (d k : ℕ) (hd : 0 < d)
    {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    mangoldtPart (((k : ℝ) + r) / d) =
      (1 - r) * mangoldtPart ((k : ℝ) / d) +
        r * mangoldtPart (((k : ℝ) + 1) / d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) < d := by linarith
  have below {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
      ((k : ℝ) + u) / d < (↑(k + 2) : ℝ) := by
    have hle := div_le_self (show 0 ≤ (k : ℝ) + u by linarith) hdR
    push_cast
    linarith
  have hleft : (k : ℝ) / d < (↑(k + 2) : ℝ) := by simpa using below le_rfl zero_le_one
  rw [mangoldtPart_eq_range (div_nonneg (by linarith) hd0.le) (below hr hr'),
    mangoldtPart_eq_range (div_nonneg hk hd0.le) hleft,
    mangoldtPart_eq_range (div_nonneg (by linarith) hd0.le) (below zero_le_one le_rfl),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => ramp_unit_interpolation n d k hd hr hr'

private theorem hinge_eq_parts {x : ℝ} (hx : 0 < x) :
    hinge U x = mangoldtPart (4 * x) - 3 * mangoldtPart (2 * x) +
      2 * mangoldtPart x - 2 * x * Real.log 2 := by
  unfold hinge
  rw [U_eq_complete_ramps (by positivity : 0 ≤ 4 * x),
    U_eq_complete_ramps (by positivity : 0 ≤ 2 * x), U_eq_complete_ramps hx.le,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne',
    show Real.log 4 = Real.log 2 + Real.log 2 by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]]
  ring

/-- Every knot of the centered triangular Mangoldt sum lies on the quarter grid. -/
private theorem hinge_quarter_interpolation {k : ℕ} (hk : 0 < k)
    {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    hinge U (((k : ℝ) + r) / 4) =
      (1 - r) * hinge U ((k : ℝ) / 4) + r * hinge U (((k : ℝ) + 1) / 4) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [hinge_eq_parts (by linarith), hinge_eq_parts (by positivity),
    hinge_eq_parts (by positivity)]
  have h1 := part_unit_interpolation 1 k (by decide) hr hr'
  have h2 := part_unit_interpolation 2 k (by decide) hr hr'
  have h4 := part_unit_interpolation 4 k (by decide) hr hr'
  norm_num only [Nat.cast_one, div_one, Nat.cast_ofNat] at h1 h2 h4
  simp only [show ∀ t : ℝ, 4 * (t / 4) = t by intro t; ring,
    show ∀ t : ℝ, 2 * (t / 4) = t / 2 by intro t; ring, h1, h2, h4]
  ring

/-- The exact quarterly samples of the finite triangular sum control all
large real scales at the same exponent. -/
private theorem eventually_hinge_lower_of_quarter_grid {θ A : ℝ} (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (hs : ∀ᶠ k : ℕ in atTop, -A * ((k : ℝ) / 4) ^ θ ≤ hinge U ((k : ℝ) / 4)) :
    ∀ᶠ x : ℝ in atTop, -(A * (2 : ℝ) ^ θ) * x ^ θ ≤ hinge U x := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hs
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with x hx
  have hx1 := (le_max_left (1 : ℝ) N).trans hx
  have hxN := (le_max_right (1 : ℝ) N).trans hx
  let k := ⌊4 * x⌋₊
  have hx0 : 0 ≤ 4 * x := by linarith
  have hk_floor : (k : ℝ) ≤ 4 * x := Nat.floor_le hx0
  have hfloor_k : 4 * x < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkN : N ≤ k := (Nat.le_floor_iff hx0).mpr (by linarith)
  have hk : 0 < k := (Nat.le_floor_iff hx0).mpr (by norm_num; linarith)
  let r := 4 * x - (k : ℝ)
  have hr : 0 ≤ r := sub_nonneg.mpr hk_floor
  have hr' : r ≤ 1 := by dsimp [r]; linarith
  have hxgrid : ((k : ℝ) + r) / 4 = x := by dsimp [r]; ring
  have hleft : ((k : ℝ) / 4) ^ θ ≤ (2 * x) ^ θ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hθ
  have hright : (((k : ℝ) + 1) / 4) ^ θ ≤ (2 * x) ^ θ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hθ
  have hl := (mul_le_mul_of_nonpos_left hleft (neg_nonpos.mpr hA)).trans (hN k hkN)
  have hu := (mul_le_mul_of_nonpos_left hright (neg_nonpos.mpr hA)).trans (by
    simpa only [Nat.cast_succ] using hN (k + 1) (hkN.trans (Nat.le_succ k)))
  rw [← hxgrid, hinge_quarter_interpolation hk hr hr', hxgrid,
    ← neg_mul, mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ x)]
  have h := add_le_add (mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hr'))
    (mul_le_mul_of_nonneg_left hu hr)
  convert h using 1
  ring

private theorem eventual_abs_U_le_sqrt (rh : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, |U x| ≤ Real.sqrt x := by
  have he := Real.tendsto_log_atTop.eventually ((RHSharpActualEnvelope.actual_G_control rh).1
    (1 - firstLiMass) (sub_pos.mpr firstLiMass_lt_one))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x h hx
  change |Real.exp (-Real.log x / 2) * U (Real.exp (Real.log x))| <
    firstLiMass + (1 - firstLiMass) at h
  have hinv : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_neg]
    congr 1
    ring
  rw [Real.exp_log hx, abs_mul, abs_of_pos (Real.exp_pos _), hinv, ← div_eq_inv_mul] at h
  exact (div_le_one (Real.sqrt_pos.mpr hx)).mp (by linarith)

private theorem eventual_hinge_lower_of_rh (rh : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, -(10 : ℝ) * Real.sqrt x ≤ hinge U x := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventual_abs_U_le_sqrt rh)
  filter_upwards [eventually_ge_atTop (max 1 T)] with x hx
  have hx1 := (le_max_left 1 T).trans hx
  have hxT := (le_max_right 1 T).trans hx
  have hxNonneg : 0 ≤ x := by linarith
  have h4 := abs_le.mp (hT (4 * x) (by linarith))
  have h2 := abs_le.mp (hT (2 * x) (by linarith))
  have h1 := abs_le.mp (hT x hxT)
  have hs4 : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hs2 : Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := by
    rw [← hs4]
    exact Real.sqrt_le_sqrt (by linarith)
  unfold hinge
  linarith [h4.1, h2.2, h1.1]

/-- RH is equivalent to an eventual square-root lower bound on only the
finite, nonnegative triangular Mangoldt sum at the exact quarter grid. -/
private theorem rh_iff_eventual_quarter_triangular_lower :
    RiemannHypothesis ↔ ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k : ℕ in atTop,
      2 * ((k : ℝ) / 4) * Real.log 2 - A * Real.sqrt ((k : ℝ) / 4) ≤
        mangoldtHingeSum ((k : ℝ) / 4) := by
  constructor
  · intro rh
    have hlim : Tendsto (fun k : ℕ => (k : ℝ) / 4) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop
    refine ⟨10, by norm_num, ?_⟩
    filter_upwards [hlim.eventually (eventual_hinge_lower_of_rh rh),
      eventually_gt_atTop (0 : ℕ)] with k h hk
    rw [hinge_mangoldtRamp_eq (by positivity : 0 < (k : ℝ) / 4)] at h
    linarith
  · rintro ⟨A, hA, hs⟩
    have hg : ∀ᶠ k : ℕ in atTop, -A * ((k : ℝ) / 4) ^ (1 / 2 : ℝ) ≤
        hinge U ((k : ℝ) / 4) := by
      filter_upwards [hs, eventually_gt_atTop (0 : ℕ)] with k h hk
      rw [hinge_mangoldtRamp_eq (by positivity : 0 < (k : ℝ) / 4), ← Real.sqrt_eq_rpow]
      linarith
    let M := A * (2 : ℝ) ^ (1 / 2 : ℝ)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    obtain ⟨X, hX⟩ := eventually_atTop.mp
      (eventually_hinge_lower_of_quarter_grid (by norm_num : (0 : ℝ) ≤ 1 / 2) hA hg)
    obtain ⟨B, hB⟩ := mangoldt_ramp_upper_bound
      (X := max 1 X) (θ := 1 / 2) (A := M)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by norm_num) (by norm_num) hM
      (fun x hx => hX x ((le_max_right _ _).trans hx))
    let D := M / ((2 ^ (1 / 2 : ℝ) - 1) * (2 - 2 ^ (1 / 2 : ℝ)))
    let C := |B| + |D| + |firstLiMass| + 1
    have hC : firstLiMass < C := by
      dsimp [C]
      linarith [le_abs_self firstLiMass, abs_nonneg B, abs_nonneg D]
    apply (MangoldtPointwiseWindows.rh_iff_pointwise_sqrt_windows (b := 2) hC (by norm_num)).mpr
    intro R
    refine ⟨max (max R 2) (max 1 X), le_max_left _ _, ?_⟩
    intro x hx
    have hxX := (le_max_right (max R 2) (max 1 X)).trans hx.1
    have hxs : 1 ≤ Real.sqrt x := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ((le_max_left 1 X).trans hxX)
    have hb := hB x hxX
    change U x ≤ B + D * x ^ (1 / 2 : ℝ) at hb
    rw [← Real.sqrt_eq_rpow] at hb
    refine hb.trans ?_
    calc
      B + D * Real.sqrt x ≤ |B| * Real.sqrt x + |D| * Real.sqrt x := by
        have hb' := mul_le_mul_of_nonneg_left hxs (abs_nonneg B)
        have hd' := mul_le_mul_of_nonneg_right (le_abs_self D) (Real.sqrt_nonneg x)
        linarith [le_abs_self B]
      _ = (|B| + |D|) * Real.sqrt x := by ring
      _ ≤ C * Real.sqrt x :=
        mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [abs_nonneg firstLiMass])
          (Real.sqrt_nonneg x)




/-- The tent weight vanishes outside `(x, 4*x)` and takes the value `1` at `2*x`. -/
def triangleWeight (x n : ℝ) : ℝ :=
  max (4 * x / n - 1) 0 - 3 * max (2 * x / n - 1) 0 + 2 * max (x / n - 1) 0

private theorem triangleWeight_bounds {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) :
    triangleWeight x n ∈ Icc (0 : ℝ) 1 := by
  let t := x / n
  have ht : 0 ≤ t := div_nonneg hx hn.le
  unfold triangleWeight
  rw [mul_div_assoc, mul_div_assoc]
  change 0 ≤ max (4 * t - 1) 0 - 3 * max (2 * t - 1) 0 + 2 * max (t - 1) 0 ∧
    max (4 * t - 1) 0 - 3 * max (2 * t - 1) 0 + 2 * max (t - 1) 0 ≤ 1
  by_cases h1 : 1 ≤ t
  · rw [max_eq_left (by linarith : 0 ≤ 4 * t - 1),
      max_eq_left (by linarith : 0 ≤ 2 * t - 1), max_eq_left (by linarith : 0 ≤ t - 1)]
    constructor <;> linarith
  rw [max_eq_right (by linarith : t - 1 ≤ 0)]
  by_cases h2 : 1 / 2 ≤ t
  · rw [max_eq_left (by linarith : 0 ≤ 4 * t - 1), max_eq_left (by linarith : 0 ≤ 2 * t - 1)]
    constructor <;> linarith
  rw [max_eq_right (by linarith : 2 * t - 1 ≤ 0)]
  constructor
  · linarith [le_max_right (4 * t - 1) (0 : ℝ)]
  · linarith [max_le (show 4 * t - 1 ≤ 1 by linarith) (show (0 : ℝ) ≤ 1 by norm_num)]

/-- Restrict the triangular sum to primes, with their literal logarithmic weights. -/
def primeTriangleSum (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊4 * x⌋₊).filter Nat.Prime, Real.log n * triangleWeight x n

private theorem triangleWeight_eq_zero_of_le {x n : ℝ} (hn : 0 < n) (h : n ≤ x) :
    triangleWeight x n = 0 := by
  have h1 : 1 ≤ x / n := (one_le_div hn).mpr h
  unfold triangleWeight
  rw [mul_div_assoc, mul_div_assoc, max_eq_left (by linarith : 0 ≤ 4 * (x / n) - 1),
    max_eq_left (by linarith : 0 ≤ 2 * (x / n) - 1),
    max_eq_left (by linarith : 0 ≤ x / n - 1)]
  ring

/-- Terms at or below the lower endpoint have zero weight. -/
private theorem primeTriangleSum_eq_prefix {x : ℝ} (hx : 0 ≤ x) :
    primeTriangleSum x =
      ∑ n ∈ (Finset.Ioc 0 ⌊4 * x⌋₊).filter Nat.Prime, Real.log n * triangleWeight x n := by
  unfold primeTriangleSum
  apply Finset.sum_subset
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hI := Finset.mem_Ioc.mp hn'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hI.2⟩, hn'.2⟩
  · intro n hn hnot
    have hn' := Finset.mem_filter.mp hn
    have hI := Finset.mem_Ioc.mp hn'.1
    have hle : n ≤ ⌊x⌋₊ := by
      by_contra! hh
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hh, hI.2⟩, hn'.2⟩)
    rw [triangleWeight_eq_zero_of_le (by exact_mod_cast hI.1) ((Nat.le_floor_iff hx).mp hle),
      mul_zero]

private theorem primeTriangle_comparison {x : ℝ} (hx : 0 ≤ x) :
    primeTriangleSum x ≤ mangoldtHingeSum x ∧
      mangoldtHingeSum x ≤ primeTriangleSum x +
        (Chebyshev.psi (4 * x) - Chebyshev.theta (4 * x)) := by
  let s := Finset.Ioc 0 ⌊4 * x⌋₊
  let f := fun n : ℕ => ArithmeticFunction.vonMangoldt n * triangleWeight x n
  have hp : ∑ n ∈ s.filter Nat.Prime, f n = primeTriangleSum x := by
    rw [primeTriangleSum_eq_prefix hx]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show f n = ArithmeticFunction.vonMangoldt n * triangleWeight x n from rfl,
      ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  have hsplit : mangoldtHingeSum x =
      primeTriangleSum x + ∑ n ∈ s.filter (fun n => ¬n.Prime), f n := by
    change ∑ n ∈ s, f n = _
    rw [← hp]
    exact (Finset.sum_filter_add_sum_filter_not s Nat.Prime f).symm
  have hnonneg : 0 ≤ ∑ n ∈ s.filter (fun n => ¬n.Prime), f n := by
    apply Finset.sum_nonneg
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (triangleWeight_bounds hx hn').1
  have hupper : (∑ n ∈ s.filter (fun n => ¬n.Prime), f n) ≤
      ∑ n ∈ s.filter (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (triangleWeight_bounds hx hn').2
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, hsplit]
  exact ⟨le_add_of_nonneg_right hnonneg, add_le_add_right hupper _⟩

/-- The prime-only triangle on `(k/4,k]` tests RH by one eventual lower bound. -/
theorem rh_iff_eventual_prime_triangle_lower :
    RiemannHypothesis ↔ ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k : ℕ in atTop,
      2 * ((k : ℝ) / 4) * Real.log 2 - A * Real.sqrt ((k : ℝ) / 4) ≤
        primeTriangleSum ((k : ℝ) / 4) := by
  rw [rh_iff_eventual_quarter_triangular_lower]
  constructor
  · rintro ⟨A, hA, hs⟩
    obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    refine ⟨A + 2 * max C 0, by positivity, ?_⟩
    filter_upwards [hs] with k hk
    let x : ℝ := (k : ℝ) / 4
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hc := (hC (4 * x)).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _))
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num] at hc
    change 2 * x * Real.log 2 - A * Real.sqrt x ≤ mangoldtHingeSum x at hk
    change 2 * x * Real.log 2 - (A + 2 * max C 0) * Real.sqrt x ≤ primeTriangleSum x
    linarith [(primeTriangle_comparison hx).2]
  · rintro ⟨A, hA, hs⟩
    exact ⟨A, hA, hs.mono fun k hk => hk.trans (primeTriangle_comparison (by positivity)).1⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle

#print axioms D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle.rh_iff_eventual_prime_triangle_lower
