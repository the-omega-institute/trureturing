/- GID: D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal three-axis floors force a lower bound on the denominator of a missed window. -/
import D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover
import D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator
import D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! The literal fixed-clock budgets convert a padded integer-box label into the
two approximation bounds at the same actual Robin cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport

open Real Filter
open scoped BigOperators Topology
open D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover
  (ShortLabel delta errorSum jointSquare phase radius short_label_miss_obstruction)
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature (d actual_root_equation)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic (fixed_layer_root_offset_tendsto)
open D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator
  (eventually_mode_three_short_denominator_exclusion)
open D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
  (price targetPrice inverseClock exists_fixedB_integerClock)

private def lambda2 (β : ℝ) : ℝ := (3 * β - 2) / 2
private def lambda3 (β : ℝ) : ℝ := (10 * β - 7) / 6
private def lambda5 (β : ℝ) : ℝ := (18 * β - 13) / 10

private def mass (rate κζ Lbar : ℝ) : ℝ := κζ * exp (rate * Lbar) * Lbar ^ 2

/-- The two nested floors on axis zero and the original floors on axes one and two. -/
def boxSizes (β κζ Lbar : ℝ) : Fin 3 → ℤ :=
  let A2 : ℤ := ⌊mass (lambda2 β) κζ Lbar⌋
  ![⌊log 2 * (A2 : ℝ) / (32 * Lbar)⌋,
    ⌊mass (lambda3 β) κζ Lbar⌋, ⌊mass (lambda5 β) κζ Lbar⌋]

/-- The three ratios from the actual cutoffs at the single supplied parameter. -/
def coordinates (X : ℝ) : Fin 3 → ℝ :=
  ![log X / d 2 X, d 3 X / d 2 X, d 5 X / d 2 X]

def transportConstant (κζ : ℝ) : ℝ :=
  64 * exp (1 / 15) * sqrt 43 / (3 * log 2 * κζ)

private theorem abs_delta_le_of_jointSquare
    {N : Fin 3 → ℤ} {θ : Fin 3 → ℝ} {w : ℝ} {h : ℤ} {p : Fin 3 → ℤ}
    (hsq : jointSquare N h p θ w ≤ (43 : ℝ) / 9) (i : Fin 3)
    (hpad : 0 < (N i : ℝ) + 2) :
    |delta h p θ i| ≤ (sqrt 43 / 3) / ((N i : ℝ) + 2) := by
  let a (j : Fin 3) : ℝ := ((N j : ℝ) + 2) * delta h p θ j
  change (∑ j, a j ^ 2) + (w * (h : ℝ)) ^ 2 ≤ (43 : ℝ) / 9 at hsq
  have hs : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
    Finset.single_le_sum (f := fun j => a j ^ 2) (fun j _ => sq_nonneg (a j))
      (Finset.mem_univ i)
  have hC : (sqrt (43 : ℝ) / 3) ^ 2 = 43 / 9 := by
    rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 43)]
    norm_num
  have ha : |a i| ≤ sqrt 43 / 3 :=
    abs_le_of_sq_le_sq (by rw [hC]; linarith only [hs, hsq, sq_nonneg (w * (h : ℝ))])
      (div_nonneg (sqrt_nonneg _) (by norm_num))
  change |((N i : ℝ) + 2) * delta h p θ i| ≤ _ at ha
  rw [abs_mul, abs_of_pos hpad, mul_comm] at ha
  exact (le_div_iff₀ hpad).2 ha

/-- The padded literal floors give both errors uniformly over the reference log and signed label. -/
theorem floor_budget_errors {β κζ X Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ}
    (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κζ)
    (hL2 : 2 ≤ log X) (hLκ : 1 + 2 / κζ ≤ log X) (hclose : |log X - Lbar| ≤ 1)
    (hsq : jointSquare (boxSizes β κζ Lbar) h p (coordinates X) w ≤ (43 : ℝ) / 9) :
    let L := log X
    let K := transportConstant κζ
    |(h : ℝ) * (L / d 2 X) - (p 0 : ℝ)| ≤ K * exp (-(L / 15)) ∧
    |(h : ℝ) * (d 3 X / d 2 X) - (p 1 : ℝ)| ≤ K * exp (-(L / 15)) / L ^ 2 := by
  let L := log X
  let N := boxSizes β κζ Lbar
  let M2 := mass (lambda2 β) κζ Lbar
  let M3 := mass (lambda3 β) κζ Lbar
  let A2 : ℤ := ⌊M2⌋
  let C := sqrt 43 / 3
  let c := log 2 * κζ / 64
  let E := exp (1 / 15)
  let e := exp (-(L / 15))
  change 2 ≤ L at hL2
  change 1 + 2 / κζ ≤ L at hLκ
  change |L - Lbar| ≤ 1 at hclose
  have hL : 0 < L := by linarith only [hL2]
  have hnear := (abs_le.mp hclose).2
  have hbarHalf : L / 2 ≤ Lbar := by linarith only [hnear, hL2]
  have hbarOne : 1 ≤ Lbar := by linarith only [hnear, hL2]
  have hbar : 0 < Lbar := zero_lt_one.trans_le hbarOne
  have hbarκ : 2 / κζ ≤ Lbar := by linarith only [hnear, hLκ]
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog2le : log 2 ≤ 1 := log_two_lt_d9.le.trans (by norm_num)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlambda2 : 1 / 15 ≤ lambda2 β := by unfold lambda2; linarith only [hβ.1]
  have hlambda3 : 1 / 15 ≤ lambda3 β := by unfold lambda3; linarith only [hβ.1]
  have hexp2 : 1 ≤ exp (lambda2 β * Lbar) :=
    one_le_exp_iff.mpr (mul_nonneg (by linarith only [hlambda2]) hbar.le)
  have hM2 : 2 ≤ M2 := calc
    2 ≤ Lbar * κζ := (div_le_iff₀ hκζ).mp hbarκ
    _ = κζ * Lbar := mul_comm _ _
    _ ≤ (κζ * exp (lambda2 β * Lbar)) * Lbar :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hκζ.le hexp2) hbar.le
    _ ≤ M2 := by
      change (κζ * exp (lambda2 β * Lbar)) * Lbar ≤
        (κζ * exp (lambda2 β * Lbar)) * Lbar ^ 2
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simpa only [pow_two] using le_mul_of_one_le_right hbar.le hbarOne
  have hfloor2 : M2 < (A2 : ℝ) + 1 := Int.lt_floor_add_one M2
  have hA2 : M2 / 2 ≤ (A2 : ℝ) := by linarith only [hM2, hfloor2]
  have hJquot : log 2 * (κζ * exp (lambda2 β * Lbar)) * Lbar / 64 ≤
      log 2 * (A2 : ℝ) / (32 * Lbar) := by
    apply (le_div_iff₀ (show 0 < 32 * Lbar by positivity)).mpr
    calc
      _ = log 2 * (M2 / 2) := by dsimp only [M2, mass]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hA2 hlog2.le
  have hJfloor : log 2 * (A2 : ℝ) / (32 * Lbar) < (N 0 : ℝ) + 1 :=
    Int.lt_floor_add_one (log 2 * (A2 : ℝ) / (32 * Lbar))
  have hJpad : log 2 * (κζ * exp (lambda2 β * Lbar)) * Lbar / 64 ≤ (N 0 : ℝ) + 2 := by
    linarith only [hJquot, hJfloor]
  have hJ : log 2 * (κζ * exp (lambda2 β * Lbar)) / 64 ≤ (N 0 : ℝ) + 2 := calc
    _ ≤ log 2 * (κζ * exp (lambda2 β * Lbar)) * Lbar / 64 :=
      div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hbarOne) (by norm_num)
    _ ≤ _ := hJpad
  have hfloor3 : M3 < (N 1 : ℝ) + 1 := Int.lt_floor_add_one M3
  have hA3 : M3 ≤ (N 1 : ℝ) + 2 := by linarith only [hfloor3]
  have hpad0 : 0 < (N 0 : ℝ) + 2 := (by positivity :
    0 < log 2 * (κζ * exp (lambda2 β * Lbar)) / 64).trans_le hJ
  have hpad1 : 0 < (N 1 : ℝ) + 2 := (show 0 < M3 by
    dsimp only [M3, mass]; positivity).trans_le hA3
  have hexp (a : ℝ) (ha : 1 / 15 ≤ a) : 1 ≤ E * e * exp (a * Lbar) := by
    have hm := mul_le_mul_of_nonneg_right ha hbar.le
    dsimp only [E, e]
    rw [← exp_add, ← exp_add]
    exact one_le_exp_iff.mpr (by linarith only [hnear, hm])
  have hscale0 : c ≤ E * e * ((N 0 : ℝ) + 2) := calc
    c = c * 1 := (mul_one c).symm
    _ ≤ c * (E * e * exp (lambda2 β * Lbar)) :=
      mul_le_mul_of_nonneg_left (hexp _ hlambda2) hc.le
    _ = E * e * (log 2 * (κζ * exp (lambda2 β * Lbar)) / 64) := by dsimp only [c]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by positivity)
  have hc4 : c ≤ κζ / 4 := calc
    _ ≤ 1 * κζ / 64 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlog2le hκζ.le) (by norm_num)
    _ ≤ _ := by linarith only [hκζ]
  have hbarSq : (L / 2) ^ 2 ≤ Lbar ^ 2 :=
    pow_le_pow_left₀ (by positivity) hbarHalf 2
  have hscale1 : c * L ^ 2 ≤ E * e * ((N 1 : ℝ) + 2) := calc
    _ ≤ (κζ / 4) * L ^ 2 := mul_le_mul_of_nonneg_right hc4 (sq_nonneg L)
    _ ≤ ((κζ / 4) * L ^ 2) * (E * e * exp (lambda3 β * Lbar)) :=
      le_mul_of_one_le_right (by positivity) (hexp _ hlambda3)
    _ = E * e * ((κζ * exp (lambda3 β * Lbar)) * (L / 2) ^ 2) := by ring
    _ ≤ E * e * M3 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hbarSq (by positivity)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hA3 (by positivity)
  have hK : C / c * E = transportConstant κζ := by
    dsimp only [C, c, E, transportConstant]
    field_simp [hκζ.ne', hlog2.ne'] <;> ring
  have htransport (D T : ℝ) (hD : 0 < D) (hT : 0 < T)
      (hs : c * T ≤ E * e * D) : C / D ≤ transportConstant κζ * e / T := by
    have hdiv : C / c * c = C := div_mul_cancel₀ C hc.ne'
    have hC : 0 ≤ C := div_nonneg (sqrt_nonneg _) (by norm_num)
    apply (div_le_div_iff₀ hD hT).mpr
    calc
      C * T = C / c * (c * T) := by rw [← mul_assoc, hdiv]
      _ ≤ C / c * (E * e * D) := mul_le_mul_of_nonneg_left hs (div_nonneg hC hc.le)
      _ = (C / c * E) * e * D := by ring
      _ = _ := by rw [hK]
  have herror0 := abs_delta_le_of_jointSquare hsq 0 hpad0
  have herror1 := abs_delta_le_of_jointSquare hsq 1 hpad1
  change |delta h p (coordinates X) 0| ≤ transportConstant κζ * e ∧
    |delta h p (coordinates X) 1| ≤ transportConstant κζ * e / L ^ 2
  refine ⟨herror0.trans ?_, herror1.trans (htransport _ _ hpad1 (sq_pos_of_pos hL) hscale1)⟩
  simpa only [mul_one, div_one] using
    htransport _ 1 hpad0 zero_lt_one (by simpa only [mul_one] using hscale0)

/-- Every signed padded label at the actual cutoffs has denominator beyond the short range. -/
private theorem eventually_padded_label_denominator_gt {β κζ : ℝ}
    (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κζ) :
    ∀ᶠ X : ℝ in atTop, ∀ Lbar : ℝ, |log X - Lbar| ≤ 1 → ∀ w : ℝ,
      ∀ Q : ShortLabel (boxSizes β κζ Lbar) (coordinates X) w,
        log X / (50 * log (log X)) < (Q.h : ℝ) := by
  let K := transportConstant κζ
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp only [K, transportConstant]; positivity
  have hd2 : Tendsto (d 2) atTop (𝓝 (log 2)) :=
    fixed_layer_root_offset_tendsto (by norm_num)
  have hd3 : Tendsto (d 3) atTop (𝓝 (log 3)) :=
    fixed_layer_root_offset_tendsto (by norm_num)
  have hθ : Tendsto (fun X : ℝ => d 3 X / d 2 X) atTop (𝓝 (log 3 / log 2)) :=
    hd3.div hd2 hlog2.ne'
  have hratio : (3 / 2 : ℝ) < log 3 / log 2 := (lt_div_iff₀ hlog2).mpr (by
    linarith only [log_three_gt_d9, log_two_lt_d9])
  have hlog2lt : log 2 < 1 := log_two_lt_d9.trans (by norm_num)
  filter_upwards [eventually_mode_three_short_denominator_exclusion hK,
    actual_root_equation (j := 2) (by norm_num),
    hd2.eventually (eventually_lt_nhds hlog2lt), hθ.eventually (eventually_gt_nhds hratio),
    tendsto_log_atTop.eventually_ge_atTop 2,
    tendsto_log_atTop.eventually_ge_atTop (1 + 2 / κζ),
    tendsto_log_atTop.eventually_ge_atTop (15 * K)]
    with X hexclude hroot hd2lt hθgt hL2 hLκ hLK
  dsimp only at hexclude
  intro Lbar hclose w Q
  obtain ⟨he0, he1⟩ := floor_budget_errors hβ hκζ hL2 hLκ hclose Q.joint_bound
  let L := log X
  let x := L / d 2 X
  let θ := d 3 X / d 2 X
  change 2 ≤ L at hL2
  change 15 * K ≤ L at hLK
  change (3 / 2 : ℝ) < θ at hθgt
  change d 2 X < 1 at hd2lt
  change |(Q.h : ℝ) * x - (Q.p 0 : ℝ)| ≤ K * exp (-(L / 15)) at he0
  change |(Q.h : ℝ) * θ - (Q.p 1 : ℝ)| ≤ K * exp (-(L / 15)) / L ^ 2 at he1
  have hL : 0 < L := by linarith only [hL2]
  have hx : L ≤ x := (le_div_iff₀ hroot.1).mpr (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd2lt.le hL.le)
  have hsmall : K * exp (-(L / 15)) ≤ 1 := calc
    _ ≤ exp (L / 15) * exp (-(L / 15)) :=
      mul_le_mul_of_nonneg_right
        ((show K ≤ L / 15 + 1 by linarith only [hLK]).trans (add_one_le_exp _))
        (exp_pos _).le
    _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hLsq : 1 ≤ L ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1)
      (show 1 ≤ L by linarith only [hL2]) 2
  have hsmall' : K * exp (-(L / 15)) / L ^ 2 ≤ 1 :=
    (div_le_iff₀ (sq_pos_of_pos hL)).mpr (by simpa only [one_mul] using hsmall.trans hLsq)
  have hh := Q.positive
  have hhR : (1 : ℝ) ≤ (Q.h : ℝ) := by exact_mod_cast hh
  have label_pos (k : ℤ) (z : ℝ) (hz : 1 < z)
      (he : |(Q.h : ℝ) * z - (k : ℝ)| ≤ 1) : 0 < k := by
    have hzle := le_mul_of_one_le_left (show 0 ≤ z by linarith only [hz]) hhR
    have hk : (0 : ℝ) < (k : ℝ) := by linarith only [(abs_le.mp he).2, hz, hzle]
    exact_mod_cast hk
  have hp0 := label_pos (Q.p 0) x (by linarith only [hx, hL2]) (he0.trans hsmall)
  have hp3 := label_pos (Q.p 1) θ (by linarith only [hθgt]) (he1.trans hsmall')
  have hNat : 0 < Q.h.toNat := by
    have hc : (Q.h.toNat : ℤ) = Q.h := Int.toNat_of_nonneg (by omega)
    omega
  have cast_toNat (k : ℤ) (hk : 0 ≤ k) : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk
  have hhcast := cast_toNat Q.h (by omega)
  have hp0cast := cast_toNat (Q.p 0) hp0.le
  have hp3cast := cast_toNat (Q.p 1) hp3.le
  apply lt_of_not_ge
  intro hshort
  exact hexclude Q.h.toNat (Q.p 0).toNat (Q.p 1).toNat hNat
    (by simpa only [hhcast] using hshort)
    ⟨by simpa only [hhcast, hp0cast] using he0,
      by simpa only [hhcast, hp3cast] using he1⟩

private theorem eventually_box_scale {β κ ζ : ℝ}
    (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κ * ζ) (hζ : 0 < ζ) :
    ∀ᶠ X : ℝ in atTop, ∀ Lbar : ℝ, |log X - Lbar| ≤ 1 →
      ∀ i, (43 : ℝ) / 9 < (boxSizes β (κ * ζ) Lbar i : ℝ) *
        (ζ * exp (-((3 / 2 - 2 * β) * log X)) * (log X) ^ 5 / (4 * d 2 X)) := by
  let r : ℝ := 4 / 125
  let ε := 3 / 2 - 2 * β
  let c := log 2 * (κ * ζ) / 64
  let a := c * exp (-r) / 2
  have hr : 0 < r := by norm_num [r]
  have hrate : 0 < r - ε := by dsimp [r, ε]; linarith only [hβ.1]
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog2lt : log 2 < 1 := log_two_lt_d9.trans (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hcoef : 0 < a * (ζ / 4) := by positivity
  have hexp {s : ℝ} (hs : 0 < s) : Tendsto (fun X : ℝ => exp (s * log X)) atTop atTop :=
    tendsto_exp_atTop.comp ((tendsto_id.const_mul_atTop hs).comp tendsto_log_atTop)
  have hd₂ : Tendsto (d 2) atTop (𝓝 (log 2)) :=
    fixed_layer_root_offset_tendsto (by norm_num)
  filter_upwards [tendsto_log_atTop.eventually_ge_atTop 2,
    tendsto_log_atTop.eventually_ge_atTop (1 + 2 / (κ * ζ)),
    ((hexp hr).const_mul_atTop ha).eventually_ge_atTop 1,
    ((hexp hrate).const_mul_atTop hcoef).eventually_gt_atTop (43 / 9),
    actual_root_equation (j := 2) (by norm_num),
    hd₂.eventually (eventually_lt_nhds hlog2lt)]
    with X hL2 hLκ hgrowth hfast hroot hd₂lt
  intro Lbar hclose i
  let L := log X
  have hnear : L - Lbar ≤ 1 := (abs_le.mp hclose).2
  have hbarOne : 1 ≤ Lbar := by linarith only [hnear, hL2]
  have hbar : 0 < Lbar := zero_lt_one.trans_le hbarOne
  have hbarκ : 2 / (κ * ζ) ≤ Lbar := by linarith only [hnear, hLκ]
  have hr2 : r ≤ lambda2 β := by dsimp [r, lambda2]; linarith only [hβ.1]
  have hr3 : r ≤ lambda3 β := by dsimp [r, lambda3]; linarith only [hβ.1]
  have hr5 : r ≤ lambda5 β := by dsimp [r, lambda5]; linarith only [hβ.1]
  have hcc : c ≤ κ * ζ := calc
    _ ≤ 1 * (κ * ζ) / 64 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlog2lt.le hκζ.le) (by norm_num)
    _ ≤ _ := by linarith only [hκζ]
  have hbarSq : 1 ≤ Lbar ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) hbarOne 2
  have hcomp {s : ℝ} (hs : r ≤ s) : 2 * (a * exp (r * L)) ≤ c * exp (s * Lbar) := by
    have hp := mul_le_mul_of_nonneg_right hs hbar.le
    have hn := mul_le_mul_of_nonneg_left hnear hr.le
    calc
      _ = c * exp (r * L - r) := by dsimp [a]; rw [sub_eq_add_neg, exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hp, hn])) hc.le
  have hfloor (v : ℝ) (hv : 2 * (a * exp (r * L)) ≤ v) :
      a * exp (r * L) ≤ (⌊v⌋ : ℝ) := by
    linarith only [hv, Int.lt_floor_add_one v, hgrowth]
  have hrounded {s : ℝ} (hs : r ≤ s) :
      a * exp (r * L) ≤ (⌊mass s (κ * ζ) Lbar⌋ : ℝ) := by
    apply hfloor
    calc
      _ ≤ c * exp (s * Lbar) := hcomp hs
      _ ≤ (κ * ζ) * exp (s * Lbar) := mul_le_mul_of_nonneg_right hcc (exp_pos _).le
      _ ≤ mass s (κ * ζ) Lbar := le_mul_of_one_le_right (by positivity) hbarSq
  have hJ : a * exp (r * L) ≤ (boxSizes β (κ * ζ) Lbar 0 : ℝ) := by
    let M := mass (lambda2 β) (κ * ζ) Lbar
    have hs : 0 ≤ lambda2 β := hr.le.trans hr2
    have he : 1 ≤ exp (lambda2 β * Lbar) := one_le_exp_iff.mpr (mul_nonneg hs hbar.le)
    have hM : 2 ≤ M := calc
      _ ≤ Lbar * (κ * ζ) := (div_le_iff₀ hκζ).mp hbarκ
      _ = (κ * ζ) * Lbar := mul_comm _ _
      _ ≤ (κ * ζ) * exp (lambda2 β * Lbar) * Lbar :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hκζ.le he) hbar.le
      _ ≤ M := mul_le_mul_of_nonneg_left
        (by simpa only [pow_two] using le_mul_of_one_le_right hbar.le hbarOne) (by positivity)
    have hA : M / 2 ≤ (⌊M⌋ : ℝ) := by linarith only [hM, Int.lt_floor_add_one M]
    change a * exp (r * L) ≤ (⌊log 2 * (⌊M⌋ : ℝ) / (32 * Lbar)⌋ : ℝ)
    apply hfloor
    calc
      _ ≤ c * exp (lambda2 β * Lbar) := hcomp hr2
      _ ≤ (c * exp (lambda2 β * Lbar)) * Lbar :=
        le_mul_of_one_le_right (by positivity) hbarOne
      _ ≤ log 2 * (⌊M⌋ : ℝ) / (32 * Lbar) := by
        apply (le_div_iff₀ (show 0 < 32 * Lbar by positivity)).mpr
        convert mul_le_mul_of_nonneg_left hA hlog2.le using 1
        dsimp [c, M, mass]
        ring
  have hN : a * exp (r * L) ≤ (boxSizes β (κ * ζ) Lbar i : ℝ) := by
    fin_cases i
    · exact hJ
    · exact hrounded hr3
    · exact hrounded hr5
  have hLpow : 1 ≤ L ^ 5 := by
    simpa only [one_pow] using pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1)
      (show 1 ≤ L by linarith only [hL2]) 5
  have hw : (ζ / 4) * exp (-(ε * L)) ≤ ζ * exp (-(ε * L)) * L ^ 5 / (4 * d 2 X) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hroot.1)).mpr
    calc
      _ = (ζ * exp (-(ε * L))) * d 2 X := by ring
      _ ≤ (ζ * exp (-(ε * L))) * L ^ 5 :=
        mul_le_mul_of_nonneg_left (hd₂lt.le.trans hLpow) (by positivity)
  exact hfast.trans_le (calc
    _ = (a * exp (r * L)) * ((ζ / 4) * exp (-(ε * L))) := by
      rw [sub_mul, sub_eq_add_neg, exp_add]
      ring
    _ ≤ _ := mul_le_mul hN hw (by positivity) ((by positivity : 0 ≤ a * exp (r * L)).trans hN))

/-- Every late miss at a fixed perturbation of the exact integer clock gives the
original primitive phase obstruction and a denominator beyond the mode-three short range. -/
theorem exists_fixed_clock_box_miss_obstruction
    {β κ ζ : ℝ} (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κ * ζ) (hζ : 0 < ζ)
    : ∃ clock : ℝ → ℤ → ℝ, ∀ B : ℝ,
    Tendsto (clock B) atTop atTop ∧ ∀ᶠ e : ℤ in atTop,
      let X := exp (clock B e)
      let L := log X
      let N := boxSizes β (κ * ζ) (clock 0 e)
      let θ := coordinates X
      let w := ζ * exp (-((3 / 2 - 2 * β) * L)) * L ^ 5 / (4 * d 2 X)
      let t := log 2 / d 2 X - 2 * w
      price (3 / 2 - 2 * β) B L = targetPrice e ∧
      inverseClock (3 / 2 - 2 * β) B L = (e : ℝ) ∧
      ((¬ ∃ (b : Fin 3 → ℤ) (a : ℤ),
        (∀ i, N i ≤ b i ∧ b i ≤ 2 * N i) ∧
        t < (∑ i, (b i : ℝ) * θ i) - (a : ℝ) ∧
        (∑ i, (b i : ℝ) * θ i) - (a : ℝ) < t + w) →
      ∃ Q : ShortLabel N θ w,
        (∀ Q' : ShortLabel N θ w, Q' = Q) ∧
        (∀ n : ℤ, radius N Q.h Q.p θ w - (Q.h : ℝ) * errorSum Q.h Q.p θ ≤
          |(n : ℝ) - phase N Q.h Q.p θ t w|) ∧
        ((Q.h : ℝ) * w + ∑ i, ((N i : ℝ) - 2 * (Q.h : ℝ)) * |delta Q.h Q.p θ i|) ≤ 1 ∧
        L / (50 * log L) < (Q.h : ℝ) ∧ (Q.h : ℝ) ≤ 1 / w) := by
  have hε : 0 < (3 / 2 : ℝ) - 2 * β := by linarith only [hβ.2]
  obtain ⟨clock, _, hclock⟩ := exists_fixedB_integerClock hε
  refine ⟨clock, fun B => ?_⟩
  obtain ⟨hT, R, hR, hsol⟩ := hclock B
  refine ⟨hT, ?_⟩
  have hX : Tendsto (fun e => exp (clock B e)) atTop atTop := tendsto_exp_atTop.comp hT
  filter_upwards [hX.eventually (eventually_padded_label_denominator_gt hβ hκζ),
    hX.eventually (eventually_box_scale hβ hκζ hζ), hsol] with e hgt hscale hroot
  dsimp only
  refine ⟨by simpa only [log_exp] using hroot.2.1,
    by simpa only [log_exp] using hroot.2.2.1, ?_⟩
  intro hmiss
  let X := exp (clock B e)
  let L := log X
  let N := boxSizes β (κ * ζ) (clock 0 e)
  let θ := coordinates X
  let w := ζ * exp (-((3 / 2 - 2 * β) * L)) * L ^ 5 / (4 * d 2 X)
  let t := log 2 / d 2 X - 2 * w
  have hnear : |log X - clock 0 e| ≤ 1 := by simpa only [X, log_exp] using hroot.2.2.2.1
  have hNw : ∀ i, (43 : ℝ) / 9 < (N i : ℝ) * w := hscale (clock 0 e) hnear
  have hN1 : 0 ≤ N 1 := by
    change 0 ≤ ⌊mass (lambda3 β) (κ * ζ) (clock 0 e)⌋
    exact Int.floor_nonneg.mpr
      (mul_nonneg (mul_nonneg hκζ.le (exp_pos _).le) (sq_nonneg _))
  have hN1R : (0 : ℝ) ≤ (N 1 : ℝ) := by exact_mod_cast hN1
  have hprod : 0 < (N 1 : ℝ) * w := (by norm_num : (0 : ℝ) < 43 / 9).trans (hNw 1)
  have hw : 0 < w := pos_of_mul_pos_right hprod hN1R
  obtain ⟨Q, huniq, hphase, hweight, hupper⟩ :=
    short_label_miss_obstruction N θ t w hw hNw hmiss
  exact ⟨Q, huniq, hphase, hweight, hgt (clock 0 e) hnear w Q, hupper⟩

end D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
