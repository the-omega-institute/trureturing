/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Central-binomial coordinate formulae for the actual Gaussian resolvents. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement

/-! The central-binomial formulae use ordinary complex bilinear transpose. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter Set Metric

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent

open OriginalGaussianMatrix OriginalGaussianResolvent
open OriginalGaussianWeightedResolvent OriginalGaussianDifferentiation
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open D5.S3.Analytic.OriginalHalfBinomialPeriod

/-- Shifted central-binomial series, with its constant term retained. -/
def shiftedCentralSeries (x : ℂ) (s : ℕ) : ℂ :=
  ∑' k : ℕ, (centralWeight k : ℂ) * centralWeight (k + s) * x ^ k

/-- The derivative series is indexed without negative powers at the origin. -/
def shiftedCentralDerivative (x : ℂ) (s : ℕ) : ℂ :=
  ∑' k : ℕ, (k + 1 : ℂ) * centralWeight (k + 1) *
    centralWeight (k + 1 + s) * x ^ k

def centralColumnJet (x : ℂ) (s : ℕ) : ℂ :=
  s * shiftedCentralSeries x s + 2 * x * shiftedCentralDerivative x s -
    2 * x * shiftedCentralSeries x s * shiftedCentralDerivative x 0 / period x

def explicitOddEntry (z : ℂ) (s t : ℕ) : ℂ :=
  (-1 : ℂ) ^ (s + t) * z ^ (s + t) * (1 - z ^ 2) *
    ((s : ℂ) * shiftedCentralSeries (z ^ 2) s * centralColumnJet (z ^ 2) t +
      (t : ℂ) * centralColumnJet (z ^ 2) s * shiftedCentralSeries (z ^ 2) t) /
    (2 * (Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (t : ℝ) : ℂ) * (s + t))

def squareResolvent (z : ℂ) : H →L[ℂ] H := ∑' k : ℕ, (operator z ^ 2) ^ k

def oddResolvent (z : ℂ) : H →L[ℂ] H := operator z * squareResolvent z

private lemma weight_norm_le (n : ℕ) : ‖(centralWeight n : ℂ)‖ ≤ 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (centralWeight_nonneg n)] using weight_le_one n

private lemma central_coefficient_bound (s k : ℕ) :
    ‖(centralWeight k : ℂ) * centralWeight (k + s)‖ ≤ 1 := by
  simpa only [norm_mul, one_mul] using
    mul_le_mul (weight_norm_le k) (weight_norm_le (k + s)) (norm_nonneg _) zero_le_one

private lemma polynomial_series {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (n + 1 : ℝ) ^ 2) {x : ℂ} (hx : ‖x‖ < 1) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, a n * w ^ n)
      (∑' n : ℕ, (n + 1 : ℂ) * a (n + 1) * x ^ n) x := by
  obtain ⟨R, hxR, hR1⟩ := exists_between hx
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg x) hxR
  have hs := derivative_shifted_geometric hR hR1 2
  have hb (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) R) :
      ‖a n * w ^ n‖ ≤ (n + 1 : ℝ) ^ 2 * R ^ n := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (ha n)
      (pow_le_pow_left₀ (norm_nonneg w) (by simpa using (Metric.mem_ball.mp hw).le) n)
      (by positivity) (by positivity)
  have hd (n : ℕ) : DifferentiableOn ℂ (fun w : ℂ => a n * w ^ n)
      (Metric.ball 0 R) := fun w _ =>
    ((hasDerivAt_pow n w).const_mul (a n)).differentiableAt.differentiableWithinAt
  have hm : x ∈ Metric.ball (0 : ℂ) R := by simpa using hxR
  have hsum := Complex.hasSum_deriv_of_summable_norm hs hd Metric.isOpen_ball hb hm
  have hshift := (hasSum_nat_add_iff' 1).mpr hsum
  simp only [Finset.sum_range_one, deriv_const_mul_field, deriv_pow_field,
    Nat.cast_zero, zero_mul, mul_zero, sub_zero, Nat.add_sub_cancel] at hshift
  have hdiff := (Complex.differentiableOn_tsum_of_summable_norm hs hd
    Metric.isOpen_ball hb).differentiableAt (Metric.isOpen_ball.mem_nhds hm)
  convert hdiff.hasDerivAt using 1
  exact (tsum_congr (fun n => by push_cast; ring)).trans hshift.tsum_eq

private lemma central_hasDerivAt {x : ℂ} (hx : ‖x‖ < 1) (s : ℕ) :
    HasDerivAt (fun w => shiftedCentralSeries w s) (shiftedCentralDerivative x s) x := by
  have hb (k : ℕ) : ‖(centralWeight k : ℂ) * centralWeight (k + s)‖ ≤
      (k + 1 : ℝ) ^ 2 := (central_coefficient_bound s k).trans
        (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  simpa only [shiftedCentralSeries, shiftedCentralDerivative, mul_assoc] using
    polynomial_series hb hx

private lemma central_derivative_differentiable {x : ℂ} (hx : ‖x‖ < 1) (s : ℕ) :
    DifferentiableAt ℂ (fun w => shiftedCentralDerivative w s) x := by
  have hb (k : ℕ) :
      ‖(k + 1 : ℂ) * centralWeight (k + 1) * centralWeight (k + 1 + s)‖ ≤
        (k + 1 : ℝ) ^ 2 := by
    have h := central_coefficient_bound s (k + 1)
    rw [mul_assoc, norm_mul, show ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) by
      exact_mod_cast Complex.norm_natCast (k + 1)]
    calc
      _ ≤ (k + 1 : ℝ) * 1 := mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ _ := by nlinarith
  exact (polynomial_series hb hx).differentiableAt

private lemma period_eq_central (x : ℂ) : period x = shiftedCentralSeries x 0 := by
  apply tsum_congr
  intro k
  rw [halfBinomial_eq_signed_centralWeight]
  rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
  norm_num [pow_two]

private lemma central_ofReal (r : ℝ) (s : ℕ) :
    shiftedCentralSeries (r : ℂ) s = (L r s : ℂ) := by
  rw [L, Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  push_cast
  rfl

lemma period_ofReal (r : ℝ) : period (r : ℂ) = (F r : ℂ) := by
  rw [period_eq_central, central_ofReal]
  have h := congrArg Complex.re (period_eq_central (r : ℂ))
  rw [central_ofReal] at h
  change F r = L r 0 at h
  rw [h]

private lemma norm_sq_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖z ^ 2‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)

private def explicitColumn (z : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + 1) * z ^ (n + 1) * shiftedCentralSeries (z ^ 2) (n + 1) /
    ((Real.sqrt (n + 1 : ℝ) : ℂ) * period (z ^ 2))

private lemma explicitColumn_differentiable {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    DifferentiableAt ℂ (fun w => explicitColumn w n) z := by
  have hp : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z := by fun_prop
  have hA := (central_hasDerivAt (norm_sq_lt_one hz) (n + 1)).differentiableAt.comp z hp
  have hP := (picard_fuchs (norm_sq_lt_one hz)).1.comp z hp
  exact (((differentiableAt_const _).mul (differentiableAt_id.pow _)).mul hA).div
    ((differentiableAt_const _).mul hP)
    (mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne')
      (OriginalGaussianPeriodIdentity.period_ne_zero (norm_sq_lt_one hz)))

private lemma column_radial {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (n : ℕ) :
    columnSeries (t : ℂ) n = explicitColumn (t : ℂ) n := by
  have hr1 : t ^ 2 < 1 := pow_lt_one₀ ht.le ht1 (by norm_num)
  have hs : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht.le
  have hc : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have he := resolvent_column (sq_pos_of_pos ht) hr1 n
  rw [hs] at he
  have hsrc := sourceFamily_zero_eq_source (sq_nonneg t) hr1
  rw [hs] at hsrc
  rw [columnSeries, hsrc, he]
  simp only [explicitColumn, hc, central_ofReal, period_ofReal]

/-- The prescribed source column on the entire complex disk, including zero. -/
theorem columnSeries_entry_explicit_complex {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    columnSeries z n = (-1 : ℂ) ^ (n + 1) * z ^ (n + 1) *
      shiftedCentralSeries (z ^ 2) (n + 1) /
        ((Real.sqrt (n + 1 : ℝ) : ℂ) * period (z ^ 2)) := by
  have hleft : DifferentiableOn ℂ (fun w => columnSeries w n) (Metric.ball 0 1) := by
    intro w hw
    exact ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).hasFDerivAt.comp_hasDerivAt w
      (hasDerivAt_columnSeries (by simpa using hw))).differentiableAt.differentiableWithinAt
  have hright : DifferentiableOn ℂ (fun w => explicitColumn w n) (Metric.ball 0 1) :=
    fun w hw => (explicitColumn_differentiable (by simpa using hw) n).differentiableWithinAt
  have hacc : ∃ᶠ w in 𝓝[≠] (0 : ℂ), columnSeries w n = explicitColumn w n := by
    have ht : Tendsto (fun k : ℕ => 1 / ((k : ℂ) + 1)) atTop (𝓝 (0 : ℂ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hp : Tendsto (fun k : ℕ => 1 / ((k : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨ht, Eventually.of_forall (fun k => by
        simpa using (div_ne_zero one_ne_zero (by exact_mod_cast Nat.succ_ne_zero k) :
          (1 / ((k : ℂ) + 1)) ≠ 0))⟩
    apply hp.frequently
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hpos : 0 < (1 / ((k : ℝ) + 1)) := by positivity
    have hsmall : (1 / ((k : ℝ) + 1)) < 1 :=
      (div_lt_one (by positivity : 0 < (k : ℝ) + 1)).mpr (by linarith)
    have hcast : ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) = 1 / ((k : ℂ) + 1) := by
      push_cast
      rfl
    simpa only [hcast] using column_radial hpos hsmall n
  exact (hleft.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hright.analyticOnNhd Metric.isOpen_ball) isPreconnected_ball (by simp) hacc
    (by simpa using hz)

private lemma radial_column_derivative {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (Real.sqrt r : ℂ) • columnSeriesDerivative (Real.sqrt r : ℂ) =
      (1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ))) •
        resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) := by
  have h := congrArg (fun x : H => (2 : ℂ) • x)
    (radial_column_derivative_scaled hr hr1)
  simp only [radialColumnDerivative, smul_smul] at h
  have hz : (Real.sqrt r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  have hcoef : (2 : ℂ) * ((r : ℂ) * ((1 / (2 * Real.sqrt r) : ℝ) : ℂ)) =
      (Real.sqrt r : ℂ) := by
    push_cast
    rw [← hs]
    field_simp [hz]
    <;> ring
  rw [hcoef] at h
  convert h using 1
  congr 1
  simp only [radialNormalization]
  push_cast
  ring

private lemma column_derivative_jet {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    z * columnSeriesDerivative z n =
      (-1 : ℂ) ^ (n + 1) * z ^ (n + 1) * centralColumnJet (z ^ 2) (n + 1) /
        ((Real.sqrt (n + 1 : ℝ) : ℂ) * period (z ^ 2)) := by
  have hq := hasDerivAt_pow 2 z
  have hA := (central_hasDerivAt (norm_sq_lt_one hz) (n + 1)).comp z hq
  have hP : HasDerivAt (fun w : ℂ => period (w ^ 2))
      (shiftedCentralDerivative (z ^ 2) 0 * (2 * z)) z := by
    simpa only [← period_eq_central, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_def] using
      (central_hasDerivAt (norm_sq_lt_one hz) 0).comp z hq
  have hden : (Real.sqrt (n + 1 : ℝ) : ℂ) * period (z ^ 2) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne')
      (OriginalGaussianPeriodIdentity.period_ne_zero (norm_sq_lt_one hz))
  have hd := (((hasDerivAt_pow (n + 1) z).const_mul ((-1 : ℂ) ^ (n + 1))).mul hA).div
    (hP.const_mul (Real.sqrt (n + 1 : ℝ) : ℂ)) hden
  have hc := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_columnSeries hz)
  have he := hd.congr_of_eventuallyEq (show
      (fun w : ℂ => columnSeries w n) =ᶠ[𝓝 z] (fun w : ℂ => explicitColumn w n) from by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact columnSeries_entry_explicit_complex hw n)
  have hv := hc.unique he
  change columnSeriesDerivative z n = _ at hv
  rw [hv]
  simp only [centralColumnJet, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_apply, Pi.mul_apply, pow_succ] at *
  field_simp [hden, OriginalGaussianPeriodIdentity.period_ne_zero (norm_sq_lt_one hz)]
  <;> ring

private lemma radial_positive_column {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n =
      (-1 : ℂ) ^ (n + 1) * (Real.sqrt r : ℂ) ^ (n + 1) *
        (Real.sqrt (1 - r) : ℂ) * centralColumnJet (r : ℂ) (n + 1) /
          (Real.sqrt (n + 1 : ℝ) : ℂ) := by
  have he := congrArg (fun x : H => x n) (radial_column_derivative hr hr1)
  change (Real.sqrt r : ℂ) * columnSeriesDerivative (Real.sqrt r : ℂ) n =
    (1 / ((Real.sqrt (1 - r) : ℂ) * (F r : ℂ))) *
      resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n at he
  rw [column_derivative_jet (radial_norm_lt_one hr1),
    show (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) by exact_mod_cast Real.sq_sqrt hr.le,
    period_ofReal] at he
  have hF : (F r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)))
  have hb : (Real.sqrt (1 - r) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by linarith : 0 < 1 - r)).ne'
  have hn : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  field_simp [hF, hb, hn] at he ⊢
  linear_combination -he

private lemma radial_negative_column {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n =
      (-1 : ℂ) ^ (n + 1) * (Real.sqrt r : ℂ) ^ (n + 1) *
        (Real.sqrt (n + 1 : ℝ) : ℂ) * (Real.sqrt (1 - r) : ℂ) *
          shiftedCentralSeries (r : ℂ) (n + 1) := by
  rw [opposite_resolvent_weighted_source hr hr1]
  change ((Real.sqrt (1 - r) * F r : ℝ) : ℂ) * ((n + 1 : ℂ) * columnValue r n) = _
  rw [columnValue, central_ofReal]
  have hF : (F r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)))
  have hn : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  have hsq : (Real.sqrt (n + 1 : ℝ) : ℂ) ^ 2 = (n + 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  push_cast
  field_simp [hF, hn]
  simp only [← hsq]
  ring

private lemma signed_units {z : ℂ} (hz : ‖z‖ < 1) :
    resolvent z * (1 - operator z) = 1 ∧
      oppositeResolvent z * (1 + operator z) = 1 := by
  constructor
  · exact (summable_geometric_of_norm_lt_one (operator_norm_lt_one hz)).tsum_pow_mul_one_sub
  · simpa only [oppositeResolvent, sub_neg_eq_add] using
      (summable_geometric_of_norm_lt_one
        (by simpa using operator_norm_lt_one hz : ‖-operator z‖ < 1)).tsum_pow_mul_one_sub

private lemma square_unit {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - operator z ^ 2) * squareResolvent z = 1 := by
  have hb : ‖operator z ^ 2‖ < 1 := (norm_pow_le _ _).trans_lt
    (pow_lt_one₀ (norm_nonneg _) (operator_norm_lt_one hz) (by norm_num))
  exact (summable_geometric_of_norm_lt_one hb).one_sub_mul_tsum_pow

private lemma signed_square_factorization {z : ℂ} (hz : ‖z‖ < 1) :
    resolvent z = (1 + operator z) * squareResolvent z ∧
      oppositeResolvent z = (1 - operator z) * squareResolvent z := by
  have h := square_unit hz
  have hR := (signed_units hz).1
  have hV := (signed_units hz).2
  constructor
  · calc
      _ = resolvent z * ((1 - operator z ^ 2) * squareResolvent z) := by rw [h, mul_one]
      _ = (resolvent z * (1 - operator z)) * ((1 + operator z) * squareResolvent z) := by noncomm_ring
      _ = _ := by rw [hR, one_mul]
  · calc
      _ = oppositeResolvent z * ((1 - operator z ^ 2) * squareResolvent z) := by rw [h, mul_one]
      _ = (oppositeResolvent z * (1 + operator z)) * ((1 - operator z) * squareResolvent z) := by noncomm_ring
      _ = _ := by rw [hV, one_mul]

private lemma odd_eq_half_difference {z : ℂ} (hz : ‖z‖ < 1) :
    oddResolvent z = (1 / 2 : ℂ) • (resolvent z - oppositeResolvent z) := by
  rw [(signed_square_factorization hz).1, (signed_square_factorization hz).2]
  have he : (1 + operator z) * squareResolvent z - (1 - operator z) * squareResolvent z =
      (2 : ℂ) • (operator z * squareResolvent z) := by
    rw [two_smul]
    noncomm_ring
  rw [he, smul_smul]
  norm_num [oddResolvent]

/-- The bounded square-resolvent equation, used in external contractions. -/
lemma square_eq_one_add {z : ℂ} (hz : ‖z‖ < 1) :
    squareResolvent z = 1 + operator z * oddResolvent z := by
  have h := square_unit hz
  rw [sub_mul, one_mul] at h
  exact (sub_eq_iff_eq_add.mp h).trans (by simp only [oddResolvent, pow_two, mul_assoc])

private lemma opposite_differentiable {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ oppositeResolvent z := by
  have hunit : IsUnit (1 + operator z) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using operator_norm_lt_one hz : ‖-operator z‖ < 1)
  have hd := (differentiableAt_inverse (𝕜 := ℂ) hunit).comp z
    ((differentiableAt_const (1 : H →L[ℂ] H)).add (hasDerivAt_operator hz).differentiableAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
  change (∑' k : ℕ, (-operator w) ^ k) = Ring.inverse (1 + operator w)
  rw [← sub_neg_eq_add]
  exact (NormedRing.inverse_one_sub (-operator w)
    (by simpa only [norm_neg] using operator_norm_lt_one hw)).symm

private lemma odd_entry_differentiable {z : ℂ} (hz : ‖z‖ < 1) (n m : ℕ) :
    DifferentiableAt ℂ (fun w => oddResolvent w (basis m) n) z := by
  have hd := (((hasDerivAt_resolvent hz).differentiableAt.sub
    (opposite_differentiable hz)).const_smul (1 / 2 : ℂ)).hasDerivAt
  have he := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp
    (ContinuousLinearMap.apply ℂ H (basis m))).hasFDerivAt.comp_hasDerivAt z hd
  apply he.differentiableAt.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
  rw [odd_eq_half_difference hw]
  rfl

private lemma explicitOdd_differentiable {z : ℂ} (hz : ‖z‖ < 1) (n m : ℕ) :
    DifferentiableAt ℂ (fun w => explicitOddEntry w (n + 1) (m + 1)) z := by
  have hsq : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z := by fun_prop
  have hA (s : ℕ) := (central_hasDerivAt (norm_sq_lt_one hz) s).differentiableAt.comp z hsq
  have hE (s : ℕ) := (central_derivative_differentiable (norm_sq_lt_one hz) s).comp z hsq
  have hP := (picard_fuchs (norm_sq_lt_one hz)).1.comp z hsq
  have hP0 := OriginalGaussianPeriodIdentity.period_ne_zero (norm_sq_lt_one hz)
  have hQ (s : ℕ) : DifferentiableAt ℂ (fun w => centralColumnJet (w ^ 2) s) z := by
    unfold centralColumnJet
    fun_prop
  unfold explicitOddEntry
  fun_prop

private lemma odd_entry_radial {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n m : ℕ) :
    oddResolvent (Real.sqrt r : ℂ) (basis m) n =
      explicitOddEntry (Real.sqrt r : ℂ) (n + 1) (m + 1) := by
  have hd := OriginalGaussianDisplacement.signed_resolvent_displacement hr.le hr1 n m
  have hsum : ((n + 1 : ℂ) + (m + 1 : ℂ)) *
      oddResolvent (Real.sqrt r : ℂ) (basis m) n =
        (oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n *
          resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) m +
        resolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n *
          oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) m) / 2 := by
    rw [odd_eq_half_difference (radial_norm_lt_one hr1)]
    change ((n + 1 : ℂ) + (m + 1 : ℂ)) * ((1 / 2) *
      (resolvent (Real.sqrt r : ℂ) (basis m) n -
        oppositeResolvent (Real.sqrt r : ℂ) (basis m) n)) = _
    linear_combination (hd.1 - hd.2) / 2
  rw [radial_positive_column hr hr1 n, radial_positive_column hr hr1 m,
    radial_negative_column hr hr1 n, radial_negative_column hr hr1 m] at hsum
  have hn : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  have hm : (Real.sqrt (m + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < m + 1)).ne'
  have hst : (n + 1 : ℂ) + (m + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (n + 1 : ℝ) + (m + 1) ≠ 0)
  have hsn : (Real.sqrt (n + 1 : ℝ) : ℂ) ^ 2 = (n + 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  have hsm : (Real.sqrt (m + 1 : ℝ) : ℂ) ^ 2 = (m + 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m + 1)
  have hb : (Real.sqrt (1 - r) : ℂ) ^ 2 = 1 - (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1 - r)
  unfold explicitOddEntry
  rw [show (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) by exact_mod_cast Real.sq_sqrt hr.le]
  simp only [pow_add, Nat.cast_add, Nat.cast_one] at *
  field_simp [hn, hm, hst] at hsum ⊢
  ring_nf at hsum hsn hsm
  rw [hb, hsn, hsm] at hsum
  simp only [show (1 + (n : ℝ)) = n + 1 by ring,
    show (1 + (m : ℝ)) = m + 1 by ring,
    Nat.add_comm 1 n, Nat.add_comm 1 m] at hsum
  linear_combination hsum

/-- Every odd resolvent entry is explicit, with both physical frequencies
positive and with no unresolved resolvent entry on the right. -/
theorem oddResolvent_entry_explicit {z : ℂ} (hz : ‖z‖ < 1) (n m : ℕ) :
    oddResolvent z (basis m) n = explicitOddEntry z (n + 1) (m + 1) := by
  have hleft : DifferentiableOn ℂ (fun w => oddResolvent w (basis m) n) (ball 0 1) :=
    fun w hw => (odd_entry_differentiable (by simpa using hw) n m).differentiableWithinAt
  have hright : DifferentiableOn ℂ (fun w => explicitOddEntry w (n + 1) (m + 1)) (ball 0 1) :=
    fun w hw => (explicitOdd_differentiable (by simpa using hw) n m).differentiableWithinAt
  have hacc : ∃ᶠ w in 𝓝[≠] (0 : ℂ),
      oddResolvent w (basis m) n = explicitOddEntry w (n + 1) (m + 1) := by
    have ht : Tendsto (fun k : ℕ => 1 / ((k : ℂ) + 1)) atTop (𝓝 (0 : ℂ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hp : Tendsto (fun k : ℕ => 1 / ((k : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨ht, Eventually.of_forall (fun k => by
        simpa using (div_ne_zero one_ne_zero (by exact_mod_cast Nat.succ_ne_zero k) :
          (1 / ((k : ℂ) + 1)) ≠ 0))⟩
    apply hp.frequently
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    let t : ℝ := 1 / ((k : ℝ) + 1)
    have ht0 : 0 < t := by dsimp [t]; positivity
    have ht1 : t < 1 := (div_lt_one (by positivity : 0 < (k : ℝ) + 1)).mpr (by linarith)
    have h := odd_entry_radial (sq_pos_of_pos ht0)
      (pow_lt_one₀ ht0.le ht1 (by norm_num : (2 : ℕ) ≠ 0)) n m
    rw [Real.sqrt_sq ht0.le] at h
    simpa only [t, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] using h
  exact (hleft.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hright.analyticOnNhd isOpen_ball) isPreconnected_ball (by simp) hacc
    (by simpa using hz)

private lemma row_summable {z : ℂ} (hz : ‖z‖ < 1) (x : H) (n : ℕ) :
    Summable (fun k : ℕ => ‖matrixEntry z (n + 1) (k + 1) * x k‖) := by
  have hg := (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg z) hz)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (hg.mul_left (‖z‖ ^ (n + 1) * ‖x‖))
  rw [norm_mul]
  calc
    _ ≤ ‖z‖ ^ ((n + 1) + (k + 1)) * ‖x‖ :=
      mul_le_mul (entry_bound z (n + 1) (k + 1) (by omega) (by omega))
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x k)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The identity term and the absolutely convergent explicit convolution
determine every square-resolvent entry, including the diagonal. -/
theorem squareResolvent_entry_explicit {z : ℂ} (hz : ‖z‖ < 1) (n m : ℕ) :
    Summable (fun k : ℕ => ‖matrixEntry z (n + 1) (k + 1) *
      explicitOddEntry z (k + 1) (m + 1)‖) ∧
    squareResolvent z (basis m) n = (if n = m then 1 else 0) +
      ∑' k : ℕ, matrixEntry z (n + 1) (k + 1) * explicitOddEntry z (k + 1) (m + 1) := by
  constructor
  · simpa only [oddResolvent_entry_explicit hz] using row_summable hz (oddResolvent z (basis m)) n
  · rw [square_eq_one_add hz]
    change basis m n + operator z (oddResolvent z (basis m)) n = _
    rw [operator_apply hz]
    simp_rw [oddResolvent_entry_explicit hz]
    simp [basis, lp.single_apply, Pi.single_apply, eq_comm]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianAllIndexResolvent
