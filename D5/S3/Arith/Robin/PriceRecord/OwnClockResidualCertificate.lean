/- GID: D5/S3/Arith/Robin/PriceRecord/OwnClockResidualCertificate
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/OwnClockResidualCertificate
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Exact finite real-image residual enclosure for the canonical own-clock objective. -/

/- UNCOMPILED SOURCE CANDIDATE. This module consumes the repaired
OwnClockContraction/Attainment/UniqueMinimum chain. The infimum is the
unchanged realInfimum of OwnClockFixedSupport; the certificate uses an actual
attained minimizer and never replaces the image infimum by a stationary-clock
definition. -/

import D5.S3.Arith.Robin.PriceRecord.OwnClockUniqueMinimum
import D5.S3.Arith.Robin.ArithmeticMixedCornerResponse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.OwnClockResidualCertificate

open Real Set Finset
open scoped Topology
open D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open D5.S3.Arith.Robin.PriceRecord.OwnClockContraction
open D5.S3.Arith.Robin.PriceRecord.OwnClockAttainment
open D5.S3.Arith.Robin.PriceRecord.OwnClockUniqueMinimum
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice

def clockLambda (L : ℝ) : ℝ := 1 / (L * log L)

def boundaryCoordinates {S : Finset ℕ} (L : ℝ) : S → ℝ :=
  fun p => boundary (p : ℝ) (clockLambda L)

def residualJ (L T : ℝ) : ℝ := tangentRemainder L T

def residualQ (S : Finset ℕ) (L : ℝ) : ℝ :=
  phi S (extend (S := S) (boundaryCoordinates L)) + residualJ L (responseClock S L)

private def reciprocalClock (t : ℝ) : ℝ := 1 / (t * log t)

private def curvatureWeight (t : ℝ) : ℝ :=
  (1 + log t) / (t ^ 2 * (log t) ^ 2)

private lemma clockLambda_pos {L : ℝ} (hL : 1 < L) : 0 < clockLambda L := by
  dsimp [clockLambda]
  positivity

private lemma terminalCost_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt terminalCost (reciprocalClock t) t := by
  have ht0 : 0 < t := by linarith
  have hlog : log t ≠ 0 := (log_pos ht).ne'
  have hd := (Real.hasDerivAt_log ht0.ne').log hlog
  convert hd using 1 <;> dsimp [terminalCost, reciprocalClock] <;>
    field_simp [ht0.ne', hlog] <;> ring

private lemma reciprocalClock_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt reciprocalClock (-curvatureWeight t) t := by
  simpa only [reciprocalClock, curvatureWeight,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.g,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity, add_comm] using
      D5.S3.Arith.Robin.ActualRobinClockCovariance.g_has_deriv_at ht

private lemma curvatureWeight_continuousOn {H : ℝ} (hH : 1 < H) :
    ContinuousOn curvatureWeight (Ici H) := by
  have h0 : ∀ t ∈ Ici H, t ≠ 0 := fun t ht => ne_of_gt (by linarith [hH.trans_le ht])
  have hl0 : ∀ t ∈ Ici H, log t ≠ 0 := fun t ht => (log_pos (hH.trans_le ht)).ne'
  exact (continuousOn_const.add (continuousOn_id.log h0)).div
    ((continuousOn_id.pow 2).mul ((continuousOn_id.log h0).pow 2))
    (fun t ht => mul_ne_zero (pow_ne_zero 2 (h0 t ht)) (pow_ne_zero 2 (hl0 t ht)))

private lemma reciprocalClock_continuousOn {H : ℝ} (hH : 1 < H) :
    ContinuousOn reciprocalClock (Ici H) := by
  intro t ht
  exact (reciprocalClock_hasDerivAt (hH.trans_le ht)).continuousAt.continuousWithinAt

private lemma curvatureWeight_antitoneOn {H : ℝ} (hH : 1 < H) :
    AntitoneOn curvatureWeight (Ici H) := by
  intro s hs t ht hst
  simpa only [curvatureWeight,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity, add_comm] using
      D5.S3.Arith.Robin.ArithmeticMixedCornerResponse.density_antitone (hH.trans_le hs) hst

private lemma curvatureWeight_pos {t : ℝ} (ht : 1 < t) : 0 < curvatureWeight t := by
  simpa only [curvatureWeight,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity, add_comm] using
      D5.S3.Arith.Robin.ArithmeticMixedCornerResponse.density_pos ht

private lemma reciprocal_gap_forward {H L T : ℝ} (hH : 1 < H)
    (hHL : H ≤ L) (hLT : L ≤ T) :
    reciprocalClock L - reciprocalClock T =
      ∫ u in L..T, curvatureWeight u := by
  simpa only [reciprocalClock, curvatureWeight,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.g,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity, add_comm] using
      (D5.S3.Arith.Robin.ActualRobinClockCovariance.density_integral
        (hH.trans_le hHL) hLT).symm

private lemma reciprocal_gap_backward {H T L : ℝ} (hH : 1 < H)
    (hHT : H ≤ T) (hTL : T ≤ L) :
    reciprocalClock T - reciprocalClock L =
      ∫ u in T..L, curvatureWeight u := by
  exact reciprocal_gap_forward hH hHT hTL

private lemma tangent_integral_forward {H L T : ℝ} (hH : 1 < H)
    (hHL : H ≤ L) (hLT : L ≤ T) :
    residualJ L T =
      ∫ u in L..T, (reciprocalClock L - reciprocalClock u) := by
  have hcont : ContinuousOn terminalCost (Icc L T) := by
    intro u hu
    exact (terminalCost_hasDerivAt (hH.trans_le (hHL.trans hu.1))).continuousAt.continuousWithinAt
  have hderiv : ∀ u ∈ Ioo L T, HasDerivAt terminalCost (reciprocalClock u) u := by
    intro u hu
    exact terminalCost_hasDerivAt (hH.trans_le (hHL.trans hu.1.le))
  have hint : IntervalIntegrable reciprocalClock volume L T := by
    exact (reciprocalClock_continuousOn hH).mono_set
      (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hHL))
      |>.intervalIntegrable_of_Icc hLT
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hLT hcont hderiv hint
  dsimp [residualJ, tangentRemainder]
  have hrewrite : terminalCost L + reciprocalClock L * (T - L) - terminalCost T =
      reciprocalClock L * (T - L) - (∫ u in L..T, reciprocalClock u) := by
    rw [hftc]
    ring
  rw [hrewrite]
  simp only [intervalIntegral.integral_sub, intervalIntegral.integral_const]
  ring

private lemma tangent_integral_backward {H T L : ℝ} (hH : 1 < H)
    (hHT : H ≤ T) (hTL : T ≤ L) :
    residualJ L T =
      ∫ u in T..L, (reciprocalClock u - reciprocalClock L) := by
  have hcont : ContinuousOn terminalCost (Icc T L) := by
    intro u hu
    exact (terminalCost_hasDerivAt (hH.trans_le (hHT.trans hu.1))).continuousAt.continuousWithinAt
  have hderiv : ∀ u ∈ Ioo T L, HasDerivAt terminalCost (reciprocalClock u) u := by
    intro u hu
    exact terminalCost_hasDerivAt (hH.trans_le (hHT.trans hu.1.le))
  have hint : IntervalIntegrable reciprocalClock volume T L := by
    exact (reciprocalClock_continuousOn hH).mono_set
      (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hHT))
      |>.intervalIntegrable_of_Icc hTL
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hTL hcont hderiv hint
  dsimp [residualJ, tangentRemainder]
  have hrewrite : terminalCost L + reciprocalClock L * (T - L) - terminalCost T =
      (∫ u in T..L, reciprocalClock u) + reciprocalClock L * (T - L) := by
    calc
      terminalCost L + reciprocalClock L * (T - L) - terminalCost T =
          (terminalCost L - terminalCost T) + reciprocalClock L * (T - L) := by ring
      _ = (∫ u in T..L, reciprocalClock u) + reciprocalClock L * (T - L) := by rw [hftc]
  rw [hrewrite]
  simp only [intervalIntegral.integral_sub, intervalIntegral.integral_const]
  ring

private lemma tangent_remainder_quadratic_forward {H L T : ℝ} (hH : 1 < H)
    (hHL : H ≤ L) (hLT : L ≤ T) :
    0 ≤ residualJ L T ∧
      residualJ L T ≤ curvatureWeight H / 2 * (T - L) ^ 2 := by
  have hmono := curvatureWeight_antitoneOn hH
  have hgap (u : ℝ) (hu : u ∈ Icc L T) :
      reciprocalClock L - reciprocalClock u ≤ curvatureWeight H * (u - L) := by
    have hinner := reciprocal_gap_forward hH hHL hu.1
    have hbound : ∀ v ∈ Ioo L u, curvatureWeight v ≤ curvatureWeight H := by
      intro v hv
      exact hmono (hHL.trans hv.1.le) le_rfl
    have hint₁ : IntervalIntegrable curvatureWeight volume L u := by
      exact (curvatureWeight_continuousOn hH).mono_set
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hHL))
        |>.intervalIntegrable_of_Icc hu.1.le
    have hint₂ : IntervalIntegrable (fun _ : ℝ => curvatureWeight H) volume L u :=
      continuousOn_const.intervalIntegrable_of_Icc hu.1.le
    have hint := intervalIntegral.integral_mono_on_of_le_Ioo hbound
      hint₁ hint₂
    rw [intervalIntegral.integral_const] at hint
    rw [hinner]
    nlinarith
  have hJ := tangent_integral_forward hH hHL hLT
  have hbound : ∀ u ∈ Ioo L T,
      reciprocalClock L - reciprocalClock u ≤ curvatureWeight H * (u - L) := by
    intro u hu
    exact hgap u ⟨hu.1.le, hu.2.le⟩
  have hleft : IntervalIntegrable (fun u => reciprocalClock L - reciprocalClock u) volume L T := by
    exact ((continuousOn_const.sub
      (reciprocalClock_continuousOn hH).mono_set
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hHL))).
        intervalIntegrable_of_Icc hLT)
  have hright : IntervalIntegrable (fun u => curvatureWeight H * (u - L)) volume L T := by
    exact (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).
      intervalIntegrable_of_Icc hLT
  have houter := intervalIntegral.integral_mono_on_of_le_Ioo hbound hleft hright
  have houterJ : residualJ L T ≤
      ∫ u in L..T, curvatureWeight H * (u - L) := by
    rw [hJ]
    exact houter
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
    intervalIntegral.integral_id, intervalIntegral.integral_const] at houterJ
  constructor
  · exact (tangent_remainder_nonnegative (hH.trans_le hHL)
      (hH.trans_le (hHL.trans hLT))).1
  · nlinarith [houterJ]

private lemma tangent_remainder_quadratic_backward {H T L : ℝ} (hH : 1 < H)
    (hHT : H ≤ T) (hTL : T ≤ L) :
    0 ≤ residualJ L T ∧
      residualJ L T ≤ curvatureWeight H / 2 * (T - L) ^ 2 := by
  have hmono := curvatureWeight_antitoneOn hH
  have hgap (u : ℝ) (hu : u ∈ Icc T L) :
      reciprocalClock u - reciprocalClock L ≤ curvatureWeight H * (L - u) := by
    have hinner := reciprocal_gap_backward hH hHT hu.2
    have hbound : ∀ v ∈ Ioo u L, curvatureWeight v ≤ curvatureWeight H := by
      intro v hv
      exact hmono (hHT.trans (hu.1.trans hv.1.le)) le_rfl
    have hint₁ : IntervalIntegrable curvatureWeight volume u L := by
      exact (curvatureWeight_continuousOn hH).mono_set
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hHT))
        |>.intervalIntegrable_of_Icc hu.2.le
    have hint₂ : IntervalIntegrable (fun _ : ℝ => curvatureWeight H) volume u L :=
      continuousOn_const.intervalIntegrable_of_Icc hu.2.le
    have hint := intervalIntegral.integral_mono_on_of_le_Ioo hbound
      hint₁ hint₂
    rw [intervalIntegral.integral_const] at hint
    rw [hinner]
    nlinarith
  have hJ := tangent_integral_backward hH hHT hTL
  have hbound : ∀ u ∈ Ioo T L,
      reciprocalClock u - reciprocalClock L ≤ curvatureWeight H * (L - u) := by
    intro u hu
    exact hgap u ⟨hu.1.le, hu.2.le⟩
  have hleft : IntervalIntegrable (fun u => reciprocalClock u - reciprocalClock L) volume T L := by
    exact (((reciprocalClock_continuousOn hH).mono_set
      (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hHT))).sub
      continuousOn_const).intervalIntegrable_of_Icc hTL
  have hright : IntervalIntegrable (fun u => curvatureWeight H * (L - u)) volume T L := by
    exact (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).
      intervalIntegrable_of_Icc hTL
  have houter := intervalIntegral.integral_mono_on_of_le_Ioo hbound hleft hright
  have houterJ : residualJ L T ≤
      ∫ u in T..L, curvatureWeight H * (L - u) := by
    rw [hJ]
    exact houter
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
    intervalIntegral.integral_const, intervalIntegral.integral_id] at houterJ
  constructor
  · exact (tangent_remainder_nonnegative (hH.trans_le (hHT.trans hTL))
      (hH.trans_le hHT)).1
  · nlinarith [houterJ, sq_nonneg (T - L)]

private lemma tangent_remainder_quadratic {H L T : ℝ} (hH : 1 < H)
    (hHL : H ≤ L) (hHT : H ≤ T) :
    0 ≤ residualJ L T ∧
      residualJ L T ≤ curvatureWeight H / 2 * (T - L) ^ 2 := by
  rcases le_total L T with hLT | hTL
  · exact tangent_remainder_quadratic_forward hH hHL hLT
  · exact tangent_remainder_quadratic_backward hH hHT hTL

lemma boundary_clock_eq_response {S : Finset ℕ} (hS : naturalSupport S)
    (hθ : 1 < theta S) {L : ℝ} (hL : theta S ≤ L) :
    clock S (extend (S := S) (boundaryCoordinates L)) = responseClock S L := by
  classical
  have hL1 : 1 < L := hθ.trans_le hL
  have hl : 0 < log L := log_pos hL1
  have hlam : 0 < clockLambda L := clockLambda_pos hL1
  have hcut : log (cutoff (clockLambda L)) = logCutoff L := by
    dsimp [cutoff, clockLambda, logCutoff]
    simp only [one_div, inv_inv]
  rw [clock_coordinates]
  calc
    (∑ p : S, boundaryCoordinates L p * log (p : ℝ)) =
        ∑ p : S, max (log (p : ℝ)) (logCutoff L - log (p : ℝ)) := by
      apply sum_congr rfl
      intro p hp
      have hp1 : 1 < (p : ℝ) := by
        exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p p.property)
      have hw : 0 < log (p : ℝ) := log_pos hp1
      dsimp [boundaryCoordinates, boundary, critical]
      rw [hcut, max_mul_of_nonneg _ _ hw.le, one_mul]
      congr 1
      field_simp [hw.ne']
      ring
    _ = responseClock S L := (sum_coe_sort S _).trans rfl


private lemma finite_price_identity {S : Finset ℕ} (hS : naturalSupport S)
    (hθ : 1 < theta S) {L : ℝ} (hL : theta S ≤ L) {x : S → ℝ} (hx : x ∈ orthant S) :
    phi S (extend x) = residualQ S L +
      (∑ p : S, priceLoss (p : ℝ) (clockLambda L) (x p)) -
        residualJ L (clock S (extend x)) := by
  have hb := boundary_clock_eq_response hS hθ hL
  have hsum (y : S → ℝ) :
      (∑ p : S, priceObjective (p : ℝ) (clockLambda L) (y p)) =
        (∑ p : S, benefit (p : ℝ) (y p)) -
          clockLambda L * (∑ p : S, y p * log (p : ℝ)) := by
    simp only [priceObjective, sum_sub_distrib, Finset.mul_sum]
    ring
  have hloss :
      (∑ p : S, priceLoss (p : ℝ) (clockLambda L) (x p)) =
        (∑ p : S, benefit (p : ℝ) (boundaryCoordinates L p)) -
          (∑ p : S, benefit (p : ℝ) (x p)) +
          clockLambda L * (clock S (extend x) -
            clock S (extend (S := S) (boundaryCoordinates L))) := by
    change (∑ p : S, (priceObjective (p : ℝ) (clockLambda L)
      (boundaryCoordinates L p) - priceObjective (p : ℝ) (x p))) = _
    rw [sum_sub_distrib, hsum, hsum, clock_coordinates, clock_coordinates]
    ring
  rw [phi_coordinates, phi_coordinates, residualQ, residualJ, hloss]
  dsimp [tangentRemainder]
  rw [hb]
  ring

private lemma price_losses_nonneg {S : Finset ℕ} (hS : naturalSupport S)
    (hθ : 1 < theta S) {L : ℝ} (hL : theta S ≤ L) {x : S → ℝ} (hx : x ∈ orthant S) :
    ∀ p : S, 0 ≤ priceLoss (p : ℝ) (clockLambda L) (x p) := by
  intro p
  have hp : 1 < (p : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p p.property)
  exact sub_nonneg.mpr (boundary_maximum hp (clockLambda_pos (hθ.trans_le hL)) (hx p))

lemma fixed_clock_residual {S : Finset ℕ} (hS : naturalSupport S)
    (hθ : 1 < theta S) {L τ : ℝ} (hL : theta S ≤ L)
    (hτ : theta S ≤ τ) (hτfix : responseClock S τ = τ) :
    |τ - L| ≤ (36 / 11 : ℝ) * |responseClock S L - L| := by
  have hLips := response_global_lipschitz hS hθ hL hτ
  have htri : |τ - L| ≤ |responseClock S τ - responseClock S L| +
      |responseClock S L - L| := by
    calc
      |τ - L| = |responseClock S τ - L| := by rw [hτfix]
      _ =
          |(responseClock S τ - responseClock S L) +
            (responseClock S L - L)| := by ring_nf
      _ ≤ _ := abs_add _ _
  rw [hτfix] at hLips
  nlinarith [abs_nonneg (τ - L), abs_nonneg (responseClock S L - L), htri, hLips]

theorem real_infimum_residual_enclosure {S : Finset ℕ} (hS : naturalSupport S)
    (hθ : 1 < theta S) {L : ℝ} (hL : theta S ≤ L) :
    residualQ S L - (648 / 121 : ℝ) *
        ((1 + log (theta S)) /
          ((theta S) ^ 2 * (log (theta S)) ^ 2)) *
        (responseClock S L - L) ^ 2 ≤ realInfimum S ∧
      realInfimum S ≤ phi S (extend (S := S) (boundaryCoordinates L)) := by
  obtain ⟨τ, hτray, hτfix, hτuniq, hrest⟩ := unique_real_minimum hS hθ
  dsimp at hrest
  let astar : S → ℝ := fun p => max 1 (logCutoff τ / log (p : ℝ) - 1)
  have hastar : astar ∈ orthant S := by simpa [astar] using hrest.1
  have hmin : IsMinOn (fun b : S → ℝ => phi S (extend b)) (orthant S) astar := by
    simpa [astar] using hrest.2.1
  have hinf : realInfimum S = phi S (extend astar) := by
    simpa [astar] using hrest.2.2.2
  have hresp := minimizer_response hS hθ hastar hmin
  have hclock_resp : responseClock S (clock S (extend astar)) =
      clock S (extend astar) := response_clock_identity hS hresp
  have hclock_eq : clock S (extend astar) = τ := by
    exact hτuniq _ (theta_le_clock_of_naturalSupport hS (extend_admissible hastar))
      hclock_resp
  have hidentity := finite_price_identity hS hθ hL hastar
  have hloss_nonneg : 0 ≤ ∑ p : S,
      priceLoss (p : ℝ) (clockLambda L) (astar p) := by
    exact sum_nonneg (fun p _ => price_losses_nonneg hS hθ hL hastar p)
  have hupper : residualQ S L - realInfimum S ≤ residualJ L τ := by
    rw [hinf, hclock_eq] at hidentity
    linarith [hidentity, hloss_nonneg]
  have hmin_b : realInfimum S ≤ phi S (extend (S := S) (boundaryCoordinates L)) := by
    rw [hinf]
    exact hmin (boundaryCoordinates L) (by intro p; exact le_max_left _ _)
  have hlowerJ : residualJ L (responseClock S L) ≤ residualQ S L - realInfimum S := by
    dsimp [residualQ]
    linarith [hmin_b]
  have hQnonneg : 0 ≤ residualQ S L - realInfimum S := by
    have hJb := (tangent_remainder_nonnegative (hθ.trans_le hL)
      (hθ.trans_le (response_selfmap S L))).1
    exact hJb.trans hlowerJ
  have hquad := tangent_remainder_quadratic hθ hL hτray
  have hres := fixed_clock_residual hS hθ hL hτray hτfix
  have hres_abs : |τ - L| ≤
      |(36 / 11 : ℝ) * (responseClock S L - L)| := by
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 36 / 11)] using hres
  have hres_sq : (τ - L) ^ 2 ≤
      ((36 / 11 : ℝ) * (responseClock S L - L)) ^ 2 :=
    sq_le_sq.mpr hres_abs
  have hcoeff : (curvatureWeight (theta S) / 2) *
      ((36 / 11 : ℝ) * (responseClock S L - L)) ^ 2 =
      (648 / 121 : ℝ) * curvatureWeight (theta S) *
        (responseClock S L - L) ^ 2 := by
    ring
  constructor
  · have hQ := hupper.trans (hquad.2)
    have hQ' : residualQ S L - realInfimum S ≤
        curvatureWeight (theta S) / 2 *
          ((36 / 11 : ℝ) * (responseClock S L - L)) ^ 2 :=
      hQ.trans (mul_le_mul_of_nonneg_left hres_sq
        (by positivity : 0 ≤ curvatureWeight (theta S) / 2))
    have hQ'' := hQ'
    rw [hcoeff] at hQ''
    linarith [hQnonneg]
  · exact hmin_b

end D5.S3.Arith.Robin.PriceRecord.OwnClockResidualCertificate
