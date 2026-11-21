/- GID: D5/S3/Analytic/Polynomial/DiagonalPadeResidue
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/DiagonalPadeResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The reflected residue logarithm and Gaussian comparison for central Padé poles. -/
module

public import D5.S3.Analytic.Polynomial.DiagonalPadeCentralPoles
import all D5.S3.Analytic.Polynomial.DiagonalPadePhase
import all D5.S3.Analytic.Polynomial.DiagonalPadeCentralPoles
import all D5.S3.Analytic.Polynomial.DiagonalPadeExponential
import all D5.S3.Analytic.HalfIntegerBessel
import all D5.S3.Analytic.HalfIntegerBesselSector
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Central residues of the diagonal exponential Padé denominator

Escape audit unfinished for the public theorems in this module.
https://github.com/the-omega-institute/trureturing/issues/32304
-/

public section

open Set Metric
open Polynomial (aeval)
open D5.S3.Analytic.HalfIntegerBessel (order S eta F_K F_K_eq_carrier S_re_pos sectorMass
  sector_K_estimate hasDerivAt_S)
open D5.S3.Analytic.Polynomial.DiagonalPadeExponential (denominator normalization residueWeight
  denominator_root_derivative residueWeight_eq residueWeight_pos norm_normalized_residueWeight_le eval_denominator_reciprocal)
open D5.S3.Analytic.Polynomial.DiagonalPadePhase (polePhase polePhaseLattice
  exists_central_poles norm_polePhaseLattice polePhase_sector polePhase_compact_estimate
  analyticOnNhd_eta closedBall_subset_sector re_ge_half_on_disk
  re_pos_of_close_to_one isOpen_sector)

namespace D5.S3.Analytic.Polynomial.DiagonalPadeResidue

private theorem order_pos (m : ℕ) : 0 < order m := by unfold order; positivity

private theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  rintro rfl
  simp at hz

/-- A logarithm of the decaying amplitude with its square-root factor removed. -/
noncomputable def residueAmplitudeLog (m : ℕ) (w : ℂ) : ℂ :=
  Complex.log (F_K m w) - Complex.log (S w) / 2

/-- The residue exponent centered at the reference pole in scaled coordinates. -/
noncomputable def normalizedResidueLog (m : ℕ) (w₀ w : ℂ) : ℂ :=
  -(order m : ℂ) * (Complex.log w - Complex.log w₀) +
    (order m : ℂ) * (w - w₀) - (order m : ℂ) * (eta w - eta w₀) +
    (residueAmplitudeLog m w - residueAmplitudeLog m w₀)

private theorem exp_half_log {w : ℂ} (hw : w ≠ 0) :
    Complex.exp (Complex.log w / 2) = Complex.sqrt w := by
  rw [Complex.sqrt, Complex.cpow_def_of_ne_zero hw, div_eq_mul_inv]

private theorem exp_order_log (m : ℕ) {w : ℂ} (hw : w ≠ 0) :
    Complex.exp (-(order m : ℂ) * Complex.log w) = Complex.sqrt w / w ^ (m + 1) := by
  rw [show -(order m : ℂ) * Complex.log w =
      Complex.log w / 2 - ((m + 1 : ℕ) : ℂ) * Complex.log w by
        simp only [order, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_natCast,
          Complex.ofReal_one, Complex.ofReal_ofNat, Nat.cast_add, Nat.cast_one]
        ring,
    Complex.exp_sub, exp_half_log hw, Complex.exp_nat_mul, Complex.exp_log hw]

private noncomputable def residueLog (m : ℕ) (w : ℂ) : ℂ :=
  -(order m : ℂ) * Complex.log w + (order m : ℂ) * w -
    (order m : ℂ) * eta w + residueAmplitudeLog m w

private theorem exp_residueLog (m : ℕ) (hm : Odd m) {w : ℂ} (hw : 0 < w.re)
    (hFK : F_K m w ≠ 0) (hroot : aeval (2 * (order m : ℂ) * w) (denominator m) = 0) :
    Complex.exp (residueLog m w) =
      ((normalization m : ℂ) * (2 * (order m : ℂ)) ^ (m + 1)) *
        residueWeight m (2 * (order m : ℂ) * w) := by
  let z : ℂ := 2 * (order m : ℂ) * w
  have hw₀ := ne_zero_of_re_pos hw
  have hν : (order m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (order_pos m).ne'
  have hz : z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hν) hw₀
  have hN : (normalization m : ℂ) ≠ 0 :=
    DiagonalPadeExponential.normalization_ne_zero m
  have hS : S w ≠ 0 := ne_zero_of_re_pos (S_re_pos hw)
  have hsqrt {v : ℂ} (hv : v ≠ 0) : Complex.sqrt v ≠ 0 := by
    rw [← exp_half_log hv]
    exact Complex.exp_ne_zero _
  have harg : -2 / -z = ((order m : ℂ) * w)⁻¹ := by
    dsimp [z]
    field_simp
  have hweight :
      residueWeight m z =
        aeval (((order m : ℂ) * w)⁻¹) (HalfIntegerBesselPolynomial.carrier m) /
          ((normalization m : ℂ) * z ^ (m + 1)) := by
    rw [residueWeight_eq m hm hroot, eval_denominator_reciprocal m (neg_ne_zero.mpr hz),
      neg_neg, harg, show 2 * m + 1 = m + (m + 1) by omega, pow_add]
    field_simp [hN, hz]
    ring
  change Complex.exp (residueLog m w) = _ * residueWeight m z
  rw [hweight, residueLog, residueAmplitudeLog, Complex.exp_add, Complex.exp_sub,
    Complex.exp_add, exp_order_log m hw₀, Complex.exp_sub, Complex.exp_log hFK,
    exp_half_log hS, F_K_eq_carrier m hw, mul_sub, Complex.exp_sub]
  dsimp [z]
  rw [mul_pow]
  field_simp [hN, hν, hw₀, hsqrt hw₀, hsqrt hS, Complex.exp_ne_zero]
  ring

/-- Exponentiating the centered branch gives the exact ratio of the two odd-order residues. -/
theorem exp_normalizedResidueLog (m : ℕ) (hm : Odd m) {w₀ w : ℂ}
    (hw₀ : 0 < w₀.re) (hw : 0 < w.re) (hFK₀ : F_K m w₀ ≠ 0) (hFK : F_K m w ≠ 0)
    (hroot₀ : aeval (2 * (order m : ℂ) * w₀) (denominator m) = 0)
    (hroot : aeval (2 * (order m : ℂ) * w) (denominator m) = 0) :
    Complex.exp (normalizedResidueLog m w₀ w) =
      residueWeight m (2 * (order m : ℂ) * w) /
        residueWeight m (2 * (order m : ℂ) * w₀) := by
  rw [show normalizedResidueLog m w₀ w = residueLog m w - residueLog m w₀ by
    unfold normalizedResidueLog residueLog
    ring,
    Complex.exp_sub, exp_residueLog m hm hw hFK hroot, exp_residueLog m hm hw₀ hFK₀ hroot₀]
  have hν : (order m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (order_pos m).ne'
  have hscale : (normalization m : ℂ) * (2 * (order m : ℂ)) ^ (m + 1) ≠ 0 :=
    mul_ne_zero (DiagonalPadeExponential.normalization_ne_zero m)
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hν))
  rw [mul_div_mul_left _ _ hscale]

private theorem analyticAt_S {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ S w := by
  have h : DifferentiableOn ℂ S {z : ℂ | 0 < z.re} :=
    fun _ hz => (hasDerivAt_S hz).differentiableAt.differentiableWithinAt
  exact h.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re) _ hw

private theorem analyticAt_F_K (m : ℕ) {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ (F_K m) w := by
  have hs : AnalyticAt ℂ (fun z => Complex.sqrt (S z)) w :=
    (analyticAt_S hw).cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl (S_re_pos hw)))
  have hw' : AnalyticAt ℂ Complex.sqrt w :=
    analyticAt_id.cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  have hν : (order m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (order_pos m).ne'
  have ha : AnalyticAt ℂ (fun z : ℂ => ((order m : ℂ) * z)⁻¹) w :=
    (analyticAt_const.mul analyticAt_id).inv (mul_ne_zero hν (ne_zero_of_re_pos hw))
  have harg : AnalyticAt ℂ (fun z => (order m : ℂ) * (eta z - z)) w :=
    analyticAt_const.mul ((analyticOnNhd_eta w hw).sub analyticAt_id)
  have hnorm : Complex.sqrt w ≠ 0 := by
    rw [← exp_half_log (ne_zero_of_re_pos hw)]
    exact Complex.exp_ne_zero _
  refine (((hs.div hw' hnorm).mul harg.cexp).mul
    (ha.aeval_polynomial (HalfIntegerBesselPolynomial.carrier m))).congr ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
  exact (F_K_eq_carrier m hz).symm

private theorem phaseThreshold {m : ℕ} (hm : 160 * sectorMass (1 / 4) ≤ order m) :
    40 * sectorMass (1 / 4) / (1 / 4) ≤ order m := by
  convert hm using 1
  ring

private theorem sectorMass_pos : 0 < sectorMass (1 / 4) := by unfold sectorMass; positivity

private theorem logAmplitude_sector (m : ℕ) (hm : 160 * sectorMass (1 / 4) ≤ order m)
    {w : ℂ} (hw : (1 / 4 : ℝ) * ‖w‖ < w.re) :
    0 < (F_K m w).re ∧ AnalyticAt ℂ (fun z => Complex.log (F_K m z)) w ∧
      ‖Complex.log (F_K m w)‖ ≤ 3 * sectorMass (1 / 4) / order m := by
  have hwr : 0 < w.re := (mul_nonneg (by norm_num) (norm_nonneg _)).trans_lt hw
  have hm' : 4 * sectorMass (1 / 4) ≤ order m := by linarith [sectorMass_pos]
  obtain ⟨hb, hh, _⟩ := sector_K_estimate m (by norm_num) hm' (ne_zero_of_re_pos hwr) hw.le
  have hr := re_pos_of_close_to_one (hb.trans hh)
  refine ⟨hr, (analyticAt_F_K m hwr).clog (Complex.mem_slitPlane_iff.mpr (Or.inl hr)), ?_⟩
  have hlog := Complex.norm_log_one_add_half_le_self (hb.trans hh)
  rw [show 1 + (F_K m w - 1) = F_K m w by ring] at hlog
  calc
    _ ≤ (3 / 2) * (2 * sectorMass (1 / 4) / order m) :=
      hlog.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by ring

private theorem residueAmplitudeLog_uniform {c : ℝ} (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 1 ≤ order m →
      160 * sectorMass (1 / 4) ≤ order m →
      ∀ x ∈ closedBall (c : ℂ) (c / 4), ∀ y ∈ closedBall (c : ℂ) (c / 4),
        ‖residueAmplitudeLog m y - residueAmplitudeLog m x‖ ≤ A * ‖y - x‖ := by
  let U : Set ℂ := closedBall (c : ℂ) (c / 4)
  let f : ℂ → ℂ := fun w => Complex.log (S w) / 2
  have hf (w : ℂ) (hw : w ∈ U) : AnalyticAt ℂ f w := by
    have hr := (show 0 < c / 2 by positivity).trans_le (re_ge_half_on_disk hc le_rfl hw)
    exact ((analyticAt_S hr).clog (Complex.mem_slitPlane_iff.mpr (Or.inl (S_re_pos hr)))).div_const
  have hcont : ContinuousOn (fun z => ‖deriv f z‖) U :=
    fun w hw => (hf w hw).deriv.continuousAt.norm.continuousWithinAt
  obtain ⟨v, -, hmax⟩ := (isCompact_closedBall (c : ℂ) (c / 4)).exists_isMaxOn
    ⟨(c : ℂ), mem_closedBall_self (by positivity)⟩ hcont
  let A := 12 * sectorMass (1 / 4) / c + ‖deriv f v‖
  refine ⟨A, add_pos_of_pos_of_nonneg (by positivity [sectorMass_pos]) (norm_nonneg _), ?_⟩
  intro m hν hm x hx y hy
  let k : ℂ → ℂ := fun z => Complex.log (F_K m z)
  let V : Set ℂ := {z | (1 / 4 : ℝ) * ‖z‖ < z.re}
  have hk (w : ℂ) (hw : w ∈ V) : AnalyticAt ℂ k w := (logAmplitude_sector m hm hw).2.1
  have hU : U ⊆ V :=
    (closedBall_subset_closedBall (by linarith)).trans (closedBall_subset_sector hc)
  have hderiv (w : ℂ) (hw : w ∈ U) :
      ‖deriv k w‖ ≤ 12 * sectorMass (1 / 4) / c := by
    have hball : closedBall w (c / 4) ⊆ closedBall (c : ℂ) (c / 2) := by
      apply closedBall_subset_closedBall'
      have := mem_closedBall.mp hw
      linarith
    rw [← Complex.cderiv_eq_deriv (isOpen_sector (1 / 4))
      (fun z hz => (hk z hz).differentiableAt.differentiableWithinAt) (by positivity)
      (hball.trans (closedBall_subset_sector hc))]
    calc
      _ ≤ (3 * sectorMass (1 / 4) / order m) / (c / 4) :=
        Complex.norm_cderiv_le (by positivity) fun z hz =>
          (logAmplitude_sector m hm
            (closedBall_subset_sector hc (hball (sphere_subset_closedBall hz)))).2.2
      _ ≤ (3 * sectorMass (1 / 4)) / (c / 4) := by
        gcongr
        exact div_le_self (by positivity [sectorMass_pos]) hν
      _ = _ := by ring
  have hconv : Convex ℝ U := convex_closedBall _ _
  have hkl := hconv.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hk z (hU hz)).differentiableAt) hderiv hx hy
  have hfl := hconv.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf z hz).differentiableAt) (fun z hz => hmax hz) hx hy
  calc
    ‖residueAmplitudeLog m y - residueAmplitudeLog m x‖ =
        ‖(k y - k x) - (f y - f x)‖ := by
      congr 1
      unfold residueAmplitudeLog k f
      ring
    _ ≤ _ := (norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add hkl hfl)

private theorem phase_error_difference (m : ℕ) {c : ℝ} (hc : 0 < c)
    (hm : 160 * sectorMass (1 / 4) ≤ order m)
    {x y : ℂ} (hx : x ∈ closedBall (c : ℂ) (c / 4)) (hy : y ∈ closedBall (c : ℂ) (c / 4)) :
    ‖(polePhase m y - eta y) - (polePhase m x - eta x)‖ ≤
      (240 * sectorMass (1 / 4) / (c * order m ^ 2)) * ‖y - x‖ := by
  let f : ℂ → ℂ := fun z => polePhase m z - eta z
  have hf (z : ℂ) (hz : z ∈ closedBall (c : ℂ) (c / 4)) :
      HasDerivAt f (deriv (polePhase m) z - deriv eta z) z := by
    have hs := closedBall_subset_sector hc (closedBall_subset_closedBall (by linarith) hz)
    have hr : 0 < z.re := (mul_nonneg (by norm_num) (norm_nonneg _)).trans_lt hs
    have hp := (polePhase_sector m (by norm_num) (by norm_num) (phaseThreshold hm) hs).2.2.2.1
    exact hp.differentiableAt.hasDerivAt.sub (analyticOnNhd_eta z hr).differentiableAt.hasDerivAt
  exact (convex_closedBall (c : ℂ) (c / 4)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf z hz).differentiableAt)
    (fun z hz => (hf z hz).deriv ▸ (polePhase_compact_estimate m hc hm).2 z hz) hx hy

private theorem inverse_displacement_bound {ν T C : ℝ} {a s G : ℂ}
    (hν : 1 ≤ ν) (hs : ‖s‖ ≤ T) (hC : 0 ≤ C)
    (hG : ‖G - a * s‖ ≤ C * (‖s‖ / ν ^ 2 + ‖s‖ ^ 2)) :
    ‖G‖ ≤ (‖a‖ + C * (1 + T)) * ‖s‖ := by
  have hν₂ : 1 ≤ ν ^ 2 := by nlinarith
  have hlin : ‖s‖ / ν ^ 2 ≤ ‖s‖ := div_le_self (norm_nonneg _) hν₂
  have hquad : ‖s‖ ^ 2 ≤ T * ‖s‖ := by
    simpa [pow_two] using mul_le_mul_of_nonneg_right hs (norm_nonneg s)
  calc
    ‖G‖ = ‖(G - a * s) + a * s‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (by
      rw [norm_mul]
      have h := mul_le_mul_of_nonneg_left (add_le_add hlin hquad) hC
      linarith)

private theorem residueLog_expansion (m : ℕ) {c A C T : ℝ} {a b D : ℂ}
    (hc : 0 < c) (hν : 1 ≤ order m) (hm : 160 * sectorMass (1 / 4) ≤ order m)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hT : 0 ≤ T)
    {x y s : ℂ} (hx : x ∈ closedBall (c : ℂ) (c / 4)) (hy : y ∈ closedBall (c : ℂ) (c / 4))
    (hs : ‖s‖ ≤ T) (hph : polePhase m y - polePhase m x = s)
    (hH : ‖residueAmplitudeLog m y - residueAmplitudeLog m x‖ ≤ A * ‖y - x‖)
    (hG : ‖y - x - a * s‖ ≤ C * (‖s‖ / order m ^ 2 + ‖s‖ ^ 2))
    (hL : ‖Complex.log y - Complex.log x - (b * s - D * s ^ 2)‖ ≤
      C * (‖s‖ / order m ^ 2 + ‖s‖ ^ 3)) :
    ‖normalizedResidueLog m x y - (order m : ℂ) * (a - b - 1) * s‖ ≤
      (C * (3 + T) + ‖D‖ + (240 * sectorMass (1 / 4) / c + A) * (‖a‖ + C * (1 + T))) *
        (order m * ‖s‖ ^ 2 + ‖s‖) := by
  let ν := order m
  let W := ‖a‖ + C * (1 + T)
  let P := 240 * sectorMass (1 / 4) / c
  let Q := ν * ‖s‖ ^ 2 + ‖s‖
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity [sectorMass_pos]
  have hνp := order_pos m
  have hsmall : ν * (‖s‖ / ν ^ 2) ≤ ‖s‖ := by
    rw [show ν * (‖s‖ / ν ^ 2) = ‖s‖ / ν by field_simp]
    exact div_le_self (norm_nonneg _) hν
  have hQ : ‖s‖ ≤ Q := le_add_of_nonneg_left (by positivity)
  have hQ₂ : ν * ‖s‖ ^ 2 ≤ Q := le_add_of_nonneg_right (norm_nonneg _)
  have hG' : ‖y - x‖ ≤ W * ‖s‖ := inverse_displacement_bound hν hs hC hG
  have hη : ‖eta y - eta x - s‖ ≤ (P / ν ^ 2) * (W * ‖s‖) := by
    have h := phase_error_difference m hc hm hx hy
    rw [show eta y - eta x - s = -((polePhase m y - eta y) - (polePhase m x - eta x)) by
      rw [← hph]
      ring, norm_neg]
    exact (h.trans_eq (by dsimp [P, ν]; ring)).trans
      (mul_le_mul_of_nonneg_left hG' (by positivity))
  have hgScaled : ν * ‖y - x - a * s‖ ≤ C * Q := by
    apply (mul_le_mul_of_nonneg_left hG hνp.le).trans
    rw [mul_left_comm, mul_add]
    apply mul_le_mul_of_nonneg_left _ hC
    simpa [Q, add_comm] using add_le_add_right hsmall (ν * ‖s‖ ^ 2)
  have hL' : ‖Complex.log y - Complex.log x - b * s‖ ≤
      C * (‖s‖ / ν ^ 2 + ‖s‖ ^ 3) + ‖D‖ * ‖s‖ ^ 2 := by
    rw [show Complex.log y - Complex.log x - b * s =
      (Complex.log y - Complex.log x - (b * s - D * s ^ 2)) - D * s ^ 2 by ring]
    exact (norm_sub_le _ _).trans (by rw [norm_mul, norm_pow]; gcongr)
  have hcube : ν * ‖s‖ ^ 3 ≤ T * Q := by
    calc
      ν * ‖s‖ ^ 3 = ‖s‖ * (ν * ‖s‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul hs hQ₂ (by positivity) hT
  have hlScaled : ν * ‖Complex.log y - Complex.log x - b * s‖ ≤
      (C * (1 + T) + ‖D‖) * Q := by
    refine (mul_le_mul_of_nonneg_left hL' hνp.le).trans ?_
    calc
      _ = C * (ν * (‖s‖ / ν ^ 2) + ν * ‖s‖ ^ 3) + ‖D‖ * (ν * ‖s‖ ^ 2) := by ring
      _ ≤ C * (Q + T * Q) + ‖D‖ * Q := by
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add (hsmall.trans hQ) hcube) hC)
          (mul_le_mul_of_nonneg_left hQ₂ (norm_nonneg _))
      _ = _ := by ring
  have hηScaled : ν * ‖eta y - eta x - s‖ ≤ (P * W) * Q := by
    refine (mul_le_mul_of_nonneg_left hη hνp.le).trans ?_
    calc
      _ = (P * W) * (ν * (‖s‖ / ν ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsmall.trans hQ) (mul_nonneg hP hW)
  have hH' : ‖residueAmplitudeLog m y - residueAmplitudeLog m x‖ ≤ (A * W) * Q := by
    refine hH.trans ((mul_le_mul_of_nonneg_left hG' hA).trans ?_)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hQ (mul_nonneg hA hW)
  rw [show normalizedResidueLog m x y - (order m : ℂ) * (a - b - 1) * s =
      (-(ν : ℂ) * (Complex.log y - Complex.log x - b * s) +
        (ν : ℂ) * (y - x - a * s)) - (ν : ℂ) * (eta y - eta x - s) +
          (residueAmplitudeLog m y - residueAmplitudeLog m x) by
        dsimp [normalizedResidueLog, ν]
        ring]
  refine ((norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans ?_
  have hνnorm : ‖ν‖ = ν := Real.norm_of_nonneg hνp.le
  simp only [norm_mul, norm_neg, Complex.norm_real, hνnorm]
  have hsum := add_le_add (add_le_add (add_le_add hlScaled hgScaled) hηScaled) hH'
  refine hsum.trans ?_
  change (C * (1 + T) + ‖D‖) * Q + C * Q + P * W * Q + A * W * Q ≤
    (C * (3 + T) + ‖D‖ + (P + A) * W) * Q
  nlinarith [mul_nonneg hC (show 0 ≤ Q by positivity)]

/-- The scaled pole with phase index `j` for the chosen central inverse. -/
noncomputable def centralPole (m : ℕ) (g : ℂ → ℂ) (j : ℤ) : ℂ :=
  2 * (order m : ℂ) * g (polePhaseLattice m j)

/-- The exponent of the normalized contribution from a scaled pole. -/
noncomputable def centralSummandExponent (m n : ℕ) (w₀ w : ℂ) : ℂ :=
  normalizedResidueLog m w₀ w - (n : ℂ) * (Complex.log w - Complex.log w₀)

/-- The Gaussian exponent with the residue phase and the signed pole phase. -/
noncomputable def gaussianSummandExponent (c : ℝ) (m n : ℕ) (j : ℤ) : ℂ :=
  let b := 1 / Real.sqrt (1 + c ^ 2)
  let D := c ^ 2 / (2 * (1 + c ^ 2) ^ 2)
  let θ := Real.pi * (c / Real.sqrt (1 + c ^ 2) - b - 1) -
    Real.pi * b * (n : ℝ) / order m
  ((-(Real.pi ^ 2 * D * ((n : ℝ) / order m ^ 2) * (j : ℝ) ^ 2) : ℝ) : ℂ) +
    (((j : ℝ) * θ : ℝ) : ℂ) * Complex.I

private theorem exp_centralSummandExponent (m n : ℕ) (hm : Odd m) {w₀ w : ℂ}
    (hw₀ : 0 < w₀.re) (hw : 0 < w.re) (hFK₀ : F_K m w₀ ≠ 0) (hFK : F_K m w ≠ 0)
    (hroot₀ : aeval (2 * (order m : ℂ) * w₀) (denominator m) = 0)
    (hroot : aeval (2 * (order m : ℂ) * w) (denominator m) = 0) :
    Complex.exp (centralSummandExponent m n w₀ w) =
      (residueWeight m (2 * (order m : ℂ) * w) /
        residueWeight m (2 * (order m : ℂ) * w₀)) *
        ((2 * (order m : ℂ) * w₀) / (2 * (order m : ℂ) * w)) ^ n := by
  have hν : (order m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (order_pos m).ne'
  rw [centralSummandExponent, Complex.exp_sub, exp_normalizedResidueLog m hm hw₀ hw hFK₀ hFK
    hroot₀ hroot, Complex.exp_nat_mul, Complex.exp_sub, Complex.exp_log (ne_zero_of_re_pos hw),
    Complex.exp_log (ne_zero_of_re_pos hw₀),
    mul_div_mul_left _ _ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hν),
    div_eq_mul_inv, ← inv_pow, inv_div]

private theorem gaussianSummandExponent_lattice (c : ℝ) (m n : ℕ) (j : ℤ) :
    gaussianSummandExponent c m n j =
      let a : ℂ := ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
      let b : ℂ := ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
      let D : ℂ := ((c ^ 2 / (2 * (1 + c ^ 2) ^ 2) : ℝ) : ℂ)
      let s := polePhaseLattice m j
      (order m : ℂ) * (a - b - 1) * s - (n : ℂ) * (b * s - D * s ^ 2) := by
  have hν : (order m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (order_pos m).ne'
  simp only [gaussianSummandExponent, polePhaseLattice, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_intCast,
    Complex.ofReal_natCast, Complex.ofReal_one]
  ring_nf
  rw [Complex.I_sq]
  field_simp [hν]
  ring

private theorem centralSummandExponent_bound (c : ℝ) (m n : ℕ) (j : ℤ)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hn : (n : ℝ) / order m ^ 2 ≤ 1 / 2)
    {w₀ w : ℂ}
    (hV : let a : ℂ := ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
          let b : ℂ := ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
          let s := polePhaseLattice m j
          ‖normalizedResidueLog m w₀ w - (order m : ℂ) * (a - b - 1) * s‖ ≤
            A * (order m * ‖s‖ ^ 2 + ‖s‖))
    (hL : let b : ℂ := ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
          let D : ℂ := ((c ^ 2 / (2 * (1 + c ^ 2) ^ 2) : ℝ) : ℂ)
          let s := polePhaseLattice m j
          ‖Complex.log w - Complex.log w₀ - (b * s - D * s ^ 2)‖ ≤
            C * (‖s‖ / order m ^ 2 + ‖s‖ ^ 3)) :
    ‖centralSummandExponent m n w₀ w - gaussianSummandExponent c m n j‖ ≤
      ((A + C) * (Real.pi + Real.pi ^ 2 + Real.pi ^ 3)) *
        (|(j : ℝ)| + (j : ℝ) ^ 2 + |(j : ℝ)| ^ 3) / order m := by
  let a : ℂ := ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
  let b : ℂ := ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
  let D : ℂ := ((c ^ 2 / (2 * (1 + c ^ 2) ^ 2) : ℝ) : ℂ)
  let s := polePhaseLattice m j
  let ν := order m
  have hν := order_pos m
  have hnp : (n : ℝ) ≤ ν ^ 2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hν)).mp hn
    linarith [sq_nonneg ν]
  have hrew : centralSummandExponent m n w₀ w - gaussianSummandExponent c m n j =
      (normalizedResidueLog m w₀ w - (ν : ℂ) * (a - b - 1) * s) -
        (n : ℂ) * (Complex.log w - Complex.log w₀ - (b * s - D * s ^ 2)) := by
    rw [centralSummandExponent, gaussianSummandExponent_lattice]
    dsimp [a, b, D, s, ν]
    ring
  rw [hrew]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_natCast]
  refine (add_le_add hV ((mul_le_mul_of_nonneg_left hL (by positivity)).trans
    (mul_le_mul_of_nonneg_right hnp (by positivity)))).trans ?_
  have hs : ‖s‖ = |(j : ℝ)| * Real.pi / ν := norm_polePhaseLattice m j
  have habs : |(j : ℝ)| ^ 2 = (j : ℝ) ^ 2 := sq_abs _
  let E := |(j : ℝ)| + (j : ℝ) ^ 2 + |(j : ℝ)| ^ 3
  let P := Real.pi + Real.pi ^ 2 + Real.pi ^ 3
  have hV' : |(j : ℝ)| * Real.pi + (j : ℝ) ^ 2 * Real.pi ^ 2 ≤ P * E := by
    calc
      _ ≤ (Real.pi + Real.pi ^ 2) * (|(j : ℝ)| + (j : ℝ) ^ 2) := by
        nlinarith [mul_nonneg (abs_nonneg (j : ℝ)) (sq_nonneg Real.pi),
          mul_nonneg (sq_nonneg (j : ℝ)) Real.pi_pos.le]
      _ ≤ _ := by
        gcongr
        · exact le_add_of_nonneg_right (pow_nonneg Real.pi_pos.le _)
        · exact le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) _)
  have hL' : |(j : ℝ)| * Real.pi + |(j : ℝ)| ^ 3 * Real.pi ^ 3 ≤ P * E := by
    calc
      _ ≤ (Real.pi + Real.pi ^ 3) * (|(j : ℝ)| + |(j : ℝ)| ^ 3) := by
        nlinarith [mul_nonneg (abs_nonneg (j : ℝ)) (pow_nonneg Real.pi_pos.le 3),
          mul_nonneg (pow_nonneg (abs_nonneg (j : ℝ)) 3) Real.pi_pos.le]
      _ ≤ _ := by
        gcongr
        · dsimp [P]; linarith [sq_nonneg Real.pi]
        · dsimp [E]; linarith [sq_nonneg (j : ℝ)]
  rw [hs]
  have heV : ν * (|(j : ℝ)| * Real.pi / ν) ^ 2 + |(j : ℝ)| * Real.pi / ν =
      (|(j : ℝ)| * Real.pi + (j : ℝ) ^ 2 * Real.pi ^ 2) / ν := by
    rw [div_pow, mul_pow, habs]
    field_simp [hν.ne']
    ring
  have heL : ν ^ 2 * (C * (|(j : ℝ)| * Real.pi / ν / ν ^ 2 +
      (|(j : ℝ)| * Real.pi / ν) ^ 3)) =
      C * (|(j : ℝ)| * Real.pi + |(j : ℝ)| ^ 3 * Real.pi ^ 3) / ν := by
    field_simp [hν.ne']
  rw [heV, heL, ← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ hν.le
  change A * _ + C * _ ≤ (A + C) * P * E
  rw [mul_assoc (A + C), add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hV' hA) (mul_le_mul_of_nonneg_left hL' hC)

private theorem analyticAt_normalizedResidueLog (m : ℕ) (w₀ : ℂ)
    (hm : 160 * sectorMass (1 / 4) ≤ order m)
    {w : ℂ} (hw : (1 / 4 : ℝ) * ‖w‖ < w.re) :
    AnalyticAt ℂ (normalizedResidueLog m w₀) w := by
  have hr : 0 < w.re := (mul_nonneg (by norm_num) (norm_nonneg _)).trans_lt hw
  have hlog : AnalyticAt ℂ Complex.log w :=
    analyticAt_id.clog (Complex.mem_slitPlane_iff.mpr (Or.inl hr))
  have hS : AnalyticAt ℂ (fun z => Complex.log (S z)) w :=
    (analyticAt_S hr).clog (Complex.mem_slitPlane_iff.mpr (Or.inl (S_re_pos hr)))
  have hAmp : AnalyticAt ℂ (residueAmplitudeLog m) w :=
    (logAmplitude_sector m hm hw).2.1.sub hS.div_const
  exact ((analyticAt_const.mul (hlog.sub analyticAt_const)).add
    (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))).sub
      (analyticAt_const.mul ((analyticOnNhd_eta w hr).sub analyticAt_const)) |>.add
        (hAmp.sub analyticAt_const)

private theorem norm_exp_sub_exp_le {u v : ℂ} (hu : ‖Complex.exp u‖ ≤ 1)
    (hv : ‖Complex.exp v‖ ≤ 1) : ‖Complex.exp u - Complex.exp v‖ ≤ ‖u - v‖ := by
  have hu' : u.re ≤ 0 := Real.exp_le_one_iff.mp (Complex.norm_exp u ▸ hu)
  have hv' : v.re ≤ 0 := Real.exp_le_one_iff.mp (Complex.norm_exp v ▸ hv)
  calc
    _ ≤ 1 * ‖u - v‖ :=
      (convex_halfSpace_re_le 0).norm_image_sub_le_of_norm_deriv_le
        (fun z _ => (Complex.hasDerivAt_exp z).differentiableAt)
        (fun z hz => by
          rw [(Complex.hasDerivAt_exp z).deriv, Complex.norm_exp]
          exact Real.exp_le_one_iff.mpr hz) hv' hu'
    _ = _ := one_mul _

private theorem norm_exp_gaussianSummandExponent_le_one (c : ℝ) (m n : ℕ) (j : ℤ) :
    ‖Complex.exp (gaussianSummandExponent c m n j)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp only [gaussianSummandExponent, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact neg_nonpos.mpr (by positivity)

private theorem exists_central_residue_comparison_with_bounds {c : ℝ} (hc : 0 < c)
    (hzero : eta (c : ℂ) = 0) :
    ∃ t₀ ε A B K : ℝ, 0 < t₀ ∧ 0 < ε ∧ 0 < A ∧ 0 < B ∧ 0 < K ∧
      (∀ J : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∀ j : ℤ, |(j : ℝ)| ≤ J → ‖polePhaseLattice m j‖ ≤ t₀) ∧
      ∃ M : ℕ, ∀ m ≥ M, Odd m →
        ∃ g : ℂ → ℂ, ∃ r W : ℝ, 0 < r ∧ 0 < W ∧
          centralPole m g 0 = (r : ℂ) ∧ residueWeight m (r : ℂ) = (W : ℂ) ∧
          ‖g 0 - (c : ℂ)‖ ≤ K / order m ^ 2 ∧
          (∀ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ →
            Real.pi ^ 2 * c ^ 2 / (4 * (1 + c ^ 2) ^ 2) * ((j : ℝ) / order m) ^ 2 ≤
              Real.log (‖centralPole m g j‖ / r)) ∧
          InjOn (centralPole m g) {j | ‖polePhaseLattice m j‖ ≤ t₀} ∧
          (∀ w ∈ ball (c : ℂ) ε, aeval (2 * (order m : ℂ) * w) (denominator m) = 0 ↔
            ∃ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ ∧ w = g (polePhaseLattice m j)) ∧
          AnalyticOnNhd ℂ (fun s => normalizedResidueLog m (g 0) (g s)) (closedBall 0 t₀) ∧
          (∀ s ∈ closedBall (0 : ℂ) t₀,
            let a : ℂ := ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
            let b : ℂ := ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
            ‖normalizedResidueLog m (g 0) (g s) - (order m : ℂ) * (a - b - 1) * s‖ ≤
              A * (order m * ‖s‖ ^ 2 + ‖s‖)) ∧
          ∀ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ →
            let s := polePhaseLattice m j
            aeval (centralPole m g j) (denominator m) = 0 ∧
            Complex.exp (normalizedResidueLog m (g 0) (g s)) =
              residueWeight m (centralPole m g j) / (W : ℂ) ∧
            ∀ n : ℕ, (n : ℝ) / order m ^ 2 ∈ Icc (1 / 4) (1 / 2) →
              Complex.exp (centralSummandExponent m n (g 0) (g s)) =
                (residueWeight m (centralPole m g j) / (W : ℂ)) *
                  ((r : ℂ) / centralPole m g j) ^ n ∧
              ‖centralSummandExponent m n (g 0) (g s) - gaussianSummandExponent c m n j‖ ≤
                B * (|(j : ℝ)| + (j : ℝ) ^ 2 + |(j : ℝ)| ^ 3) / order m ∧
              ‖(residueWeight m (centralPole m g j) / (W : ℂ)) *
                  ((r : ℂ) / centralPole m g j) ^ n -
                  Complex.exp (gaussianSummandExponent c m n j)‖ ≤
                B * (|(j : ℝ)| + (j : ℝ) ^ 2 + |(j : ℝ)| ^ 3) / order m := by
  obtain ⟨δ, ε, ρ, K, t₀, C, hε, hεδ, hδ, hρ, hK, ht₀, htρ, hC, hindices, M, hM⟩ :=
    exists_central_poles hc hzero
  obtain ⟨H, hH, hAmp⟩ := residueAmplitudeLog_uniform hc
  let a : ℂ := ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
  let b : ℂ := ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
  let D : ℂ := ((c ^ 2 / (2 * (1 + c ^ 2) ^ 2) : ℝ) : ℂ)
  let A := C * (3 + t₀) + ‖D‖ +
    (240 * sectorMass (1 / 4) / c + H) * (‖a‖ + C * (1 + t₀))
  let B := (A + C) * (Real.pi + Real.pi ^ 2 + Real.pi ^ 3)
  have hA : 0 < A := by dsimp [A]; positivity [sectorMass_pos]
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (160 * sectorMass (1 / 4)))
  refine ⟨t₀, ε, A, B, K, ht₀, hε, hA, hB, hK, hindices, max M N, ?_⟩
  intro m hm hodd
  have hmM := (le_max_left M N).trans hm
  have hmN := (le_max_right M N).trans hm
  have hcast : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmN
  have horder : (N : ℝ) ≤ order m := by unfold order; linarith
  have hν : 1 ≤ order m := ((le_max_left _ _).trans hN.le).trans horder
  have hmass : 160 * sectorMass (1 / 4) ≤ order m :=
    ((le_max_right _ _).trans hN.le).trans horder
  obtain ⟨g, hgA, hg, hgr, hgi, hgclose, hroot, hinj, hmod, htaylor, hcover⟩ := hM m hmM hodd
  let r := 2 * order m * (g 0).re
  have hr : 0 < r := by dsimp [r]; positivity [order_pos m]
  have hg0 : g 0 = (((g 0).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hgi
  have hs0 : polePhaseLattice m 0 = 0 := by simp [polePhaseLattice]
  have hr0 : 2 * (order m : ℂ) * g 0 = (r : ℂ) := by
    rw [hg0]
    push_cast [r]
    rfl
  have hcent : centralPole m g 0 = (r : ℂ) := by
    rw [centralPole, hs0, hr0]
  have hroot0 : aeval (2 * (order m : ℂ) * g 0) (denominator m) = 0 := by
    have h := hroot 0 (by simp [hs0, ht₀.le])
    simpa only [hs0] using h
  obtain ⟨W, hW, hW'⟩ := residueWeight_pos m hodd hr (by rwa [← hr0])
  have hz : (0 : ℂ) ∈ ball 0 ρ := mem_ball_self hρ
  have hsmall (z : ℂ) (hz : z ∈ ball 0 ρ) : g z ∈ closedBall (c : ℂ) (c / 4) :=
    closedBall_subset_closedBall hδ (ball_subset_closedBall (hg z hz).1)
  have hlarge (z : ℂ) (hz : z ∈ ball 0 ρ) : g z ∈ closedBall (c : ℂ) (c / 2) :=
    closedBall_subset_closedBall (by linarith) (hsmall z hz)
  have hright (z : ℂ) (hz : z ∈ ball 0 ρ) : 0 < (g z).re :=
    (show 0 < c / 2 by positivity).trans_le (re_ge_half_on_disk hc le_rfl (hsmall z hz))
  have hFK (z : ℂ) (hz : z ∈ ball 0 ρ) : F_K m (g z) ≠ 0 :=
    ne_zero_of_re_pos (logAmplitude_sector m hmass
      (closedBall_subset_sector hc (hlarge z hz))).1
  have hlog : AnalyticOnNhd ℂ (fun s => normalizedResidueLog m (g 0) (g s))
      (closedBall 0 t₀) := by
    intro s hs
    have hmem := closedBall_subset_ball htρ hs
    exact (analyticAt_normalizedResidueLog m (g 0) hmass
      (closedBall_subset_sector hc (hlarge s hmem))).comp (hgA s hmem)
  have hV (s : ℂ) (hs : s ∈ closedBall 0 t₀) :
      ‖normalizedResidueLog m (g 0) (g s) - (order m : ℂ) * (a - b - 1) * s‖ ≤
        A * (order m * ‖s‖ ^ 2 + ‖s‖) := by
    have hmem := closedBall_subset_ball htρ hs
    have hnorm : ‖s‖ ≤ t₀ := by simpa only [mem_closedBall_iff_norm, sub_zero] using hs
    have hph : polePhase m (g s) - polePhase m (g 0) = s := by
      rw [(hg s hmem).2.1, (hg 0 hz).2.1, sub_zero]
    exact residueLog_expansion m hc hν hmass hH.le hC.le ht₀.le (hsmall 0 hz) (hsmall s hmem)
      hnorm hph (hAmp m hν hmass _ (hsmall 0 hz) _ (hsmall s hmem))
      (htaylor s hs).1 (htaylor s hs).2
  have hquadratic (j : ℤ) (hj : ‖polePhaseLattice m j‖ ≤ t₀) :
      Real.pi ^ 2 * c ^ 2 / (4 * (1 + c ^ 2) ^ 2) * ((j : ℝ) / order m) ^ 2 ≤
        Real.log (‖centralPole m g j‖ / r) := by
    let t := (j : ℝ) * Real.pi / order m
    have ht : polePhaseLattice m j = (t : ℂ) * Complex.I := by
      simp only [t, polePhaseLattice, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_intCast]
      ring
    rw [ht, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hj
    have hrnorm : ‖(r : ℂ)‖ = r := by simp [Real.norm_of_nonneg hr.le]
    have hfactor : ‖2 * (order m : ℂ)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (order_pos m).ne'))
    rw [← hrnorm, ← hr0, centralPole, norm_mul (2 * (order m : ℂ)) (g _),
      norm_mul (2 * (order m : ℂ)) (g 0), mul_div_mul_left _ _ hfactor, ht]
    convert hmod t hj using 1
    dsimp [t]
    ring
  refine ⟨g, r, W, hr, hW, hcent, hW', hgclose, hquadratic, hinj, hcover, hlog, hV, ?_⟩
  intro j hj
  dsimp only
  let s := polePhaseLattice m j
  have hsc : s ∈ closedBall (0 : ℂ) t₀ := by
    simpa only [mem_closedBall_iff_norm, sub_zero] using hj
  have hs := closedBall_subset_ball htρ hsc
  have hExact := exp_normalizedResidueLog m hodd (hright 0 hz) (hright s hs) (hFK 0 hz)
    (hFK s hs) hroot0 (hroot j hj)
  rw [hr0, hW'] at hExact
  refine ⟨hroot j hj, hExact, ?_⟩
  intro n hn
  have hSummand := exp_centralSummandExponent m n hodd (hright 0 hz) (hright s hs) (hFK 0 hz)
    (hFK s hs) hroot0 (hroot j hj)
  rw [hr0, hW'] at hSummand
  have hEstimate := centralSummandExponent_bound c m n j hA.le hC.le hn.2
    (hV s hsc) (htaylor s hsc).2
  refine ⟨hSummand, hEstimate, ?_⟩
  have hrle : r ≤ ‖centralPole m g j‖ := by
    have hzn : 0 < ‖centralPole m g j‖ :=
      norm_pos_iff.mpr (denominator_root_derivative m (hroot j hj)).1
    have hnonneg : 0 ≤ Real.log (‖centralPole m g j‖ / r) :=
      (by positivity : 0 ≤ Real.pi ^ 2 * c ^ 2 / (4 * (1 + c ^ 2) ^ 2) *
        ((j : ℝ) / order m) ^ 2).trans (hquadratic j hj)
    simpa only [one_mul] using
      (le_div_iff₀ hr).mp ((Real.log_nonneg_iff (div_pos hzn hr)).mp hnonneg)
  have hunit : ‖Complex.exp (centralSummandExponent m n (g 0) (g s))‖ ≤ 1 := by
    rw [hSummand, ← hW']
    have hb := norm_normalized_residueWeight_le m n hodd hr (by rwa [← hr0])
      (hroot j hj) hrle
    exact hb.trans (pow_le_one₀ (by positivity) ((div_le_one (hr.trans_le hrle)).mpr hrle))
  unfold centralPole
  rw [← hSummand]
  exact (norm_exp_sub_exp_le hunit (norm_exp_gaussianSummandExponent_le_one c m n j)).trans hEstimate

/-- The central residues have a common branch and a uniform Gaussian exponent comparison.
Every fixed finite range of indices is eventually included, simultaneously for all
coefficient indices in the closed window. -/
theorem exists_central_residue_comparison {c : ℝ} (hc : 0 < c)
    (hzero : eta (c : ℂ) = 0) :
    ∃ t₀ ε A B : ℝ, 0 < t₀ ∧ 0 < ε ∧ 0 < A ∧ 0 < B ∧
      (∀ J : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∀ j : ℤ, |(j : ℝ)| ≤ J → ‖polePhaseLattice m j‖ ≤ t₀) ∧
      ∃ M : ℕ, ∀ m ≥ M, Odd m →
        ∃ g : ℂ → ℂ, ∃ r W : ℝ, 0 < r ∧ 0 < W ∧
          centralPole m g 0 = (r : ℂ) ∧ residueWeight m (r : ℂ) = (W : ℂ) ∧
          InjOn (centralPole m g) {j | ‖polePhaseLattice m j‖ ≤ t₀} ∧
          (∀ w ∈ ball (c : ℂ) ε, aeval (2 * (order m : ℂ) * w) (denominator m) = 0 ↔
            ∃ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ ∧ w = g (polePhaseLattice m j)) ∧
          AnalyticOnNhd ℂ (fun s => normalizedResidueLog m (g 0) (g s)) (closedBall 0 t₀) ∧
          (∀ s ∈ closedBall (0 : ℂ) t₀,
            let a : ℂ := ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
            let b : ℂ := ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
            ‖normalizedResidueLog m (g 0) (g s) - (order m : ℂ) * (a - b - 1) * s‖ ≤
              A * (order m * ‖s‖ ^ 2 + ‖s‖)) ∧
          ∀ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ →
            let s := polePhaseLattice m j
            aeval (centralPole m g j) (denominator m) = 0 ∧
            Complex.exp (normalizedResidueLog m (g 0) (g s)) =
              residueWeight m (centralPole m g j) / (W : ℂ) ∧
            ∀ n : ℕ, (n : ℝ) / order m ^ 2 ∈ Icc (1 / 4) (1 / 2) →
              Complex.exp (centralSummandExponent m n (g 0) (g s)) =
                (residueWeight m (centralPole m g j) / (W : ℂ)) *
                  ((r : ℂ) / centralPole m g j) ^ n ∧
              ‖centralSummandExponent m n (g 0) (g s) - gaussianSummandExponent c m n j‖ ≤
                B * (|(j : ℝ)| + (j : ℝ) ^ 2 + |(j : ℝ)| ^ 3) / order m ∧
              ‖(residueWeight m (centralPole m g j) / (W : ℂ)) *
                  ((r : ℂ) / centralPole m g j) ^ n -
                  Complex.exp (gaussianSummandExponent c m n j)‖ ≤
                B * (|(j : ℝ)| + (j : ℝ) ^ 2 + |(j : ℝ)| ^ 3) / order m := by
  obtain ⟨t₀, ε, A, B, _, ht₀, hε, hA, hB, _, hindices, M, hM⟩ :=
    exists_central_residue_comparison_with_bounds hc hzero
  refine ⟨t₀, ε, A, B, ht₀, hε, hA, hB, hindices, M, ?_⟩
  intro m hm hodd
  obtain ⟨g, r, W, hr, hW, hzeroPole, hzeroWeight, _, _, hrest⟩ := hM m hm hodd
  exact ⟨g, r, W, hr, hW, hzeroPole, hzeroWeight, hrest⟩

/-- A fixed finite collection of central summands has a uniform Gaussian error bound
throughout the closed coefficient window, using one threshold for the whole collection. -/
theorem exists_uniform_central_residue_truncation {c : ℝ} (hc : 0 < c)
    (hzero : eta (c : ℂ) = 0) (J : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∃ M : ℕ, ∀ m ≥ M, Odd m →
      ∃ g : ℂ → ℂ, ∃ r W : ℝ, 0 < r ∧ 0 < W ∧
        centralPole m g 0 = (r : ℂ) ∧ residueWeight m (r : ℂ) = (W : ℂ) ∧
        InjOn (centralPole m g) {j | |(j : ℝ)| ≤ J} ∧
        (∀ j : ℤ, |(j : ℝ)| ≤ J → aeval (centralPole m g j) (denominator m) = 0) ∧
        ∀ (n : ℕ), (n : ℝ) / order m ^ 2 ∈ Icc (1 / 4) (1 / 2) →
          ∀ indices : Finset ℤ, (∀ j ∈ indices, |(j : ℝ)| ≤ J) →
            ‖(∑ j ∈ indices, (residueWeight m (centralPole m g j) / (W : ℂ)) *
                ((r : ℂ) / centralPole m g j) ^ n) -
              ∑ j ∈ indices, Complex.exp (gaussianSummandExponent c m n j)‖ ≤
                B * (indices.card : ℝ) / order m := by
  obtain ⟨t₀, ε, A, B, ht₀, _, hA, hB, hcutoff, M, hM⟩ :=
    exists_central_residue_comparison hc hzero
  obtain ⟨N, hN⟩ := hcutoff J
  let C := B * (1 + (J : ℝ) + (J : ℝ) ^ 2 + (J : ℝ) ^ 3)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, max M N, ?_⟩
  intro m hm hodd
  obtain ⟨g, r, W, hr, hW, hzeroPole, hzeroWeight, hinj, _, _, _, hpoint⟩ :=
    hM m ((le_max_left _ _).trans hm) hodd
  have hj (j : ℤ) (hj : |(j : ℝ)| ≤ J) : ‖polePhaseLattice m j‖ ≤ t₀ :=
    hN m ((le_max_right _ _).trans hm) j hj
  refine ⟨g, r, W, hr, hW, hzeroPole, hzeroWeight, hinj.mono (fun j hj' => hj j hj'),
    fun j hj' => (hpoint j (hj j hj')).1, ?_⟩
  intro n hn indices hindices
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j ∈ indices, C / order m := by
      apply Finset.sum_le_sum
      intro j hmem
      have hJ := hindices j hmem
      have hbound := ((hpoint j (hj j hJ)).2.2 n hn).2.2
      refine hbound.trans ?_
      rw [← sq_abs (j : ℝ)]
      apply div_le_div_of_nonneg_right _ (order_pos m).le
      apply mul_le_mul_of_nonneg_left _ hB.le
      calc
        _ ≤ (J : ℝ) + (J : ℝ) ^ 2 + (J : ℝ) ^ 3 := by gcongr
        _ ≤ _ := by linarith
    _ = _ := by simp [nsmul_eq_mul]; ring

end D5.S3.Analytic.Polynomial.DiagonalPadeResidue
