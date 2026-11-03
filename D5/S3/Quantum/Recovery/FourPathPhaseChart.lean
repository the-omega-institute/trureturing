/- GID: D5/S3/Quantum/Recovery/FourPathPhaseChart
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathPhaseChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual four-phase feedbacks have local trace-deficit and relative-phase coordinates. -/

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-! Trace-deficit coordinates for the actual diagonal phase feedback. -/

noncomputable section

open scoped Topology
open Real Filter Set
open Complex (I arg)

namespace D5.S3.Quantum.Recovery.FourPathPhaseChart

abbrev PhaseVector := Fin 4 → ℂ
abbrev Coordinates := Fin 4 → ℝ

/-- The original trace modulus, on the actual four entries. -/
def traceModulus (w : PhaseVector) : ℝ := ‖w 0 + w 1 + w 2 + w 3‖

/-- The other original optimizer-sign trace modulus. -/
def oppositeModulus (w : PhaseVector) : ℝ :=
  ‖w 0 - w 1 + I * (w 2 - w 3)‖

def amplitudeP (h c : ℝ) (w : PhaseVector) : ℂ :=
  h * (w 0 + w 1) + c * (w 2 + w 3)

def amplitudeQ (h s : ℝ) (w : PhaseVector) : ℂ :=
  h * (w 0 - w 1) + I * s * (w 2 - w 3)

/-- The positive radical for the first pair's real part. -/
def radialX (δ a b : ℝ) : ℝ :=
  -cos b * cos a + sqrt ((2 - δ / 2) ^ 2 - cos b ^ 2 * sin a ^ 2)

/-- The fourth real coordinate is the one common scalar argument. -/
def phaseChart (τ : ℝ) (p : Coordinates) : PhaseVector :=
  let X := radialX (p 0) (p 1) (p 2)
  let Y := sqrt (1 - X ^ 2)
  let scalar := Complex.exp ((p 3 : ℂ) * I)
  let z := Complex.exp ((p 1 : ℂ) * I)
  ![scalar * (z * (X + τ * I * Y)), scalar * (z * (X - τ * I * Y)),
    scalar * Complex.exp (((τ * p 2 : ℝ) : ℂ) * I),
    scalar * Complex.exp (((-τ * p 2 : ℝ) : ℂ) * I)]

/-- Local inverse from the four actual arguments and the original trace modulus. -/
def phaseCoordinates (τ : ℝ) (w : PhaseVector) : Coordinates :=
  ![4 - traceModulus w,
    (arg (w 0) + arg (w 1) - arg (w 2) - arg (w 3)) / 2,
    τ * (arg (w 2) - arg (w 3)) / 2,
    (arg (w 2) + arg (w 3)) / 2]

/-- The oriented half difference of the first two actual arguments. -/
def halfAngle (τ : ℝ) (w : PhaseVector) : ℝ :=
  τ * (arg (w 0) - arg (w 1)) / 2

private lemma phase_norm (t : ℝ) : ‖Complex.exp ((t : ℂ) * I)‖ = 1 := by
  simp

private lemma phase_add (u v : ℝ) :
    Complex.exp (((u + v : ℝ) : ℂ) * I) =
      Complex.exp ((u : ℂ) * I) * Complex.exp ((v : ℂ) * I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

private lemma unit_phase (w : ℂ) (hw : ‖w‖ = 1) :
    Complex.exp ((arg w : ℂ) * I) = w := by
  simpa [hw] using Complex.norm_mul_exp_arg_mul_I w

private lemma euler (t : ℝ) :
    Complex.exp ((t : ℂ) * I) = (cos t : ℂ) + I * (sin t : ℂ) := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

private lemma exp_angle_arg {t : ℝ} (hl : -Real.pi < t) (hr : t < Real.pi) :
    arg (Complex.exp ((t : ℂ) * I)) = t := by
  simpa [Circle.coe_exp] using Circle.arg_exp hl hr.le

private lemma sqrt_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (hx : 0 < f x) :
    AnalyticAt ℝ (fun y => sqrt (f y)) x := by
  have heq : (fun y => sqrt (f y)) =ᶠ[𝓝 x]
      (fun y => Real.exp (Real.log (f y) * (1 / 2 : ℝ))) := by
    filter_upwards [hf.continuousAt.eventually (isOpen_Ioi.mem_nhds hx)] with y hy
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]
  have hlog : AnalyticAt ℝ (fun y => Real.log (f y)) x := (analyticAt_log hx).comp hf
  have hexp : AnalyticAt ℝ (fun y => Real.exp (Real.log (f y) * (1 / 2 : ℝ))) x :=
    (hlog.mul analyticAt_const).rexp
  exact hexp.congr heq.symm

private lemma arg_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} (hf : AnalyticAt ℝ f x) (hx : f x ∈ Complex.slitPlane) :
    AnalyticAt ℝ (fun y => arg (f y)) x := by
  have hlog := (analyticAt_clog hx).restrictScalars (𝕜 := ℝ)
  have hlogf : AnalyticAt ℝ (fun y => Complex.log (f y)) x := hlog.comp hf
  have him : AnalyticAt ℝ (fun y => (Complex.log (f y)).im) x :=
    (Complex.imCLM.analyticAt _).comp hlogf
  simpa only [Complex.log_im] using him

private lemma norm_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} (hf : AnalyticAt ℝ f x) (hx : f x ≠ 0) :
    AnalyticAt ℝ (fun y => ‖f y‖) x := by
  have hre : AnalyticAt ℝ (fun y => (f y).re) x := (Complex.reCLM.analyticAt _).comp hf
  have him : AnalyticAt ℝ (fun y => (f y).im) x := (Complex.imCLM.analyticAt _).comp hf
  have hpos : 0 < (f x).re ^ 2 + (f x).im ^ 2 := by
    simpa only [← Complex.normSq_apply, pow_two] using Complex.normSq_pos.mpr hx
  simpa only [Complex.norm_eq_sqrt_sq_add_sq, Pi.add_apply, Pi.pow_apply] using
    sqrt_analytic ((hre.pow 2).add (him.pow 2)) hpos

private def angular (τ θ a b m : ℝ) : PhaseVector :=
  ![Complex.exp (((m + a + τ * θ : ℝ) : ℂ) * I),
    Complex.exp (((m + a - τ * θ : ℝ) : ℂ) * I),
    Complex.exp (((m + τ * b : ℝ) : ℂ) * I),
    Complex.exp (((m - τ * b : ℝ) : ℂ) * I)]

private lemma angular_form {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (θ a b m : ℝ) :
    angular τ θ a b m =
      ![Complex.exp ((m : ℂ) * I) * (Complex.exp ((a : ℂ) * I) *
          ((cos θ : ℂ) + τ * I * (sin θ : ℂ))),
        Complex.exp ((m : ℂ) * I) * (Complex.exp ((a : ℂ) * I) *
          ((cos θ : ℂ) - τ * I * (sin θ : ℂ))),
        Complex.exp ((m : ℂ) * I) * Complex.exp (((τ * b : ℝ) : ℂ) * I),
        Complex.exp ((m : ℂ) * I) * Complex.exp (((-τ * b : ℝ) : ℂ) * I)] := by
  have hplus : Complex.exp (((τ * θ : ℝ) : ℂ) * I) =
      (cos θ : ℂ) + τ * I * (sin θ : ℂ) := by
    rw [euler]
    rcases hτ with rfl | rfl <;> simp [cos_neg, sin_neg] <;> ring
  have hminus : Complex.exp (((-τ * θ : ℝ) : ℂ) * I) =
      (cos θ : ℂ) - τ * I * (sin θ : ℂ) := by
    rw [euler]
    rcases hτ with rfl | rfl <;> simp [cos_neg, sin_neg] <;> ring
  funext i
  fin_cases i
  · change Complex.exp (((m + a + τ * θ : ℝ) : ℂ) * I) = _
    rw [phase_add, phase_add, hplus, mul_assoc]
  · change Complex.exp (((m + a - τ * θ : ℝ) : ℂ) * I) = _
    rw [show m + a - τ * θ = m + a + (-τ * θ) by ring,
      phase_add, phase_add, hminus, mul_assoc]
  · change Complex.exp (((m + τ * b : ℝ) : ℂ) * I) = _
    exact phase_add _ _
  · change Complex.exp (((m - τ * b : ℝ) : ℂ) * I) = _
    rw [show m - τ * b = m + (-τ * b) by ring]
    exact phase_add _ _

private lemma angular_unit (τ θ a b m : ℝ) (i : Fin 4) :
    ‖angular τ θ a b m i‖ = 1 := by
  fin_cases i <;> dsimp only [angular] <;> exact phase_norm _

private lemma angular_trace {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (θ a b m : ℝ) :
    traceModulus (angular τ θ a b m) =
      2 * ‖(cos θ : ℂ) * Complex.exp ((a : ℂ) * I) + (cos b : ℂ)‖ := by
  rw [angular_form hτ]
  unfold traceModulus
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_succ, Function.comp_apply, Matrix.vecHead, Matrix.vecTail]
  have hlast : Complex.exp (((τ * b : ℝ) : ℂ) * I) +
      Complex.exp (((-τ * b : ℝ) : ℂ) * I) = 2 * (cos b : ℂ) := by
    rcases hτ with rfl | rfl <;>
      simp only [one_mul, neg_one_mul, neg_mul, neg_neg] <;>
      rw [euler, euler] <;>
      simp only [cos_neg, sin_neg, Complex.ofReal_neg] <;> ring
  have heq :
      Complex.exp ((m : ℂ) * I) * (Complex.exp ((a : ℂ) * I) *
        ((cos θ : ℂ) + τ * I * (sin θ : ℂ))) +
      Complex.exp ((m : ℂ) * I) * (Complex.exp ((a : ℂ) * I) *
        ((cos θ : ℂ) - τ * I * (sin θ : ℂ))) +
      Complex.exp ((m : ℂ) * I) * Complex.exp (((τ * b : ℝ) : ℂ) * I) +
      Complex.exp ((m : ℂ) * I) * Complex.exp (((-τ * b : ℝ) : ℂ) * I) =
      Complex.exp ((m : ℂ) * I) *
        (2 * ((cos θ : ℂ) * Complex.exp ((a : ℂ) * I) + (cos b : ℂ))) := by
    linear_combination Complex.exp ((m : ℂ) * I) * hlast
  rw [heq, norm_mul, phase_norm, one_mul, norm_mul]
  norm_num

private lemma trace_square (X a b : ℝ) :
    ‖(X : ℂ) * Complex.exp ((a : ℂ) * I) + (cos b : ℂ)‖ ^ 2 =
      X ^ 2 + 2 * X * cos b * cos a + cos b ^ 2 := by
  rw [euler, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im]
  nlinarith [show X ^ 2 * (sin a ^ 2 + cos a ^ 2) = X ^ 2 by
    rw [Real.sin_sq_add_cos_sq, mul_one]]

private lemma angular_recovery {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (w : PhaseVector) (hw : ∀ i, ‖w i‖ = 1) :
    angular τ (halfAngle τ w) (phaseCoordinates τ w 1)
      (phaseCoordinates τ w 2) (phaseCoordinates τ w 3) = w := by
  ext i
  fin_cases i <;>
    simp only [angular, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
  all_goals
    convert unit_phase (w _) (hw _) using 2
    congr 2
    rcases hτ with rfl | rfl <;> simp [phaseCoordinates, halfAngle] <;> ring

private lemma reconstructed_radicals {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (w : PhaseVector) (hw : ∀ i, ‖w i‖ = 1)
    (hθ : 0 < halfAngle τ w ∧ halfAngle τ w < Real.pi / 2)
    (hc : 0 ≤ cos (phaseCoordinates τ w 2) * cos (phaseCoordinates τ w 1)) :
    radialX (phaseCoordinates τ w 0) (phaseCoordinates τ w 1)
        (phaseCoordinates τ w 2) = cos (halfAngle τ w) ∧
    sqrt (1 - radialX (phaseCoordinates τ w 0) (phaseCoordinates τ w 1)
        (phaseCoordinates τ w 2) ^ 2) = sin (halfAngle τ w) := by
  let θ := halfAngle τ w
  let a := phaseCoordinates τ w 1
  let b := phaseCoordinates τ w 2
  have hcos : 0 < cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hsin : 0 < sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos])
  have htrace : traceModulus w =
      2 * ‖(cos θ : ℂ) * Complex.exp ((a : ℂ) * I) + (cos b : ℂ)‖ := by
    calc
      traceModulus w = traceModulus (angular τ θ a b (phaseCoordinates τ w 3)) :=
        congrArg traceModulus (angular_recovery hτ w hw).symm
      _ = _ := angular_trace hτ _ _ _ _
  have hquad := trace_square (cos θ) a b
  have hsq : (traceModulus w / 2) ^ 2 =
      cos θ ^ 2 + 2 * cos θ * cos b * cos a + cos b ^ 2 := by
    rw [htrace]
    simpa using hquad
  have hrad : (2 - phaseCoordinates τ w 0 / 2) ^ 2 - cos b ^ 2 * sin a ^ 2 =
      (cos θ + cos b * cos a) ^ 2 := by
    have htrig : cos b ^ 2 * (sin a ^ 2 + cos a ^ 2) = cos b ^ 2 := by
      rw [Real.sin_sq_add_cos_sq, mul_one]
    have hδ : 2 - phaseCoordinates τ w 0 / 2 = traceModulus w / 2 := by
      change 2 - (4 - traceModulus w) / 2 = traceModulus w / 2
      ring
    rw [hδ]
    nlinarith [hsq]
  have hX : radialX (phaseCoordinates τ w 0) a b = cos θ := by
    unfold radialX
    rw [hrad, Real.sqrt_sq (by linarith : 0 ≤ cos θ + cos b * cos a)]
    ring
  refine ⟨hX, ?_⟩
  rw [hX, show 1 - cos θ ^ 2 = sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ],
    Real.sqrt_sq hsin.le]

private lemma actual_reconstruction {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (w : PhaseVector) (hw : ∀ i, ‖w i‖ = 1)
    (hθ : 0 < halfAngle τ w ∧ halfAngle τ w < Real.pi / 2)
    (hc : 0 ≤ cos (phaseCoordinates τ w 2) * cos (phaseCoordinates τ w 1)) :
    phaseChart τ (phaseCoordinates τ w) = w := by
  obtain ⟨hX, hY⟩ := reconstructed_radicals hτ w hw hθ hc
  calc
    phaseChart τ (phaseCoordinates τ w) =
        angular τ (halfAngle τ w) (phaseCoordinates τ w 1)
          (phaseCoordinates τ w 2) (phaseCoordinates τ w 3) := by
      rw [angular_form hτ]
      dsimp only [phaseChart]
      rw [hY, hX]
    _ = w := angular_recovery hτ w hw

private def chartAngles (τ : ℝ) (p : Coordinates) : Coordinates :=
  let θ := arccos (radialX (p 0) (p 1) (p 2))
  ![p 3 + p 1 + τ * θ, p 3 + p 1 - τ * θ, p 3 + τ * p 2, p 3 - τ * p 2]

private lemma chart_angular {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (p : Coordinates)
    (hX : 0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1) :
    phaseChart τ p = angular τ (arccos (radialX (p 0) (p 1) (p 2))) (p 1) (p 2) (p 3) := by
  rw [angular_form hτ, Real.cos_arccos (by linarith : -1 ≤ radialX (p 0) (p 1) (p 2)) hX.2.le,
    Real.sin_arccos]
  rfl

private lemma chart_unit {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (p : Coordinates)
    (hX : 0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1) :
    ∀ i, ‖phaseChart τ p i‖ = 1 := by
  rw [chart_angular hτ p hX]
  exact angular_unit _ _ _ _ _

private lemma chart_trace {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (p : Coordinates)
    (hX : 0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1)
    (hR : 0 ≤ (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2)
    (hδ : p 0 < 4) : traceModulus (phaseChart τ p) = 4 - p 0 := by
  let X := radialX (p 0) (p 1) (p 2)
  have hsqrt := Real.sq_sqrt hR
  have hid := Real.sin_sq_add_cos_sq (p 1)
  have hw : cos (p 2) ^ 2 * (sin (p 1) ^ 2 + cos (p 1) ^ 2) = cos (p 2) ^ 2 := by
    rw [hid, mul_one]
  have hroot : X + cos (p 2) * cos (p 1) =
      sqrt ((2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2) := by
    dsimp [X, radialX]
    ring
  have hquad := trace_square X (p 1) (p 2)
  have hnorm : ‖(X : ℂ) * Complex.exp ((p 1 : ℂ) * I) + (cos (p 2) : ℂ)‖ =
      2 - p 0 / 2 := by
    have hh : (X + cos (p 2) * cos (p 1)) ^ 2 =
        (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2 := by
      rw [hroot]
      exact hsqrt
    nlinarith [norm_nonneg ((X : ℂ) * Complex.exp ((p 1 : ℂ) * I) + (cos (p 2) : ℂ))]
  rw [chart_angular hτ p hX, angular_trace hτ,
    Real.cos_arccos (by linarith : -1 ≤ X) hX.2.le, hnorm]
  ring

private lemma chart_args {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (p : Coordinates)
    (hX : 0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1)
    (ha : ∀ i, -Real.pi < chartAngles τ p i ∧ chartAngles τ p i < Real.pi) :
    ∀ i, arg (phaseChart τ p i) = chartAngles τ p i := by
  rw [chart_angular hτ p hX]
  intro i
  have h := exp_angle_arg (ha i).1 (ha i).2
  fin_cases i <;> exact h

private lemma chart_left_inverse {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (p : Coordinates)
    (hX : 0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1)
    (hR : 0 ≤ (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2)
    (hδ : p 0 < 4)
    (ha : ∀ i, -Real.pi < chartAngles τ p i ∧ chartAngles τ p i < Real.pi) :
    phaseCoordinates τ (phaseChart τ p) = p := by
  have harg := chart_args hτ p hX ha
  have htrace := chart_trace hτ p hX hR hδ
  funext i
  fin_cases i
  · change 4 - traceModulus (phaseChart τ p) = p 0
    rw [htrace]
    ring
  all_goals
    simp only [phaseCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, harg]
    rcases hτ with rfl | rfl <;> dsimp [chartAngles] <;> ring

private lemma coordinate_analytic (p : Coordinates) (i : Fin 4) :
    AnalyticAt ℝ (fun q : Coordinates => q i) p :=
  (ContinuousLinearMap.proj i : Coordinates →L[ℝ] ℝ).analyticAt p

private lemma real_complex_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y : ℂ)) x :=
  (Complex.ofRealCLM.analyticAt _).comp hf

private lemma phase_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => Complex.exp ((f y : ℂ) * I)) x := by
  have he : AnalyticAt ℝ Complex.exp ((f x : ℂ) * I) :=
    analyticAt_cexp.restrictScalars (𝕜 := ℝ)
  have hi : AnalyticAt ℝ (fun y : E => (f y : ℂ) * I) x :=
    (real_complex_analytic hf).mul analyticAt_const
  exact he.comp (f := fun y : E => (f y : ℂ) * I) hi

private lemma chart_analytic (τ : ℝ) (p : Coordinates)
    (hR : 0 < (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2)
    (hX : 0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1) :
    AnalyticAt ℝ (phaseChart τ) p := by
  have hrad : AnalyticAt ℝ
      (fun q : Coordinates => (2 - q 0 / 2) ^ 2 - cos (q 2) ^ 2 * sin (q 1) ^ 2) p :=
    ((analyticAt_const.sub (coordinate_analytic p 0).div_const).pow 2).sub
      (((Real.analyticAt_cos.comp (coordinate_analytic p 2)).pow 2).mul
        ((Real.analyticAt_sin.comp (coordinate_analytic p 1)).pow 2))
  have hx : AnalyticAt ℝ (fun q : Coordinates => radialX (q 0) (q 1) (q 2)) p :=
    (((Real.analyticAt_cos.comp (coordinate_analytic p 2)).neg).mul
      (Real.analyticAt_cos.comp (coordinate_analytic p 1))).add (sqrt_analytic hrad hR)
  have hy : AnalyticAt ℝ
      (fun q : Coordinates => sqrt (1 - radialX (q 0) (q 1) (q 2) ^ 2)) p :=
    sqrt_analytic (analyticAt_const.sub (hx.pow 2)) (by nlinarith [hX.1, hX.2])
  have hcX := real_complex_analytic hx
  have hcY := real_complex_analytic hy
  have hm := phase_analytic (coordinate_analytic p 3)
  have ha := phase_analytic (coordinate_analytic p 1)
  have hb := phase_analytic (analyticAt_const.mul (coordinate_analytic p 2) :
    AnalyticAt ℝ (fun q : Coordinates => τ * q 2) p)
  have hnb := phase_analytic (analyticAt_const.mul (coordinate_analytic p 2) :
    AnalyticAt ℝ (fun q : Coordinates => -τ * q 2) p)
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hm.mul (ha.mul (hcX.add ((analyticAt_const.mul analyticAt_const).mul hcY)))
  · exact hm.mul (ha.mul (hcX.sub ((analyticAt_const.mul analyticAt_const).mul hcY)))
  · exact hm.mul hb
  · exact hm.mul hnb

private lemma inverse_analytic (τ : ℝ) (w : PhaseVector)
    (hs : ∀ i, w i ∈ Complex.slitPlane)
    (hn : w 0 + w 1 + w 2 + w 3 ≠ 0) :
    AnalyticAt ℝ (phaseCoordinates τ) w := by
  have he (i : Fin 4) : AnalyticAt ℝ (fun v : PhaseVector => v i) w :=
    (ContinuousLinearMap.proj i : PhaseVector →L[ℝ] ℂ).analyticAt w
  have ha (i : Fin 4) := arg_analytic (he i) (hs i)
  have hnorm := norm_analytic (((he 0).add (he 1)).add (he 2) |>.add (he 3)) hn
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_const.sub hnorm
  · exact ((((ha 0).add (ha 1)).sub (ha 2)).sub (ha 3)).div_const
  · exact (analyticAt_const.mul ((ha 2).sub (ha 3))).div_const
  · exact ((ha 2).add (ha 3)).div_const

/-- The distinguished point in the four real coordinates. -/
def baseCoordinates (δ : ℝ) : Coordinates := ![δ, 0, 0, 0]

private lemma radial_base {δ : ℝ} (hδ : δ < 2) :
    radialX δ 0 0 = 1 - δ / 2 := by
  simp only [radialX, cos_zero, sin_zero, one_pow, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero, mul_one]
  rw [Real.sqrt_sq (by linarith : 0 ≤ 2 - δ / 2)]
  ring

private lemma base_good {δ τ : ℝ} (hδ : 0 < δ ∧ δ < 2)
    (hτ : τ = 1 ∨ τ = -1) :
    (0 < radialX δ 0 0 ∧ radialX δ 0 0 < 1) ∧
    (0 < (2 - δ / 2) ^ 2) ∧
    (∀ i, -Real.pi < chartAngles τ (baseCoordinates δ) i ∧
      chartAngles τ (baseCoordinates δ) i < Real.pi) := by
  have hx : 0 < 1 - δ / 2 ∧ 1 - δ / 2 < 1 := by constructor <;> linarith [hδ.1, hδ.2]
  have ht0 := Real.arccos_pos.mpr hx.2
  have ht1 := Real.arccos_lt_pi_div_two.mpr hx.1
  refine ⟨by simpa only [radial_base hδ.2] using hx, sq_pos_of_pos (by linarith), ?_⟩
  intro i
  rcases hτ with rfl | rfl <;> fin_cases i <;>
    simp [chartAngles, baseCoordinates, radial_base hδ.2] <;>
    first | (constructor <;> linarith [Real.pi_pos]) | linarith [Real.pi_pos]

set_option maxHeartbeats 800000 in
private lemma chart_neighborhood {δ τ : ℝ} (hδ : 0 < δ ∧ δ < 2)
    (hτ : τ = 1 ∨ τ = -1) :
    ∀ᶠ p in 𝓝 (baseCoordinates δ),
      (0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1) ∧
      0 < (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2 ∧
      p 0 < 4 ∧
      (∀ i, -Real.pi < chartAngles τ p i ∧ chartAngles τ p i < Real.pi) ∧
      0 < cos (p 2) := by
  have hx : Continuous (fun p : Coordinates => radialX (p 0) (p 1) (p 2)) := by
    unfold radialX
    fun_prop
  have hr : Continuous (fun p : Coordinates =>
      (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2) := by fun_prop
  have ha (i : Fin 4) : Continuous (fun p : Coordinates => chartAngles τ p i) := by
    fin_cases i <;> dsimp [chartAngles] <;> simp only [radialX] <;> fun_prop
  obtain ⟨hbX, hbR, hbA⟩ := base_good hδ hτ
  have ex := hx.continuousAt.eventually (isOpen_Ioo.mem_nhds hbX)
  have er := hr.continuousAt.eventually (isOpen_Ioi.mem_nhds (by
    simpa [baseCoordinates] using hbR))
  have ed := (continuous_apply (0 : Fin 4)).continuousAt.eventually
    (isOpen_Iio.mem_nhds (show baseCoordinates δ 0 < 4 by simp [baseCoordinates]; linarith [hδ.2]))
  have ea : ∀ᶠ p in 𝓝 (baseCoordinates δ),
      ∀ i, -Real.pi < chartAngles τ p i ∧ chartAngles τ p i < Real.pi := by
    exact (eventually_all.mpr fun i => (ha i).continuousAt.eventually
      (isOpen_Ioo.mem_nhds (hbA i)))
  have ec := (Real.continuous_cos.comp (continuous_apply (2 : Fin 4))).continuousAt.eventually
    (isOpen_Ioi.mem_nhds (show 0 < cos (baseCoordinates δ 2) by simp [baseCoordinates]))
  filter_upwards [ex, er, ed, ea, ec] with p hp hr hd ha hc
  exact ⟨hp, hr, hd, ha, hc⟩

private lemma base_entries {δ τ : ℝ} (hδ : δ < 2) :
    phaseChart τ (baseCoordinates δ) =
      ![((1 - δ / 2 : ℝ) : ℂ) + τ * I * (sqrt (1 - (1 - δ / 2) ^ 2) : ℂ),
        ((1 - δ / 2 : ℝ) : ℂ) - τ * I * (sqrt (1 - (1 - δ / 2) ^ 2) : ℂ), 1, 1] := by
  simp [phaseChart, baseCoordinates, radial_base hδ]

private lemma inverse_neighborhood {δ τ : ℝ} (hδ : 0 < δ ∧ δ < 2)
    (hτ : τ = 1 ∨ τ = -1) :
    ∀ᶠ w in 𝓝 (phaseChart τ (baseCoordinates δ)),
      AnalyticAt ℝ (phaseCoordinates τ) w ∧
      (0 < halfAngle τ w ∧ halfAngle τ w < Real.pi / 2) ∧
      0 ≤ cos (phaseCoordinates τ w 2) * cos (phaseCoordinates τ w 1) := by
  let w₀ := phaseChart τ (baseCoordinates δ)
  obtain ⟨hX, hR, hA⟩ := base_good hδ hτ
  have hargs := chart_args hτ (baseCoordinates δ) (by simpa [baseCoordinates] using hX) hA
  have hslit (i : Fin 4) : w₀ i ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    fin_cases i <;> simp [w₀, base_entries hδ.2, Complex.mul_re, Complex.mul_im] <;>
      linarith [hδ.2]
  have hsum : w₀ 0 + w₀ 1 + w₀ 2 + w₀ 3 ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    simp [w₀, base_entries hδ.2, Complex.mul_re, Complex.mul_im] at hRe
    linarith [hδ.2]
  have hi := inverse_analytic τ w₀ hslit hsum
  have hhalf : AnalyticAt ℝ (halfAngle τ) w₀ := by
    have he (i : Fin 4) : AnalyticAt ℝ (fun v : PhaseVector => v i) w₀ :=
      (ContinuousLinearMap.proj i : PhaseVector →L[ℝ] ℂ).analyticAt w₀
    exact (analyticAt_const.mul ((arg_analytic (he 0) (hslit 0)).sub
      (arg_analytic (he 1) (hslit 1)))).div_const
  have hhalfval : halfAngle τ w₀ = arccos (1 - δ / 2) := by
    unfold halfAngle
    change τ * (arg (phaseChart τ (baseCoordinates δ) 0) -
      arg (phaseChart τ (baseCoordinates δ) 1)) / 2 = _
    rw [hargs 0, hargs 1]
    rcases hτ with rfl | rfl <;> simp [chartAngles, baseCoordinates, radial_base hδ.2] <;> ring
  have hh := hhalf.continuousAt.eventually (isOpen_Ioo.mem_nhds
    (show 0 < halfAngle τ w₀ ∧ halfAngle τ w₀ < Real.pi / 2 by
      rw [hhalfval]
      exact ⟨Real.arccos_pos.mpr (by linarith [hδ.1]),
        Real.arccos_lt_pi_div_two.mpr (by linarith [hδ.2])⟩))
  have hleft : phaseCoordinates τ w₀ = baseCoordinates δ := by
    apply chart_left_inverse hτ _ (by simpa [baseCoordinates] using hX)
      (by simpa [baseCoordinates] using hR.le) (by simp [baseCoordinates]; linarith [hδ.2]) hA
  have he2 : ContinuousAt (fun w : PhaseVector => phaseCoordinates τ w 2) w₀ :=
    (continuous_apply 2).continuousAt.comp hi.continuousAt
  have he1 : ContinuousAt (fun w : PhaseVector => phaseCoordinates τ w 1) w₀ :=
    (continuous_apply 1).continuousAt.comp hi.continuousAt
  have hc : ContinuousAt (fun w : PhaseVector =>
      cos (phaseCoordinates τ w 2) * cos (phaseCoordinates τ w 1)) w₀ :=
    (Real.continuous_cos.continuousAt.comp he2).mul
      (Real.continuous_cos.continuousAt.comp he1)
  have ehc := hc.eventually (isOpen_Ioi.mem_nhds (show
      0 < cos (phaseCoordinates τ w₀ 2) * cos (phaseCoordinates τ w₀ 1) by
    rw [hleft]; norm_num [baseCoordinates]))
  filter_upwards [hi.eventually_analyticAt, hh, ehc] with w ha hh hc
  exact ⟨ha, hh, hc.le⟩

end D5.S3.Quantum.Recovery.FourPathPhaseChart
