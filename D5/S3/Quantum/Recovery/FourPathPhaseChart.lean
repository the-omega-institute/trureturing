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
    rfl
  · change Complex.exp (((m + a - τ * θ : ℝ) : ℂ) * I) = _
    rw [show m + a - τ * θ = m + a + (-τ * θ) by ring,
      phase_add, phase_add, hminus, mul_assoc]
    rfl
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
  have he (i : Fin 4) : Continuous (fun p : Coordinates => p i) := continuous_apply i
  have hr : Continuous (fun p : Coordinates =>
      (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2) :=
    ((continuous_const.sub ((he 0).div_const 2)).pow 2).sub
      (((Real.continuous_cos.comp (he 2)).pow 2).mul
        ((Real.continuous_sin.comp (he 1)).pow 2))
  have hx : Continuous (fun p : Coordinates => radialX (p 0) (p 1) (p 2)) :=
    (((Real.continuous_cos.comp (he 2)).neg).mul (Real.continuous_cos.comp (he 1))).add
      (Real.continuous_sqrt.comp hr)
  have hθ : Continuous (fun p : Coordinates =>
      arccos (radialX (p 0) (p 1) (p 2))) := Real.continuous_arccos.comp hx
  have ha (i : Fin 4) : Continuous (fun p : Coordinates => chartAngles τ p i) := by
    fin_cases i
    · exact ((continuous_apply 3).add (continuous_apply 1)).add (continuous_const.mul hθ)
    · exact ((continuous_apply 3).add (continuous_apply 1)).sub (continuous_const.mul hθ)
    · exact (continuous_apply 3).add (continuous_const.mul (continuous_apply 2))
    · exact (continuous_apply 3).sub (continuous_const.mul (continuous_apply 2))
  obtain ⟨hbX, hbR, hbA⟩ := base_good hδ hτ
  have ex : ∀ᶠ p in 𝓝 (baseCoordinates δ),
      0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1 :=
    (hx.continuousAt (x := baseCoordinates δ)).eventually
      (isOpen_Ioo.mem_nhds (show
        radialX (baseCoordinates δ 0) (baseCoordinates δ 1) (baseCoordinates δ 2) ∈ Ioo 0 1 by
          change 0 < radialX δ 0 0 ∧ radialX δ 0 0 < 1
          exact hbX))
  have er : ∀ᶠ p in 𝓝 (baseCoordinates δ),
      0 < (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2 :=
    (hr.continuousAt (x := baseCoordinates δ)).eventually (isOpen_Ioi.mem_nhds (by
    simpa [baseCoordinates] using hbR))
  have ed : ∀ᶠ p in 𝓝 (baseCoordinates δ), p 0 < 4 :=
    ((he 0).continuousAt (x := baseCoordinates δ)).eventually
    (isOpen_Iio.mem_nhds (show baseCoordinates δ 0 < 4 by simp [baseCoordinates]; linarith [hδ.2]))
  have ea : ∀ᶠ p in 𝓝 (baseCoordinates δ),
      ∀ i, -Real.pi < chartAngles τ p i ∧ chartAngles τ p i < Real.pi := by
    exact (eventually_all.mpr fun i => ((ha i).continuousAt (x := baseCoordinates δ)).eventually
      (isOpen_Ioo.mem_nhds (hbA i)))
  have ec : ∀ᶠ p in 𝓝 (baseCoordinates δ), 0 < cos (p 2) :=
    ((Real.continuous_cos.comp (he 2)).continuousAt (x := baseCoordinates δ)).eventually
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

private lemma chart_amplitudes {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (p : Coordinates) (h c s : ℝ) (hm : p 3 = 0) :
    amplitudeP h c (phaseChart τ p) =
      2 * ((h : ℂ) * radialX (p 0) (p 1) (p 2) * Complex.exp ((p 1 : ℂ) * I) +
        (c : ℂ) * cos (p 2)) ∧
    amplitudeQ h s (phaseChart τ p) =
      2 * τ * (I * h * sqrt (1 - radialX (p 0) (p 1) (p 2) ^ 2) *
        Complex.exp ((p 1 : ℂ) * I) - s * sin (p 2)) ∧
    oppositeModulus (phaseChart τ p) =
      2 * ‖I * sqrt (1 - radialX (p 0) (p 1) (p 2) ^ 2) *
        Complex.exp ((p 1 : ℂ) * I) - sin (p 2)‖ := by
  have heplus : Complex.exp (((τ * p 2 : ℝ) : ℂ) * I) =
      (cos (p 2) : ℂ) + τ * I * (sin (p 2) : ℂ) := by
    rw [euler]
    rcases hτ with rfl | rfl <;> simp <;> ring
  have heminus : Complex.exp (((-τ * p 2 : ℝ) : ℂ) * I) =
      (cos (p 2) : ℂ) - τ * I * (sin (p 2) : ℂ) := by
    rw [euler]
    rcases hτ with rfl | rfl <;> simp <;> ring
  have hi : I ^ 2 = -1 := Complex.I_sq
  have hb : phaseChart τ p 0 - phaseChart τ p 1 +
      I * (phaseChart τ p 2 - phaseChart τ p 3) =
      2 * τ * (I * sqrt (1 - radialX (p 0) (p 1) (p 2) ^ 2) *
        Complex.exp ((p 1 : ℂ) * I) - sin (p 2)) := by
    simp only [phaseChart, hm, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero,
      heplus, heminus]
    linear_combination 2 * (τ : ℂ) * (sin (p 2) : ℂ) * hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [amplitudeP, phaseChart, hm, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero, heplus, heminus]
    ring
  · simp only [amplitudeQ, phaseChart, hm, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero, heplus, heminus]
    linear_combination 2 * (τ : ℂ) * (s : ℂ) * (sin (p 2) : ℂ) * hi
  · unfold oppositeModulus
    rw [hb, norm_mul, norm_mul]
    rcases hτ with rfl | rfl <;> norm_num

private lemma normalized_scalar_unique {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (p q : Coordinates) (hp : p 3 = 0) (hq : q 3 = 0)
    (hcp : 0 < cos (p 2)) (hcq : 0 < cos (q 2))
    (hlp : phaseCoordinates τ (phaseChart τ p) = p)
    (hlq : phaseCoordinates τ (phaseChart τ q) = q)
    (scalar : ℂ) (heq : ∀ i, phaseChart τ p i = scalar * phaseChart τ q i) :
    p = q ∧ scalar = 1 := by
  have hprod (r : Coordinates) (hr : r 3 = 0) :
      phaseChart τ r 2 * phaseChart τ r 3 = 1 := by
    simp only [phaseChart, hr, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero]
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1 <;> push_cast <;> ring
  have hsq : scalar ^ 2 = 1 := by
    calc
      scalar ^ 2 = scalar ^ 2 * (phaseChart τ q 2 * phaseChart τ q 3) := by rw [hprod q hq, mul_one]
      _ = phaseChart τ p 2 * phaseChart τ p 3 := by rw [heq 2, heq 3]; ring
      _ = 1 := hprod p hp
  have hre (r : Coordinates) (hr : r 3 = 0) :
      (phaseChart τ r 2).re = cos (r 2) := by
    simp only [phaseChart, hr, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_mul, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero, euler]
    rcases hτ with rfl | rfl <;>
      simp only [one_mul, neg_one_mul, cos_neg, sin_neg, Complex.ofReal_neg,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.neg_im, neg_zero, zero_mul, mul_zero, sub_zero, add_zero]
  have hs : scalar = 1 := by
    rcases sq_eq_one_iff.mp hsq with hs | hs
    · exact hs
    · have hh := congrArg Complex.re (heq 2)
      rw [hs, neg_one_mul, Complex.neg_re, hre p hp, hre q hq] at hh
      linarith
  refine ⟨?_, hs⟩
  have he : phaseChart τ p = phaseChart τ q := by
    funext i
    simpa only [hs, one_mul] using heq i
  calc
    p = phaseCoordinates τ (phaseChart τ p) := hlp.symm
    _ = phaseCoordinates τ (phaseChart τ q) := congrArg (phaseCoordinates τ) he
    _ = q := hlq

/-- The original positive optimizer feedback, with its phase angle explicit. -/
def referenceFeedback (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I),
    Complex.exp ((θ : ℂ) * I), Complex.exp (((-θ : ℝ) : ℂ) * I)]

/-- Actual feedback whose relative diagonal is the chart phase vector. -/
def actualFeedback (τ : ℝ) (p : Coordinates) (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (phaseChart τ p) * referenceFeedback θ

/-- Same-feedback realization and the action of one common scalar. -/
def FeedbackLaws (τ : ℝ) (p : Coordinates) : Prop :=
  (∀ θ, actualFeedback τ p θ ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    actualFeedback τ p θ * star (referenceFeedback θ) = Matrix.diagonal (phaseChart τ p)) ∧
  ∀ scalar : ℂ, ‖scalar‖ = 1 →
    (∀ θ, Matrix.diagonal (fun i => scalar * phaseChart τ p i) * referenceFeedback θ ∈
      Matrix.unitaryGroup (Fin 4) ℂ) ∧
    traceModulus (fun i => scalar * phaseChart τ p i) = traceModulus (phaseChart τ p) ∧
    oppositeModulus (fun i => scalar * phaseChart τ p i) = oppositeModulus (phaseChart τ p) ∧
    ∀ h c s : ℝ,
      amplitudeP h c (fun i => scalar * phaseChart τ p i) = scalar * amplitudeP h c (phaseChart τ p) ∧
      amplitudeQ h s (fun i => scalar * phaseChart τ p i) = scalar * amplitudeQ h s (phaseChart τ p)

private lemma diagonal_unitary (w : PhaseVector) (hw : ∀ i, ‖w i‖ = 1) :
    Matrix.diagonal w ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  apply Matrix.diagonal_mem_unitary.mpr
  apply Pi.mem_unitary_iff.mpr
  intro i
  rw [Unitary.mem_iff, Complex.star_def]
  have hn : w i * starRingEnd ℂ (w i) = 1 := by
    rw [Complex.mul_conj', hw i]
    norm_num
  exact ⟨by rw [mul_comm]; exact hn, hn⟩

private lemma feedback_laws (τ : ℝ) (p : Coordinates) (hw : ∀ i, ‖phaseChart τ p i‖ = 1) :
    FeedbackLaws τ p := by
  have hu (θ : ℝ) : referenceFeedback θ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    apply diagonal_unitary
    intro i
    fin_cases i
    · norm_num
    · exact phase_norm (Real.pi / 4)
    · exact phase_norm θ
    · exact phase_norm (-θ)
  constructor
  · intro θ
    refine ⟨(Matrix.unitaryGroup (Fin 4) ℂ).mul_mem (diagonal_unitary _ hw) (hu θ), ?_⟩
    change (Matrix.diagonal (phaseChart τ p) * referenceFeedback θ) * star (referenceFeedback θ) = _
    rw [mul_assoc, (Matrix.mem_unitaryGroup_iff.mp (hu θ)), mul_one]
  · intro scalar hs
    have ht : traceModulus (fun i => scalar * phaseChart τ p i) =
        ‖scalar * (phaseChart τ p 0 + phaseChart τ p 1 + phaseChart τ p 2 + phaseChart τ p 3)‖ := by
      unfold traceModulus
      congr 1
      ring
    have hb : oppositeModulus (fun i => scalar * phaseChart τ p i) =
        ‖scalar * (phaseChart τ p 0 - phaseChart τ p 1 + I * (phaseChart τ p 2 - phaseChart τ p 3))‖ := by
      unfold oppositeModulus
      congr 1
      ring
    have hscaled (i : Fin 4) : ‖scalar * phaseChart τ p i‖ = 1 := by
      rw [norm_mul, hs, hw i, one_mul]
    refine ⟨fun θ => (Matrix.unitaryGroup (Fin 4) ℂ).mul_mem
      (diagonal_unitary _ hscaled) (hu θ), by rw [ht, norm_mul, hs, one_mul]; rfl,
      by rw [hb, norm_mul, hs, one_mul]; rfl, ?_⟩
    intro h c s
    constructor <;> simp only [amplitudeP, amplitudeQ] <;> ring

/-- Local analytic inverse laws on the actual four-dimensional phase torus,
with unique normalized representatives under one common scalar. -/
theorem local_phase_chart {δ τ : ℝ} (hδ : 0 < δ ∧ δ < 2)
    (hτ : τ = 1 ∨ τ = -1) :
    ∃ S : Set Coordinates, ∃ V : Set PhaseVector,
      IsOpen S ∧ IsOpen V ∧ baseCoordinates δ ∈ S ∧
      phaseChart τ (baseCoordinates δ) ∈ V ∧
      (∀ p ∈ S, (∀ i, ‖phaseChart τ p i‖ = 1) ∧
        traceModulus (phaseChart τ p) = 4 - p 0 ∧
        phaseCoordinates τ (phaseChart τ p) = p ∧
        AnalyticAt ℝ (phaseChart τ) p ∧ 0 < cos (p 2) ∧
        (∀ h c s : ℝ, p 3 = 0 →
          amplitudeP h c (phaseChart τ p) =
            2 * ((h : ℂ) * radialX (p 0) (p 1) (p 2) * Complex.exp ((p 1 : ℂ) * I) +
              (c : ℂ) * cos (p 2)) ∧
          amplitudeQ h s (phaseChart τ p) =
            2 * τ * (I * h * sqrt (1 - radialX (p 0) (p 1) (p 2) ^ 2) *
              Complex.exp ((p 1 : ℂ) * I) - s * sin (p 2)) ∧
          oppositeModulus (phaseChart τ p) =
            2 * ‖I * sqrt (1 - radialX (p 0) (p 1) (p 2) ^ 2) *
              Complex.exp ((p 1 : ℂ) * I) - sin (p 2)‖) ∧
        (0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1) ∧
        0 < (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2 ∧ FeedbackLaws τ p) ∧
      (∀ w ∈ V, AnalyticAt ℝ (phaseCoordinates τ) w ∧
        ((∀ i, ‖w i‖ = 1) → phaseCoordinates τ w ∈ S ∧
          phaseChart τ (phaseCoordinates τ w) = w)) ∧
      (∀ p ∈ S, ∀ q ∈ S, p 3 = 0 → q 3 = 0 → ∀ scalar : ℂ,
        (∀ i, phaseChart τ p i = scalar * phaseChart τ q i) → p = q ∧ scalar = 1) ∧
      Set.BijOn (phaseChart τ) S (V ∩ {w | ∀ i, ‖w i‖ = 1}) := by
  obtain ⟨S, hSsub, hSopen, hSbase⟩ := eventually_nhds_iff.mp (chart_neighborhood hδ hτ)
  have hSp (p : Coordinates) (hp : p ∈ S) := hSsub p hp
  have hleft (p : Coordinates) (hp : p ∈ S) : phaseCoordinates τ (phaseChart τ p) = p :=
    chart_left_inverse hτ p (hSp p hp).1 (hSp p hp).2.1.le
      (hSp p hp).2.2.1 (hSp p hp).2.2.2.1
  have hInv := inverse_neighborhood hδ hτ
  have hi : AnalyticAt ℝ (phaseCoordinates τ) (phaseChart τ (baseCoordinates δ)) :=
    (Filter.Eventually.self_of_nhds hInv).1
  have hInto : ∀ᶠ w in 𝓝 (phaseChart τ (baseCoordinates δ)), phaseCoordinates τ w ∈ S :=
    hi.continuousAt.eventually (hSopen.mem_nhds (by rw [hleft _ hSbase]; exact hSbase))
  have ev : ∀ᶠ w in 𝓝 (phaseChart τ (baseCoordinates δ)),
      AnalyticAt ℝ (phaseCoordinates τ) w ∧
      ((∀ i, ‖w i‖ = 1) → phaseCoordinates τ w ∈ S ∧
        phaseChart τ (phaseCoordinates τ w) = w) := by
    filter_upwards [hInv, hInto] with w hw hin
    exact ⟨hw.1, fun hu => ⟨hin, actual_reconstruction hτ w hu hw.2.1 hw.2.2⟩⟩
  obtain ⟨V, hVsub, hVopen, hVbase⟩ := eventually_nhds_iff.mp ev
  let S' := S ∩ phaseChart τ ⁻¹' V
  have hc : ContinuousOn (phaseChart τ) S := fun p hp =>
    (chart_analytic τ p (hSp p hp).2.1 (hSp p hp).1).continuousAt.continuousWithinAt
  have hopen : IsOpen S' := hc.isOpen_inter_preimage hSopen hVopen
  refine ⟨S', V, hopen, hVopen, ⟨hSbase, hVbase⟩, hVbase, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hh := hSp p hp.1
    exact ⟨chart_unit hτ p hh.1, chart_trace hτ p hh.1 hh.2.1.le hh.2.2.1,
      hleft p hp.1, chart_analytic τ p hh.2.1 hh.1, hh.2.2.2.2,
      (fun h c s hm => chart_amplitudes hτ p h c s hm),
      hh.1, hh.2.1, feedback_laws τ p (chart_unit hτ p hh.1)⟩
  · intro w hw
    refine ⟨(hVsub w hw).1, fun hu => ?_⟩
    obtain ⟨hin, hr⟩ := (hVsub w hw).2 hu
    exact ⟨⟨hin, by change phaseChart τ (phaseCoordinates τ w) ∈ V; rw [hr]; exact hw⟩, hr⟩
  · intro p hp q hq hpm hqm scalar hs
    exact normalized_scalar_unique hτ p q hpm hqm (hSp p hp.1).2.2.2.2
      (hSp q hq.1).2.2.2.2 (hleft p hp.1) (hleft q hq.1) scalar hs
  · refine ⟨?_, ?_, ?_⟩
    · intro p hp
      exact ⟨hp.2, chart_unit hτ p (hSp p hp.1).1⟩
    · intro p hp q hq heq
      calc
        p = phaseCoordinates τ (phaseChart τ p) := (hleft p hp.1).symm
        _ = phaseCoordinates τ (phaseChart τ q) := congrArg (phaseCoordinates τ) heq
        _ = q := hleft q hq.1
    · intro w hw
      obtain ⟨hin, hr⟩ := (hVsub w hw.1).2 hw.2
      exact ⟨phaseCoordinates τ w,
        ⟨hin, by change phaseChart τ (phaseCoordinates τ w) ∈ V; rw [hr]; exact hw.1⟩, hr⟩

end D5.S3.Quantum.Recovery.FourPathPhaseChart
