import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments

namespace CFMPPairedSupportConormal230Transient

abbrev W := Fin 4 → ℝ

def projected (N P : W) : W := P - lorentz N P • N

def conormal (N P : W) : W :=
  (Real.sqrt (1 - (lorentz N P)^2))⁻¹ • projected N P

-- These algebraic checks do not identify an existing triangle's dualUnit.
theorem conormal_readout (A N P : W) :
    lorentz A (conormal N P) =
      (lorentz A P - lorentz N P * lorentz A N) /
        Real.sqrt (1 - (lorentz N P)^2) := by
  simp [conormal, projected, lorentz, Fin.sum_univ_four, smul_eq_mul, div_eq_mul_inv]
  ring

theorem conormal_orthogonal (N P : W) (hN : lorentz N N = 1) :
    lorentz N (conormal N P) = 0 := by
  rw [conormal_readout, hN]
  ring

theorem projected_norm (N P : W) (hN : lorentz N N = 1)
    (hP : lorentz P P = 1) :
    lorentz (projected N P) (projected N P) = 1 - (lorentz N P)^2 := by
  have he : lorentz (projected N P) (projected N P) =
      lorentz P P - 2 * lorentz N P * lorentz N P +
        (lorentz N P)^2 * lorentz N N := by
    simp [projected, lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  rw [he, hN, hP]
  ring

theorem conormal_unit (N P : W) (hN : lorentz N N = 1)
    (hP : lorentz P P = 1) (hc : 0 < 1 - (lorentz N P)^2) :
    lorentz (conormal N P) (conormal N P) = 1 := by
  have hs : Real.sqrt (1 - (lorentz N P)^2) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have he : lorentz (conormal N P) (conormal N P) =
      (Real.sqrt (1 - (lorentz N P)^2))⁻¹ ^ 2 *
        lorentz (projected N P) (projected N P) := by
    simp [conormal, lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  rw [he, projected_norm N P hN hP, inv_pow, Real.sq_sqrt hc.le]
  exact inv_mul_cancel₀ hc.ne'

theorem paired_readout (N P dN dP : W)
    (hN : lorentz dN N = 0) (hP : lorentz dP P = 0) :
    lorentz dN (conormal N P) + lorentz dP (conormal P N) =
      (lorentz dN P + lorentz N dP) / Real.sqrt (1 - (lorentz N P)^2) := by
  rw [conormal_readout, conormal_readout, hN, hP, lorentz_symm P N,
    lorentz_symm dP N]
  ring

theorem lorentz_hasDerivAt (N P : ℝ → W) (dN dP : W) (t : ℝ)
    (hN : ∀ i, HasDerivAt (fun s => N s i) (dN i) t)
    (hP : ∀ i, HasDerivAt (fun s => P s i) (dP i) t) :
    HasDerivAt (fun s => lorentz (N s) (P s))
      (lorentz dN (P t) + lorentz (N t) dP) t := by
  convert ((((hN 0).mul (hP 0)).add ((hN 1).mul (hP 1))).add
    ((hN 2).mul (hP 2))).sub ((hN 3).mul (hP 3)) using 1 <;>
    simp [lorentz, Fin.sum_univ_four] <;> first | rfl | ring

theorem paired_angle_readout (N P dN dP : W) (alpha dalpha : ℝ)
    (hN : lorentz dN N = 0) (hP : lorentz dP P = 0)
    (ha0 : 0 < alpha) (hapi : alpha < Real.pi)
    (hc : lorentz N P = -Real.cos alpha)
    (hdc : lorentz dN P + lorentz N dP = Real.sin alpha * dalpha) :
    lorentz dN (conormal N P) + lorentz dP (conormal P N) = dalpha := by
  have hs : 0 < Real.sin alpha := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsqrt : Real.sqrt (1 - (lorentz N P)^2) = Real.sin alpha := by
    have hsq : 1 - (lorentz N P)^2 = (Real.sin alpha)^2 := by
      rw [hc]
      nlinarith [Real.sin_sq_add_cos_sq alpha]
    rw [hsq, Real.sqrt_sq hs.le]
  rw [paired_readout N P dN dP hN hP, hdc, hsqrt]
  exact mul_div_cancel_left₀ dalpha hs.ne'

theorem unit_derivative_orthogonal (N : ℝ → W) (dN : W) (t : ℝ)
    (hN : ∀ i, HasDerivAt (fun s => N s i) (dN i) t)
    (hunit : (fun s => lorentz (N s) (N s)) =ᶠ[𝓝 t] fun _ => (1 : ℝ)) :
    lorentz dN (N t) = 0 := by
  have hd := lorentz_hasDerivAt N N dN dN t hN hN
  have hz := hd.unique ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hunit)
  rw [lorentz_symm (N t) dN] at hz
  linarith

theorem angle_pairing_derivative (N P : ℝ → W) (dN dP : W)
    (alpha : ℝ → ℝ) (dalpha t : ℝ)
    (hN : ∀ i, HasDerivAt (fun s => N s i) (dN i) t)
    (hP : ∀ i, HasDerivAt (fun s => P s i) (dP i) t)
    (ha : HasDerivAt alpha dalpha t)
    (hpair : (fun s => lorentz (N s) (P s)) =ᶠ[𝓝 t]
      fun s => -Real.cos (alpha s)) :
    lorentz dN (P t) + lorentz (N t) dP = Real.sin (alpha t) * dalpha := by
  have hd := lorentz_hasDerivAt N P dN dP t hN hP
  have hc := ha.cos.neg.congr_of_eventuallyEq hpair
  simpa only [neg_mul, neg_neg] using hd.unique hc

theorem paired_angle_path (N P : ℝ → W) (dN dP : W)
    (alpha : ℝ → ℝ) (dalpha t : ℝ)
    (hN : ∀ i, HasDerivAt (fun s => N s i) (dN i) t)
    (hP : ∀ i, HasDerivAt (fun s => P s i) (dP i) t)
    (ha : HasDerivAt alpha dalpha t)
    (hunitN : (fun s => lorentz (N s) (N s)) =ᶠ[𝓝 t] fun _ => (1 : ℝ))
    (hunitP : (fun s => lorentz (P s) (P s)) =ᶠ[𝓝 t] fun _ => (1 : ℝ))
    (hpair : (fun s => lorentz (N s) (P s)) =ᶠ[𝓝 t]
      fun s => -Real.cos (alpha s))
    (ha0 : 0 < alpha t) (hapi : alpha t < Real.pi) :
    lorentz dN (conormal (N t) (P t)) +
      lorentz dP (conormal (P t) (N t)) = dalpha := by
  exact paired_angle_readout (N t) (P t) dN dP (alpha t) dalpha
    (unit_derivative_orthogonal N dN t hN hunitN)
    (unit_derivative_orthogonal P dP t hP hunitP) ha0 hapi hpair.eq_of_nhds
    (angle_pairing_derivative N P dN dP alpha dalpha t hN hP ha hpair)

end CFMPPairedSupportConormal230Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPPairedSupportConormal230Transient.conormal_unit,
      ``CFMPPairedSupportConormal230Transient.paired_angle_path] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP230 target absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP230 disallowed axiom {ax} in {name}"
    Lean.logInfo m!"CFMP230 CHECKED {name} axioms={axioms}"

