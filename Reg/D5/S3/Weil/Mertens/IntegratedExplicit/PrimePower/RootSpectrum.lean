import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum

/-! Source readouts of the boundary zero tail, error envelope and oriented primitive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum

open SquareSpectrum (signature actual)

abbrev transformArena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 < r → ∀ v : ℝ,
    let y := Real.exp v
    r * Real.exp ((1 - r / 2) * v) * (-(R.readout () () (Real.log y)).re +
      (r - 1) * Real.exp ((r - 1) * v) *
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) = rootDensity r (r * v)

def transformAltered : Realization signature :=
  realize signature (fun _ _ u => zeroTail u + 1) (fun e => nomatch e)

private theorem transform_rejected : ¬ transformArena.Law transformAltered := by
  intro h
  have hbad := h (r := 2) (by norm_num) 0
  have hgood := root_spectral_transform (r := 2) (by norm_num) 0
  simp only [transformAltered, realize, Real.exp_zero, Real.log_one, mul_zero,
    mul_one, Complex.add_re, Complex.one_re] at hbad hgood
  linarith only [hbad, hgood]

def transformFamily : Registration transformArena (type_of% @root_spectral_transform) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@root_spectral_transform, transformAltered, transform_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    transformArena.Law actual transformAltered transform_rejected
  dependence := SquareSpectrum.family.dependence

abbrev envelopeSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def envelopeActual : Realization envelopeSignature :=
  realize envelopeSignature (fun _ _ u => Real.exp u) (fun e => nomatch e)

def envelopeAltered : Realization envelopeSignature :=
  realize envelopeSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev envelopeArena : Arena where
  signature := envelopeSignature
  Law R := ∀ {r : ℝ}, 1 < r → ∀ {v : ℝ}, Real.log 2 ≤ v →
    |centered r (Real.exp (r * v)) - rootDensity r (r * v)| ≤
      (2 * r - 1) * C * R.readout () () (-(r * v) / 2)

private theorem envelope_rejected : ¬ envelopeArena.Law envelopeAltered := by
  intro h
  have hbad := h (r := 2) (by norm_num) (le_refl (Real.log 2))
  have hC : 0 < C := by
    unfold C
    apply abs_pos.mpr
    exact (Real.log_pos (by linarith [Real.pi_gt_three])).ne'
  change |centered 2 (Real.exp (2 * Real.log 2)) - rootDensity 2 (2 * Real.log 2)| ≤
    (2 * 2 - 1) * C * (-1) at hbad
  linarith only [hbad, hC, abs_nonneg (centered 2 (Real.exp (2 * Real.log 2)) -
    rootDensity 2 (2 * Real.log 2))]

def envelopeFamily : Registration envelopeArena (type_of% @root_centered_error) where
  actual := envelopeActual
  bridge := Iff.rfl
  variation := ⟨@root_centered_error, envelopeAltered, envelope_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    envelopeArena.Law envelopeActual envelopeAltered envelope_rejected
  dependence := by
    intro i
    cases i
    exact ⟨(), 0, 1, fun h => zero_ne_one (Real.exp_injective h)⟩

abbrev primitiveSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def primitiveActual : Realization primitiveSignature :=
  realize primitiveSignature (fun _ r x => rootPrimitive r x) (fun e => nomatch e)

def primitiveAltered : Realization primitiveSignature :=
  realize primitiveSignature (fun _ r x => rootPrimitive r x + 1) (fun e => nomatch e)

abbrev primitiveArena : Arena where
  signature := primitiveSignature
  Law R := ∀ {r : ℝ}, 1 < r → ∀ a b : ℝ,
    IntervalIntegrable (rootDensity r) volume a b ∧
      (∫ u in a..b, rootDensity r u) =
        R.readout () r (Real.exp b) - rootPrimitive r (Real.exp a)

private theorem primitive_rejected : ¬ primitiveArena.Law primitiveAltered := by
  intro h
  have hbad := (h (r := 2) (by norm_num) 0 0).2
  change (∫ u in (0 : ℝ)..0, rootDensity 2 u) =
    rootPrimitive 2 (Real.exp 0) + 1 - rootPrimitive 2 (Real.exp 0) at hbad
  rw [intervalIntegral.integral_same] at hbad
  linarith only [hbad]

private def squarePrimitiveCoeff (k : ℕ) : ℂ :=
  4 / (actualZero k * (2 - actualZero k) * (1 - actualZero k))

private theorem squarePrimitive_at_zero : rootPrimitive 2 0 = 0 := by
  have h (k : ℕ) : actualZero k / 2 - 1 / 2 ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    norm_num [Complex.div_re] at hre
    linarith [zero_re_lt_one k]
  change (∑' k : ℕ, (2 * (2 : ℂ) ^ 2) * ((0 : ℝ) : ℂ) ^
    (actualZero k / 2 - 1 / 2) /
    (actualZero k * (2 - actualZero k) * (2 - 2 * actualZero k))).re = 0
  have hz (k : ℕ) : (0 : ℂ) ^ (actualZero k / 2 - 1 / 2) = 0 :=
    Complex.zero_cpow (h k)
  simp only [Complex.ofReal_zero, hz, mul_zero, zero_div, tsum_zero, Complex.zero_re]

private theorem squarePrimitive_at_one : 0 < rootPrimitive 2 1 := by
  have hcoeff (k : ℕ) : squarePrimitiveCoeff k = 4 * actualCoeff k / (2 - actualZero k) := by
    unfold squarePrimitiveCoeff actualCoeff
    rw [← mul_div_assoc, mul_one, div_div]
    congr 1
    ring
  have hs : Summable squarePrimitiveCoeff := by
    apply (actualCoeff_hasSum.summable.norm.mul_left 4).of_norm_bounded
    intro k
    have hgap : 1 ≤ ‖2 - actualZero k‖ := by
      apply le_trans _ (Complex.re_le_norm _)
      simp only [Complex.sub_re, Complex.re_ofNat]
      linarith [zero_re_lt_one k]
    rw [hcoeff, norm_div, norm_mul]
    norm_num
    exact div_le_self (by positivity) hgap
  have hterm (k : ℕ) : 0 < (squarePrimitiveCoeff k).re := by
    let z := actualZero k
    have hβ : 0 < z.re := zero_re_pos k
    have hβ₁ : 0 < 1 - z.re := sub_pos.mpr (zero_re_lt_one k)
    have hβ₂ : 0 < 2 - z.re := by linarith
    have hre : (z * (2 - z) * (1 - z)).re =
        z.re * (1 - z.re) * (2 - z.re) + 3 * (1 - z.re) * z.im ^ 2 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im, zero_sub]
      ring
    have hpos : 0 < (z * (2 - z) * (1 - z)).re := by rw [hre]; positivity
    have hn : z * (2 - z) * (1 - z) ≠ 0 := by
      intro he
      exact hpos.ne' (by simp [he])
    change 0 < ((4 : ℂ) / (z * (2 - z) * (1 - z))).re
    simp only [Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, zero_div,
      add_zero]
    exact div_pos (by positivity) (Complex.normSq_pos.mpr hn)
  have hseries : (0 : ℝ) < ∑' k : ℕ, (squarePrimitiveCoeff k).re := by
    have h := Summable.tsum_lt_tsum (i := 0) (f := fun _ : ℕ => (0 : ℝ))
      (fun k => (hterm k).le) (hterm 0) summable_zero (Complex.hasSum_re hs.hasSum).summable
    simpa only [tsum_zero] using h
  rw [← Complex.re_tsum hs] at hseries
  convert hseries using 1
  change (∑' k : ℕ, (2 * (2 : ℂ) ^ 2) * ((1 : ℝ) : ℂ) ^
    (actualZero k / 2 - 1 / 2) /
    (actualZero k * (2 - actualZero k) * (2 - 2 * actualZero k))).re = _
  congr 1
  apply tsum_congr
  intro k
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one, squarePrimitiveCoeff]
  rw [show (2 : ℂ) - 2 * actualZero k = 2 * (1 - actualZero k) by ring]
  rw [show actualZero k * (2 - actualZero k) * (2 * (1 - actualZero k)) =
    2 * (actualZero k * (2 - actualZero k) * (1 - actualZero k)) by ring]
  rw [← div_div]
  norm_num

def primitiveFamily : Registration primitiveArena (type_of% @root_density_integral) where
  actual := primitiveActual
  bridge := Iff.rfl
  variation := ⟨@root_density_integral, primitiveAltered, primitive_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    primitiveArena.Law primitiveActual primitiveAltered primitive_rejected
  dependence := by
    intro i
    cases i
    refine ⟨2, 1, 0, ?_⟩
    change rootPrimitive 2 1 ≠ rootPrimitive 2 0
    rw [squarePrimitive_at_zero]
    exact squarePrimitive_at_one.ne'

def transformRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@root_spectral_transform) (Realization signature) Unit Unit where
  unitName := .str ``root_spectral_transform "__information_unit"
  realizationName := ``transformFamily
  realizationSource := none
  generated := false
  arena := .source ⟨transformArena⟩
  objectArena := .source ⟨transformArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transformArena ⟨transformFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => zeroTail u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def envelopeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@root_centered_error) (Realization envelopeSignature) Unit Unit where
  unitName := .str ``root_centered_error "__information_unit"
  realizationName := ``envelopeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨envelopeArena⟩
  objectArena := .source ⟨envelopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source envelopeArena ⟨envelopeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize envelopeSignature (fun _ _ u => Real.exp u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def primitiveRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@root_density_integral) (Realization primitiveSignature) Unit Unit where
  unitName := .str ``root_density_integral "__information_unit"
  realizationName := ``primitiveFamily
  realizationSource := none
  generated := false
  arena := .source ⟨primitiveArena⟩
  objectArena := .source ⟨primitiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source primitiveArena ⟨primitiveFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize primitiveSignature (fun _ r x => rootPrimitive r x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
