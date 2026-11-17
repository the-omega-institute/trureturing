import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import Reg.Support.SingleDependentReadout

/-! Source-bound audit for the angular kernel equality consumed by finite-cell coercivity. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaGamma.FormCore.LineFourier
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.LineFourier

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => Complex.exp z) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The angular kernel is the sole varied observation. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (f : ℝ → ℂ) (t : ℝ), angularFourier f t =
    ∫ x : ℝ, R.readout () () (((-(t*x) : ℝ) : ℂ) * Complex.I) * f x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))) 0
  rw [angularFourier_eq_integral] at hbad
  norm_num [rejected, realize, integral_indicator measurableSet_Icc,
    measureReal_def, Real.volume_Icc] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, (Real.pi : ℂ) * Complex.I, ?_⟩
  change Complex.exp 0 ≠ Complex.exp ((Real.pi : ℂ) * Complex.I)
  rw [Complex.exp_zero, Complex.exp_pi_mul_I]
  norm_num

def family : Registration arena (type_of% @angularFourier_eq_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@angularFourier_eq_integral, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@angularFourier_eq_integral) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.LineFourier.angularFourier_eq_integral.audit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.LineFourier.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => Complex.exp z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.LineFourier
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.Weil.ZetaGamma.FormCore.LineFourier
