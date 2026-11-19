import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport
import Reg.Support.SingleDependentReadout

/-! The equality observation retains the full compact meromorphic telescope. -/

noncomputable section

open _root_.D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory Complex
open scoped Interval

namespace Reg.D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (f : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b)
    (hf : MeromorphicOn f (Icc a b ×ℂ uIcc u v))
    (hfinite : ∀ z ∈ Icc a b ×ℂ uIcc u v, meromorphicOrderAt f z ≠ ⊤),
    R.readout () ()
      ((∫ x in a..b, Real.log ‖f ((x : ℂ) + I * (v : ℂ))‖) -
        (∫ x in a..b, Real.log ‖f ((x : ℂ) + I * (u : ℂ))‖))
      (∫ t in u..v, -(∫ x in a..b,
        (deriv f ((x : ℂ) + I * (t : ℂ)) /
          f ((x : ℂ) + I * (t : ℂ))).im))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (fun _ => 1) 0 0 0 0 le_rfl
    (fun z _ => MeromorphicAt.const 1 z) (by
      intro z hz
      rw [meromorphicOrderAt_const (E := ℂ) z (1 : ℂ)]
      simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @meromorphic_horizontal_lognorm_transport) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@meromorphic_horizontal_lognorm_transport, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@meromorphic_horizontal_lognorm_transport) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport.meromorphic_horizontal_lognorm_transport.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport
