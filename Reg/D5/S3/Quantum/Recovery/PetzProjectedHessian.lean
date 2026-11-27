import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzProjectedHessian
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the exact energy of the weighted representative. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzProjectedHessian
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

namespace Reg.D5.S3.Quantum.Recovery.PetzProjectedHessian

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (w : Weights) (Y : Joint)
    (_hw : ∀ i j, 0 < w i j) (_hs : ∀ i j, w i j = w j i) (_hY : Y.IsHermitian),
    (representative w Y).IsHermitian ∧ partialTraceRight (representative w Y) = 0 ∧
    (∀ Z : Joint, partialTraceRight Z = 0 →
      pairing w (representative w Y) Z = (Y * Z).trace.re) ∧
    F.readout () () (energy w (representative w Y))
      (∑ b : Fin 2, ∑ d : Fin 2,
        (reducedWeight w b d * Complex.normSq (Y (b, 0) (d, 0) - Y (b, 1) (d, 1)) +
         w (b, 0) (d, 1) * Complex.normSq (Y (b, 0) (d, 1)) +
         w (b, 1) (d, 0) * Complex.normSq (Y (b, 1) (d, 0))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (fun _ _ => 1) 0 (fun _ _ => zero_lt_one) (fun _ _ => rfl)
    Matrix.isHermitian_zero).2.2.2

def sourceRegistration : Registration arena (type_of% @representative_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@representative_spec, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@representative_spec) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzProjectedHessian.representative_spec.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzProjectedHessian.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzProjectedHessian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Recovery.PetzProjectedHessian
