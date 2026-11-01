import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the encoding scale and cyclic character unit identity. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample

open _root_.D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (Complex.normSq ((Real.sqrt 2 : ℂ)⁻¹)) (1 / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

def source_registration : Registration arena (type_of% @scale_normSq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scale_normSq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@scale_normSq) (Realization signature) Unit Unit := {
  unitName := .str ``scale_normSq "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample

namespace Reg.D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample.ChiUnit

open _root_.D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample (chi_unit)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe multiplication of the conjugate character value and the character value. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x * y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (i : Fin 3) (g : Multiplicative (ZMod 3)),
    R.readout () () (star (ZMod.stdAddChar (ZMod.finEquiv 3 i * g.toAdd)))
      (ZMod.stdAddChar (ZMod.finEquiv 3 i * g.toAdd)) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 1
  change (0 : ℂ) = 1 at hbad
  exact zero_ne_one hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad := congrFun he 1
  change (0 : ℂ) * 1 = 1 * 1 at hbad
  simp at hbad

def source_registration : Registration arena (type_of% @chi_unit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chi_unit, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@chi_unit) (Realization signature) Unit Unit := {
  unitName := .str ``chi_unit "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ x y => x * y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print chi_unit
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample.ChiUnit
