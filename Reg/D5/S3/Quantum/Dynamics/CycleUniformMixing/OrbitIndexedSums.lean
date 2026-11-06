import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of conjugation of the standard cyclic character. -/

namespace Reg.D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier

open _root_.D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier (char_star)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe complex conjugation at the character value in the source equality. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => (starRingEnd ℂ) z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the modulus, its nonzero instance, and every character argument. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} [NeZero N] (x : ZMod N),
    R.readout () () (ZMod.stdAddChar x) = ZMod.stdAddChar (-x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := @h 1 inferInstance 0
  change (0 : ℂ) = ZMod.stdAddChar (-(0 : ZMod 1)) at hbad
  simp at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (starRingEnd ℂ) 0 ≠ (starRingEnd ℂ) 1
  simp

def source_registration : Registration arena (type_of% @char_star) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@char_star, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@char_star) (Realization signature) Unit Unit := {
  unitName := .str ``char_star "__information_unit"
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
    (realize signature (fun _ _ z => (starRingEnd ℂ) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print char_star
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier
