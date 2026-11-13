import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Words.OriginalGenerationBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.OriginalGenerationBoundary

open _root_.D5.S1.Words.OriginalGenerationBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature :=
  Reg.Support.SingleDependentReadout.signature (List Bool)
    (fun _ => List Bool) (fun _ => List Bool)

def actual : Realization signature :=
  realize signature
    (fun _ _ state => sigmaThree state ++ [false, true])
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (uK w : List Bool),
    R.readout () uK w = [false, true] ++ tauWord w ∧
      finitePrefix uK w = uK ++ tauWord w ++ [false, false]

private theorem actual_law : arena.Law actual := by
  intro uK w
  have h := _root_.D5.S1.Words.OriginalGenerationBoundary.original_generation_boundary uK w
  exact ⟨h.1, h.2⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h [] []).1
  change [] = [false, true] at hh
  simp at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨[], [], [true], ?_⟩
  change sigmaThree [] ++ [false, true] ≠ sigmaThree [true] ++ [false, true]
  decide

def family : Registration arena
    (type_of% (@_root_.D5.S1.Words.OriginalGenerationBoundary.original_generation_boundary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S1.Words.OriginalGenerationBoundary.original_generation_boundary)
    (type_of% actual) Unit Unit where
  unitName := `D5.S1.Words.OriginalGenerationBoundary.original_generation_boundary.__information_unit
  realizationName := `Reg.D5.S1.Words.OriginalGenerationBoundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ state => sigmaThree state ++ [false, true])
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.OriginalGenerationBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.OriginalGenerationBoundary
