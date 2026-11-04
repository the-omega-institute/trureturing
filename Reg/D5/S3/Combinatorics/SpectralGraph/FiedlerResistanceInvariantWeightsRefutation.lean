import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of connectivity of the complete bipartite graph on two and three vertices. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation

open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe connectivity as the graph on five vertices varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => SimpleGraph (Fin 5)) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ G => @decide G.Connected (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () K23 = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change false = true at h
  exact Bool.false_ne_true h

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), K23, (⊥ : SimpleGraph (Fin 5)), ?_⟩
  change @decide K23.Connected (Classical.propDecidable _) ≠
    @decide (⊥ : SimpleGraph (Fin 5)).Connected (Classical.propDecidable _)
  simp [K23_connected, SimpleGraph.not_connected_bot]

def source_registration : Registration arena (type_of% @K23_connected) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [actual, realize] using K23_connected, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@K23_connected) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation.unit
  realizationName :=
    .str `Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ G => @decide G.Connected (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
