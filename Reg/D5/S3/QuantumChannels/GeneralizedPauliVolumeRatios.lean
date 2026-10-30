import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios
import Reg.Support.DependentFamily

/-! Source-bound audit of the generalized Pauli channel volume ratios. -/

namespace Reg.D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios

open _root_.D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe real equality in the completely positive to box volume ratio. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

/-- Retain the dimension hypothesis and all three ratio equalities. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ d : ℕ, 2 ≤ d →
    r.readout () () (channelVolume d (cpRegion d) / channelVolume d (boxRegion d))
        ((d : ℝ) / ((d + 1).factorial : ℝ)) ∧
    channelVolume d (generatorRegion d) / channelVolume d (cpRegion d) =
        (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) * (((d : ℝ) - 1) / (d : ℝ)) ^ d ∧
    channelVolume d (ebRegion d) / channelVolume d (generatorRegion d) =
        1 / ((d : ℝ) + 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 2 (by norm_num)).1 (result 2 (by norm_num)).1

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.unit
  realizationName := `Reg.D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.source_registration
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
    owner := `D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios
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

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios
