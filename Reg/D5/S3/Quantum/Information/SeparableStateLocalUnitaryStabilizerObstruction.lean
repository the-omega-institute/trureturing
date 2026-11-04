import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import Reg.Support.DependentFamily

/-! Source-bound audit of the two coordinates of the unit vector. -/

namespace Reg.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
open _root_.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ i => (![1, 0] : Fin 2 → ℂ) i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := unitVector (fun i => R.readout () () i)

theorem rejected_law : ¬ arena.Law rejected := by
  change ¬ unitVector (fun _ : Fin 2 => (0 : ℂ))
  norm_num [unitVector, dotProduct, Fin.sum_univ_two]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (1 : ℂ) ≠ 0
  exact one_ne_zero

def source_registration : Registration arena (type_of% unit_e0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unit_e0, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@unit_e0) (Realization signature) Unit Unit := {
  unitName := `SeparableStateLocalUnitaryStabilizerObstruction.unit
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
  readout := some (realize signature
    (fun _ _ i => (![1, 0] : Fin 2 → ℂ) i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
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
end Reg.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
