import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.KuNearLineRefutation
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Geometry.KuNearLineRefutation
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open KuGeometry

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Finset P) (fun _ => ℕ)

def actual : Realization signature := realize signature
  (fun _ _ S => S.card) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 9) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ S : Finset P, Config S → R.readout () () S ≤ 8

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he : Config (∅ : Finset P) := by simp [Config]
  have hn := h ∅ he
  change 9 ≤ 8 at hn
  omega

def family : Registration arena (type_of% (@config_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨config_bound, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    refine ⟨(), ∅, {fun _ => 0}, ?_⟩
    change (∅ : Finset P).card ≠ ({fun _ => 0} : Finset P).card
    simp

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@config_bound) (Realization signature) Type Unit := {
  unitName := `KuGeometry.config_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.KuNearLineRefutation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => S.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.KuNearLineRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Geometry.KuNearLineRefutation
