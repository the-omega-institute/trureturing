import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
import Reg.Support.SingleDependentReadout

/-! The support-order readout on the actual configurations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement

open _root_.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Configuration) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ c => c.vertexOrder) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : Configuration, Nat.card (supportEquiv.symm c).val = R.readout () () c

private def singletonConfig : Configuration := .firstOnly ⟨(0, 0), le_rfl⟩

private def twoVertexConfig : Configuration := .firstOnly ⟨(0, 1), by decide⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h singletonConfig
  rw [supportEquiv_order] at hs
  exact Nat.noConfusion (show (1 : ℕ) = 0 from hs)

def family : Registration arena (type_of% @supportEquiv_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨supportEquiv_order, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(), singletonConfig, twoVertexConfig, by change (1 : ℕ) ≠ 2; decide⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@supportEquiv_order) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.supportEquiv_order.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c.vertexOrder) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
