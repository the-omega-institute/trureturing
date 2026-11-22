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

namespace SupportVertices

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Configuration) (fun _ => Set Vertex)

def actual : Realization signature :=
  realize signature (fun _ _ c => c.vertices) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : Configuration, (supportEquiv.symm c).val = R.readout () () c

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : singletonConfig.vertices = (∅ : Set Vertex) :=
    (supportEquiv_symm_verts _).symm.trans (h _)
  have hn : singletonConfig.vertices.Nonempty :=
    Set.nonempty_coe_sort.mp singletonConfig.supportConnected.nonempty
  exact hn.ne_empty he

def family : Registration arena (type_of% @supportEquiv_symm_verts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨supportEquiv_symm_verts, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), singletonConfig, twoVertexConfig, ?_⟩
    intro e
    have h : firstPath 1 ∈ twoVertexConfig.vertices := by
      change (1 : Fin 500) ∈ Set.Icc 0 1
      decide
    have h' : firstPath 1 ∈ singletonConfig.vertices :=
      (show singletonConfig.vertices = twoVertexConfig.vertices from e).symm ▸ h
    change (1 : Fin 500) ∈ Set.Icc 0 0 at h'
    exact (by decide : (1 : Fin 500) ∉ Set.Icc 0 0) h'

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@supportEquiv_symm_verts) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.supportEquiv_symm_verts.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.SupportVertices.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c.vertices) (fun e => nomatch e))
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

end SupportVertices

namespace SupportConnected

abbrev arena : Arena where
  signature := SupportVertices.signature
  Law R := ∀ c : Configuration, (G500.induce (R.readout () () c)).Connected

private theorem rejected_law : ¬ arena.Law SupportVertices.rejected := by
  intro h
  have vacant := h singletonConfig
  change (G500.induce (∅ : Set Vertex)).Connected at vacant
  exact Set.not_nonempty_empty (Set.nonempty_coe_sort.mp vacant.nonempty)

def family : Registration arena (type_of% @Configuration.supportConnected) where
  actual := SupportVertices.actual
  bridge := Iff.rfl
  variation := ⟨Configuration.supportConnected, SupportVertices.rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := SupportVertices.family.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@Configuration.supportConnected) (Realization SupportVertices.signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.Configuration.supportConnected.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.SupportConnected.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize SupportVertices.signature (fun _ _ c => c.vertices) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SupportConnected
end
end Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
