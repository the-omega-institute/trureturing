import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments
import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Summation
import Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices

/-! The configuration observations in the actual connected and tree moment transports. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments

open _root_.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature := _root_.Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.signature

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

namespace ConnectedOrder

abbrev actual : Realization signature := _root_.Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.actual

abbrev arena : Arena where
  signature := signature
  Law R := (letI : Fintype (ConnectedSets G500) := Fintype.ofFinite _
     ∑ S : ConnectedSets G500, Nat.card S.val) =
    ∑ c : Configuration, R.readout () () c

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (letI : Fintype (ConnectedSets G500) := Fintype.ofFinite _
     ∑ S : ConnectedSets G500, Nat.card S.val) = ∑ _c : Configuration, (0 : ℕ) at h
  simp only [Finset.sum_const_zero] at h
  have hExact := congrArg Prod.snd induced_exact_moments
  exact (by decide : (43855001336852520 : ℕ) ≠ 0) (hExact.symm.trans h)

def family : Registration arena (type_of% @connectedOrder_transport) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨connectedOrder_transport, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.family.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@connectedOrder_transport) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.connectedOrder_transport.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments.ConnectedOrder.family
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
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end ConnectedOrder

namespace TreeCount

abbrev actual : Realization signature := _root_.Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.Cardinality.actual

abbrev arena : Arena where
  signature := signature
  Law R := totalSubtreeCount G500 =
    ∑ c : Configuration, R.readout () () c

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change totalSubtreeCount G500 = ∑ _c : Configuration, (0 : ℕ) at h
  simp only [Finset.sum_const_zero] at h
  have hExact := congrArg Prod.fst tree_exact_moments
  exact (by decide : (14578492765509 : ℕ) ≠ 0) (hExact.symm.trans h)

def family : Registration arena (type_of% @subtreeCount_transport) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨subtreeCount_transport, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.Cardinality.family.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@subtreeCount_transport) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.subtreeCount_transport.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments.TreeCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => Nat.card (DeletionChoices c)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end TreeCount

namespace TreeOrder

abbrev actual : Realization signature := _root_.Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.actual

abbrev arena : Arena where
  signature := signature
  Law R := totalSubtreeOrder G500 =
    ∑ c : Configuration, R.readout () () c * Nat.card (DeletionChoices c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change totalSubtreeOrder G500 = ∑ c : Configuration, (0 : ℕ) * Nat.card (DeletionChoices c) at h
  simp only [Nat.zero_mul, Finset.sum_const_zero] at h
  have hExact := congrArg Prod.snd tree_exact_moments
  exact (by decide : (61323620645707018 : ℕ) ≠ 0) (hExact.symm.trans h)

def family : Registration arena (type_of% @subtreeOrder_transport) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨subtreeOrder_transport, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.family.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@subtreeOrder_transport) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.subtreeOrder_transport.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments.TreeOrder.family
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
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end TreeOrder

end
end Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments
