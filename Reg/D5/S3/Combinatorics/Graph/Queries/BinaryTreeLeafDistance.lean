import D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-! Depth determines the dyadic weight of all leaves. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance

noncomputable section

private abbrev signature : Signature where
  Params := ℕ
  State k := {x : List Bool // x.length ≤ k}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def depth : Realization signature :=
  realize signature (fun _ _ x => x.1.length) (fun e => nomatch e)

private def zero : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (x : {x : List Bool // x.length ≤ k}),
    (leafWords k).Nodup ∧
    (∀ y : List Bool, y ∈ leafWords k ↔ y.length = k) ∧
    ((leafWords k).attach.map (fun y => (1 / 2 : ℚ) ^
      (boundedWordTree k).dist x ⟨y.1, ((weighted_leaf_distance k x).2.1 y.1 |>.mp y.2).le⟩)).sum =
      3 / 2 - (1 / 2 : ℚ) ^ (R.readout () k x + 1)

private def child : {x : List Bool // x.length ≤ 1} := ⟨[false], by decide⟩

private theorem rejectsZero : ¬ arena.Law zero := by
  intro h
  have hz := (h 1 child).2.2
  have hc := (weighted_leaf_distance 1 child).2.2
  rw [hc] at hz
  norm_num [child, zero, realize] at hz

private theorem dependence : ObservationalDependence signature depth := by
  intro i
  refine ⟨1, ⟨[], by decide⟩, child, ?_⟩
  change (0 : ℕ) ≠ 1
  decide

def evidence : Registration arena (type_of% (@weighted_leaf_distance)) where
  actual := depth
  bridge := Iff.rfl
  variation := ⟨@weighted_leaf_distance, zero, rejectsZero⟩
  sensitivity := ⟨fun i => ⟨zero,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsZero⟩, fun e => nomatch e⟩
  dependence := dependence


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      weighted_leaf_distance (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance.weighted_leaf_distance
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.1.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance

namespace Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private abbrev extensionSignature : Signature where
  Params := Bool
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def appendChild : Realization extensionSignature :=
  realize extensionSignature (fun _ b p => p ++ [b]) (fun e => nomatch e)

private def stayAtParent : Realization extensionSignature :=
  realize extensionSignature (fun _ _ p => p) (fun e => nomatch e)

private abbrev extensionArena : Arena where
  signature := extensionSignature
  Law R := ∀ (p : List Bool) (b : Bool), wordTree.Adj p (R.readout () b p)

private theorem stayAtParent_invalid : ¬ extensionArena.Law stayAtParent := by
  intro h
  exact (wordTree.loopless.irrefl []) (h [] false)

private theorem child_varies :
    appendChild.readout () false [] ≠ appendChild.readout () false [false] := by decide

noncomputable def childAdjEvidence : Registration extensionArena (type_of% (@child_adj)) where
  actual := appendChild
  bridge := Iff.rfl
  variation := ⟨@child_adj, stayAtParent, stayAtParent_invalid⟩
  sensitivity := ⟨fun i => ⟨stayAtParent,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, stayAtParent_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨false, [], [false], child_varies⟩

noncomputable def childAdjRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@child_adj) (Realization extensionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance.child_adj
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance.childAdjEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨extensionArena⟩
  objectArena := .source ⟨extensionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source extensionArena ⟨childAdjEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize extensionSignature (fun _ b p => p ++ [b]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance

namespace Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
open _root_.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private abbrev endpointSignature : Signature where
  Params := List Bool
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def stepTarget : Realization endpointSignature :=
  realize endpointSignature (fun _ _ endpoint => endpoint) (fun e => nomatch e)

private def stepSource : Realization endpointSignature :=
  realize endpointSignature (fun _ source _ => source) (fun e => nomatch e)

private abbrev endpointArena : Arena where
  signature := endpointSignature
  Law R := ∀ {x y : Word}, wordTree.Adj x y → Step x (R.readout () x y)

private theorem stepSource_invalid : ¬ endpointArena.Law stepSource := by
  intro h
  have impossible : Step [] [] := h (child_adj [] false)
  have differentLengths {x y : Word} (step : Step x y) : x.length ≠ y.length := by
    cases step <;> simp
  exact differentLengths impossible rfl

private theorem target_varies :
    stepTarget.readout () [] [false] ≠ stepTarget.readout () [] [true] := by
  decide

noncomputable def adjStepEvidence : Registration endpointArena (type_of% (@adj_step)) where
  actual := stepTarget
  bridge := Iff.rfl
  variation := ⟨@adj_step, stepSource, stepSource_invalid⟩
  sensitivity := ⟨fun i => ⟨stepSource,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, stepSource_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨[], [false], [true], target_varies⟩

noncomputable def adjStepRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@adj_step) (Realization endpointSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance.adj_step
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance.adjStepEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨endpointArena⟩
  objectArena := .source ⟨endpointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source endpointArena ⟨adjStepEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize endpointSignature (fun _ _ endpoint => endpoint) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
