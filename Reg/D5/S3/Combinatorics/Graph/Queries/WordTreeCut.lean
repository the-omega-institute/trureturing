import D5.S3.Combinatorics.Graph.Queries.WordTreeCut
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Child-prefix membership distinguishes the two components after deleting the parent edge. -/

open LeanInformationAudit
open SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
open _root_.D5.S3.Combinatorics.Graph.Queries.WordTreeCut
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Queries.WordTreeCut

private abbrev Vertex (k : ℕ) := {word : List Bool // word.length ≤ k}

private abbrev cutSignature : Signature where
  Params := Σ k : ℕ, Σ (_ : Vertex k), Bool
  State p := Vertex p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def prefixMembership : Realization cutSignature :=
  realize cutSignature (fun _ p word => belowChild p.1 p.2.1 p.2.2 word) (fun e => nomatch e)

private def emptyMembership : Realization cutSignature :=
  realize cutSignature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := cutSignature
  Law R := ∀ (k : ℕ) (p : Vertex k) (a : Bool) (hChild : (p.1 ++ [a]).length ≤ k),
    let side := R.readout () ⟨k, p, a⟩
    ∀ u v : Vertex k,
      ((boundedWordTree k).deleteEdges {s(p, ⟨p.1 ++ [a], hChild⟩)}).Reachable u v ↔
        (side u ↔ side v)

private def parent : Vertex 1 := ⟨[], by simp⟩
private theorem childBound : (parent.1 ++ [false]).length ≤ 1 := by decide
private def child : Vertex 1 := ⟨parent.1 ++ [false], childBound⟩

private theorem parent_outside : ¬ belowChild 1 parent false parent := by
  simp [belowChild, parent]

private theorem child_inside : belowChild 1 parent false child :=
  List.prefix_refl _

private theorem emptyMembership_invalid : ¬ arena.Law emptyMembership := by
  intro h
  have hFalse : (False ↔ False) := Iff.rfl
  have hReach := (h 1 parent false childBound parent child).mpr hFalse
  have hSide := (bounded_reachable_after_extension_cut 1 parent false childBound parent child).mp hReach
  exact parent_outside (hSide.mpr child_inside)

private theorem membership_varies :
    prefixMembership.readout () ⟨1, parent, false⟩ parent ≠
      prefixMembership.readout () ⟨1, parent, false⟩ child := by
  intro h
  change belowChild 1 parent false parent = belowChild 1 parent false child at h
  exact parent_outside (h ▸ child_inside)

noncomputable def evidence : Registration arena (type_of% (@bounded_reachable_after_extension_cut)) where
  actual := prefixMembership
  bridge := Iff.rfl
  variation := ⟨@bounded_reachable_after_extension_cut, emptyMembership, emptyMembership_invalid⟩
  sensitivity := ⟨fun i => ⟨emptyMembership,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, emptyMembership_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨⟨1, parent, false⟩, parent, child, membership_varies⟩

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bounded_reachable_after_extension_cut) (Realization cutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.WordTreeCut.bounded_reachable_after_extension_cut
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.WordTreeCut.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize cutSignature (fun _ p word => belowChild p.1 p.2.1 p.2.2 word) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.WordTreeCut
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Queries.WordTreeCut
