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
