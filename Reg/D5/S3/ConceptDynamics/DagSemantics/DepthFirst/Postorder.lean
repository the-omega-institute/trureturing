import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Postorder
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Postorder

open AdjListClass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w z t

/-- The selected readout depends only on the vertex type and the forest. -/
def signature : Signature where
  Params := Type u
  State V := Forest V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := List V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => f.post) (fun e => nomatch e)

/-- A whole-family intervention duplicates the selected postorder. -/
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ f => List.append f.post f.post) (fun e => nomatch e)

/-- All original binders and clauses remain; only the first postorder is read out. -/
def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToList EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] {g : G}
    {i o : Set V} {f : Forest V} (_hf : IsDFSForest g i o f),
      (r.readout () V f).Nodup ∧
        (∀ a, a ∈ f.post ↔ a ∈ f.support) ∧
        f.post.Pairwise (fun earlier later => Adj g earlier later → Reachable g later earlier)

theorem rejected_law : ¬ arena.{u, v, w, z, t}.Law rejected := by
  intro law
  let : ToList (ULift.{w} Unit) (ULift.{v} Unit) := {
    toList := fun _ => []
    toArray := fun _ => #[]
    toArray_eq_mk_toList := fun _ => rfl
    isEmpty := fun _ => true
    isEmpty_iff_forall_not_mem := by simp }
  let : EmptyCollection (ULift.{w} Unit) := ⟨⟨()⟩⟩
  let : LawfulEmptyCollection (ULift.{w} Unit) (ULift.{v} Unit) :=
    { not_mem_empty := fun _ => List.not_mem_nil }
  let : DefaultDict.ReadOnly (ULift.{z} Unit) (ULift.{u} Unit) (ULift.{w} Unit)
      (fun _ ↦ ∅) := {
    getElem := fun _ _ _ => ∅
    toDFinsupp' := fun _ => ⟨fun _ => ∅, Trunc.mk ⟨0, fun _ => .inr rfl⟩⟩
    coe_toDFinsupp'_eq_getElem := fun _ => rfl }
  let : AdjListClass (ULift.{t} Unit) (ULift.{u} Unit) (ULift.{v} Unit)
      (ULift.{w} Unit) (ULift.{z} Unit) := {
    snd := fun _ _ => ⟨()⟩
    star := fun _ => ⟨()⟩ }
  let g : ULift.{t} Unit := ⟨()⟩
  let a : ULift.{u} Unit := ⟨()⟩
  have noSucc : succSet g {a} ⊆ ({a} : Set (ULift.{u} Unit)) := by
    rintro b ⟨c, _, ⟨edge⟩⟩
    exact (not_mem_empty edge.val.info edge.val.mem_star).elim
  have hf : IsDFSForest g ∅ {a} (.node a .nil .nil) := by
    apply IsDFSForest.node (g := g) {a} (by simp)
    · simpa using IsDFSForest.nil (g := g) {a}
    · exact Set.empty_subset _
    · exact noSucc
    · exact IsDFSForest.nil (g := g) _
  have nodup := (law hf).1
  change ([a, a] : List (ULift.{u} Unit)).Nodup at nodup
  simp at nodup

def registration : Registration arena.{u, v, w, z, t} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsDFSForest.post_spec.{u, v, w, z, t}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j different
      exact (different (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro role
    refine ⟨ULift.{u} Unit, .nil, .node ⟨()⟩ .nil .nil, ?_⟩
    change ([] : List (ULift.{u} Unit)) ≠ [⟨()⟩]
    simp

register_information_theorem IsDFSForest.post_spec in arena
  readout via (realize signature.{u} (fun _ _ f => f.post) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Postorder
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 13 }] })
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Postorder
