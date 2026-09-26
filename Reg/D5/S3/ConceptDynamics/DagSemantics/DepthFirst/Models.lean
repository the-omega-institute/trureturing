import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Search
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Models
open AdjListClass
universe u v w z t q

abbrev V := ULift.{u} Unit
abbrev I := ULift.{v} Unit
abbrev E := ULift.{w} Bool
abbrev S := ULift.{z} Bool

/-- Phantom parameters retain all independent source universes. -/
structure Graph (Vertex : Type u) (Info : Type v) (Edges : Type w) (Stars : Type z) : Type t where
  hasEdge : Bool

abbrev G := Graph.{u,v,w,z,t} V I E S

instance edgeList : ToList E.{w} I.{v} where
  toList c := if c.down then [⟨()⟩] else []
  toArray c := (if c.down then [⟨()⟩] else []).toArray
  toArray_eq_mk_toList _ := rfl
  isEmpty c := !c.down
  isEmpty_iff_forall_not_mem := by
    intro c
    cases c with | up b => cases b <;> simp

instance edgeEmpty : EmptyCollection E.{w} := ⟨⟨false⟩⟩
instance edgeLawful : LawfulEmptyCollection E.{w} I.{v} where
  not_mem_empty _ := List.not_mem_nil

instance stars : DefaultDict.ReadOnly S.{z} V.{u} E.{w} (fun _ => ∅) where
  getElem s _ _ := ⟨s.down⟩
  toDFinsupp' s := ⟨fun _ => ⟨s.down⟩,
    Trunc.mk ⟨{⟨()⟩}, fun i => .inl (by simp [Subsingleton.elim i (⟨()⟩ : V.{u})])⟩⟩
  coe_toDFinsupp'_eq_getElem _ := rfl

instance graph : AdjListClass G.{u,v,w,z,t} V.{u} I.{v} E.{w} S.{z} where
  snd _ _ := ⟨()⟩
  star g := ⟨g.hasEdge⟩

def empty : G.{u,v,w,z,t} := ⟨false⟩
def loop : G.{u,v,w,z,t} := ⟨true⟩

theorem empty_no_adj (a b : V.{u}) : ¬ Adj empty.{u,v,w,z,t} a b := by
  rintro ⟨edge⟩
  exact List.not_mem_nil edge.val.mem_star

theorem singleton_dfs : IsDFSForest empty.{u,v,w,z,t} ∅ {⟨()⟩}
    (.node ⟨()⟩ .nil .nil) := by
  apply IsDFSForest.node (g := empty.{u,v,w,z,t}) {⟨()⟩} (by simp)
  · simpa using IsDFSForest.nil (g := empty.{u,v,w,z,t}) {⟨()⟩}
  · exact Set.empty_subset _
  · rintro b ⟨a, _, hab⟩
    exact (empty_no_adj a b hab).elim
  · exact IsDFSForest.nil (g := empty.{u,v,w,z,t}) _

theorem loop_adj : Adj loop.{u,v,w,z,t} (⟨()⟩ : V.{u}) ⟨()⟩ :=
  ⟨homOfStar (g := loop.{u,v,w,z,t}) (v := ⟨()⟩) ⟨()⟩ (List.mem_cons_self ..)⟩

instance visited : DefaultDict (ULift.{q} Bool) V.{u} Bool (fun _ => false) where
  Valid := fun _ _ => True
  all_valid := trivial
  getElem b _ _ := b.down
  setElem _ _ b := ⟨b⟩
  getElem_default _ := rfl
  getElem_setElem_self _ _ _ := rfl
  getElem_setElem_of_ne _ _ _ _ h := (h (Subsingleton.elim _ _)).elim
  toDFinsupp' b := ⟨fun _ => b.down,
    Trunc.mk ⟨{⟨()⟩}, fun i => .inl (by simp [Subsingleton.elim i (⟨()⟩ : V.{u})])⟩⟩
  coe_toDFinsupp'_eq_getElem _ := rfl

end Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Models
