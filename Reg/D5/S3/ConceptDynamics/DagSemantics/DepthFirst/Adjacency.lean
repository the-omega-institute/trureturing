import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Adjacency
import Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Models

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Adjacency
open AdjListClass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v w z t

abbrev Vertex := ULift.{u} Bool
abbrev TargetGraph : Type t := Models.Graph Vertex.{u} Models.I.{v} Models.E.{w} Models.S.{z}

instance twoStars : DefaultDict.ReadOnly Models.S.{z} Vertex.{u} Models.E.{w} (fun _ => ∅) where
  getElem s a _ := ⟨s.down && !a.down⟩
  toDFinsupp' s := ⟨fun a => ⟨s.down && !a.down⟩,
    Trunc.mk ⟨{⟨false⟩, ⟨true⟩}, fun a => .inl (by
      rcases a with ⟨b⟩; cases b <;> simp)⟩⟩
  coe_toDFinsupp'_eq_getElem _ := rfl

instance twoGraph : AdjListClass TargetGraph.{u,v,w,z,t} Vertex.{u} Models.I.{v} Models.E.{w} Models.S.{z} where
  snd _ _ := ⟨true⟩
  star g := ⟨g.hasEdge⟩

def emptyTarget : TargetGraph.{u,v,w,z,t} := ⟨false⟩
def edgeTarget : TargetGraph.{u,v,w,z,t} := ⟨true⟩

theorem empty_no_adj (a b : Vertex.{u}) : ¬ Adj emptyTarget.{u,v,w,z,t} a b := by
  rintro ⟨edge⟩
  exact List.not_mem_nil edge.val.mem_star

abbrev signature : Signature where
  Params := Type t
  State G := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ G := G
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{t} :=
  realize signature (fun _ _ g => g) (fun e => nomatch e)
def rejected : Realization signature.{t} := by
  classical
  exact realize signature
    (fun _ => Function.update (fun (G : Type t) (g : G) => g)
      TargetGraph.{u,v,w,z,t} (fun _ => emptyTarget.{u,v,w,z,t})) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{t}
  Law r := ∀ {V : Type u} {Info : Type v}
    {EColl : Type w} [ToMultiset EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    {StarColl : Type z} [DefaultDict.ReadOnly StarColl V EColl fun _ => ∅]
    {G : Type t} [AdjListClass G V Info EColl StarColl] (g : G),
    Reachable (r.readout () G g : G) = Relation.ReflTransGen (Adj g)

theorem rejected_law : ¬ arena.{u,v,w,z,t}.Law rejected.{u,v,w,z,t} := by
  classical
  intro law
  have eq := congrFun (congrFun (law edgeTarget.{u,v,w,z,t}) (⟨false⟩ : Vertex.{u})) ⟨true⟩
  have edge : Adj edgeTarget.{u,v,w,z,t} (⟨false⟩ : Vertex.{u}) ⟨true⟩ :=
    ⟨homOfStar (g := edgeTarget.{u,v,w,z,t}) (v := ⟨false⟩) ⟨()⟩ (List.mem_cons_self ..)⟩
  have reach := eq.mpr (Relation.ReflTransGen.single edge)
  simp only [rejected, realize, Function.update_self] at reach
  rw [reachable_eq_reflTransGen] at reach
  have same : (⟨false⟩ : Vertex.{u}) = ⟨true⟩ := by
    exact ((Relation.reflTransGen_iff_eq
      (fun b => empty_no_adj.{u,v,w,z,t} ⟨false⟩ b)).mp reach).symm
  cases same

def registration : Registration arena.{u,v,w,z,t} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reachable_eq_reflTransGen.{u,v,w,z,t}, rejected, rejected_law⟩
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
    refine ⟨ULift.{t} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
    intro same
    cases same

register_information_theorem reachable_eq_reflTransGen in arena
  readout via (realize signature.{t} (fun _ _ g => g) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Adjacency
    coordinates := #[8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 10 }] })
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.DagSemantics.DepthFirst.Adjacency
