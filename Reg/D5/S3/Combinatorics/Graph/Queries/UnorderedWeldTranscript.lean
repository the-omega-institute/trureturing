import D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The portion of the graph exposed outside the fixed edges varies with the transcript. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory (Side)
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
open _root_.D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory
open _root_.D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript

noncomputable section
universe u v

private abbrev WeldSignature : Signature where
  Params := Σ V : Type u, Σ L : Type v, Σ _ : L ↪ V, SimpleGraph V
  State p := History p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := SimpleGraph p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def exposedWeld : Realization WeldSignature.{u, v} :=
  realize WeldSignature (fun _ p history => (revealedEdges history \ p.2.2.2).comap p.2.2.1) (fun e => nomatch e)

private def allEdges : Realization WeldSignature.{u, v} :=
  realize WeldSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

private abbrev WeldArena : Arena where
  signature := WeldSignature.{u, v}
  Law R := ∀ {V : Type u} {L : Type v} [Finite V] [Fintype L] (e : L ↪ V) (k : L → Bool) (n : ℕ) (_hn : 2 ≤ n)
    (_hr : Nat.card (Side k false) = n) (_hb : Nat.card (Side k true) = n)
    (p : PassiveProtocol V (fun _ => Set V)) (fixed : SimpleGraph V)
    (ref : AlternatingCompletedGraph k ⊥) (_hdisjoint : Disjoint fixed (ref.1.1.map e))
    (μ : PMF (AlternatingCompletedGraph k ⊥))
    (_hμ : ∀ C, μ C = ((n.factorial * (n - 1).factorial / 2 : ℕ) : ℝ≥0∞)⁻¹),
    let T := runPassiveProtocol readNeighbors p (fixed ⊔ ref.1.1.map e)
    let F := R.readout () ⟨V, L, e, fixed⟩ T
    let event : Set (AlternatingCompletedGraph k ⊥) :=
      {C | runPassiveProtocol readNeighbors p (fixed ⊔ C.1.1.map e) = T}
    event = {C | F ≤ C.1.1} ∧
    μ.toOuterMeasure event =
      (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞) /
        (n.factorial * (n - 1).factorial / 2 : ℕ) ∧
    ∀ hEvent : ∃ C ∈ event, C ∈ μ.support,
      ∃ ν : PMF (AlternatingCompletedGraph k F),
        (∀ C, ν C = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
        μ.filter event hEvent = ν.map (forgetPrescribedEdges k)

private abbrev Four := ULift.{u} (Fin 4)

private def color (x : Four.{u}) : Bool := decide (x.down.val % 2 = 1)

private theorem color_count (b : Bool) : Nat.card (Side color.{u} b) = 2 := by
  let e : Side color.{u} b ≃ {v : Fin 4 // decide (v.val % 2 = 1) = b} :=
    Equiv.subtypeEquiv Equiv.ulift (fun _ => Iff.rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  cases b <;> decide

private def embedFour : Four.{v} ↪ Four.{u} :=
  (Equiv.ulift.trans Equiv.ulift.symm).toEmbedding

private theorem rejectsAllEdges : ¬ WeldArena.{u, v}.Law allEdges := by
  classical
  intro h
  let e := embedFour.{u, v}
  obtain ⟨_, μ, hu, _, _, _⟩ :=
    alternating_undirected_completion_law color.{v} (⊥ : SimpleGraph Four.{v})
      2 (by decide) (color_count false) (color_count true)
  obtain ⟨ref, _⟩ := μ.support_nonempty
  have hEvent := (h e color.{v} 2 (by decide) (color_count false) (color_count true)
    .stop ⊥ ref (by simp) μ hu).1
  have hRef : ref ∈ {C : AlternatingCompletedGraph color.{v} ⊥ |
      runPassiveProtocol readNeighbors .stop (⊥ ⊔ C.1.1.map e) =
        runPassiveProtocol readNeighbors .stop (⊥ ⊔ ref.1.1.map e)} := rfl
  rw [hEvent] at hRef
  have htop : (⊤ : SimpleGraph Four.{v}) ≤ ref.1.1 := hRef
  have heq : ref.1.1 = ⊤ := top_unique htop
  have hd := ref.1.2.2.1 (ULift.up (0 : Fin 4))
  rw [heq, SimpleGraph.ncard_neighborSet, SimpleGraph.complete_graph_degree] at hd
  simp at hd

private theorem exposure_varies (ref : AlternatingCompletedGraph color.{v} ⊥) :
    let e := embedFour.{u, v}
    let x : Four.{v} := ULift.up 0
    let p : PassiveProtocol Four.{u} (fun _ => Set Four.{u}) := .query (e x) (fun _ => .stop)
    exposedWeld.readout () ⟨Four.{u}, Four.{v}, e, ⊥⟩ [] ≠
      exposedWeld.readout () ⟨Four.{u}, Four.{v}, e, ⊥⟩
        (runPassiveProtocol readNeighbors p (⊥ ⊔ ref.1.1.map e)) := by
  intro e x p h
  have hPos : 0 < (ref.1.1.neighborSet x).ncard := by rw [ref.1.2.2.1]; decide
  obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hPos.ne'
  let G := ref.1.1.map e
  have hxy : G.Adj (e x) (e y) := SimpleGraph.map_adj_apply.mpr hy
  have hadj : (revealedEdges (runPassiveProtocol readNeighbors p G)).Adj (e x) (e y) := by
    rw [revealedEdges, SimpleGraph.fromRel_adj]
    exact ⟨G.ne_of_adj hxy, Or.inl ⟨⟨e x, G.neighborSet (e x)⟩, List.mem_cons_self, rfl, hxy⟩⟩
  have hbot : (⊥ : SimpleGraph Four.{u}) ⊔ G = G := by simp
  change ((revealedEdges ([] : History Four.{u})) \ (⊥ : SimpleGraph Four.{u})).comap e =
    ((revealedEdges (runPassiveProtocol readNeighbors p (⊥ ⊔ G))) \ ⊥).comap e at h
  simp only [hbot, sdiff_bot] at h
  change ((revealedEdges (runPassiveProtocol readNeighbors p G)).comap e).Adj x y at hadj
  rw [← h, SimpleGraph.comap_adj, revealedEdges, SimpleGraph.fromRel_adj] at hadj
  simp at hadj

def evidence : Registration WeldArena.{u, v} (type_of% (@weld_transcript_law.{u, v})) where
  actual := exposedWeld
  bridge := Iff.rfl
  variation := ⟨@weld_transcript_law.{u, v}, allEdges, rejectsAllEdges⟩
  sensitivity := ⟨fun i => ⟨allEdges,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsAllEdges⟩, fun e => nomatch e⟩
  dependence := by
    intro _
    obtain ⟨_, μ, _, _, _, _⟩ :=
      alternating_undirected_completion_law color.{v} (⊥ : SimpleGraph Four.{v})
        2 (by decide) (color_count false) (color_count true)
    obtain ⟨ref, _⟩ := μ.support_nonempty
    refine ⟨⟨Four.{u}, Four.{v}, embedFour.{u, v}, ⊥⟩, [], _, exposure_varies ref⟩


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weld_transcript_law.{u, v}) (Realization WeldSignature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript.weld_transcript_law
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨WeldArena.{u, v}⟩
  objectArena := .source ⟨WeldArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source WeldArena.{u, v} ⟨evidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize WeldSignature
    (fun _ p history => (revealedEdges history \ p.2.2.2).comap p.2.2.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript
    definition := none
    coordinates := #[0, 1, 4, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript
