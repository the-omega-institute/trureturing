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
universe u

private abbrev WeldSignature : Signature where
  Params := Σ V : Type u, SimpleGraph V
  State p := History p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := SimpleGraph p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def exposedWeld : Realization WeldSignature.{u} :=
  realize WeldSignature (fun _ p history => revealedEdges history \ p.2) (fun e => nomatch e)

private def allEdges : Realization WeldSignature.{u} :=
  realize WeldSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

private abbrev WeldArena : Arena where
  signature := WeldSignature.{u}
  Law R := ∀ {V : Type u} [Fintype V] (k : V → Bool) (n : ℕ) (_hn : 2 ≤ n)
    (_hr : Nat.card (Side k false) = n) (_hb : Nat.card (Side k true) = n)
    (p : PassiveProtocol V (fun _ => Set V)) (fixed : SimpleGraph V)
    (ref : AlternatingCompletedGraph k ⊥) (_hdisjoint : Disjoint fixed ref.1.1)
    (μ : PMF (AlternatingCompletedGraph k ⊥))
    (_hμ : ∀ C, μ C = ((n.factorial * (n - 1).factorial / 2 : ℕ) : ℝ≥0∞)⁻¹),
    let T := runPassiveProtocol readNeighbors p (fixed ⊔ ref.1.1)
    let F := R.readout () ⟨V, fixed⟩ T
    let event : Set (AlternatingCompletedGraph k ⊥) :=
      {C | runPassiveProtocol readNeighbors p (fixed ⊔ C.1.1) = T}
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

private theorem rejectsAllEdges : ¬ WeldArena.{u}.Law allEdges := by
  classical
  intro h
  obtain ⟨_, μ, hu, _, _, _⟩ :=
    alternating_undirected_completion_law color.{u} (⊥ : SimpleGraph Four.{u})
      2 (by decide) (color_count false) (color_count true)
  obtain ⟨ref, _⟩ := μ.support_nonempty
  have hEvent := (h color.{u} 2 (by decide) (color_count false) (color_count true)
    .stop ⊥ ref (by simp) μ hu).1
  have hRef : ref ∈ {C : AlternatingCompletedGraph color.{u} ⊥ |
      runPassiveProtocol readNeighbors .stop (⊥ ⊔ C.1.1) =
        runPassiveProtocol readNeighbors .stop (⊥ ⊔ ref.1.1)} := rfl
  rw [hEvent] at hRef
  have htop : (⊤ : SimpleGraph Four.{u}) ≤ ref.1.1 := hRef
  have heq : ref.1.1 = ⊤ := top_unique htop
  have hd := ref.1.2.2.1 (ULift.up (0 : Fin 4))
  rw [heq, SimpleGraph.ncard_neighborSet, SimpleGraph.complete_graph_degree] at hd
  simp at hd

private theorem exposure_varies (ref : AlternatingCompletedGraph color.{u} ⊥) :
    let x : Four.{u} := ULift.up 0
    let p : PassiveProtocol Four.{u} (fun _ => Set Four.{u}) := .query x (fun _ => .stop)
    exposedWeld.readout () ⟨Four.{u}, ⊥⟩ [] ≠
      exposedWeld.readout () ⟨Four.{u}, ⊥⟩
        (runPassiveProtocol readNeighbors p (⊥ ⊔ ref.1.1)) := by
  intro x p h
  have hPos : 0 < (ref.1.1.neighborSet x).ncard := by rw [ref.1.2.2.1]; decide
  obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hPos.ne'
  have hadj : (revealedEdges (runPassiveProtocol readNeighbors p ref.1.1)).Adj x y := by
    rw [revealedEdges, SimpleGraph.fromRel_adj]
    exact ⟨ref.1.1.ne_of_adj hy, Or.inl ⟨⟨x, ref.1.1.neighborSet x⟩, List.mem_cons_self, rfl, hy⟩⟩
  have hbot : (⊥ : SimpleGraph Four.{u}) ⊔ ref.1.1 = ref.1.1 := by simp
  simp only [exposedWeld, realize, hbot, sdiff_bot] at h
  rw [← h, revealedEdges, SimpleGraph.fromRel_adj] at hadj
  simp at hadj

def evidence : Registration WeldArena.{u} (type_of% (@weld_transcript_law.{u})) where
  actual := exposedWeld
  bridge := Iff.rfl
  variation := ⟨@weld_transcript_law.{u}, allEdges, rejectsAllEdges⟩
  sensitivity := ⟨fun i => ⟨allEdges,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsAllEdges⟩, fun e => nomatch e⟩
  dependence := by
    intro _
    obtain ⟨_, μ, _, _, _, _⟩ :=
      alternating_undirected_completion_law color.{u} (⊥ : SimpleGraph Four.{u})
        2 (by decide) (color_count false) (color_count true)
    obtain ⟨ref, _⟩ := μ.support_nonempty
    refine ⟨⟨Four.{u}, ⊥⟩, [], _, exposure_varies ref⟩


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weld_transcript_law.{u}) (Realization WeldSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript.weld_transcript_law
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨WeldArena.{u}⟩
  objectArena := .source ⟨WeldArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source WeldArena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize WeldSignature
    (fun _ p history => revealedEdges history \ p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript
    definition := none
    coordinates := #[0, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript
