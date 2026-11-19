import D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The size of the actual target set controls the new-weld-edge estimate. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open _root_.D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound
open _root_.D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound

noncomputable section
universe u v

private abbrev signature : Signature where
  Params := Type v
  State L := Finset L
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def cardinality : Realization signature.{v} :=
  realize signature (fun _ _ S => S.card) (fun e => nomatch e)

private def zero : Realization signature.{v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {V : Type u} {L : Type v} [Finite V] [Fintype L]
    (e : L ↪ V) (k : L → Bool) (n : ℕ) (_hn : 2 ≤ n)
    (_h0 : Nat.card (Side k false) = n) (_h1 : Nat.card (Side k true) = n)
    (p : PassiveProtocol V (fun _ => Set V)) (fixed : SimpleGraph V)
    (ref : AlternatingCompletedGraph k ⊥) (_hdisjoint : Disjoint fixed (ref.1.1.map e))
    (μ : PMF (AlternatingCompletedGraph k ⊥))
    (_hμ : ∀ C, μ C = ((n.factorial * (n - 1).factorial / 2 : ℕ) : ℝ≥0∞)⁻¹)
    (x : L) (S : Finset L),
    let T := runPassiveProtocol readNeighbors p (fixed ⊔ ref.1.1.map e)
    let F := (revealedEdges T \ fixed).comap e
    let event : Set (AlternatingCompletedGraph k ⊥) :=
      {C | runPassiveProtocol readNeighbors p (fixed ⊔ C.1.1.map e) = T}
    ∀ hEvent : ∃ C ∈ event, C ∈ μ.support,
      2 * T.length + 2 ≤ n →
      (μ.filter event hEvent).toOuterMeasure
        {C | ∃ y ∈ S, C.1.1.Adj x y ∧ ¬ F.Adj x y} ≤
        (2 * R.readout () L S : ℝ≥0∞) / ((n - 2 * T.length - 1 : ℕ) : ℝ≥0∞)

private abbrev Four := ULift.{u} (Fin 4)

private def color (x : Four.{u}) : Bool := decide (x.down.val % 2 = 1)

private theorem color_count (b : Bool) : Nat.card (Side color.{u} b) = 2 := by
  let e : Side color.{u} b ≃ {v : Fin 4 // decide (v.val % 2 = 1) = b} :=
    Equiv.subtypeEquiv Equiv.ulift (fun _ => Iff.rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  cases b <;> decide

private def embedFour : Four.{v} ↪ Four.{u} :=
  (Equiv.ulift.trans Equiv.ulift.symm).toEmbedding


private theorem rejectsZero : ¬ arena.{u, v}.Law zero := by
  classical
  intro h
  let e := embedFour.{u, v}
  let x : Four.{v} := ULift.up 0
  let p : PassiveProtocol Four.{u} (fun _ => Set Four.{u}) := .stop
  let A := AlternatingCompletedGraph color.{v} (⊥ : SimpleGraph Four.{v})
  obtain ⟨_, μ, hu, _, _, _⟩ :=
    alternating_undirected_completion_law color.{v} (⊥ : SimpleGraph Four.{v})
      2 (by decide) (color_count false) (color_count true)
  obtain ⟨ref, href⟩ := μ.support_nonempty
  let event : Set A := {C | runPassiveProtocol readNeighbors p (⊥ ⊔ C.1.1.map e) =
    runPassiveProtocol readNeighbors p (⊥ ⊔ ref.1.1.map e)}
  have hEvent : ∃ C ∈ event, C ∈ μ.support := ⟨ref, rfl, href⟩
  have hq : 2 * (runPassiveProtocol readNeighbors p
      (⊥ ⊔ ref.1.1.map e)).length + 2 ≤ 2 := by simp [p, runPassiveProtocol]
  have hBound := h e color.{v} 2 (by decide) (color_count false) (color_count true)
    p ⊥ ref (by simp) μ hu x Finset.univ hEvent hq
  let F := (revealedEdges ([] : History Four.{u}) \ (⊥ : SimpleGraph Four.{u})).comap e
  have hEmpty : F = ⊥ := by
    ext a b
    simp [F, revealedEdges, SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
  have hAll : {C : A | ∃ y ∈ (Finset.univ : Finset Four.{v}), C.1.1.Adj x y ∧
      ¬ F.Adj x y} = Set.univ := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Finset.mem_univ, true_and, hEmpty,
      SimpleGraph.bot_adj, not_false_eq_true, and_true]
    have hd : 0 < (C.1.1.neighborSet x).ncard := by rw [C.1.2.2.1]; decide
    exact Set.nonempty_of_ncard_ne_zero hd.ne'
  change (μ.filter event hEvent).toOuterMeasure
    {C : A | ∃ y ∈ (Finset.univ : Finset Four.{v}), C.1.1.Adj x y ∧ ¬ F.Adj x y} ≤ _ at hBound
  rw [hAll, PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe] at hBound
  have hOne : (1 : ℝ≥0∞) ≤ 0 := by
    simpa only [zero, realize, Nat.cast_zero, mul_zero, ENNReal.zero_div] using hBound
  exact (not_le_of_gt zero_lt_one) hOne

private theorem dependence : ObservationalDependence signature.{v} cardinality := by
  intro _
  refine ⟨Four.{v}, ∅, {ULift.up 0}, ?_⟩
  change (∅ : Finset Four.{v}).card ≠ ({ULift.up 0} : Finset Four.{v}).card
  simp

def evidence : Registration arena.{u, v} (type_of% (@weld_query_prefix_bound.{u, v})) where
  actual := cardinality
  bridge := Iff.rfl
  variation := ⟨@weld_query_prefix_bound.{u, v}, zero, rejectsZero⟩
  sensitivity := ⟨fun i => ⟨zero,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsZero⟩, fun e => nomatch e⟩
  dependence := dependence


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weld_query_prefix_bound.{u, v}) (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound.weld_query_prefix_bound
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨evidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => S.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 17
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound
