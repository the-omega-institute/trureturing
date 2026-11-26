import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
import Reg.Support.DependentFamily

/-! # Completed-graph cardinality in the undirected completion law -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw

noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State V := SimpleGraph V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ F => Nat.card (CompletedGraph F)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V),
    Nonempty (CompletedGraph F) →
    ∃ (μ : PMF (Lift F)) (ν : PMF (CompletedGraph F)),
      (∀ l, μ l = (Nat.card (Lift F) : ℝ≥0∞)⁻¹) ∧
      (∀ C, ν C = (R.readout () V F : ℝ≥0∞)⁻¹) ∧
      μ.map (forget hn) = ν

private theorem complete_three : Nonempty (CompletedGraph (⊥ : SimpleGraph (ULift.{u} (Fin 3)))) := by
  classical
  refine ⟨⟨⊤, SimpleGraph.connected_top, ?_, bot_le⟩⟩
  intro v
  rw [SimpleGraph.ncard_neighborSet, SimpleGraph.complete_graph_degree]
  simp

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} (Fin 3)
  obtain ⟨_, ν, _, hu, _⟩ := h (V := V) (by simp [V]) ⊥ complete_three
  obtain ⟨C, _⟩ := ν.support_nonempty
  apply ν.apply_ne_top C
  simpa [rejected, realize] using hu C

private theorem variation_at_four :
    Nat.card (CompletedGraph (⊥ : SimpleGraph (ULift.{u} (Fin 4)))) ≠
      Nat.card (CompletedGraph (⊤ : SimpleGraph (ULift.{u} (Fin 4)))) := by
  classical
  let V := ULift.{u} (Fin 4)
  let e : Fin 4 ≃ V := Equiv.ulift.symm
  let G := (SimpleGraph.cycleGraph 4).map e
  let i : SimpleGraph.cycleGraph 4 ≃g G := SimpleGraph.Iso.map e _
  have hbot : Nonempty (CompletedGraph (⊥ : SimpleGraph V)) := by
    refine ⟨⟨G, (SimpleGraph.connected_cycleGraph_add_one (n := 3)).map i.toHom i.surjective, ?_,
      bot_le⟩⟩
    intro x
    obtain ⟨y, rfl⟩ := i.surjective x
    rw [SimpleGraph.ncard_neighborSet, i.degree_eq]
    exact SimpleGraph.cycleGraph_degree_three_le
  have htop : IsEmpty (CompletedGraph (⊤ : SimpleGraph V)) := by
    refine ⟨fun C => ?_⟩
    have hC : C.1 = ⊤ := le_antisymm le_top C.2.2.2
    let x : V := ULift.up 0
    have hd := C.2.2.1 x
    rw [hC, SimpleGraph.ncard_neighborSet, SimpleGraph.complete_graph_degree] at hd
    simp [V] at hd
  have hpositive : 0 < Nat.card (CompletedGraph (⊥ : SimpleGraph V)) :=
    Finite.card_pos_iff.mpr hbot
  rw [Finite.card_eq_zero_iff.mpr htop]
  exact hpositive.ne'

def evidence : Registration arena.{u} (type_of% (@uniform_undirected_completion.{u})) where
  actual := actual
  bridge := by rfl
  variation := ⟨@uniform_undirected_completion.{u}, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨ULift.{u} (Fin 4), ⊥, ⊤, ?_⟩
    exact variation_at_four

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@uniform_undirected_completion.{u}) (Realization signature.{u}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw.uniform_undirected_completion
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => Nat.card (CompletedGraph F)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "fn", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
