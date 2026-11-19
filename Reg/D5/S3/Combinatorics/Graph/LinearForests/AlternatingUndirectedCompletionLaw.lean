import D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! # Completion counts in the alternating undirected law -/

open LeanInformationAudit
open SimpleGraph Equiv
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory (Side)
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw

noncomputable section
universe u

private def parityFour (x : Fin 4) : Bool := decide (x.val % 2 = 1)

private theorem parityFour_counts :
    Nat.card (Side parityFour false) = 2 ∧ Nat.card (Side parityFour true) = 2 := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

private theorem parityFour_cross :
    ∀ u v : Fin 4, (SimpleGraph.cycleGraph 4).Adj u v → parityFour u ≠ parityFour v := by
  decide

private abbrev auditSignature : Signature where
  Params := Σ V : Type u, V → Bool
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualCompletionCount : Realization auditSignature.{u} :=
  realize auditSignature
    (fun _ p F => Nat.card (AlternatingCompletedGraph p.2 F)) (fun e => nomatch e)

private def constantZeroCompletionCount : Realization auditSignature.{u} :=
  realize auditSignature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev auditArena : Arena where
  signature := auditSignature.{u}
  Law R := ∀ {V : Type u} [Fintype V] (k : V → Bool) (F : SimpleGraph V)
      (n : ℕ) (_hnColors : 2 ≤ n)
      (_hr : Nat.card (Side k false) = n) (_hb : Nat.card (Side k true) = n),
      let A := AlternatingCompletedGraph k (⊥ : SimpleGraph V)
      let S : Set A := {C | F ≤ C.1.1}
      let D := n.factorial * (n - 1).factorial / 2
      Nat.card A = D ∧ ∃ μ : PMF A,
        (∀ C, μ C = (D : ℝ≥0∞)⁻¹) ∧
        μ.toOuterMeasure S = (R.readout () ⟨V, k⟩ F : ℝ≥0∞) / D ∧
        (0 < μ.toOuterMeasure S ↔ Nonempty (AlternatingCompletedGraph k F)) ∧
        ∀ hs : ∃ C ∈ S, C ∈ μ.support,
          ∃ ν : PMF (AlternatingCompletedGraph k F),
            (∀ C, ν C = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
            μ.filter S hs = ν.map (forgetPrescribedEdges k)

private def liftedParityFour (x : ULift.{u} (Fin 4)) : Bool := parityFour x.down

private theorem liftedParityFour_count (b : Bool) :
    Nat.card (Side liftedParityFour.{u} b) = 2 := by
  let e : Side liftedParityFour.{u} b ≃ Side parityFour b :=
    Equiv.subtypeEquiv Equiv.ulift (fun _ => Iff.rfl)
  rw [Nat.card_congr e]
  cases b
  · exact parityFour_counts.1
  · exact parityFour_counts.2

private theorem rejectedLaw : ¬ auditArena.{u}.Law constantZeroCompletionCount := by
  intro h
  obtain ⟨_, μ, _, hm, _, _⟩ := h (V := ULift.{u} (Fin 4)) liftedParityFour
    (⊥ : SimpleGraph (ULift.{u} (Fin 4))) 2 (by decide) (liftedParityFour_count false)
    (liftedParityFour_count true)
  let V4 := ULift.{u} (Fin 4)
  have hAll : {C : AlternatingCompletedGraph liftedParityFour (⊥ : SimpleGraph V4) |
      (⊥ : SimpleGraph V4) ≤ C.1.1} = Set.univ :=
    Set.eq_univ_of_forall (fun C => show (⊥ : SimpleGraph V4) ≤ C.1.1 from bot_le)
  rw [hAll, PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe] at hm
  simp [constantZeroCompletionCount, realize] at hm

private theorem liftedVariation :
    let V4 := ULift.{u} (Fin 4)
    Nat.card (AlternatingCompletedGraph liftedParityFour.{u} (⊥ : SimpleGraph V4)) ≠
      Nat.card (AlternatingCompletedGraph liftedParityFour.{u} (⊤ : SimpleGraph V4)) := by
  classical
  let V4 := ULift.{u} (Fin 4)
  let e : Fin 4 ≃ V4 := Equiv.ulift.symm
  let G := (SimpleGraph.cycleGraph 4).map e
  let i : SimpleGraph.cycleGraph 4 ≃g G := SimpleGraph.Iso.map e _
  have hbot : Nonempty (AlternatingCompletedGraph liftedParityFour.{u} (⊥ : SimpleGraph V4)) := by
    have connected := (SimpleGraph.connected_cycleGraph_add_one (n := 3)).map i.toHom i.surjective
    refine ⟨⟨⟨G, connected, ?_, bot_le⟩, ?_⟩⟩
    · intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [SimpleGraph.ncard_neighborSet]
      change G.degree (i y) = 2
      rw [i.degree_eq]
      exact SimpleGraph.cycleGraph_degree_three_le
    · intro x y h
      obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      have hxy : (SimpleGraph.cycleGraph 4).Adj x y := i.map_rel_iff.mp h
      exact parityFour_cross x y hxy
  have htop : IsEmpty (AlternatingCompletedGraph liftedParityFour.{u} (⊤ : SimpleGraph V4)) := by
    refine ⟨fun C => ?_⟩
    have hC : C.1.1 = ⊤ := le_antisymm le_top C.1.2.2.2
    have hd := C.1.2.2.1 (ULift.up (0 : Fin 4))
    rw [hC, SimpleGraph.ncard_neighborSet, SimpleGraph.complete_graph_degree] at hd
    simp at hd
  let : Finite (AlternatingCompletedGraph liftedParityFour.{u} (⊥ : SimpleGraph V4)) :=
    Finite.of_injective (fun C => C.1.1) (fun _ _ h => Subtype.ext (Subtype.ext h))
  dsimp only
  rw [Finite.card_eq_zero_iff.mpr htop]
  exact (Finite.card_pos_iff.mpr hbot).ne'

def auditEvidence :
    Registration auditArena.{u} (type_of% (@alternating_undirected_completion_law.{u})) where
  actual := actualCompletionCount
  bridge := Iff.rfl
  variation :=
    ⟨@alternating_undirected_completion_law.{u}, constantZeroCompletionCount, rejectedLaw⟩
  sensitivity := ⟨fun i => ⟨constantZeroCompletionCount,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectedLaw⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 4), liftedParityFour⟩, ⊥, ⊤, ?_⟩
    exact liftedVariation

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@alternating_undirected_completion_law.{u}) (Realization auditSignature.{u}) Unit Unit := {
  unitName :=
    Lean.Name.str `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
      "alternating_undirected_completion_law"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw.auditEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨auditArena.{u}⟩
  objectArena := .source ⟨auditArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source auditArena.{u} ⟨auditEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize auditSignature
    (fun _ p F => Nat.card (AlternatingCompletedGraph p.2 F)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "body", "arg", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
