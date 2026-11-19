import D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Counting the undirected prescribed edges records exactly the size of their orientation. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw
noncomputable section
universe u

private abbrev signature : Signature where
  Params := Type u
  State V := SimpleGraph V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ G => Nat.card G.edgeSet) (fun e => nomatch e)

private def zero : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] {F : SimpleGraph V} (_hn : 3 ≤ Fintype.card V)
    (k : V → Bool) (_reference : AlternatingCompletedGraph k F),
    ∃ (μ : PMF (OrientedCompletion (F := F) k)) (ν : PMF (AlternatingCompletedGraph k F)),
      (∀ l, μ l = (Nat.card (OrientedCompletion (F := F) k) : ℝ≥0∞)⁻¹) ∧
      (∀ C, ν C = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
      μ.map (forgetOrientation _hn k) = ν ∧
      ∀ ref : OrientedCompletion (F := F) k,
        Nat.card {edge : V × V // ref.1.E edge.1 edge.2} = R.readout () V F ∧
        let event : Set (OrientedCompletion (F := F) k) := {l | l.1.E = ref.1.E}
        ∀ h : ∃ l ∈ event, l ∈ μ.support,
          ∃ (ρ : PMF (AlternatingCompletion ref.1.E k))
            (toLift : AlternatingCompletion ref.1.E k → OrientedCompletion (F := F) k),
            (∀ c, ρ c = (Nat.card (AlternatingCompletion ref.1.E k) : ℝ≥0∞)⁻¹) ∧
            (∀ c, (toLift c).1.E = ref.1.E ∧ (toLift c).1.σ = c.1) ∧
            μ.filter event h = ρ.map toLift

private abbrev Four := ULift.{u} (Fin 4)

private def color (x : Four.{u}) : Bool := decide (x.down.val % 2 = 1)

private theorem color_count (b : Bool) : Nat.card (Side color.{u} b) = 2 := by
  let e : Side color.{u} b ≃ {v : Fin 4 // decide (v.val % 2 = 1) = b} :=
    Equiv.subtypeEquiv Equiv.ulift (fun _ => Iff.rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  cases b <;> decide

private theorem cycleExists : Nonempty (AlternatingCompletedGraph color.{u} (⊥ : SimpleGraph Four.{u})) := by
  obtain ⟨_, μ, _, _, _, _⟩ :=
    alternating_undirected_completion_law color.{u} (⊥ : SimpleGraph Four.{u})
      2 (by decide) (color_count false) (color_count true)
  obtain ⟨C, _⟩ := μ.support_nonempty
  exact ⟨C⟩

private theorem edge_count_pos (C : AlternatingCompletedGraph color.{u} (⊥ : SimpleGraph Four.{u})) :
    0 < Nat.card C.1.1.edgeSet := by
  let x : Four.{u} := ULift.up 0
  have hd : 0 < (C.1.1.neighborSet x).ncard := by rw [C.1.2.2.1]; decide
  obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hd.ne'
  exact Finite.card_pos_iff.mpr ⟨⟨s(x, y), hy⟩⟩

private theorem rejectsZero : ¬ arena.{u}.Law zero := by
  intro hZero
  obtain ⟨C⟩ := cycleExists.{u}
  let F := C.1.1
  let ref : AlternatingCompletedGraph color.{u} F :=
    ⟨⟨F, C.1.2.1, C.1.2.2.1, le_rfl⟩, C.2⟩
  have hn : 3 ≤ Fintype.card Four.{u} := by simp [Four]
  obtain ⟨μ, _, _, _, _, hAlwaysZero⟩ := hZero hn color ref
  obtain ⟨l, _⟩ := μ.support_nonempty
  obtain ⟨_, _, _, _, _, hCount⟩ := alternating_weld_orientation_law hn color ref
  have hm := (hCount l).1
  have hz : Nat.card {edge : Four.{u} × Four.{u} // l.1.E edge.1 edge.2} = 0 :=
    (hAlwaysZero l).1
  exact (edge_count_pos C).ne' (hm.symm.trans hz)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  obtain ⟨C⟩ := cycleExists.{u}
  refine ⟨Four.{u}, ⊥, C.1.1, ?_⟩
  change Nat.card (⊥ : SimpleGraph Four.{u}).edgeSet ≠ Nat.card C.1.1.edgeSet
  have hbot : Nat.card (⊥ : SimpleGraph Four.{u}).edgeSet = 0 := by simp
  rw [hbot]
  exact (edge_count_pos C).ne

def evidence : Registration arena.{u} (type_of% (@alternating_weld_orientation_law.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@alternating_weld_orientation_law.{u}, zero, rejectsZero⟩
  sensitivity := ⟨fun i => ⟨zero,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsZero⟩, fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@alternating_weld_orientation_law.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw.alternating_weld_orientation_law
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ G => Nat.card G.edgeSet) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw
