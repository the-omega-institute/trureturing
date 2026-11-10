import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiveAnchorFaithfulPlacement

/-! The full graph telescope is reconstructed with its actual distance
readout varied on Euclidean points. Parameters retain the arbitrary vertex
type, its finite enumeration and the graph. -/

noncomputable section
set_option maxHeartbeats 1000000

open _root_.D5.S3.Geometry.FiveAnchorFaithfulPlacement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.FiveAnchorFaithfulPlacement

universe u
local notation "E₅" => EuclideanSpace ℝ (Fin 5)

abbrev signature : Signature where
  Params := Σ V : Type u, Fintype V × SimpleGraph V
  State _ := E₅
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := E₅ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => dist x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V),
    G.IsBipartiteWith (A : Set V) (B : Set V) →
    (∀ v, v ∈ A ∨ v ∈ B) → A.card ≤ 5 → G.edgeFinset.card ≤ 21 →
    ∃ P : V → E₅, Function.Injective P ∧
      (∀ u v, G.Adj u v ↔ R.readout 0 ⟨V, inferInstance, G⟩ (P u) (P v) = 1) ∧
      (∀ a ∈ A, ‖P a‖ = 1 / 4) ∧
      (∀ a ∈ A, ∀ a' ∈ A, dist (P a) (P a') < 1) ∧
      (∀ b ∈ B, (1 / 4 : ℝ) < ‖P b‖ ∧ ‖P b‖ < 1) ∧
      ∀ b ∈ B, ∀ b' ∈ B, dist (P b) (P b') < 2

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let v₀ : ULift.{u} (Fin 2) := ⟨0⟩
  let v₁ : ULift.{u} (Fin 2) := ⟨1⟩
  have hG : (⊤ : SimpleGraph (ULift.{u} (Fin 2))).IsBipartiteWith
      (↑({v₀} : Finset _) : Set _) (↑({v₁} : Finset _) : Set _) := by
    constructor
    · simp [v₀, v₁]
    · intro a b hab
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      fin_cases a <;> fin_cases b <;> simp_all [v₀, v₁]
  have hcover : ∀ v : ULift.{u} (Fin 2), v ∈ ({v₀} : Finset _) ∨ v ∈ ({v₁} : Finset _) := by
    rintro ⟨v⟩
    fin_cases v <;> simp [v₀, v₁]
  have hE : (⊤ : SimpleGraph (ULift.{u} (Fin 2))).edgeFinset.card ≤ 21 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    norm_num
  obtain ⟨P, _, hP, _⟩ := h (V := ULift.{u} (Fin 2)) ⊤ {v₀} {v₁} hG hcover
    (by simp) hE
  have hh := (hP v₀ v₁).mp (by simp [v₀, v₁])
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  obtain ⟨e, he⟩ := exists_norm_eq E₅ (by norm_num : (0 : ℝ) ≤ 1)
  let p : signature.{u}.Params := ⟨ULift.{u} (Fin 2), inferInstance, ⊤⟩
  refine ⟨p, 0, e, ?_⟩
  intro hh
  have h := congrFun hh 0
  change dist (0 : E₅) 0 = dist e 0 at h
  rw [dist_self, dist_zero_right, he] at h
  norm_num at h

def family : Registration arena.{u}
    (type_of% (@exists_faithful_five_anchor_placement.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_faithful_five_anchor_placement.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

end Reg.D5.S3.Geometry.FiveAnchorFaithfulPlacement
