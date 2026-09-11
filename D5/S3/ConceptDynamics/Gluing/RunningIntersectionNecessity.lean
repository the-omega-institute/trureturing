/- GID: D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hasse]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity.EdgeMatchingSufficesWithoutRI; result=D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity.edge_matching_without_ri_is_false; claim=D5/S3/ConceptDynamics/Gluing/RunningIntersectionNecessity.EdgeMatchingSufficesWithoutRI
   digest: The literal three-node path has matching empty edge projections but contradictory values of one shared variable. -/

import D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.RunningIntersectionNecessity

open SimpleGraph
open D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords

/-- The finite restriction of the assertion that edge matching suffices without RI. -/
def EdgeMatchingSufficesWithoutRI : Prop :=
  ∀ (T : SimpleGraph (Fin 3)) (S : Fin 3 → Set (Fin 2))
    (Γ : (n : Fin 3) → Set (Assignment (fun _ : Fin 2 => Fin 2) (S n))),
    T.IsTree → (∀ n, (Γ n).Nonempty) →
    EdgeProjectionConsistency T (fun _ : Fin 2 => Fin 2) S Γ →
    (rawJoin (fun _ : Fin 2 => Fin 2) S Γ Set.univ).Nonempty

private def scopes (n : Fin 3) : Set (Fin 2) := {if n = 1 then 1 else 0}

private def row (n : Fin 3) : Assignment (fun _ : Fin 2 => Fin 2) (scopes n) :=
  fun _ => if n = 2 then 1 else 0

private def rows (n : Fin 3) : Set (Assignment (fun _ : Fin 2 => Fin 2) (scopes n)) :=
  {row n}

private theorem literal_tree : (pathGraph 3).IsTree := by
  let : DecidableRel (pathGraph 3).Adj := fun p q =>
    decidable_of_iff (p.val + 1 = q.val ∨ q.val + 1 = p.val) pathGraph_adj.symm
  apply isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 2, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

private theorem empty_separators (p q : Fin 3) (h : (pathGraph 3).Adj p q) :
    scopes p ∩ scopes q = ∅ := by
  fin_cases p <;> fin_cases q <;> simp [pathGraph_adj, scopes] at *

private theorem literal_matching :
    EdgeProjectionConsistency (pathGraph 3) (fun _ : Fin 2 => Fin 2) scopes rows := by
  intro p q hpq
  have hs := empty_separators p q hpq
  let empty : Assignment (fun _ : Fin 2 => Fin 2) (scopes p ∩ scopes q) :=
    restrictAssignment (fun _ : Fin 2 => Fin 2) hs.subset
      (emptyAssignment (fun _ : Fin 2 => Fin 2))
  have left : restrictAssignment (fun _ : Fin 2 => Fin 2)
      (D := scopes p ∩ scopes q) Set.inter_subset_left (row p) = empty := by
    funext x
    exact (show x.val ∈ (∅ : Set (Fin 2)) from hs ▸ x.property).elim
  have right : restrictAssignment (fun _ : Fin 2 => Fin 2)
      (D := scopes p ∩ scopes q) Set.inter_subset_right (row q) = empty := by
    funext x
    exact (show x.val ∈ (∅ : Set (Fin 2)) from hs ▸ x.property).elim
  simp only [rows, Set.image_singleton, left, right]

private theorem no_global_row :
    ¬ (rawJoin (fun _ : Fin 2 => Fin 2) scopes rows Set.univ).Nonempty := by
  rintro ⟨j, hj⟩
  have hzero := hj 0 (Set.mem_univ _)
  have hone := hj 2 (Set.mem_univ _)
  change restrictAssignment _ _ j = row 0 at hzero
  change restrictAssignment _ _ j = row 2 at hone
  have h0 := congrFun hzero ⟨0, by simp [scopes]⟩
  have h1 := congrFun hone ⟨0, by simp [scopes]⟩
  have heq : (0 : Fin 2) = 1 := h0.symm.trans h1
  exact (by decide : (0 : Fin 2) ≠ 1) heq

/-- Complete edge checks accept these three singleton rows, but their shared x is inconsistent. -/
theorem edge_matching_without_ri_is_false : Not EdgeMatchingSufficesWithoutRI := by
  intro h
  exact no_global_row (h (pathGraph 3) scopes rows literal_tree
    (fun n => ⟨row n, rfl⟩) literal_matching)

private theorem literal_not_running_intersection : ¬ RunningIntersection (pathGraph 3) scopes := by
  intro hRI
  obtain ⟨j, _⟩ := local_row_extends_raw_join (pathGraph 3) (fun _ : Fin 2 => Fin 2)
    scopes rows literal_tree hRI (fun n => ⟨row n, rfl⟩) literal_matching 0 (row 0) rfl
  exact no_global_row ⟨j.val, j.property⟩

end D5.S3.ConceptDynamics.Gluing.RunningIntersectionNecessity
