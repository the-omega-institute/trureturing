/- GID: D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/SolidResolvingTournament
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All six tournament lower bounds of Hakanen and Pavan Conjecture 3.4. -/

/-
admission_basis: open-problem-resolution (#22881; Proved)
escape_witness: none
The admission basis uses no escape witness. The per-declaration witness below records
the same-delivery content on the result's proof path.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23622
result — proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentTerminal.card_bound_of_profile_model; consumers: settling conclusion.
  Direct frozen dependencies: D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence.IsTournament (sha256:002ac9d0879eb1d754282d3b0d7d70c92dd1967882eaf005f362f42c22a17db0); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
-/

import D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentBase
import D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentProfiles
import D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentTerminal
import D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence

namespace D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournament

open D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence (IsTournament)
open D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentBase
open D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentProfiles
open D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentTerminal
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
universe uSolid

def claim : Prop :=
  (∀ R : Fin 6 → Fin 6 → Prop, IsTournament R → 4 ≤ solidMetricDimension R) ∧
  (∀ R : Fin 7 → Fin 7 → Prop, IsTournament R → 5 ≤ solidMetricDimension R) ∧
  (∀ R : Fin 8 → Fin 8 → Prop, IsTournament R → 5 ≤ solidMetricDimension R) ∧
  (∀ R : Fin 9 → Fin 9 → Prop, IsTournament R → 5 ≤ solidMetricDimension R) ∧
  (∀ R : Fin 10 → Fin 10 → Prop, IsTournament R → 5 ≤ solidMetricDimension R) ∧
  (∀ R : Fin 11 → Fin 11 → Prop, IsTournament R → 6 ≤ solidMetricDimension R)
private theorem path_upper_certificate_3_2 :
    (List.finRange 3).all (fun i => (List.finRange 3).all
      (fun j => walkBound 2 (D32 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem representative_path_upper_3_2 {V : Type*}
    (R : V → V → Prop) (L : Fin 3 → V)
    (hE : ∀ i j, maskArc 2 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ (D32 i j : ℕ∞) := by
  intro i j
  apply directedDistance_le_walkBound R L 2 hE
  exact (List.all_eq_true.mp ((List.all_eq_true.mp path_upper_certificate_3_2)
    i (by simp))) j (by simp)
private theorem path_upper_certificate_4_4 :
    (List.finRange 4).all (fun i => (List.finRange 4).all
      (fun j => walkBound 4 (D44 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem representative_path_upper_4_4 {V : Type*}
    (R : V → V → Prop) (L : Fin 4 → V)
    (hE : ∀ i j, maskArc 4 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ (D44 i j : ℕ∞) := by
  intro i j
  apply directedDistance_le_walkBound R L 4 hE
  exact (List.all_eq_true.mp ((List.all_eq_true.mp path_upper_certificate_4_4)
    i (by simp))) j (by simp)
private theorem path_upper_certificate_5_8 :
    (List.finRange 5).all (fun i => (List.finRange 5).all
      (fun j => walkBound 8 (D58 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem representative_path_upper_5_8 {V : Type*}
    (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 8 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ (D58 i j : ℕ∞) := by
  intro i j
  apply directedDistance_le_walkBound R L 8 hE
  exact (List.all_eq_true.mp ((List.all_eq_true.mp path_upper_certificate_5_8)
    i (by simp))) j (by simp)
private theorem path_upper_certificate_5_10 :
    (List.finRange 5).all (fun i => (List.finRange 5).all
      (fun j => walkBound 10 (D510 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem representative_path_upper_5_10 {V : Type*}
    (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 10 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ (D510 i j : ℕ∞) := by
  intro i j
  apply directedDistance_le_walkBound R L 10 hE
  exact (List.all_eq_true.mp ((List.all_eq_true.mp path_upper_certificate_5_10)
    i (by simp))) j (by simp)
private theorem path_upper_certificate_5_12 :
    (List.finRange 5).all (fun i => (List.finRange 5).all
      (fun j => walkBound 12 (D512 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem representative_path_upper_5_12 {V : Type*}
    (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 12 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ (D512 i j : ℕ∞) := by
  intro i j
  apply directedDistance_le_walkBound R L 12 hE
  exact (List.all_eq_true.mp ((List.all_eq_true.mp path_upper_certificate_5_12)
    i (by simp))) j (by simp)
private theorem path_upper_certificate_5_40 :
    (List.finRange 5).all (fun i => (List.finRange 5).all
      (fun j => walkBound 40 (D540 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem representative_path_upper_5_40 {V : Type*}
    (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 40 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ (D540 i j : ℕ∞) := by
  intro i j
  apply directedDistance_le_walkBound R L 40 hE
  exact (List.all_eq_true.mp ((List.all_eq_true.mp path_upper_certificate_5_40)
    i (by simp))) j (by simp)
private theorem path_upper_certificate_5_41 :
    (List.finRange 5).all (fun i => (List.finRange 5).all
      (fun j => walkBound 41 (D541 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem representative_path_upper_5_41 {V : Type*}
    (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 41 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ (D541 i j : ℕ∞) := by
  intro i j
  apply directedDistance_le_walkBound R L 41 hE
  exact (List.all_eq_true.mp ((List.all_eq_true.mp path_upper_certificate_5_41)
    i (by simp))) j (by simp)
private theorem path_upper_certificate_5_76 :
    (List.finRange 5).all (fun i => (List.finRange 5).all
      (fun j => walkBound 76 (D576 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem representative_path_upper_5_76 {V : Type*}
    (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 76 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ (D576 i j : ℕ∞) := by
  intro i j
  apply directedDistance_le_walkBound R L 76 hE
  exact (List.all_eq_true.mp ((List.all_eq_true.mp path_upper_certificate_5_76)
    i (by simp))) j (by simp)
private lemma claim_of_card_bounds
    (h3 : ∀ n (R : Fin n → Fin n → Prop), IsTournament R →
      ∀ S : Finset (Fin n), S.card = 3 → IsSolidResolving R (S : Set (Fin n)) → n ≤ 4)
    (h4 : ∀ n (R : Fin n → Fin n → Prop), IsTournament R →
      ∀ S : Finset (Fin n), S.card = 4 → IsSolidResolving R (S : Set (Fin n)) → n ≤ 6)
    (h5 : ∀ n (R : Fin n → Fin n → Prop), IsTournament R →
      ∀ S : Finset (Fin n), S.card = 5 → IsSolidResolving R (S : Set (Fin n)) → n ≤ 10) :
    claim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R hR
    exact dimension_lower_of_fixed_card_bound R 3 4 (by simp) (by simp)
      (by simpa using h3 6 R hR)
  · intro R hR
    exact dimension_lower_of_fixed_card_bound R 4 6 (by simp) (by simp)
      (by simpa using h4 7 R hR)
  · intro R hR
    exact dimension_lower_of_fixed_card_bound R 4 6 (by simp) (by simp)
      (by simpa using h4 8 R hR)
  · intro R hR
    exact dimension_lower_of_fixed_card_bound R 4 6 (by simp) (by simp)
      (by simpa using h4 9 R hR)
  · intro R hR
    exact dimension_lower_of_fixed_card_bound R 4 6 (by simp) (by simp)
      (by simpa using h4 10 R hR)
  · intro R hR
    exact dimension_lower_of_fixed_card_bound R 5 10 (by simp) (by simp)
      (by simpa using h5 11 R hR)
private def relabelCheck {k : Nat} (m r : Nat) (p : Fin k → Fin k) : Bool :=
  (List.finRange k).all (fun i => (List.finRange k).all (fun j =>
    decide (p i = p j → i = j) && (maskArc m i j == maskArc r (p i) (p j))))
private def shapeData3 : Array (Nat × (Fin 3 → Fin 3)) := #[
(0, ![0,1,2]),(0, ![1,0,2]),(2, ![0,1,2]),(0, ![2,0,1]),(0, ![0,2,1]),(2, ![0,2,1]),(0, ![1,2,0]),(0, ![2,1,0])]
private theorem classification3_certificate :
    (List.range 8).all (fun m =>
      decide (((shapeData3.getD m (0, fun _ => 0))).1 ∈ ([0, 2] : List Nat)) &&
      relabelCheck m ((shapeData3.getD m (0, fun _ => 0))).1 ((shapeData3.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private def shapeData4 : Array (Nat × (Fin 4 → Fin 4)) := #[
(0, ![0,1,2,3]),(0, ![1,0,2,3]),(2, ![0,1,2,3]),(0, ![2,0,1,3]),(4, ![0,1,2,3]),(5, ![0,1,2,3]),(4, ![3,0,1,2]),(0, ![3,0,1,2]),
(0, ![0,2,1,3]),(2, ![0,2,1,3]),(0, ![1,2,0,3]),(0, ![2,1,0,3]),(4, ![0,2,1,3]),(4, ![3,1,0,2]),(5, ![0,2,1,3]),(0, ![3,1,0,2]),
(5, ![1,0,2,3]),(4, ![1,0,2,3]),(4, ![1,3,0,2]),(4, ![2,0,1,3]),(4, ![1,2,3,0]),(4, ![2,1,3,0]),(4, ![2,3,0,1]),(2, ![3,0,1,2]),
(0, ![0,3,1,2]),(4, ![0,3,1,2]),(0, ![1,3,0,2]),(5, ![0,3,1,2]),(2, ![0,3,1,2]),(4, ![3,2,0,1]),(0, ![2,3,0,1]),(0, ![3,2,0,1]),
(0, ![0,1,3,2]),(0, ![1,0,3,2]),(4, ![0,1,3,2]),(5, ![0,1,3,2]),(2, ![0,1,3,2]),(0, ![2,0,3,1]),(4, ![3,0,2,1]),(0, ![3,0,2,1]),
(5, ![1,0,3,2]),(4, ![1,0,3,2]),(4, ![1,2,0,3]),(4, ![2,1,0,3]),(4, ![1,3,2,0]),(4, ![2,0,3,1]),(4, ![2,3,1,0]),(2, ![3,0,2,1]),
(0, ![0,2,3,1]),(2, ![0,2,3,1]),(4, ![0,2,3,1]),(4, ![3,1,2,0]),(0, ![1,2,3,0]),(0, ![2,1,3,0]),(5, ![0,2,3,1]),(0, ![3,1,2,0]),
(0, ![0,3,2,1]),(4, ![0,3,2,1]),(2, ![0,3,2,1]),(4, ![3,2,1,0]),(0, ![1,3,2,0]),(5, ![0,3,2,1]),(0, ![2,3,1,0]),(0, ![3,2,1,0])]
private theorem classification4_certificate :
    (List.range 64).all (fun m =>
      decide (((shapeData4.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5] : List Nat)) &&
      relabelCheck m ((shapeData4.getD m (0, fun _ => 0))).1 ((shapeData4.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private def shapeData5 : Array (Nat × (Fin 5 → Fin 5)) := #[
(0, ![0,1,2,3,4]),(0, ![1,0,2,3,4]),(2, ![0,1,2,3,4]),(0, ![2,0,1,3,4]),(4, ![0,1,2,3,4]),(5, ![0,1,2,3,4]),(4, ![3,0,1,2,4]),(0, ![3,0,1,2,4]), (8, ![0,1,2,3,4]),(9, ![0,1,2,3,4]),(10, ![0,1,2,3,4]),(11, ![0,1,2,3,4]),(12, ![0,1,2,3,4]),(9, ![4,1,0,2,3]),(8, ![4,0,1,2,3]),(0, ![4,0,1,2,3]), (0, ![0,2,1,3,4]),(2, ![0,2,1,3,4]),(0, ![1,2,0,3,4]),(0, ![2,1,0,3,4]),(4, ![0,2,1,3,4]),(4, ![3,1,0,2,4]),(5, ![0,2,1,3,4]),(0, ![3,1,0,2,4]), (8, ![0,2,1,3,4]),(10, ![0,2,1,3,4]),(9, ![0,2,1,3,4]),(11, ![0,2,1,3,4]),(12, ![0,2,1,3,4]),(8, ![4,1,0,2,3]),(9, ![4,0,1,2,3]),(0, ![4,1,0,2,3]),
(5, ![1,0,2,3,4]),(4, ![1,0,2,3,4]),(4, ![1,3,0,2,4]),(4, ![2,0,1,3,4]),(4, ![1,2,3,0,4]),(4, ![2,1,3,0,4]),(4, ![2,3,0,1,4]),(2, ![3,0,1,2,4]), (40, ![0,1,2,3,4]),(41, ![0,1,2,3,4]),(41, ![0,3,1,2,4]),(10, ![4,1,2,0,3]),(41, ![0,2,3,1,4]),(10, ![4,2,0,1,3]),(10, ![4,0,1,2,3]),(2, ![4,0,1,2,3]), (0, ![0,3,1,2,4]),(4, ![0,3,1,2,4]),(0, ![1,3,0,2,4]),(5, ![0,3,1,2,4]),(2, ![0,3,1,2,4]),(4, ![3,2,0,1,4]),(0, ![2,3,0,1,4]),(0, ![3,2,0,1,4]), (8, ![0,3,1,2,4]),(12, ![0,3,1,2,4]),(9, ![0,3,1,2,4]),(9, ![4,2,1,0,3]),(10, ![0,3,1,2,4]),(8, ![4,2,0,1,3]),(11, ![0,3,1,2,4]),(0, ![4,2,0,1,3]),
(9, ![1,0,2,3,4]),(8, ![1,0,2,3,4]),(10, ![2,0,1,3,4]),(8, ![2,0,1,3,4]),(41, ![1,0,2,3,4]),(40, ![1,0,2,3,4]),(12, ![3,0,1,2,4]),(8, ![3,0,1,2,4]), (12, ![1,2,3,4,0]),(12, ![2,1,3,4,0]),(41, ![2,3,1,4,0]),(10, ![3,1,2,4,0]),(76, ![0,1,2,3,4]),(41, ![4,1,0,2,3]),(12, ![4,0,1,2,3]),(4, ![4,0,1,2,3]), (11, ![1,0,2,3,4]),(10, ![1,0,2,3,4]),(11, ![2,0,1,3,4]),(9, ![2,0,1,3,4]),(10, ![1,4,2,0,3]),(41, ![3,0,1,2,4]),(9, ![2,4,1,0,3]),(9, ![3,0,1,2,4]), (10, ![1,3,2,4,0]),(41, ![3,2,1,4,0]),(9, ![2,3,1,4,0]),(9, ![3,2,1,4,0]),(41, ![3,4,1,0,2]),(40, ![4,1,0,2,3]),(9, ![3,4,1,0,2]),(5, ![4,0,1,2,3]),
(9, ![1,4,0,2,3]),(12, ![1,0,2,3,4]),(8, ![1,4,0,2,3]),(12, ![2,0,1,3,4]),(10, ![2,4,0,1,3]),(41, ![2,0,3,1,4]),(8, ![2,4,0,1,3]),(10, ![3,0,1,2,4]), (41, ![1,4,0,2,3]),(76, ![0,4,1,2,3]),(40, ![1,4,0,2,3]),(41, ![4,3,1,0,2]),(12, ![3,4,0,1,2]),(12, ![4,3,0,1,2]),(8, ![3,4,0,1,2]),(4, ![4,3,0,1,2]), (0, ![0,4,1,2,3]),(8, ![0,4,1,2,3]),(0, ![1,4,0,2,3]),(9, ![0,4,1,2,3]),(2, ![0,4,1,2,3]),(10, ![0,4,1,2,3]),(0, ![2,4,0,1,3]),(11, ![0,4,1,2,3]), (4, ![0,4,1,2,3]),(12, ![0,4,1,2,3]),(5, ![0,4,1,2,3]),(9, ![4,3,1,0,2]),(4, ![3,4,0,1,2]),(8, ![4,3,0,1,2]),(0, ![3,4,0,1,2]),(0, ![4,3,0,1,2]),
(0, ![0,1,3,2,4]),(0, ![1,0,3,2,4]),(4, ![0,1,3,2,4]),(5, ![0,1,3,2,4]),(2, ![0,1,3,2,4]),(0, ![2,0,3,1,4]),(4, ![3,0,2,1,4]),(0, ![3,0,2,1,4]), (8, ![0,1,3,2,4]),(9, ![0,1,3,2,4]),(12, ![0,1,3,2,4]),(9, ![4,1,2,0,3]),(10, ![0,1,3,2,4]),(11, ![0,1,3,2,4]),(8, ![4,0,2,1,3]),(0, ![4,0,2,1,3]), (5, ![1,0,3,2,4]),(4, ![1,0,3,2,4]),(4, ![1,2,0,3,4]),(4, ![2,1,0,3,4]),(4, ![1,3,2,0,4]),(4, ![2,0,3,1,4]),(4, ![2,3,1,0,4]),(2, ![3,0,2,1,4]), (40, ![0,1,3,2,4]),(41, ![0,1,3,2,4]),(41, ![0,2,1,3,4]),(10, ![4,2,1,0,3]),(41, ![0,3,2,1,4]),(10, ![4,1,0,2,3]),(10, ![4,0,2,1,3]),(2, ![4,0,2,1,3]),
(0, ![0,2,3,1,4]),(2, ![0,2,3,1,4]),(4, ![0,2,3,1,4]),(4, ![3,1,2,0,4]),(0, ![1,2,3,0,4]),(0, ![2,1,3,0,4]),(5, ![0,2,3,1,4]),(0, ![3,1,2,0,4]), (8, ![0,2,3,1,4]),(10, ![0,2,3,1,4]),(12, ![0,2,3,1,4]),(8, ![4,1,2,0,3]),(9, ![0,2,3,1,4]),(11, ![0,2,3,1,4]),(9, ![4,0,2,1,3]),(0, ![4,1,2,0,3]), (0, ![0,3,2,1,4]),(4, ![0,3,2,1,4]),(2, ![0,3,2,1,4]),(4, ![3,2,1,0,4]),(0, ![1,3,2,0,4]),(5, ![0,3,2,1,4]),(0, ![2,3,1,0,4]),(0, ![3,2,1,0,4]), (8, ![0,3,2,1,4]),(12, ![0,3,2,1,4]),(10, ![0,3,2,1,4]),(8, ![4,2,1,0,3]),(9, ![0,3,2,1,4]),(9, ![4,2,0,1,3]),(11, ![0,3,2,1,4]),(0, ![4,2,1,0,3]),
(9, ![1,0,3,2,4]),(8, ![1,0,3,2,4]),(41, ![1,0,3,2,4]),(40, ![1,0,3,2,4]),(10, ![2,0,3,1,4]),(8, ![2,0,3,1,4]),(12, ![3,0,2,1,4]),(8, ![3,0,2,1,4]), (12, ![1,2,4,3,0]),(12, ![2,1,4,3,0]),(76, ![0,1,3,2,4]),(41, ![4,1,2,0,3]),(41, ![2,3,4,1,0]),(10, ![3,1,4,2,0]),(12, ![4,0,2,1,3]),(4, ![4,0,2,1,3]), (9, ![1,4,2,0,3]),(12, ![1,0,3,2,4]),(10, ![2,4,1,0,3]),(41, ![2,0,1,3,4]),(8, ![1,4,2,0,3]),(12, ![2,0,3,1,4]),(8, ![2,4,1,0,3]),(10, ![3,0,2,1,4]), (41, ![1,4,2,0,3]),(76, ![0,4,2,1,3]),(12, ![3,4,1,0,2]),(12, ![4,3,1,0,2]),(40, ![1,4,2,0,3]),(41, ![4,3,0,1,2]),(8, ![3,4,1,0,2]),(4, ![4,3,1,0,2]),
(11, ![1,0,3,2,4]),(10, ![1,0,3,2,4]),(10, ![1,4,0,2,3]),(41, ![3,0,2,1,4]),(11, ![2,0,3,1,4]),(9, ![2,0,3,1,4]),(9, ![2,4,0,1,3]),(9, ![3,0,2,1,4]), (10, ![1,3,4,2,0]),(41, ![3,2,4,1,0]),(41, ![3,4,0,1,2]),(40, ![4,1,2,0,3]),(9, ![2,3,4,1,0]),(9, ![3,2,4,1,0]),(9, ![3,4,0,1,2]),(5, ![4,0,2,1,3]), (0, ![0,4,2,1,3]),(8, ![0,4,2,1,3]),(2, ![0,4,2,1,3]),(10, ![0,4,2,1,3]),(0, ![1,4,2,0,3]),(9, ![0,4,2,1,3]),(0, ![2,4,1,0,3]),(11, ![0,4,2,1,3]), (4, ![0,4,2,1,3]),(12, ![0,4,2,1,3]),(4, ![3,4,1,0,2]),(8, ![4,3,1,0,2]),(5, ![0,4,2,1,3]),(9, ![4,3,0,1,2]),(0, ![3,4,1,0,2]),(0, ![4,3,1,0,2]),
(11, ![1,2,0,3,4]),(11, ![2,1,0,3,4]),(10, ![1,2,0,3,4]),(9, ![2,1,0,3,4]),(10, ![1,2,4,0,3]),(9, ![2,1,4,0,3]),(41, ![3,1,0,2,4]),(9, ![3,1,0,2,4]), (10, ![1,2,3,4,0]),(9, ![2,1,3,4,0]),(41, ![3,1,2,4,0]),(9, ![3,1,2,4,0]),(41, ![3,1,4,0,2]),(9, ![3,1,4,0,2]),(40, ![4,0,1,2,3]),(5, ![4,1,0,2,3]), (9, ![1,2,0,3,4]),(10, ![2,1,0,3,4]),(8, ![1,2,0,3,4]),(8, ![2,1,0,3,4]),(41, ![1,2,0,3,4]),(12, ![3,1,0,2,4]),(40, ![1,2,0,3,4]),(8, ![3,1,0,2,4]), (12, ![1,3,2,4,0]),(41, ![2,1,3,4,0]),(12, ![2,3,1,4,0]),(10, ![3,2,1,4,0]),(76, ![0,2,1,3,4]),(12, ![4,1,0,2,3]),(41, ![4,0,1,2,3]),(4, ![4,1,0,2,3]),
(9, ![1,2,4,0,3]),(10, ![2,1,4,0,3]),(12, ![1,3,0,2,4]),(41, ![2,1,0,3,4]),(8, ![1,2,4,0,3]),(8, ![2,1,4,0,3]),(12, ![2,3,0,1,4]),(10, ![3,2,0,1,4]), (41, ![1,2,4,0,3]),(12, ![3,1,4,0,2]),(76, ![0,2,4,1,3]),(12, ![4,1,3,0,2]),(40, ![1,2,4,0,3]),(8, ![3,1,4,0,2]),(41, ![4,0,3,1,2]),(4, ![4,1,3,0,2]), (9, ![1,3,0,2,4]),(41, ![1,3,0,2,4]),(8, ![1,3,0,2,4]),(40, ![1,3,0,2,4]),(10, ![2,3,0,1,4]),(12, ![3,2,0,1,4]),(8, ![2,3,0,1,4]),(8, ![3,2,0,1,4]), (12, ![1,4,2,3,0]),(76, ![0,3,1,2,4]),(12, ![2,4,1,3,0]),(41, ![4,2,1,0,3]),(41, ![2,4,3,1,0]),(12, ![4,2,0,1,3]),(10, ![3,4,1,2,0]),(4, ![4,2,0,1,3]),
(9, ![1,2,3,4,0]),(10, ![2,1,3,4,0]),(41, ![1,2,3,4,0]),(12, ![3,1,2,4,0]),(12, ![1,3,4,0,2]),(41, ![2,1,4,0,3]),(76, ![0,2,3,4,1]),(12, ![4,1,2,3,0]), (8, ![1,2,3,4,0]),(8, ![2,1,3,4,0]),(40, ![1,2,3,4,0]),(8, ![3,1,2,4,0]),(12, ![2,3,4,0,1]),(10, ![3,2,4,0,1]),(41, ![4,0,2,3,1]),(4, ![4,1,2,3,0]), (9, ![1,3,2,4,0]),(41, ![1,3,2,4,0]),(10, ![2,3,1,4,0]),(12, ![3,2,1,4,0]),(12, ![1,4,3,0,2]),(76, ![0,3,2,4,1]),(41, ![2,4,1,0,3]),(12, ![4,2,1,3,0]), (8, ![1,3,2,4,0]),(40, ![1,3,2,4,0]),(8, ![2,3,1,4,0]),(8, ![3,2,1,4,0]),(12, ![2,4,3,0,1]),(41, ![4,2,0,3,1]),(10, ![3,4,2,0,1]),(4, ![4,2,1,3,0]),
(9, ![1,3,4,0,2]),(41, ![1,3,4,0,2]),(12, ![1,4,0,2,3]),(76, ![0,3,4,1,2]),(8, ![1,3,4,0,2]),(40, ![1,3,4,0,2]),(12, ![2,4,0,1,3]),(41, ![4,2,3,1,0]), (10, ![2,3,4,0,1]),(12, ![3,2,4,0,1]),(41, ![2,4,0,3,1]),(12, ![4,2,3,0,1]),(8, ![2,3,4,0,1]),(8, ![3,2,4,0,1]),(10, ![3,4,0,1,2]),(4, ![4,2,3,0,1]), (5, ![1,4,0,2,3]),(40, ![0,4,1,2,3]),(4, ![1,4,0,2,3]),(41, ![0,4,1,2,3]),(4, ![1,4,3,0,2]),(41, ![0,4,3,1,2]),(4, ![2,4,0,1,3]),(10, ![4,3,1,2,0]), (4, ![1,4,2,3,0]),(41, ![0,4,2,3,1]),(4, ![2,4,1,3,0]),(10, ![4,3,2,0,1]),(4, ![2,4,3,0,1]),(10, ![4,3,0,1,2]),(2, ![3,4,0,1,2]),(2, ![4,3,0,1,2]),
(0, ![0,1,4,2,3]),(0, ![1,0,4,2,3]),(8, ![0,1,4,2,3]),(9, ![0,1,4,2,3]),(2, ![0,1,4,2,3]),(0, ![2,0,4,1,3]),(10, ![0,1,4,2,3]),(11, ![0,1,4,2,3]), (4, ![0,1,4,2,3]),(5, ![0,1,4,2,3]),(12, ![0,1,4,2,3]),(9, ![4,1,3,0,2]),(4, ![3,0,4,1,2]),(0, ![3,0,4,1,2]),(8, ![4,0,3,1,2]),(0, ![4,0,3,1,2]), (9, ![1,0,4,2,3]),(8, ![1,0,4,2,3]),(12, ![1,2,0,3,4]),(12, ![2,1,0,3,4]),(10, ![2,0,4,1,3]),(8, ![2,0,4,1,3]),(41, ![2,3,0,1,4]),(10, ![3,1,0,2,4]), (41, ![1,0,4,2,3]),(40, ![1,0,4,2,3]),(76, ![0,1,4,2,3]),(41, ![4,1,3,0,2]),(12, ![3,0,4,1,2]),(8, ![3,0,4,1,2]),(12, ![4,0,3,1,2]),(4, ![4,0,3,1,2]),
(0, ![0,2,4,1,3]),(2, ![0,2,4,1,3]),(8, ![0,2,4,1,3]),(10, ![0,2,4,1,3]),(0, ![1,2,4,0,3]),(0, ![2,1,4,0,3]),(9, ![0,2,4,1,3]),(11, ![0,2,4,1,3]), (4, ![0,2,4,1,3]),(4, ![3,1,4,0,2]),(12, ![0,2,4,1,3]),(8, ![4,1,3,0,2]),(5, ![0,2,4,1,3]),(0, ![3,1,4,0,2]),(9, ![4,0,3,1,2]),(0, ![4,1,3,0,2]), (11, ![1,0,4,2,3]),(10, ![1,0,4,2,3]),(10, ![1,3,0,2,4]),(41, ![3,2,0,1,4]),(11, ![2,0,4,1,3]),(9, ![2,0,4,1,3]),(9, ![2,3,0,1,4]),(9, ![3,2,0,1,4]), (10, ![1,4,3,2,0]),(41, ![3,0,4,1,2]),(41, ![3,4,2,1,0]),(40, ![4,1,3,0,2]),(9, ![2,4,3,1,0]),(9, ![3,0,4,1,2]),(9, ![3,4,2,1,0]),(5, ![4,0,3,1,2]),
(5, ![1,0,4,2,3]),(4, ![1,0,4,2,3]),(40, ![0,1,4,2,3]),(41, ![0,1,4,2,3]),(4, ![1,3,4,0,2]),(4, ![2,0,4,1,3]),(41, ![0,3,4,1,2]),(10, ![4,1,3,2,0]), (4, ![1,2,4,3,0]),(4, ![2,1,4,3,0]),(41, ![0,2,4,3,1]),(10, ![4,2,3,0,1]),(4, ![2,3,4,0,1]),(2, ![3,0,4,1,2]),(10, ![4,0,3,1,2]),(2, ![4,0,3,1,2]), (9, ![1,4,3,0,2]),(12, ![1,0,4,2,3]),(41, ![1,4,3,0,2]),(76, ![0,4,3,1,2]),(8, ![1,4,3,0,2]),(12, ![2,0,4,1,3]),(40, ![1,4,3,0,2]),(41, ![4,3,2,1,0]), (10, ![2,4,3,0,1]),(41, ![2,0,4,3,1]),(12, ![3,4,2,0,1]),(12, ![4,3,2,0,1]),(8, ![2,4,3,0,1]),(10, ![3,0,4,1,2]),(8, ![3,4,2,0,1]),(4, ![4,3,2,0,1]),
(0, ![0,3,4,1,2]),(4, ![0,3,4,1,2]),(8, ![0,3,4,1,2]),(12, ![0,3,4,1,2]),(0, ![1,3,4,0,2]),(5, ![0,3,4,1,2]),(9, ![0,3,4,1,2]),(9, ![4,2,3,1,0]), (2, ![0,3,4,1,2]),(4, ![3,2,4,0,1]),(10, ![0,3,4,1,2]),(8, ![4,2,3,0,1]),(0, ![2,3,4,0,1]),(0, ![3,2,4,0,1]),(11, ![0,3,4,1,2]),(0, ![4,2,3,0,1]), (0, ![0,4,3,1,2]),(8, ![0,4,3,1,2]),(4, ![0,4,3,1,2]),(12, ![0,4,3,1,2]),(0, ![1,4,3,0,2]),(9, ![0,4,3,1,2]),(5, ![0,4,3,1,2]),(9, ![4,3,2,1,0]), (2, ![0,4,3,1,2]),(10, ![0,4,3,1,2]),(4, ![3,4,2,0,1]),(8, ![4,3,2,0,1]),(0, ![2,4,3,0,1]),(11, ![0,4,3,1,2]),(0, ![3,4,2,0,1]),(0, ![4,3,2,0,1]),
(0, ![0,1,2,4,3]),(0, ![1,0,2,4,3]),(2, ![0,1,2,4,3]),(0, ![2,0,1,4,3]),(8, ![0,1,2,4,3]),(9, ![0,1,2,4,3]),(10, ![0,1,2,4,3]),(11, ![0,1,2,4,3]), (4, ![0,1,2,4,3]),(5, ![0,1,2,4,3]),(4, ![3,0,1,4,2]),(0, ![3,0,1,4,2]),(12, ![0,1,2,4,3]),(9, ![4,1,0,3,2]),(8, ![4,0,1,3,2]),(0, ![4,0,1,3,2]), (0, ![0,2,1,4,3]),(2, ![0,2,1,4,3]),(0, ![1,2,0,4,3]),(0, ![2,1,0,4,3]),(8, ![0,2,1,4,3]),(10, ![0,2,1,4,3]),(9, ![0,2,1,4,3]),(11, ![0,2,1,4,3]), (4, ![0,2,1,4,3]),(4, ![3,1,0,4,2]),(5, ![0,2,1,4,3]),(0, ![3,1,0,4,2]),(12, ![0,2,1,4,3]),(8, ![4,1,0,3,2]),(9, ![4,0,1,3,2]),(0, ![4,1,0,3,2]),
(9, ![1,0,2,4,3]),(8, ![1,0,2,4,3]),(10, ![2,0,1,4,3]),(8, ![2,0,1,4,3]),(12, ![1,2,3,0,4]),(12, ![2,1,3,0,4]),(41, ![2,3,1,0,4]),(10, ![3,1,2,0,4]), (41, ![1,0,2,4,3]),(40, ![1,0,2,4,3]),(12, ![3,0,1,4,2]),(8, ![3,0,1,4,2]),(76, ![0,1,2,4,3]),(41, ![4,1,0,3,2]),(12, ![4,0,1,3,2]),(4, ![4,0,1,3,2]), (11, ![1,0,2,4,3]),(10, ![1,0,2,4,3]),(11, ![2,0,1,4,3]),(9, ![2,0,1,4,3]),(10, ![1,3,2,0,4]),(41, ![3,2,1,0,4]),(9, ![2,3,1,0,4]),(9, ![3,2,1,0,4]), (10, ![1,4,2,3,0]),(41, ![3,0,1,4,2]),(9, ![2,4,1,3,0]),(9, ![3,0,1,4,2]),(41, ![3,4,1,2,0]),(40, ![4,1,0,3,2]),(9, ![3,4,1,2,0]),(5, ![4,0,1,3,2]),
(5, ![1,0,2,4,3]),(4, ![1,0,2,4,3]),(4, ![1,3,0,4,2]),(4, ![2,0,1,4,3]),(40, ![0,1,2,4,3]),(41, ![0,1,2,4,3]),(41, ![0,3,1,4,2]),(10, ![4,1,2,3,0]), (4, ![1,2,3,4,0]),(4, ![2,1,3,4,0]),(4, ![2,3,0,4,1]),(2, ![3,0,1,4,2]),(41, ![0,2,3,4,1]),(10, ![4,2,0,3,1]),(10, ![4,0,1,3,2]),(2, ![4,0,1,3,2]), (0, ![0,3,1,4,2]),(4, ![0,3,1,4,2]),(0, ![1,3,0,4,2]),(5, ![0,3,1,4,2]),(8, ![0,3,1,4,2]),(12, ![0,3,1,4,2]),(9, ![0,3,1,4,2]),(9, ![4,2,1,3,0]), (2, ![0,3,1,4,2]),(4, ![3,2,0,4,1]),(0, ![2,3,0,4,1]),(0, ![3,2,0,4,1]),(10, ![0,3,1,4,2]),(8, ![4,2,0,3,1]),(11, ![0,3,1,4,2]),(0, ![4,2,0,3,1]),
(9, ![1,4,0,3,2]),(12, ![1,0,2,4,3]),(8, ![1,4,0,3,2]),(12, ![2,0,1,4,3]),(41, ![1,4,0,3,2]),(76, ![0,4,1,3,2]),(40, ![1,4,0,3,2]),(41, ![4,3,1,2,0]), (10, ![2,4,0,3,1]),(41, ![2,0,3,4,1]),(8, ![2,4,0,3,1]),(10, ![3,0,1,4,2]),(12, ![3,4,0,2,1]),(12, ![4,3,0,2,1]),(8, ![3,4,0,2,1]),(4, ![4,3,0,2,1]), (0, ![0,4,1,3,2]),(8, ![0,4,1,3,2]),(0, ![1,4,0,3,2]),(9, ![0,4,1,3,2]),(4, ![0,4,1,3,2]),(12, ![0,4,1,3,2]),(5, ![0,4,1,3,2]),(9, ![4,3,1,2,0]), (2, ![0,4,1,3,2]),(10, ![0,4,1,3,2]),(0, ![2,4,0,3,1]),(11, ![0,4,1,3,2]),(4, ![3,4,0,2,1]),(8, ![4,3,0,2,1]),(0, ![3,4,0,2,1]),(0, ![4,3,0,2,1]),
(11, ![1,2,0,4,3]),(11, ![2,1,0,4,3]),(10, ![1,2,0,4,3]),(9, ![2,1,0,4,3]),(10, ![1,2,3,0,4]),(9, ![2,1,3,0,4]),(41, ![3,1,2,0,4]),(9, ![3,1,2,0,4]), (10, ![1,2,4,3,0]),(9, ![2,1,4,3,0]),(41, ![3,1,0,4,2]),(9, ![3,1,0,4,2]),(41, ![3,1,4,2,0]),(9, ![3,1,4,2,0]),(40, ![4,0,1,3,2]),(5, ![4,1,0,3,2]), (9, ![1,2,0,4,3]),(10, ![2,1,0,4,3]),(8, ![1,2,0,4,3]),(8, ![2,1,0,4,3]),(12, ![1,3,2,0,4]),(41, ![2,1,3,0,4]),(12, ![2,3,1,0,4]),(10, ![3,2,1,0,4]), (41, ![1,2,0,4,3]),(12, ![3,1,0,4,2]),(40, ![1,2,0,4,3]),(8, ![3,1,0,4,2]),(76, ![0,2,1,4,3]),(12, ![4,1,0,3,2]),(41, ![4,0,1,3,2]),(4, ![4,1,0,3,2]),
(9, ![1,2,3,0,4]),(10, ![2,1,3,0,4]),(41, ![1,2,3,0,4]),(12, ![3,1,2,0,4]),(8, ![1,2,3,0,4]),(8, ![2,1,3,0,4]),(40, ![1,2,3,0,4]),(8, ![3,1,2,0,4]), (12, ![1,3,4,2,0]),(41, ![2,1,4,3,0]),(76, ![0,2,3,1,4]),(12, ![4,1,2,0,3]),(12, ![2,3,4,1,0]),(10, ![3,2,4,1,0]),(41, ![4,0,2,1,3]),(4, ![4,1,2,0,3]), (9, ![1,3,2,0,4]),(41, ![1,3,2,0,4]),(10, ![2,3,1,0,4]),(12, ![3,2,1,0,4]),(8, ![1,3,2,0,4]),(40, ![1,3,2,0,4]),(8, ![2,3,1,0,4]),(8, ![3,2,1,0,4]), (12, ![1,4,3,2,0]),(76, ![0,3,2,1,4]),(41, ![2,4,1,3,0]),(12, ![4,2,1,0,3]),(12, ![2,4,3,1,0]),(41, ![4,2,0,1,3]),(10, ![3,4,2,1,0]),(4, ![4,2,1,0,3]),
(9, ![1,2,4,3,0]),(10, ![2,1,4,3,0]),(12, ![1,3,0,4,2]),(41, ![2,1,0,4,3]),(41, ![1,2,4,3,0]),(12, ![3,1,4,2,0]),(76, ![0,2,4,3,1]),(12, ![4,1,3,2,0]), (8, ![1,2,4,3,0]),(8, ![2,1,4,3,0]),(12, ![2,3,0,4,1]),(10, ![3,2,0,4,1]),(40, ![1,2,4,3,0]),(8, ![3,1,4,2,0]),(41, ![4,0,3,2,1]),(4, ![4,1,3,2,0]), (9, ![1,3,0,4,2]),(41, ![1,3,0,4,2]),(8, ![1,3,0,4,2]),(40, ![1,3,0,4,2]),(12, ![1,4,2,0,3]),(76, ![0,3,1,4,2]),(12, ![2,4,1,0,3]),(41, ![4,2,1,3,0]), (10, ![2,3,0,4,1]),(12, ![3,2,0,4,1]),(8, ![2,3,0,4,1]),(8, ![3,2,0,4,1]),(41, ![2,4,3,0,1]),(12, ![4,2,0,3,1]),(10, ![3,4,1,0,2]),(4, ![4,2,0,3,1]),
(9, ![1,3,4,2,0]),(41, ![1,3,4,2,0]),(12, ![1,4,0,3,2]),(76, ![0,3,4,2,1]),(10, ![2,3,4,1,0]),(12, ![3,2,4,1,0]),(41, ![2,4,0,1,3]),(12, ![4,2,3,1,0]), (8, ![1,3,4,2,0]),(40, ![1,3,4,2,0]),(12, ![2,4,0,3,1]),(41, ![4,2,3,0,1]),(8, ![2,3,4,1,0]),(8, ![3,2,4,1,0]),(10, ![3,4,0,2,1]),(4, ![4,2,3,1,0]), (5, ![1,4,0,3,2]),(40, ![0,4,1,3,2]),(4, ![1,4,0,3,2]),(41, ![0,4,1,3,2]),(4, ![1,4,2,0,3]),(41, ![0,4,2,1,3]),(4, ![2,4,1,0,3]),(10, ![4,3,2,1,0]), (4, ![1,4,3,2,0]),(41, ![0,4,3,2,1]),(4, ![2,4,0,3,1]),(10, ![4,3,1,0,2]),(4, ![2,4,3,1,0]),(10, ![4,3,0,2,1]),(2, ![3,4,0,2,1]),(2, ![4,3,0,2,1]),
(0, ![0,1,3,4,2]),(0, ![1,0,3,4,2]),(4, ![0,1,3,4,2]),(5, ![0,1,3,4,2]),(8, ![0,1,3,4,2]),(9, ![0,1,3,4,2]),(12, ![0,1,3,4,2]),(9, ![4,1,2,3,0]), (2, ![0,1,3,4,2]),(0, ![2,0,3,4,1]),(4, ![3,0,2,4,1]),(0, ![3,0,2,4,1]),(10, ![0,1,3,4,2]),(11, ![0,1,3,4,2]),(8, ![4,0,2,3,1]),(0, ![4,0,2,3,1]), (5, ![1,0,3,4,2]),(4, ![1,0,3,4,2]),(4, ![1,2,0,4,3]),(4, ![2,1,0,4,3]),(40, ![0,1,3,4,2]),(41, ![0,1,3,4,2]),(41, ![0,2,1,4,3]),(10, ![4,2,1,3,0]), (4, ![1,3,2,4,0]),(4, ![2,0,3,4,1]),(4, ![2,3,1,4,0]),(2, ![3,0,2,4,1]),(41, ![0,3,2,4,1]),(10, ![4,1,0,3,2]),(10, ![4,0,2,3,1]),(2, ![4,0,2,3,1]),
(9, ![1,0,3,4,2]),(8, ![1,0,3,4,2]),(41, ![1,0,3,4,2]),(40, ![1,0,3,4,2]),(12, ![1,2,4,0,3]),(12, ![2,1,4,0,3]),(76, ![0,1,3,4,2]),(41, ![4,1,2,3,0]), (10, ![2,0,3,4,1]),(8, ![2,0,3,4,1]),(12, ![3,0,2,4,1]),(8, ![3,0,2,4,1]),(41, ![2,3,4,0,1]),(10, ![3,1,4,0,2]),(12, ![4,0,2,3,1]),(4, ![4,0,2,3,1]), (9, ![1,4,2,3,0]),(12, ![1,0,3,4,2]),(10, ![2,4,1,3,0]),(41, ![2,0,1,4,3]),(41, ![1,4,2,3,0]),(76, ![0,4,2,3,1]),(12, ![3,4,1,2,0]),(12, ![4,3,1,2,0]), (8, ![1,4,2,3,0]),(12, ![2,0,3,4,1]),(8, ![2,4,1,3,0]),(10, ![3,0,2,4,1]),(40, ![1,4,2,3,0]),(41, ![4,3,0,2,1]),(8, ![3,4,1,2,0]),(4, ![4,3,1,2,0]),
(0, ![0,2,3,4,1]),(2, ![0,2,3,4,1]),(4, ![0,2,3,4,1]),(4, ![3,1,2,4,0]),(8, ![0,2,3,4,1]),(10, ![0,2,3,4,1]),(12, ![0,2,3,4,1]),(8, ![4,1,2,3,0]), (0, ![1,2,3,4,0]),(0, ![2,1,3,4,0]),(5, ![0,2,3,4,1]),(0, ![3,1,2,4,0]),(9, ![0,2,3,4,1]),(11, ![0,2,3,4,1]),(9, ![4,0,2,3,1]),(0, ![4,1,2,3,0]), (0, ![0,3,2,4,1]),(4, ![0,3,2,4,1]),(2, ![0,3,2,4,1]),(4, ![3,2,1,4,0]),(8, ![0,3,2,4,1]),(12, ![0,3,2,4,1]),(10, ![0,3,2,4,1]),(8, ![4,2,1,3,0]), (0, ![1,3,2,4,0]),(5, ![0,3,2,4,1]),(0, ![2,3,1,4,0]),(0, ![3,2,1,4,0]),(9, ![0,3,2,4,1]),(9, ![4,2,0,3,1]),(11, ![0,3,2,4,1]),(0, ![4,2,1,3,0]),
(11, ![1,0,3,4,2]),(10, ![1,0,3,4,2]),(10, ![1,4,0,3,2]),(41, ![3,0,2,4,1]),(10, ![1,3,4,0,2]),(41, ![3,2,4,0,1]),(41, ![3,4,0,2,1]),(40, ![4,1,2,3,0]), (11, ![2,0,3,4,1]),(9, ![2,0,3,4,1]),(9, ![2,4,0,3,1]),(9, ![3,0,2,4,1]),(9, ![2,3,4,0,1]),(9, ![3,2,4,0,1]),(9, ![3,4,0,2,1]),(5, ![4,0,2,3,1]), (0, ![0,4,2,3,1]),(8, ![0,4,2,3,1]),(2, ![0,4,2,3,1]),(10, ![0,4,2,3,1]),(4, ![0,4,2,3,1]),(12, ![0,4,2,3,1]),(4, ![3,4,1,2,0]),(8, ![4,3,1,2,0]), (0, ![1,4,2,3,0]),(9, ![0,4,2,3,1]),(0, ![2,4,1,3,0]),(11, ![0,4,2,3,1]),(5, ![0,4,2,3,1]),(9, ![4,3,0,2,1]),(0, ![3,4,1,2,0]),(0, ![4,3,1,2,0]),
(0, ![0,1,4,3,2]),(0, ![1,0,4,3,2]),(8, ![0,1,4,3,2]),(9, ![0,1,4,3,2]),(4, ![0,1,4,3,2]),(5, ![0,1,4,3,2]),(12, ![0,1,4,3,2]),(9, ![4,1,3,2,0]), (2, ![0,1,4,3,2]),(0, ![2,0,4,3,1]),(10, ![0,1,4,3,2]),(11, ![0,1,4,3,2]),(4, ![3,0,4,2,1]),(0, ![3,0,4,2,1]),(8, ![4,0,3,2,1]),(0, ![4,0,3,2,1]), (9, ![1,0,4,3,2]),(8, ![1,0,4,3,2]),(12, ![1,2,0,4,3]),(12, ![2,1,0,4,3]),(41, ![1,0,4,3,2]),(40, ![1,0,4,3,2]),(76, ![0,1,4,3,2]),(41, ![4,1,3,2,0]), (10, ![2,0,4,3,1]),(8, ![2,0,4,3,1]),(41, ![2,3,0,4,1]),(10, ![3,1,0,4,2]),(12, ![3,0,4,2,1]),(8, ![3,0,4,2,1]),(12, ![4,0,3,2,1]),(4, ![4,0,3,2,1]),
(5, ![1,0,4,3,2]),(4, ![1,0,4,3,2]),(40, ![0,1,4,3,2]),(41, ![0,1,4,3,2]),(4, ![1,2,4,0,3]),(4, ![2,1,4,0,3]),(41, ![0,2,4,1,3]),(10, ![4,2,3,1,0]), (4, ![1,3,4,2,0]),(4, ![2,0,4,3,1]),(41, ![0,3,4,2,1]),(10, ![4,1,3,0,2]),(4, ![2,3,4,1,0]),(2, ![3,0,4,2,1]),(10, ![4,0,3,2,1]),(2, ![4,0,3,2,1]), (9, ![1,4,3,2,0]),(12, ![1,0,4,3,2]),(41, ![1,4,3,2,0]),(76, ![0,4,3,2,1]),(10, ![2,4,3,1,0]),(41, ![2,0,4,1,3]),(12, ![3,4,2,1,0]),(12, ![4,3,2,1,0]), (8, ![1,4,3,2,0]),(12, ![2,0,4,3,1]),(40, ![1,4,3,2,0]),(41, ![4,3,2,0,1]),(8, ![2,4,3,1,0]),(10, ![3,0,4,2,1]),(8, ![3,4,2,1,0]),(4, ![4,3,2,1,0]),
(0, ![0,2,4,3,1]),(2, ![0,2,4,3,1]),(8, ![0,2,4,3,1]),(10, ![0,2,4,3,1]),(4, ![0,2,4,3,1]),(4, ![3,1,4,2,0]),(12, ![0,2,4,3,1]),(8, ![4,1,3,2,0]), (0, ![1,2,4,3,0]),(0, ![2,1,4,3,0]),(9, ![0,2,4,3,1]),(11, ![0,2,4,3,1]),(5, ![0,2,4,3,1]),(0, ![3,1,4,2,0]),(9, ![4,0,3,2,1]),(0, ![4,1,3,2,0]), (11, ![1,0,4,3,2]),(10, ![1,0,4,3,2]),(10, ![1,3,0,4,2]),(41, ![3,2,0,4,1]),(10, ![1,4,3,0,2]),(41, ![3,0,4,2,1]),(41, ![3,4,2,0,1]),(40, ![4,1,3,2,0]), (11, ![2,0,4,3,1]),(9, ![2,0,4,3,1]),(9, ![2,3,0,4,1]),(9, ![3,2,0,4,1]),(9, ![2,4,3,0,1]),(9, ![3,0,4,2,1]),(9, ![3,4,2,0,1]),(5, ![4,0,3,2,1]),
(0, ![0,3,4,2,1]),(4, ![0,3,4,2,1]),(8, ![0,3,4,2,1]),(12, ![0,3,4,2,1]),(2, ![0,3,4,2,1]),(4, ![3,2,4,1,0]),(10, ![0,3,4,2,1]),(8, ![4,2,3,1,0]), (0, ![1,3,4,2,0]),(5, ![0,3,4,2,1]),(9, ![0,3,4,2,1]),(9, ![4,2,3,0,1]),(0, ![2,3,4,1,0]),(0, ![3,2,4,1,0]),(11, ![0,3,4,2,1]),(0, ![4,2,3,1,0]), (0, ![0,4,3,2,1]),(8, ![0,4,3,2,1]),(4, ![0,4,3,2,1]),(12, ![0,4,3,2,1]),(2, ![0,4,3,2,1]),(10, ![0,4,3,2,1]),(4, ![3,4,2,1,0]),(8, ![4,3,2,1,0]), (0, ![1,4,3,2,0]),(9, ![0,4,3,2,1]),(5, ![0,4,3,2,1]),(9, ![4,3,2,0,1]),(0, ![2,4,3,1,0]),(11, ![0,4,3,2,1]),(0, ![3,4,2,1,0]),(0, ![4,3,2,1,0])]

private theorem classification5_chunk_0 :
    (List.range' 0 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_1 :
    (List.range' 32 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_2 :
    (List.range' 64 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_3 :
    (List.range' 96 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_4 :
    (List.range' 128 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_5 :
    (List.range' 160 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_6 :
    (List.range' 192 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_7 :
    (List.range' 224 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_8 :
    (List.range' 256 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_9 :
    (List.range' 288 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_10 :
    (List.range' 320 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_11 :
    (List.range' 352 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_12 :
    (List.range' 384 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_13 :
    (List.range' 416 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_14 :
    (List.range' 448 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_15 :
    (List.range' 480 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_16 :
    (List.range' 512 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_17 :
    (List.range' 544 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_18 :
    (List.range' 576 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_19 :
    (List.range' 608 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_20 :
    (List.range' 640 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_21 :
    (List.range' 672 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_22 :
    (List.range' 704 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_23 :
    (List.range' 736 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_24 :
    (List.range' 768 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_25 :
    (List.range' 800 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_26 :
    (List.range' 832 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_27 :
    (List.range' 864 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_28 :
    (List.range' 896 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_29 :
    (List.range' 928 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_30 :
    (List.range' 960 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk_31 :
    (List.range' 992 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private theorem classification5_chunk (q : Fin 32) :
    (List.range' (q.val*32) 32).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by
  fin_cases q
  · exact classification5_chunk_0
  · exact classification5_chunk_1
  · exact classification5_chunk_2
  · exact classification5_chunk_3
  · exact classification5_chunk_4
  · exact classification5_chunk_5
  · exact classification5_chunk_6
  · exact classification5_chunk_7
  · exact classification5_chunk_8
  · exact classification5_chunk_9
  · exact classification5_chunk_10
  · exact classification5_chunk_11
  · exact classification5_chunk_12
  · exact classification5_chunk_13
  · exact classification5_chunk_14
  · exact classification5_chunk_15
  · exact classification5_chunk_16
  · exact classification5_chunk_17
  · exact classification5_chunk_18
  · exact classification5_chunk_19
  · exact classification5_chunk_20
  · exact classification5_chunk_21
  · exact classification5_chunk_22
  · exact classification5_chunk_23
  · exact classification5_chunk_24
  · exact classification5_chunk_25
  · exact classification5_chunk_26
  · exact classification5_chunk_27
  · exact classification5_chunk_28
  · exact classification5_chunk_29
  · exact classification5_chunk_30
  · exact classification5_chunk_31
private theorem classification5_certificate :
    (List.range 1024).all (fun m =>
      decide (((shapeData5.getD m (0, fun _ => 0))).1 ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat)) &&
      relabelCheck m ((shapeData5.getD m (0, fun _ => 0))).1 ((shapeData5.getD m (0, fun _ => 0))).2) = true := by
  apply List.all_eq_true.mpr
  intro m hm
  have hm' : m < 1024 := List.mem_range.mp hm
  have hq : m / 32 < 32 := by omega
  have hmem : m ∈ List.range' ((m / 32)*32) 32 := by
    rw [List.mem_range'_1]
    omega
  exact List.all_eq_true.mp (classification5_chunk ⟨m / 32, hq⟩) m hmem
private theorem landmark_classification_3 (m : Fin 8) :
    ∃ r ∈ ([0, 2] : List Nat), ∃ p : Equiv.Perm (Fin 3),
      ∀ i j, maskArc m.val i j = maskArc r (p i) (p j) := by
  have hc := (List.all_eq_true.mp classification3_certificate) m.val
    (List.mem_range.mpr m.isLt)
  obtain ⟨hr, hp⟩ := Bool.and_eq_true_iff.mp hc
  let q := ((shapeData3.getD m.val (0, fun _ => 0))).2
  have hpair : ∀ i j : Fin 3, (q i = q j → i = j) ∧
      maskArc m.val i j = maskArc ((shapeData3.getD m.val (0, fun _ => 0))).1 (q i) (q j) := by
    have hp' : ∀ i j : Fin 3, (q i ≠ q j ∨ i = j) ∧
        maskArc m.val i j = maskArc ((shapeData3.getD m.val (0, fun _ => 0))).1 (q i) (q j) := by
      simpa [relabelCheck, q] using hp
    intro i j
    exact ⟨fun hij => (hp' i j).1.resolve_left (fun hn => hn hij), (hp' i j).2⟩
  have hinj : Function.Injective q := fun i j hij => (hpair i j).1 hij
  let p : Equiv.Perm (Fin 3) := Equiv.ofBijective q
    ((Fintype.bijective_iff_injective_and_card q).mpr ⟨hinj, rfl⟩)
  exact ⟨((shapeData3.getD m.val (0, fun _ => 0))).1, of_decide_eq_true hr, p, fun i j => (hpair i j).2⟩
private theorem landmark_classification_4 (m : Fin 64) :
    ∃ r ∈ ([0, 2, 4, 5] : List Nat), ∃ p : Equiv.Perm (Fin 4),
      ∀ i j, maskArc m.val i j = maskArc r (p i) (p j) := by
  have hc := (List.all_eq_true.mp classification4_certificate) m.val
    (List.mem_range.mpr m.isLt)
  obtain ⟨hr, hp⟩ := Bool.and_eq_true_iff.mp hc
  let q := ((shapeData4.getD m.val (0, fun _ => 0))).2
  have hpair : ∀ i j : Fin 4, (q i = q j → i = j) ∧
      maskArc m.val i j = maskArc ((shapeData4.getD m.val (0, fun _ => 0))).1 (q i) (q j) := by
    have hp' : ∀ i j : Fin 4, (q i ≠ q j ∨ i = j) ∧
        maskArc m.val i j = maskArc ((shapeData4.getD m.val (0, fun _ => 0))).1 (q i) (q j) := by
      simpa [relabelCheck, q] using hp
    intro i j
    exact ⟨fun hij => (hp' i j).1.resolve_left (fun hn => hn hij), (hp' i j).2⟩
  have hinj : Function.Injective q := fun i j hij => (hpair i j).1 hij
  let p : Equiv.Perm (Fin 4) := Equiv.ofBijective q
    ((Fintype.bijective_iff_injective_and_card q).mpr ⟨hinj, rfl⟩)
  exact ⟨((shapeData4.getD m.val (0, fun _ => 0))).1, of_decide_eq_true hr, p, fun i j => (hpair i j).2⟩
private theorem landmark_classification_5 (m : Fin 1024) :
    ∃ r ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat), ∃ p : Equiv.Perm (Fin 5),
      ∀ i j, maskArc m.val i j = maskArc r (p i) (p j) := by
  have hc := (List.all_eq_true.mp classification5_certificate) m.val
    (List.mem_range.mpr m.isLt)
  obtain ⟨hr, hp⟩ := Bool.and_eq_true_iff.mp hc
  let q := ((shapeData5.getD m.val (0, fun _ => 0))).2
  have hpair : ∀ i j : Fin 5, (q i = q j → i = j) ∧
      maskArc m.val i j = maskArc ((shapeData5.getD m.val (0, fun _ => 0))).1 (q i) (q j) := by
    have hp' : ∀ i j : Fin 5, (q i ≠ q j ∨ i = j) ∧
        maskArc m.val i j = maskArc ((shapeData5.getD m.val (0, fun _ => 0))).1 (q i) (q j) := by
      simpa [relabelCheck, q] using hp
    intro i j
    exact ⟨fun hij => (hp' i j).1.resolve_left (fun hn => hn hij), (hp' i j).2⟩
  have hinj : Function.Injective q := fun i j hij => (hpair i j).1 hij
  let p : Equiv.Perm (Fin 5) := Equiv.ofBijective q
    ((Fintype.bijective_iff_injective_and_card q).mpr ⟨hinj, rfl⟩)
  exact ⟨((shapeData5.getD m.val (0, fun _ => 0))).1, of_decide_eq_true hr, p, fun i j => (hpair i j).2⟩


private lemma bitsNat_lt (bs : List Bool) : List.foldr Nat.bit 0 bs < 2 ^ bs.length := by
  have hfold : List.foldr Nat.bit 0 bs = Nat.ofDigits 2 (bs.map Bool.toNat) := by
    rw [Nat.ofDigits_eq_foldr, List.foldr_map]
    congr 1
    funext b n
    simp only [Nat.cast_id, Nat.bit_val]
    omega
  rw [hfold]
  simpa only [List.length_map] using
    (Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2) (by
      intro n hn
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hn
      cases b <;> decide) : Nat.ofDigits 2 (bs.map Bool.toNat) < 2 ^ (bs.map Bool.toNat).length)
private noncomputable def encode3 (R : Fin 3 → Fin 3 → Prop) : Nat := by
  classical
  exact List.foldr Nat.bit 0 [decide (R 0 1),decide (R 0 2),decide (R 1 2)]
private lemma encode3_lt (R : Fin 3 → Fin 3 → Prop) : encode3 R < 8 := by
  classical
  simpa [encode3] using bitsNat_lt [decide (R 0 1),decide (R 0 2),decide (R 1 2)]
private lemma encode3_rel (R : Fin 3 → Fin 3 → Prop) (hR : IsTournament R) :
    ∀ i j, maskArc (encode3 R) i j = true ↔ R i j := by
  classical
  have h01 := xor_iff_not_iff'.mp (hR.2 0 1 (by decide))
  have h02 := xor_iff_not_iff'.mp (hR.2 0 2 (by decide))
  have h12 := xor_iff_not_iff'.mp (hR.2 1 2 (by decide))
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [maskArc, pairIndex, encode3, List.foldr, Nat.testBit_bit_zero,
      Nat.testBit_bit_succ, hR.1, h01, h02, h12]
private theorem tournament_classification_3 (R : Fin 3 → Fin 3 → Prop) (hR : IsTournament R) :
    ∃ r ∈ ([0, 2] : List Nat), ∃ p : Equiv.Perm (Fin 3),
      ∀ i j, maskArc r (p i) (p j) = true ↔ R i j := by
  obtain ⟨r, hr, p, hp⟩ := landmark_classification_3 ⟨encode3 R, encode3_lt R⟩
  refine ⟨r, hr, p, fun i j => ?_⟩
  rw [← hp i j]
  exact encode3_rel R hR i j
private noncomputable def encode4 (R : Fin 4 → Fin 4 → Prop) : Nat := by
  classical
  exact List.foldr Nat.bit 0 [decide (R 0 1),decide (R 0 2),decide (R 0 3),decide (R 1 2),decide (R 1 3),decide (R 2 3)]
private lemma encode4_lt (R : Fin 4 → Fin 4 → Prop) : encode4 R < 64 := by
  classical
  simpa [encode4] using bitsNat_lt [decide (R 0 1),decide (R 0 2),decide (R 0 3),decide (R 1 2),decide (R 1 3),decide (R 2 3)]
private lemma encode4_rel (R : Fin 4 → Fin 4 → Prop) (hR : IsTournament R) :
    ∀ i j, maskArc (encode4 R) i j = true ↔ R i j := by
  classical
  have h01 := xor_iff_not_iff'.mp (hR.2 0 1 (by decide))
  have h02 := xor_iff_not_iff'.mp (hR.2 0 2 (by decide))
  have h03 := xor_iff_not_iff'.mp (hR.2 0 3 (by decide))
  have h12 := xor_iff_not_iff'.mp (hR.2 1 2 (by decide))
  have h13 := xor_iff_not_iff'.mp (hR.2 1 3 (by decide))
  have h23 := xor_iff_not_iff'.mp (hR.2 2 3 (by decide))
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [maskArc, pairIndex, encode4, List.foldr, Nat.testBit_bit_zero,
      Nat.testBit_bit_succ, hR.1, h01, h02, h03, h12, h13, h23]
private theorem tournament_classification_4 (R : Fin 4 → Fin 4 → Prop) (hR : IsTournament R) :
    ∃ r ∈ ([0, 2, 4, 5] : List Nat), ∃ p : Equiv.Perm (Fin 4),
      ∀ i j, maskArc r (p i) (p j) = true ↔ R i j := by
  obtain ⟨r, hr, p, hp⟩ := landmark_classification_4 ⟨encode4 R, encode4_lt R⟩
  refine ⟨r, hr, p, fun i j => ?_⟩
  rw [← hp i j]
  exact encode4_rel R hR i j
private noncomputable def encode5 (R : Fin 5 → Fin 5 → Prop) : Nat := by
  classical
  exact List.foldr Nat.bit 0 [decide (R 0 1),decide (R 0 2),decide (R 0 3),decide (R 0 4),decide (R 1 2),decide (R 1 3),decide (R 1 4),decide (R 2 3),decide (R 2 4),decide (R 3 4)]
private lemma encode5_lt (R : Fin 5 → Fin 5 → Prop) : encode5 R < 1024 := by
  classical
  simpa [encode5] using bitsNat_lt [decide (R 0 1),decide (R 0 2),decide (R 0 3),decide (R 0 4),decide (R 1 2),decide (R 1 3),decide (R 1 4),decide (R 2 3),decide (R 2 4),decide (R 3 4)]
private lemma encode5_rel (R : Fin 5 → Fin 5 → Prop) (hR : IsTournament R) :
    ∀ i j, maskArc (encode5 R) i j = true ↔ R i j := by
  classical
  have h01 := xor_iff_not_iff'.mp (hR.2 0 1 (by decide))
  have h02 := xor_iff_not_iff'.mp (hR.2 0 2 (by decide))
  have h03 := xor_iff_not_iff'.mp (hR.2 0 3 (by decide))
  have h04 := xor_iff_not_iff'.mp (hR.2 0 4 (by decide))
  have h12 := xor_iff_not_iff'.mp (hR.2 1 2 (by decide))
  have h13 := xor_iff_not_iff'.mp (hR.2 1 3 (by decide))
  have h14 := xor_iff_not_iff'.mp (hR.2 1 4 (by decide))
  have h23 := xor_iff_not_iff'.mp (hR.2 2 3 (by decide))
  have h24 := xor_iff_not_iff'.mp (hR.2 2 4 (by decide))
  have h34 := xor_iff_not_iff'.mp (hR.2 3 4 (by decide))
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [maskArc, pairIndex, encode5, List.foldr, Nat.testBit_bit_zero,
      Nat.testBit_bit_succ, hR.1, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
private theorem tournament_classification_5 (R : Fin 5 → Fin 5 → Prop) (hR : IsTournament R) :
    ∃ r ∈ ([0, 2, 4, 5, 8, 9, 10, 11, 12, 40, 41, 76] : List Nat), ∃ p : Equiv.Perm (Fin 5),
      ∀ i j, maskArc r (p i) (p j) = true ↔ R i j := by
  obtain ⟨r, hr, p, hp⟩ := landmark_classification_5 ⟨encode5 R, encode5_lt R⟩
  refine ⟨r, hr, p, fun i j => ?_⟩
  rw [← hp i j]
  exact encode5_rel R hR i j
private lemma cast_le_upperOfCode {I : Type*} (D : I → I → Nat) (i j : I) :
    (D i j : ℕ∞) ≤ upperOfCode D i j := by
  unfold upperOfCode
  split <;> simp
private theorem nonpath_certificate_3_0 :
    (List.finRange 3).all (fun i => (List.finRange 3).all (fun j =>
      decide (nonD30 i j = 8) || walkBound 0 (nonD30 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_3_0 {V : Type*} (R : V → V → Prop) (L : Fin 3 → V)
    (hE : ∀ i j, maskArc 0 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD30 i j := by
  intro i j
  by_cases hd : nonD30 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 0 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_3_0)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_4_0 :
    (List.finRange 4).all (fun i => (List.finRange 4).all (fun j =>
      decide (nonD40 i j = 8) || walkBound 0 (nonD40 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_4_0 {V : Type*} (R : V → V → Prop) (L : Fin 4 → V)
    (hE : ∀ i j, maskArc 0 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD40 i j := by
  intro i j
  by_cases hd : nonD40 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 0 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_4_0)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_4_2 :
    (List.finRange 4).all (fun i => (List.finRange 4).all (fun j =>
      decide (nonD42 i j = 8) || walkBound 2 (nonD42 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_4_2 {V : Type*} (R : V → V → Prop) (L : Fin 4 → V)
    (hE : ∀ i j, maskArc 2 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD42 i j := by
  intro i j
  by_cases hd : nonD42 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 2 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_4_2)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_4_5 :
    (List.finRange 4).all (fun i => (List.finRange 4).all (fun j =>
      decide (nonD45 i j = 8) || walkBound 5 (nonD45 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_4_5 {V : Type*} (R : V → V → Prop) (L : Fin 4 → V)
    (hE : ∀ i j, maskArc 5 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD45 i j := by
  intro i j
  by_cases hd : nonD45 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 5 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_4_5)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_5_0 :
    (List.finRange 5).all (fun i => (List.finRange 5).all (fun j =>
      decide (nonD50 i j = 8) || walkBound 0 (nonD50 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_5_0 {V : Type*} (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 0 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD50 i j := by
  intro i j
  by_cases hd : nonD50 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 0 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_5_0)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_5_2 :
    (List.finRange 5).all (fun i => (List.finRange 5).all (fun j =>
      decide (nonD52 i j = 8) || walkBound 2 (nonD52 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_5_2 {V : Type*} (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 2 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD52 i j := by
  intro i j
  by_cases hd : nonD52 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 2 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_5_2)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_5_4 :
    (List.finRange 5).all (fun i => (List.finRange 5).all (fun j =>
      decide (nonD54 i j = 8) || walkBound 4 (nonD54 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_5_4 {V : Type*} (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 4 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD54 i j := by
  intro i j
  by_cases hd : nonD54 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 4 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_5_4)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_5_5 :
    (List.finRange 5).all (fun i => (List.finRange 5).all (fun j =>
      decide (nonD55 i j = 8) || walkBound 5 (nonD55 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_5_5 {V : Type*} (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 5 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD55 i j := by
  intro i j
  by_cases hd : nonD55 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 5 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_5_5)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_5_9 :
    (List.finRange 5).all (fun i => (List.finRange 5).all (fun j =>
      decide (nonD59 i j = 8) || walkBound 9 (nonD59 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_5_9 {V : Type*} (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 9 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD59 i j := by
  intro i j
  by_cases hd : nonD59 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 9 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_5_9)
      i (by simp))) j (by simp)
    simpa [hd] using h
private theorem nonpath_certificate_5_11 :
    (List.finRange 5).all (fun i => (List.finRange 5).all (fun j =>
      decide (nonD511 i j = 8) || walkBound 11 (nonD511 i j) i j)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
private lemma nonpath_upper_5_11 {V : Type*} (R : V → V → Prop) (L : Fin 5 → V)
    (hE : ∀ i j, maskArc 11 i j = true → R (L i) (L j)) :
    ∀ i j, directedDistance R (L i) (L j) ≤ upperOfCode nonD511 i j := by
  intro i j
  by_cases hd : nonD511 i j = 8
  · simp only [upperOfCode, hd, if_pos, le_top]
  · simp only [upperOfCode, hd, if_false]
    apply directedDistance_le_walkBound R L 11 hE
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp nonpath_certificate_5_11)
      i (by simp))) j (by simp)
    simpa [hd] using h
private lemma landmark_bound_3 {V : Type*} [Fintype V]
    (R : V → V → Prop) (hR : IsTournament R) (L : Fin 3 → V)
    (hL : Function.Injective L) (hS : IsSolidResolving R (Set.range L)) :
    Fintype.card V ≤ 3+1 := by
  classical
  have hH : IsTournament (fun i j : Fin 3 => R (L i) (L j)) := by
    refine ⟨fun i => hR.1 (L i), ?_⟩
    intro i j hij
    exact hR.2 (L i) (L j) (fun h => hij (hL h))
  obtain ⟨r, hr, p, hp⟩ := tournament_classification_3 (fun i j => R (L i) (L j)) hH
  let M : Fin 3 → V := fun i => L (p.symm i)
  have hM : Function.Injective M := hL.comp p.symm.injective
  have hRange : Set.range M = Set.range L := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨p.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨p i, by simp [M]⟩
  have hMS : IsSolidResolving R (Set.range M) := hRange.symm ▸ hS
  have hE : ∀ i j, maskArc r i j = true → R (M i) (M j) := by
    intro i j hij
    apply (hp (p.symm i) (p.symm j)).mp
    simpa using hij
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · apply card_bound_of_profile_model R M hM hMS nonD30
    · exact nonpath_upper_3_0 R M hE
    · exact fun x hA hB _ => nonstrong_profile_bound_3_0 x hA hB
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_3_0 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS D32
    · intro i j
      exact (representative_path_upper_3_2 R M hE i j).trans (cast_le_upperOfCode D32 i j)
    · exact strong_enat_profile_bound D32
        (by intro i j; fin_cases i <;> fin_cases j <;> decide) 0 nat_profile_bound_3_2
    · intro U _ f _ ha hb hc hanti
      exact strong_profile_antichain_bound_3_2 f ha hb hc hanti
private lemma landmark_bound_4 {V : Type*} [Fintype V]
    (R : V → V → Prop) (hR : IsTournament R) (L : Fin 4 → V)
    (hL : Function.Injective L) (hS : IsSolidResolving R (Set.range L)) :
    Fintype.card V ≤ 4+2 := by
  classical
  have hH : IsTournament (fun i j : Fin 4 => R (L i) (L j)) := by
    refine ⟨fun i => hR.1 (L i), ?_⟩
    intro i j hij
    exact hR.2 (L i) (L j) (fun h => hij (hL h))
  obtain ⟨r, hr, p, hp⟩ := tournament_classification_4 (fun i j => R (L i) (L j)) hH
  let M : Fin 4 → V := fun i => L (p.symm i)
  have hM : Function.Injective M := hL.comp p.symm.injective
  have hRange : Set.range M = Set.range L := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨p.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨p i, by simp [M]⟩
  have hMS : IsSolidResolving R (Set.range M) := hRange.symm ▸ hS
  have hE : ∀ i j, maskArc r i j = true → R (M i) (M j) := by
    intro i j hij
    apply (hp (p.symm i) (p.symm j)).mp
    simpa using hij
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · apply card_bound_of_profile_model R M hM hMS nonD40
    · exact nonpath_upper_4_0 R M hE
    · exact fun x hA hB _ => nonstrong_profile_bound_4_0 x hA hB
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_4_0 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS nonD42
    · exact nonpath_upper_4_2 R M hE
    · exact nonstrong_profile_bound_4_2
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_4_2 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS D44
    · intro i j
      exact (representative_path_upper_4_4 R M hE i j).trans (cast_le_upperOfCode D44 i j)
    · exact strong_enat_profile_bound D44
        (by intro i j; fin_cases i <;> fin_cases j <;> decide) 0 nat_profile_bound_4_4
    · intro U _ f _ ha hb hc hanti
      exact strong_profile_antichain_bound_4_4 f ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS nonD45
    · exact nonpath_upper_4_5 R M hE
    · exact fun x hA hB _ => nonstrong_profile_bound_4_5 x hA hB
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_4_5 f hm ha hb hc hanti
private lemma landmark_bound_5 {V : Type*} [Fintype V]
    (R : V → V → Prop) (hR : IsTournament R) (L : Fin 5 → V)
    (hL : Function.Injective L) (hS : IsSolidResolving R (Set.range L)) :
    Fintype.card V ≤ 5+5 := by
  classical
  have hH : IsTournament (fun i j : Fin 5 => R (L i) (L j)) := by
    refine ⟨fun i => hR.1 (L i), ?_⟩
    intro i j hij
    exact hR.2 (L i) (L j) (fun h => hij (hL h))
  obtain ⟨r, hr, p, hp⟩ := tournament_classification_5 (fun i j => R (L i) (L j)) hH
  let M : Fin 5 → V := fun i => L (p.symm i)
  have hM : Function.Injective M := hL.comp p.symm.injective
  have hRange : Set.range M = Set.range L := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨p.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨p i, by simp [M]⟩
  have hMS : IsSolidResolving R (Set.range M) := hRange.symm ▸ hS
  have hE : ∀ i j, maskArc r i j = true → R (M i) (M j) := by
    intro i j hij
    apply (hp (p.symm i) (p.symm j)).mp
    simpa using hij
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply card_bound_of_profile_model R M hM hMS nonD50
    · exact nonpath_upper_5_0 R M hE
    · exact fun x hA hB _ => nonstrong_profile_bound_5_0 x hA hB
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_5_0 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS nonD52
    · exact nonpath_upper_5_2 R M hE
    · exact nonstrong_profile_bound_5_2
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_5_2 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS nonD54
    · exact nonpath_upper_5_4 R M hE
    · exact nonstrong_profile_bound_5_4
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_5_4 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS nonD55
    · exact nonpath_upper_5_5 R M hE
    · exact fun x hA hB _ => nonstrong_profile_bound_5_5 x hA hB
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_5_5 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS D58
    · intro i j
      exact (representative_path_upper_5_8 R M hE i j).trans (cast_le_upperOfCode D58 i j)
    · exact strong_enat_profile_bound D58
        (by intro i j; fin_cases i <;> fin_cases j <;> decide) 0 nat_profile_bound_5_8
    · intro U _ f _ ha hb hc hanti
      exact strong_profile_antichain_bound_5_8 f ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS nonD59
    · exact nonpath_upper_5_9 R M hE
    · exact fun x hA hB _ => nonstrong_profile_bound_5_9 x hA hB
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_5_9 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS D510
    · intro i j
      exact (representative_path_upper_5_10 R M hE i j).trans (cast_le_upperOfCode D510 i j)
    · exact strong_enat_profile_bound D510
        (by intro i j; fin_cases i <;> fin_cases j <;> decide) 0 nat_profile_bound_5_10
    · intro U _ f _ ha hb hc hanti
      exact strong_profile_antichain_bound_5_10 f ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS nonD511
    · exact nonpath_upper_5_11 R M hE
    · exact fun x hA hB _ => nonstrong_profile_bound_5_11 x hA hB
    · intro U _ f hm ha hb hc hanti
      exact nonstrong_antichain_bound_5_11 f hm ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS D512
    · intro i j
      exact (representative_path_upper_5_12 R M hE i j).trans (cast_le_upperOfCode D512 i j)
    · exact strong_enat_profile_bound D512
        (by intro i j; fin_cases i <;> fin_cases j <;> decide) 0 nat_profile_bound_5_12
    · intro U _ f _ ha hb hc hanti
      exact strong_profile_antichain_bound_5_12 f ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS D540
    · intro i j
      exact (representative_path_upper_5_40 R M hE i j).trans (cast_le_upperOfCode D540 i j)
    · exact strong_enat_profile_bound D540
        (by intro i j; fin_cases i <;> fin_cases j <;> decide) 0 nat_profile_bound_5_40
    · intro U _ f _ ha hb hc hanti
      exact strong_profile_antichain_bound_5_40 f ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS D541
    · intro i j
      exact (representative_path_upper_5_41 R M hE i j).trans (cast_le_upperOfCode D541 i j)
    · exact strong_enat_profile_bound D541
        (by intro i j; fin_cases i <;> fin_cases j <;> decide) 0 nat_profile_bound_5_41
    · intro U _ f _ ha hb hc hanti
      exact strong_profile_antichain_bound_5_41 f ha hb hc hanti
  · apply card_bound_of_profile_model R M hM hMS D576
    · intro i j
      exact (representative_path_upper_5_76 R M hE i j).trans (cast_le_upperOfCode D576 i j)
    · exact strong_enat_profile_bound D576
        (by intro i j; fin_cases i <;> fin_cases j <;> decide) 0 nat_profile_bound_5_76
    · intro U _ f _ ha hb hc hanti
      exact strong_profile_antichain_bound_5_76 f ha hb hc hanti
private lemma card_bound_from_landmarks {V : Type*} [Fintype V] {k c : Nat}
    (R : V → V → Prop)
    (hModel : ∀ L : Fin k → V, Function.Injective L →
      IsSolidResolving R (Set.range L) → Fintype.card V ≤ k+c)
    (S : Finset V) (hCard : S.card = k) (hSolid : IsSolidResolving R (S : Set V)) :
    Fintype.card V ≤ k+c := by
  classical
  let e : {v // v ∈ S} ≃ Fin k := Fintype.equivFinOfCardEq (by simpa using hCard)
  let L : Fin k → V := fun i => (e.symm i).val
  have hL : Function.Injective L := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  have hRange : Set.range L = (S : Set V) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hv
      exact ⟨e ⟨v, hv⟩, by simp [L]⟩
  exact hModel L hL (hRange.symm ▸ hSolid)

theorem result : claim := by
  apply claim_of_card_bounds
  · intro n R hR S hCard hSolid
    simpa using card_bound_from_landmarks (k := 3) (c := 1) R
      (landmark_bound_3 R hR) S hCard hSolid
  · intro n R hR S hCard hSolid
    simpa using card_bound_from_landmarks (k := 4) (c := 2) R
      (landmark_bound_4 R hR) S hCard hSolid
  · intro n R hR S hCard hSolid
    simpa using card_bound_from_landmarks (k := 5) (c := 5) R
      (landmark_bound_5 R hR) S hCard hSolid

end D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournament
