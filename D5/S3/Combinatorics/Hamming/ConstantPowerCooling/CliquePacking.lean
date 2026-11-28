/- GID: D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Degrees and incidences of edge-disjoint cliques. -/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Clique
import OmegaBuild.Commands

compile_only_with_mathlib

/-! # Degrees and incidences of edge-disjoint cliques -/

open scoped BigOperators ENat
open SimpleGraph

namespace CPECCBridge
open Finset

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def packedEdgeSet (C : Finset I) (W : I → Finset V) : Set (Sym2 V) :=
  ⋃ i ∈ (C : Set I), ((W i : Set V).sym2)

def packedGraph (C : Finset I) (W : I → Finset V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (packedEdgeSet C W)

omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem packedGraph_adj_iff (C : Finset I) (W : I → Finset V) (v u : V) :
    (packedGraph C W).Adj v u ↔
      ∃ i ∈ C, v ∈ W i ∧ u ∈ (W i).erase v := by
  simp [packedGraph, packedEdgeSet, Finset.mem_erase]
  aesop

omit [Fintype V] [Fintype I] [DecidableEq I] in
private theorem packedGraph_neighborFinset (C : Finset I) (W : I → Finset V) (v : V)
    [Fintype ((packedGraph C W).neighborSet v)] :
    (packedGraph C W).neighborFinset v =
      C.biUnion (fun i => if v ∈ W i then (W i).erase v else ∅) := by
  ext u
  rw [SimpleGraph.mem_neighborFinset]
  rw [packedGraph_adj_iff]
  simp only [Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨i, hi, hv, hne, hu⟩
    refine ⟨i, hi, ?_⟩
    simp [hv, hne, hu]
  · rintro ⟨i, hi, h⟩
    by_cases hv : v ∈ W i
    · simp [hv] at h
      rcases h with ⟨hne, hu⟩
      exact ⟨i, hi, hv, hne, hu⟩
    · simp [hv] at h

omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem packedGraph_degree
    (C : Finset I) (W : I → Finset V) (k : ℕ)
    (hWcard : ∀ i ∈ C, (W i).card = k)
    (hinter : ∀ ⦃i j : I⦄, i ∈ C → j ∈ C → i ≠ j → (W i ∩ W j).card ≤ 1)
    (v : V) [Fintype ((packedGraph C W).neighborSet v)] :
    (packedGraph C W).degree v = (k - 1) * (C.filter (fun i => v ∈ W i)).card := by
  have hpair : (↑C : Set I).PairwiseDisjoint
      (fun i => if v ∈ W i then (W i).erase v else ∅) := by
    intro i hi j hj hij
    change Disjoint (if v ∈ W i then (W i).erase v else ∅)
      (if v ∈ W j then (W j).erase v else ∅)
    by_cases hvi : v ∈ W i <;> by_cases hvj : v ∈ W j
    · apply Finset.disjoint_left.mpr
      intro u hui huj
      have hui_erase : u ∈ (W i).erase v := by simpa [hvi] using hui
      have huj_erase : u ∈ (W j).erase v := by simpa [hvj] using huj
      have hui' : u ∈ W i := (Finset.mem_erase.mp hui_erase).2
      have huj' : u ∈ W j := (Finset.mem_erase.mp huj_erase).2
      have hle := hinter hi hj hij
      have hlt : 1 < (W i ∩ W j).card := by
        apply Finset.one_lt_card.mpr
        refine ⟨v, Finset.mem_inter.mpr ⟨hvi, hvj⟩, u, ?_, ?_⟩
        · exact Finset.mem_inter.mpr ⟨hui', huj'⟩
        · exact (Finset.mem_erase.mp hui_erase).1.symm
      omega
    · simp [hvi, hvj]
    · simp [hvi, hvj]
    · simp [hvi, hvj]
  rw [show (packedGraph C W).degree v =
      (C.biUnion (fun i => if v ∈ W i then (W i).erase v else ∅)).card by
        rw [degree, packedGraph_neighborFinset]]
  rw [Finset.card_biUnion hpair]
  have hcardsum : (∑ i ∈ C, #(if v ∈ W i then (W i).erase v else ∅)) =
      ∑ i ∈ C, (if v ∈ W i then ((W i).erase v).card else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hvi : v ∈ W i <;> simp [hvi]
  rw [hcardsum]
  have hsum : (∑ i ∈ C, (if v ∈ W i then ((W i).erase v).card else 0)) =
      ∑ i ∈ C, (if v ∈ W i then k - 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hvi : v ∈ W i
    · simp [hvi, Finset.card_erase_of_mem, hWcard i hi]
    · simp [hvi]
  rw [hsum]
  calc
    (∑ i ∈ C, (if v ∈ W i then k - 1 else 0)) =
        (k - 1) * (∑ i ∈ C, if v ∈ W i then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hvi : v ∈ W i <;> simp [hvi]
    _ = (k - 1) * (C.filter (fun i => v ∈ W i)).card := by
          have hb : (∑ i ∈ C, if v ∈ W i then 1 else 0) =
              (C.filter (fun i => v ∈ W i)).card := by
            simp
          rw [hb]
omit [Fintype I] [DecidableEq I] in
theorem incidence_sum
    (C : Finset I) (W : I → Finset V) (k : ℕ)
    (hWcard : ∀ i ∈ C, (W i).card = k) :
    (∑ v : V, (C.filter (fun i => v ∈ W i)).card) = k * C.card := by
  have hsum (i : I) : (∑ v : V, if v ∈ W i then 1 else 0) = (W i).card := by
    rw [← Finset.sum_filter]
    simp
  calc
    (∑ v : V, (C.filter (fun i => v ∈ W i)).card) =
        ∑ v : V, (∑ i ∈ C, if v ∈ W i then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro v hv
          simp
    _ = (∑ i ∈ C, ∑ v : V, if v ∈ W i then 1 else 0) := by
          rw [Finset.sum_comm]
    _ = (∑ i ∈ C, (W i).card) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hsum i
    _ = (∑ i ∈ C, k) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hWcard i hi
    _ = k * C.card := by
          simp [Nat.mul_comm]

end
end CPECCBridge
