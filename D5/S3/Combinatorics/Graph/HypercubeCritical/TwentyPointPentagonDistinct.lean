/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonDistinct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonDistinct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Actual coordinate differences for five distinct pentagon matching directions.
 -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonCoordinates

/-! Coordinate normalizations retain the actual vertices and their difference sets. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonDistinct

open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced)
open private matching_direction_bit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagon
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_self from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry

attribute [local instance] Classical.propDecidable

private def shape (i : Fin 5) : Finset (Fin 5) :=
  Finset.univ.filter (fun j => i ≠ j ∧ ¬ (cycleGraph 5).Adj i j)

private theorem distinct_direction_normal_form {n : ℕ}
    (A B : Fin 5 → Q n) (c : Fin 5 → Fin n) (hc : Function.Injective c)
    (hflip : ∀ i, B i = flip (A i) (c i))
    (hno : ∀ i j, i ≠ j → ¬ (hypercube n).Adj (A i) (B j))
    (hA : ∀ i j, (cycleGraph 5).Adj i j → hammingDist (A i) (A j) = 2)
    (hB : ∀ i j, i ≠ j → ¬ (cycleGraph 5).Adj i j →
      hammingDist (B i) (B j) = 2) :
    ∃ z : Q n, ∀ i, diff (A i) z = (shape i).image c ∧
      diff (B i) z = insert (c i) ((shape i).image c) := by
  have hbit := matching_direction_bit A B c hflip hno hA hB
  have hshape (i j : Fin 5) : A i (c j) ≠ A j (c j) ↔ j ∈ shape i := by
    by_cases hij : i = j
    · subst j; simp [shape]
    · have hh := hbit j i (Ne.symm hij)
      have hci : c j ≠ c i := hc.ne (Ne.symm hij)
      simpa [shape, hij, hci, SimpleGraph.adj_comm, ne_comm] using not_congr hh
  let T : Fin 5 → Finset (Fin 5) := fun i =>
    (shape i \ shape 0) ∪ (shape 0 \ shape i)
  have hTbit (i j : Fin 5) : A i (c j) ≠ A 0 (c j) ↔ j ∈ T i := by
    simp only [T, Finset.mem_union, Finset.mem_sdiff, ← hshape]
    cases hi : A i (c j) <;> cases h0 : A 0 (c j) <;> cases hj : A j (c j) <;> decide
  have hTcard (i : Fin 5) : (T i).card =
      if i = 0 then 0 else if (cycleGraph 5).Adj i 0 then 2 else 4 := by
    change ((shape i \ shape 0) ∪ (shape 0 \ shape i)).card = _
    revert i
    decide +kernel
  have hbound (i : Fin 5) : (diff (A i) (A 0)).card ≤ (T i).card := by
    rw [hTcard]
    split_ifs with hi he
    · subst i; rw [diff_self]; simp
    · exact (hA i 0 he).le
    · have hBi := hB i 0 hi he
      have hi1 : hammingDist (A i) (B i) = 1 := by
        rw [hflip]; exact BalancedCriticalSpectrum.flip_adj _ _
      have h01 : hammingDist (B 0) (A 0) = 1 := by
        rw [hflip, hammingDist_comm]; exact BalancedCriticalSpectrum.flip_adj _ _
      have h1 := hammingDist_triangle (A i) (B i) (A 0)
      have h2 := hammingDist_triangle (B i) (B 0) (A 0)
      change hammingDist (A i) (A 0) ≤ 4
      omega
  have hdiff (i : Fin 5) : diff (A i) (A 0) = (T i).image c := by
    have hsub : (T i).image c ⊆ diff (A i) (A 0) := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hTbit i j).mpr hj⟩
    have hcard : ((T i).image c).card = (T i).card := Finset.card_image_of_injective _ hc
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hbound i)).symm
  have houtside (i : Fin 5) (k : Fin n) (hk : ¬ ∃ j, c j = k) : A i k = A 0 k := by
    by_contra hne
    have hm : k ∈ diff (A i) (A 0) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hdiff] at hm
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact hk ⟨j, hj⟩
  let z : Q n := fun k => if h : ∃ j, c j = k then A h.choose k else A 0 k
  have hz (j : Fin 5) : z (c j) = A j (c j) := by
    dsimp [z]
    rw [dif_pos (show ∃ k, c k = c j from ⟨j, rfl⟩)]
    have he := (show ∃ k, c k = c j from ⟨j, rfl⟩).choose_spec
    rw [hc he]
  refine ⟨z, ?_⟩
  intro i
  have hAi : diff (A i) z = (shape i).image c := by
    ext k
    by_cases hk : ∃ j, c j = k
    · obtain ⟨j, rfl⟩ := hk
      have hmem : c j ∈ (shape i).image c ↔ j ∈ shape i := by
        constructor
        · intro h; obtain ⟨l, hl, he⟩ := Finset.mem_image.mp h; exact hc he ▸ hl
        · intro h; exact Finset.mem_image.mpr ⟨j, h, rfl⟩
      simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and, hz, hmem]
      exact hshape i j
    · have hmem : k ∉ (shape i).image c := by
        intro h; obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h; exact hk ⟨j, hj⟩
      have hzk : z k = A 0 k := dif_neg hk
      simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and, hzk,
        houtside i k hk, ne_eq, not_true_eq_false, hmem]
  refine ⟨hAi, ?_⟩
  have hci : c i ∉ (shape i).image c := by
    intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
    have hi : j = i := hc he
    subst j
    simp [shape] at hj
  rw [hflip, diff_flip, hAi, if_neg hci]

#print axioms distinct_direction_normal_form

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonDistinct
