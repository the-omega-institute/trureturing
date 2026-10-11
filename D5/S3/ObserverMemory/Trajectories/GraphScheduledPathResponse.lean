/- GID: D5/S3/ObserverMemory/Trajectories/GraphScheduledPathResponse
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/GraphScheduledPathResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct canonical future responses with a two-symbol path-graph register. -/

import D5.S3.ObserverMemory.Trajectories.GraphScheduledColoringCorrectness
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.Trajectories.GraphScheduledPathResponse

open Finset GraphScheduledSelection GraphScheduledSelectionCapacity
  GraphScheduledColoringCorrectness
open scoped BigOperators Classical

/-- The actual first-selected prefix supplies its rank in the original dictionary.
The choice is unique; no accepting-word or suffix restriction is added to the dictionary. -/
def firstCode (r : ℕ) (G : SimpleGraph (Fin r)) (hr : 3 ≤ r) (rho : Bool)
    (w : Finset ℕ) : ℕ :=
  let c := (schedule_first_freeze G hr w).choose
  colexRank (if c < wordLength r then selectedFiber r G rho (bareAddress r rho c (atCut w c))
    else stopBlock r G rho (decide (wordLength r ∈ w))) (atCut w c)

/-- At the completed identity block, every compatible balanced tail has exactly
one occupied position. This function returns the canonical code for each such tail. -/
def identityResponse (r : ℕ) (G : SimpleGraph (Fin r)) (hr : 3 ≤ r)
    (i : Fin r) (j : Fin (tailLength r)) : ℕ :=
  firstCode r G hr true (edgePrefix r (i.val + 1) (j.val + 1))

private theorem first_code_at {r c : ℕ} (G : SimpleGraph (Fin r)) (hr : 3 ≤ r)
    (rho : Bool) (w : Finset ℕ) (hw : IsPrefix c w) (hs : FirstSelected r G c w) :
    firstCode r G hr rho w = colexRank (selectedFiber r G rho (bareAddress r rho c w)) w := by
  have hc := selection_before_end G hr w hs
  have he := (schedule_first_freeze G hr w).choose_spec.2 c
    ⟨hc, (first_selected_at_cut G w).mpr hs⟩
  have hcut : atCut w c = w := filter_eq_self.mpr (fun k hk => (mem_Icc.mp (hw hk)).2)
  simp only [firstCode, ← he, if_pos hc, hcut]

private theorem edge_test_response {r j : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r)
    (u v : Fin r) (he : edgeAt r j = some (u, v)) (hG : G.Adj u v) (i : Fin r) :
    firstCode r G hr true (edgePrefix r (i.val + 1) j) = if i = v then 1 else 0 := by
  have hir : i.val + 1 ≤ r := by have := i.isLt; omega
  by_cases hi : i = u ∨ i = v
  · have hret : Retained r G j (i.val + 1) :=
      ⟨hj, hjQ, u, v, he, hG, hi.elim (fun h => Or.inl (by rw [h]))
        (fun h => Or.inr (by rw [h]))⟩
    have hw := edge_prefix_subset (by omega : 1 ≤ i.val + 1) hir hj
    have hs := (early_first_selection_support G hr hj hjQ _ hw).mpr ⟨i.val + 1, hret, rfl⟩
    rw [first_code_at G hr true _ hw hs]
    have hb : bareAddress r true (identityEnd r + j) (edgePrefix r (i.val + 1) j) =
        earlyAddress r j := by
      have hz := edge_prefix_syndrome hr (by omega : 1 ≤ i.val + 1) hir hj hjQ true
      simp only [bareAddress, earlyAddress, edge_prefix_card (by omega : 1 ≤ i.val + 1) hir hj]
      congr 1
    rw [hb, early_rank_at_endpoint G hr hj hjQ u v he hG true i hi (Or.inl rfl)]
    simp
  · have hret : ¬ Retained r G j (i.val + 1) := by
      rintro ⟨_, _, a, b, hab, _, hm⟩
      have hab' : (a, b) = (u, v) := Option.some.inj (hab.symm.trans he)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab'
      apply hi
      rcases hm with hm | hm
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    have hd := delayed_target_bounds hr (by omega : 1 ≤ i.val + 1) hir hj (by omega)
    have hw := (edge_prefix_subset (by omega : 1 ≤ i.val + 1) hir hj).trans
      (Icc_subset_Icc_right
        (by omega : identityEnd r + j ≤ identityEnd r + delayedTarget r (i.val + 1) j))
    have hs := (delayed_selected_support G hr (by omega : 1 ≤ i.val + 1) hir hj
      (by omega) hret _ (edge_prefix_card (by omega : 1 ≤ i.val + 1) hir hj)).mpr rfl
    rw [first_code_at G hr true _ hw hs,
      (delayed_selected_fiber_and_rank G hr (by omega : 1 ≤ i.val + 1) hir hj
        (by omega) hret true).2, if_neg (fun h => hi (Or.inr h))]

private theorem pair_count_lt_tail (r : ℕ) : pairCount r < tailLength r := by
  have : pairCount r ≤ (r + 2) * pairCount r := by nlinarith
  dsimp [tailLength, lastTarget]
  omega

private theorem path_response_injective {r : ℕ} (hr : 3 ≤ r) :
    Function.Injective (identityResponse r (SimpleGraph.pathGraph r) hr) := by
  have separate (i a : Fin r) (hia : i < a) :
      identityResponse r (SimpleGraph.pathGraph r) hr i ≠
        identityResponse r (SimpleGraph.pathGraph r) hr a := by
    have ha : 1 ≤ a.val := by omega
    let u : Fin r := ⟨a.val - 1, by have := a.isLt; omega⟩
    have hua : u < a := by change a.val - 1 < a.val; omega
    have hG : (SimpleGraph.pathGraph r).Adj u a :=
      SimpleGraph.pathGraph_adj.mpr (Or.inl (by dsimp [u]; omega))
    obtain ⟨j, hj, hjQ, he⟩ := edge_at_complete u a hua
    let t : Fin (tailLength r) := ⟨j - 1, by have := pair_count_lt_tail r; omega⟩
    have ht : t.val + 1 = j := by dsimp [t]; omega
    intro h
    have hv := congrFun h t
    simp only [identityResponse, ht] at hv
    rw [edge_test_response _ hr hj hjQ u a he hG i,
      edge_test_response _ hr hj hjQ u a he hG a] at hv
    simp [ne_of_lt hia] at hv
  intro i a h
  rcases lt_trichotomy i a with hi | hi | hi
  · exact False.elim (separate i a hi h)
  · exact hi
  · exact False.elim (separate a i hi h.symm)

private theorem word_length_split {r : ℕ} (hr : 3 ≤ r) :
    wordLength r = identityEnd r + tailLength r := by
  have hR : 3 ≤ lastTarget r := by dsimp [lastTarget]; omega
  dsimp [wordLength, identityEnd, tailLength, halfLength, initialLength]
  omega

private theorem identity_domain {r : ℕ} (G : SimpleGraph (Fin r)) (hr : 3 ≤ r)
    (i : Fin r) :
    let p := insert (initialLength r + (i.val + 1)) (Icc 1 (initialLength r))
    bareAddress r true (identityEnd r) p = ⟨identityEnd r, halfLength r - 1, 1⟩ ∧
    (∀ d, d ≤ identityEnd r → ¬ Trigger r G d p) ∧
    (∀ t : Fin (tailLength r), Accepted r true (edgePrefix r (i.val + 1) (t.val + 1)) ∧
      atCut (edgePrefix r (i.val + 1) (t.val + 1)) (identityEnd r) = p) ∧
    (∀ w, Accepted r true w → atCut w (identityEnd r) = p →
      ∃ t : Fin (tailLength r), w = edgePrefix r (i.val + 1) (t.val + 1)) := by
  dsimp only
  let p := insert (initialLength r + (i.val + 1)) (Icc 1 (initialLength r))
  have hir : i.val + 1 ≤ r := by have := i.isLt; omega
  have hp : IsPrefix (identityEnd r) p := by
    intro a ha
    simp only [p, mem_insert, mem_Icc] at ha ⊢
    dsimp [identityEnd]; omega
  have hcard : p.card = initialLength r + 1 := by
    simp [p, card_insert_of_notMem, Nat.card_Icc]
  have hz : syndrome r true p = 1 := by
    simp [syndrome, initialSyndrome, coefficient, hcard, halfLength,
      Nat.cast_add, Nat.cast_ofNat]
    have h := CharTwo.add_self_eq_zero (initialLength r : ZMod 2)
    linear_combination (norm := ring_nf) h
    exact CharTwo.two_eq_zero
  have hs := (zero_deadline_support G hr (by omega : 1 ≤ i.val + 1) hir p
    (hp.trans (Icc_subset_Icc_right (by omega)))).mpr rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change bareAddress r true (identityEnd r) p = _
    simp [bareAddress, hcard, hz, halfLength]
  · intro d hd
    exact hs.2 d (by omega)
  · intro t
    have ht : 1 ≤ t.val + 1 := by omega
    have htc : identityEnd r + (t.val + 1) ≤ wordLength r := by
      rw [word_length_split hr]
      have := t.isLt
      omega
    refine ⟨⟨(edge_prefix_subset (by omega : 1 ≤ i.val + 1) hir ht).trans
      (Icc_subset_Icc_right htc), edge_prefix_card (by omega : 1 ≤ i.val + 1) hir ht, ?_⟩, ?_⟩
    · have hcard' := edge_prefix_card (by omega : 1 ≤ i.val + 1) hir ht
      simpa [syndrome, initialSyndrome, coefficient, hcard'] using
        CharTwo.add_self_eq_zero (halfLength r : ZMod 2)
    · simpa [Nat.add_assoc] using edge_cut_wait i ht
        (by dsimp [identityEnd]; omega : initialLength r + i.val + 1 ≤ identityEnd r)
        (by omega : identityEnd r < identityEnd r + (t.val + 1))
  · intro w hw hwp
    change atCut w (identityEnd r) = p at hwp
    have hsub : p ⊆ w := by rw [← hwp]; exact filter_subset _ _
    have hc : (w \ p).card = 1 := by
      rw [card_sdiff_of_subset hsub, hw.2.1, hcard]
      simp [halfLength]
    obtain ⟨a, ha⟩ := card_eq_one.mp hc
    have ham : a ∈ w \ p := by rw [ha]; simp
    obtain ⟨haw, hap⟩ := mem_sdiff.mp ham
    have hEa : identityEnd r < a := by
      by_contra hn
      apply hap
      rw [← hwp]
      exact mem_filter.mpr ⟨haw, by omega⟩
    have han := (mem_Icc.mp (hw.1 haw)).2
    let t : Fin (tailLength r) := ⟨a - identityEnd r - 1, by
      rw [word_length_split hr] at han
      omega⟩
    have hat : identityEnd r + (t.val + 1) = a := by dsimp [t]; omega
    refine ⟨t, ?_⟩
    have hu := sdiff_union_of_subset hsub
    rw [ha] at hu
    change w = insert (identityEnd r + (t.val + 1)) p
    rw [hat, ← singleton_union]
    exact hu.symm

/-- The path family has r distinct canonical future responses from its identity
pasts, while blind and pre-decision registers both need exactly two symbols. -/
theorem path_response_gap (r : ℕ) (hr : 3 ≤ r) :
    Function.Injective (identityResponse r (SimpleGraph.pathGraph r) hr) ∧
    ((univ : Finset (Fin r)).image (identityResponse r (SimpleGraph.pathGraph r) hr)).card = r ∧
    blindCapacity r (SimpleGraph.pathGraph r) = 2 ∧
      preCapacity r (SimpleGraph.pathGraph r) = 2 ∧
    ∀ i : Fin r,
      let p := insert (initialLength r + (i.val + 1)) (Icc 1 (initialLength r))
      bareAddress r true (identityEnd r) p = ⟨identityEnd r, halfLength r - 1, 1⟩ ∧
      (∀ d, d ≤ identityEnd r → ¬ Trigger r (SimpleGraph.pathGraph r) d p) ∧
      (∀ t : Fin (tailLength r), Accepted r true (edgePrefix r (i.val + 1) (t.val + 1)) ∧
        atCut (edgePrefix r (i.val + 1) (t.val + 1)) (identityEnd r) = p) ∧
      (∀ w, Accepted r true w → atCut w (identityEnd r) = p →
        ∃ t : Fin (tailLength r), w = edgePrefix r (i.val + 1) (t.val + 1)) := by
  have hinj := path_response_injective hr
  have hedge : ∃ u v, (SimpleGraph.pathGraph r).Adj u v :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩
  have hcap := blind_pre_capacity_eq_chromatic (SimpleGraph.pathGraph r) hr hedge
  rw [SimpleGraph.chromaticNumber_pathGraph r (by omega)] at hcap
  refine ⟨hinj, ?_, hcap.1, hcap.2, identity_domain _ hr⟩
  rw [card_image_of_injective _ hinj]
  simp

end D5.S3.ObserverMemory.Trajectories.GraphScheduledPathResponse
