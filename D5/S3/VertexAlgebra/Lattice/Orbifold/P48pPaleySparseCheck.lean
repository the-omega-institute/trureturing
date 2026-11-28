/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseCheck
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseCheck
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite anchored Paley rows for the actual P48p ternary graph. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleyNormFour
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleySparseReduction
import OmegaBuild.Commands

/-!
# Anchored sparse rows for the P48p Paley graph

The finite checker below uses the actual `paleyC`.  Its computation is carried
out through the character-table matrix from `P48pTernaryPaleyGraph`, and the
private equality between the two matrices is retained as an explicit theorem.
The anchored list fixes the three directions `∞, 0, 1`, fixes the coefficient
at `∞` to `1`, and enumerates signed subsets of the remaining slopes.

Every normalized row of weight `3 + k` with these three occupied directions
belongs to the list. The one- and two-support shapes have separate lists.
The exact checks cover weights one through five. The unrestricted certificate
also takes the finite check for weight six as a hypothesis.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleySparseCheck

open scoped BigOperators Matrix
open P48pTernaryPaleyGraph (F3 paleyC)
open P48pPaleySparseReduction (rowSupport mem_rowSupport HasAnchoredSupport
  exists_anchored_paleyRow)

open private paleyCComputable paleyC_eq_computable from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48pTernaryPaleyGraph

abbrev Entry := Fin 24 × F3

private def freeSlopes : List (Fin 24) :=
  (List.finRange 24).filter (fun d => 2 ≤ d.val ∧ d.val ≤ 22)

private def signPairs : List (F3 × F3) :=
  [(1, 1), (1, 2), (2, 1), (2, 2)]

/- Exact signed subsets.  The first argument is traversed once, so every
   generated support has distinct slopes. -/
private def exactSignedSubsets : List (Fin 24) → ℕ → List (List Entry)
  | [], 0 => [[]]
  | [], _ + 1 => []
  | _ :: _, 0 => [[]]
  | d :: ds, k + 1 =>
      (exactSignedSubsets ds k).map (fun w => (d, 1) :: w) ++
      (exactSignedSubsets ds k).map (fun w => (d, 2) :: w) ++
      exactSignedSubsets ds (k + 1)

private def anchorWord (s : F3 × F3) (extra : List Entry) (d : Fin 24) : F3 :=
  if d = 23 then 1
  else if d = 0 then s.1
  else if d = 1 then s.2
  else ((extra.filter (fun e => e.1 = d)).map Prod.snd).sum

private def anchoredChunk (k : ℕ) (s : F3 × F3) : List (Fin 24 → F3) :=
  (exactSignedSubsets freeSlopes k).map (anchorWord s)

/-- The finite list for anchored supports with `3 + k` occupied directions. -/
def anchoredSupports (k : ℕ) : List (Fin 24 → F3) :=
  signPairs.flatMap (fun s => anchoredChunk k s)

/-- The sign pair and extra entries used to construct an enumerated row. -/
def IsAnchored (k : ℕ) (a : Fin 24 → F3) : Prop :=
  ∃ s, s ∈ signPairs ∧ ∃ extra,
    extra ∈ exactSignedSubsets freeSlopes k ∧ a = anchorWord s extra

theorem mem_anchoredSupports_iff (k : ℕ) (a : Fin 24 → F3) :
    a ∈ anchoredSupports k ↔ IsAnchored k a := by
  constructor
  · intro h
    simp only [anchoredSupports, List.mem_flatMap] at h
    rcases h with ⟨s, hs, h⟩
    rcases List.mem_map.mp h with ⟨extra, he, hvalue⟩
    exact ⟨s, hs, extra, he, hvalue.symm⟩
  · rintro ⟨s, hs, extra, he, rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨s, hs, ?_⟩
    exact List.mem_map.mpr ⟨extra, he, rfl⟩

private theorem signPair_cases (s : F3 × F3) (hs : s ∈ signPairs) :
    s = (1, 1) ∨ s = (1, 2) ∨ s = (2, 1) ∨ s = (2, 2) := by
  simpa [signPairs] using hs

private theorem eq_one_or_two_of_ne_zero {x : F3} (hx : x ≠ 0) : x = 1 ∨ x = 2 :=
  (by decide +kernel : ∀ x : F3, x ≠ 0 → x = 1 ∨ x = 2) x hx

private def signedSupport (a : Fin 24 → F3) (slopes : List (Fin 24)) : List Entry :=
  (slopes.filter fun d => decide (a d ≠ 0)).map fun d => (d, a d)

private theorem signedSupport_cons (a : Fin 24 → F3) (d : Fin 24) (ds : List (Fin 24)) :
    signedSupport a (d :: ds) =
      if a d = 0 then signedSupport a ds else (d, a d) :: signedSupport a ds := by
  by_cases hd : a d = 0 <;> simp [signedSupport, hd]

private theorem signedSupport_mem (a : Fin 24 → F3) (slopes : List (Fin 24)) :
    signedSupport a slopes ∈ exactSignedSubsets slopes (signedSupport a slopes).length := by
  induction slopes with
  | nil => simp [signedSupport, exactSignedSubsets]
  | cons d ds ih =>
    rw [signedSupport_cons]
    by_cases hd : a d = 0
    · rw [if_pos hd]
      cases hlength : (signedSupport a ds).length with
      | zero =>
        have hempty := List.length_eq_zero_iff.mp hlength
        simp [hempty, exactSignedSubsets]
      | succ k =>
        simp only [exactSignedSubsets, List.mem_append]
        exact Or.inr (by simpa only [hlength] using ih)
    · rw [if_neg hd, List.length_cons]
      simp only [exactSignedSubsets, List.mem_append]
      rcases eq_one_or_two_of_ne_zero hd with h | h
      · rw [h]
        exact Or.inl (Or.inl (List.mem_map_of_mem ih))
      · rw [h]
        exact Or.inl (Or.inr (List.mem_map_of_mem ih))

private theorem signedSupport_coeff (a : Fin 24 → F3) (slopes : List (Fin 24))
    (hslopes : slopes.Nodup) (i : Fin 24) :
    (((signedSupport a slopes).filter fun e => e.1 = i).map Prod.snd).sum =
      if i ∈ slopes then a i else 0 := by
  induction slopes with
  | nil => simp [signedSupport]
  | cons d ds ih =>
    obtain ⟨hd, hds⟩ := List.nodup_cons.mp hslopes
    have ht := ih hds
    rw [signedSupport_cons]
    by_cases hi : i = d
    · subst i
      rw [if_neg hd] at ht
      by_cases hz : a d = 0 <;> simp [hz, ht]
    · have hi' := Ne.symm hi
      by_cases hz : a d = 0 <;> simpa [hz, hi, hi'] using ht

private theorem freeSlopes_nodup : freeSlopes.Nodup :=
  (List.nodup_finRange 24).filter _

private theorem mem_freeSlopes_iff (d : Fin 24) :
    d ∈ freeSlopes ↔ d ≠ 23 ∧ d ≠ 0 ∧ d ≠ 1 :=
  (by decide +kernel : ∀ d : Fin 24, d ∈ freeSlopes ↔ d ≠ 23 ∧ d ≠ 0 ∧ d ≠ 1) d

private theorem signedSupport_length (a : Fin 24 → F3)
    (h23 : a 23 = 1) (h0 : a 0 ≠ 0) (h1 : a 1 ≠ 0) :
    (signedSupport a freeSlopes).length + 3 = hammingNorm a := by
  let anchors : Finset (Fin 24) := {23, 0, 1}
  have hsubset : anchors ⊆ rowSupport a := by
    intro i hi
    simp only [anchors, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact mem_rowSupport.mpr (by simp [h23])
    · exact mem_rowSupport.mpr h0
    · exact mem_rowSupport.mpr h1
  have hfree : (freeSlopes.filter fun d => decide (a d ≠ 0)).toFinset =
      rowSupport a \ anchors := by
    ext d
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_freeSlopes_iff,
      Finset.mem_sdiff, mem_rowSupport, anchors, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hcard := Finset.card_sdiff_add_card_eq_card hsubset
  have hanchors : anchors.card = 3 := by
    change ({23, 0, 1} : Finset (Fin 24)).card = 3
    decide +kernel
  rw [← hfree, List.toFinset_card_of_nodup (freeSlopes_nodup.filter _), hanchors] at hcard
  simpa [signedSupport, rowSupport, hammingNorm, List.length_map] using hcard

/-- A normalized row with three occupied anchors and `k` other occupied slopes
is included in the finite list. The remaining `Fin 24` coordinates are exactly
the slopes `2` through `22`. -/
theorem mem_anchoredSupports_of_shape {k : ℕ} {a : Fin 24 → F3}
    (h23 : a 23 = 1) (h0 : a 0 ≠ 0) (h1 : a 1 ≠ 0)
    (hweight : hammingNorm a = 3 + k) : a ∈ anchoredSupports k := by
  have hs : (a 0, a 1) ∈ signPairs := by
    rcases eq_one_or_two_of_ne_zero h0 with ha0 | ha0 <;>
      rcases eq_one_or_two_of_ne_zero h1 with ha1 | ha1 <;>
      simp [signPairs, ha0, ha1]
  have hlength : (signedSupport a freeSlopes).length = k := by
    have hcard := signedSupport_length a h23 h0 h1
    omega
  have hmem := signedSupport_mem a freeSlopes
  rw [hlength] at hmem
  apply (mem_anchoredSupports_iff k a).mpr
  refine ⟨(a 0, a 1), hs, signedSupport a freeSlopes, hmem, ?_⟩
  funext d
  by_cases hd23 : d = 23
  · subst d
    simpa [anchorWord] using h23
  by_cases hd0 : d = 0
  · subst d
    simp [anchorWord, hd23]
  by_cases hd1 : d = 1
  · subst d
    simp [anchorWord, hd23, hd0]
  have hd := (mem_freeSlopes_iff d).mpr ⟨hd23, hd0, hd1⟩
  have hcoeff := signedSupport_coeff a freeSlopes freeSlopes_nodup d
  simpa [anchorWord, hd23, hd0, hd1, hd] using hcoeff.symm

theorem anchored_support_shape {k : ℕ} {a : Fin 24 → F3}
    (ha : a ∈ anchoredSupports k) :
    a 23 = 1 ∧ a 0 ≠ 0 ∧ a 1 ≠ 0 := by
  obtain ⟨s, hs, extra, he, rfl⟩ := (mem_anchoredSupports_iff k _).mp ha
  rcases signPair_cases s hs with rfl | rfl | rfl | rfl <;>
    simp [anchorWord] <;> decide +kernel

private def paleyRowWeightComputed (a : Fin 24 → F3) : ℕ :=
  hammingNorm a + hammingNorm (a ᵥ* paleyCComputable)

/-- The actual row weight, with the character-table implementation exposed. -/
def paleyRowWeight (a : Fin 24 → F3) : ℕ :=
  hammingNorm a + hammingNorm (a ᵥ* paleyC)

theorem paleyRowWeight_eq_computed (a : Fin 24 → F3) :
    paleyRowWeight a = paleyRowWeightComputed a := by
  simp only [paleyRowWeight, paleyRowWeightComputed]
  rw [paleyC_eq_computable]

private def chunkCheck (k : ℕ) (s : F3 × F3) : Bool :=
  (anchoredChunk k s).all (fun a => decide (12 < paleyRowWeightComputed a))

private def supportCheck (k : ℕ) : Bool :=
  (anchoredSupports k).all (fun a => decide (hammingNorm a = 3 + k))

private theorem chunkCheck_sound {k : ℕ} {s : F3 × F3}
    (hcheck : chunkCheck k s = true) :
    ∀ a ∈ anchoredChunk k s, 12 < paleyRowWeight a := by
  intro a ha
  have hdec : decide (12 < paleyRowWeightComputed a) = true := by
    exact (List.all_eq_true.mp hcheck) a ha
  have hcomputed : 12 < paleyRowWeightComputed a := of_decide_eq_true hdec
  rw [paleyRowWeight_eq_computed a]
  exact hcomputed

/- The one- and two-support anchored cases are kept separate from the
   three-point normalization. -/
private def infinityWord (d : Fin 24) : F3 := if d = 23 then 1 else 0

private def infinityZeroWord (s : F3) (d : Fin 24) : F3 :=
  if d = 23 then 1 else if d = 0 then s else 0

def oneSupportChunk : List (Fin 24 → F3) := [infinityWord]

def twoSupportChunk : List (Fin 24 → F3) :=
  [infinityZeroWord 1, infinityZeroWord 2]

/-- The normalized row supported at infinity is the only one-support entry. -/
theorem mem_oneSupportChunk_of_shape {a : Fin 24 → F3}
    (h23 : a 23 = 1) (hs : rowSupport a = {23}) : a ∈ oneSupportChunk := by
  have ha : a = infinityWord := by
    funext d
    by_cases hd : d = 23
    · subst d
      simpa [infinityWord] using h23
    · have hz : a d = 0 := by
        by_contra hne
        have hm : d ∈ rowSupport a := mem_rowSupport.mpr hne
        rw [hs] at hm
        exact hd (Finset.mem_singleton.mp hm)
      simp [infinityWord, hd, hz]
  simp [oneSupportChunk, ha]

/-- The normalized row supported at infinity and zero is a two-support entry. -/
theorem mem_twoSupportChunk_of_shape {a : Fin 24 → F3}
    (h23 : a 23 = 1) (hs : rowSupport a = {23, 0}) : a ∈ twoSupportChunk := by
  have h0 : a 0 ≠ 0 := by
    apply mem_rowSupport.mp
    rw [hs]
    simp
  have ha : a = infinityZeroWord (a 0) := by
    funext d
    by_cases hd23 : d = 23
    · subst d
      simpa [infinityZeroWord] using h23
    by_cases hd0 : d = 0
    · subst d
      simp [infinityZeroWord, hd23]
    have hz : a d = 0 := by
      by_contra hne
      have hm : d ∈ rowSupport a := mem_rowSupport.mpr hne
      rw [hs] at hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hd23 h
      · exact hd0 (Finset.mem_singleton.mp h)
    simp [infinityZeroWord, hd23, hd0, hz]
  rcases eq_one_or_two_of_ne_zero h0 with h | h <;>
    rw [ha, h] <;> simp [twoSupportChunk]

private def oneSupportCheck : Bool :=
  oneSupportChunk.all (fun a => decide (12 < paleyRowWeightComputed a))

private def twoSupportCheck : Bool :=
  twoSupportChunk.all (fun a => decide (12 < paleyRowWeightComputed a))

set_option maxHeartbeats 6000000 in
theorem anchored_weight_one_check : oneSupportCheck = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_two_check : twoSupportCheck = true := by
  decide +kernel

theorem anchored_weight_one_sound {a : Fin 24 → F3} (ha : a ∈ oneSupportChunk) :
    12 < paleyRowWeight a := by
  have hdec : decide (12 < paleyRowWeightComputed a) = true :=
    (List.all_eq_true.mp anchored_weight_one_check) a ha
  have hcomputed : 12 < paleyRowWeightComputed a := of_decide_eq_true hdec
  rw [paleyRowWeight_eq_computed a]
  exact hcomputed

theorem anchored_weight_two_sound {a : Fin 24 → F3} (ha : a ∈ twoSupportChunk) :
    12 < paleyRowWeight a := by
  have hdec : decide (12 < paleyRowWeightComputed a) = true :=
    (List.all_eq_true.mp anchored_weight_two_check) a ha
  have hcomputed : 12 < paleyRowWeightComputed a := of_decide_eq_true hdec
  rw [paleyRowWeight_eq_computed a]
  exact hcomputed

set_option maxHeartbeats 6000000 in
theorem anchored_support_weight_three_check : supportCheck 0 = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_support_weight_four_check : supportCheck 1 = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_support_weight_five_check : supportCheck 2 = true := by
  decide +kernel

theorem anchored_support_weight_three {a : Fin 24 → F3}
    (ha : a ∈ anchoredSupports 0) : hammingNorm a = 3 := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp anchored_support_weight_three_check) a ha)

theorem anchored_support_weight_four {a : Fin 24 → F3}
    (ha : a ∈ anchoredSupports 1) : hammingNorm a = 4 := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp anchored_support_weight_four_check) a ha)

theorem anchored_support_weight_five {a : Fin 24 → F3}
    (ha : a ∈ anchoredSupports 2) : hammingNorm a = 5 := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp anchored_support_weight_five_check) a ha)

/- Each theorem below is one bounded kernel computation.  Splitting by the
   four sign pairs keeps the `decide` terms independent and small. -/
set_option maxHeartbeats 6000000 in
theorem anchored_weight_three_11 : chunkCheck 0 (1, 1) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_three_12 : chunkCheck 0 (1, 2) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_three_21 : chunkCheck 0 (2, 1) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_three_22 : chunkCheck 0 (2, 2) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_four_11 : chunkCheck 1 (1, 1) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_four_12 : chunkCheck 1 (1, 2) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_four_21 : chunkCheck 1 (2, 1) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_four_22 : chunkCheck 1 (2, 2) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_five_11 : chunkCheck 2 (1, 1) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_five_12 : chunkCheck 2 (1, 2) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_five_21 : chunkCheck 2 (2, 1) = true := by
  decide +kernel

set_option maxHeartbeats 6000000 in
theorem anchored_weight_five_22 : chunkCheck 2 (2, 2) = true := by
  decide +kernel

theorem anchored_weight_three_sound {a : Fin 24 → F3} (ha : a ∈ anchoredSupports 0) :
    12 < paleyRowWeight a := by
  simp only [anchoredSupports, List.mem_flatMap] at ha
  rcases ha with ⟨s, hs, hchunk⟩
  rcases signPair_cases s hs with rfl | rfl | rfl | rfl
  · exact chunkCheck_sound anchored_weight_three_11 _ hchunk
  · exact chunkCheck_sound anchored_weight_three_12 _ hchunk
  · exact chunkCheck_sound anchored_weight_three_21 _ hchunk
  · exact chunkCheck_sound anchored_weight_three_22 _ hchunk

theorem anchored_weight_four_sound {a : Fin 24 → F3} (ha : a ∈ anchoredSupports 1) :
    12 < paleyRowWeight a := by
  simp only [anchoredSupports, List.mem_flatMap] at ha
  rcases ha with ⟨s, hs, hchunk⟩
  rcases signPair_cases s hs with rfl | rfl | rfl | rfl
  · exact chunkCheck_sound anchored_weight_four_11 _ hchunk
  · exact chunkCheck_sound anchored_weight_four_12 _ hchunk
  · exact chunkCheck_sound anchored_weight_four_21 _ hchunk
  · exact chunkCheck_sound anchored_weight_four_22 _ hchunk

theorem anchored_weight_five_sound {a : Fin 24 → F3} (ha : a ∈ anchoredSupports 2) :
    12 < paleyRowWeight a := by
  simp only [anchoredSupports, List.mem_flatMap] at ha
  rcases ha with ⟨s, hs, hchunk⟩
  rcases signPair_cases s hs with rfl | rfl | rfl | rfl
  · exact chunkCheck_sound anchored_weight_five_11 _ hchunk
  · exact chunkCheck_sound anchored_weight_five_12 _ hchunk
  · exact chunkCheck_sound anchored_weight_five_21 _ hchunk
  · exact chunkCheck_sound anchored_weight_five_22 _ hchunk

/-- Every nonzero support of weight at most six has a weight-preserving
representative in one of the finite lists. -/
def SparseReduction : Prop :=
  ∀ a : Fin 24 → F3, a ≠ 0 → hammingNorm a ≤ 6 →
    (∃ b ∈ oneSupportChunk, paleyRowWeight b = paleyRowWeight a) ∨
    (∃ b ∈ twoSupportChunk, paleyRowWeight b = paleyRowWeight a) ∨
    (∃ k : Fin 4, ∃ b ∈ anchoredSupports k.val,
      paleyRowWeight b = paleyRowWeight a)

theorem sparseReduction : SparseReduction := by
  intro a ha hweight
  obtain ⟨_, b, _, hin, hout, hshape⟩ := exists_anchored_paleyRow a ha
  simp only [HasAnchoredSupport] at hshape
  obtain ⟨h23, hone, htwo, hthree⟩ := hshape
  have htotal : paleyRowWeight b = paleyRowWeight a := by
    simp only [paleyRowWeight, hin, hout]
  by_cases h1 : hammingNorm b = 1
  · exact Or.inl ⟨b, mem_oneSupportChunk_of_shape h23 (hone h1), htotal⟩
  by_cases h2 : hammingNorm b = 2
  · exact Or.inr (Or.inl ⟨b, mem_twoSupportChunk_of_shape h23 (htwo h2), htotal⟩)
  have hpos := hammingNorm_pos_iff.mpr ha
  have hlarge : 3 ≤ hammingNorm b := by omega
  obtain ⟨h0, hAnchorOne⟩ := hthree hlarge
  let k : Fin 4 := ⟨hammingNorm b - 3, by omega⟩
  have hk : hammingNorm b = 3 + k.val := by
    change hammingNorm b = 3 + (hammingNorm b - 3)
    omega
  exact Or.inr (Or.inr ⟨k, b, mem_anchoredSupports_of_shape h23 h0 hAnchorOne hk, htotal⟩)

/-- Exact missing finite sublemma for the remaining anchored support size. -/
def WeightSixCheck : Prop :=
  ∀ b ∈ anchoredSupports 3, 12 < paleyRowWeight b

theorem paley_small_support_certificate_of_reduction
    (hReduction : SparseReduction) (hSix : WeightSixCheck) :
    ∀ a : Fin 24 → F3, a ≠ 0 → hammingNorm a ≤ 6 →
      12 < paleyRowWeight a := by
  intro a ha hweight
  rcases hReduction a ha hweight with hOne | hTwo | hAnchored
  · rcases hOne with ⟨b, hb, hEq⟩
    rw [← hEq]
    exact anchored_weight_one_sound hb
  · rcases hTwo with ⟨b, hb, hEq⟩
    rw [← hEq]
    exact anchored_weight_two_sound hb
  · rcases hAnchored with ⟨k, b, hb, hEq⟩
    have hk := (by decide +kernel : ∀ k : Fin 4,
      k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3) k
    rcases hk with hk | hk | hk | hk
    · rw [hk] at hb
      rw [← hEq]
      exact anchored_weight_three_sound hb
    · rw [hk] at hb
      rw [← hEq]
      exact anchored_weight_four_sound hb
    · rw [hk] at hb
      rw [← hEq]
      exact anchored_weight_five_sound hb
    · rw [hk] at hb
      rw [← hEq]
      exact hSix b hb

/-- The weight-six finite check suffices for the unrestricted sparse bound. -/
theorem paley_small_support_certificate_of_weight_six (hSix : WeightSixCheck) :
    ∀ a : Fin 24 → F3, a ≠ 0 → hammingNorm a ≤ 6 →
      12 < paleyRowWeight a :=
  paley_small_support_certificate_of_reduction sparseReduction hSix

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleySparseCheck
