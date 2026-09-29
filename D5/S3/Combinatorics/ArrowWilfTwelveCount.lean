/- GID: D5/S3/Combinatorics/ArrowWilfTwelveCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfTwelveCount
   mirror-E: none(waiver:decorated-gap-count-for-the-twelve-arrow-pattern)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: Avoiders of the twelve arrow pattern decompose by their largest Foata fixed point. -/

import D5.S3.Combinatorics.ArrowWilfGapData
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfTwelveCount

noncomputable section

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowWilfCountingCore
open D5.S3.Combinatorics.ArrowWilfFixedInsertion
open D5.S3.Combinatorics.ArrowWilfGapData

/-- The values `1,...,n`. -/
def fullSupport (n : ℕ) : Finset ℕ := (List.range' 1 n).toFinset

/-- The values strictly below `m`. -/
def lowerSupport (m : ℕ) : Finset ℕ := (List.range' 1 (m - 1)).toFinset

/-- The values from `m+1` through `n`. -/
def upperSupport (n m : ℕ) : Finset ℕ := (List.range' (m + 1) (n - m)).toFinset

/-- Gap labels following the upper fixed values. -/
def fixedGapLabels (H K : Finset ℕ) : Finset (Option ↑H) :=
  (H \ K).attach.map
    ⟨fun x => some ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩, by
      intro x y h
      simp only [Option.some.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext h⟩

/-- The decorated objects in the `m,k` summand of Theorem 3.1. -/
structure TwelveData (n m k : ℕ) where
  K : ↑((upperSupport n m).powersetCard k)
  sigma : ExactFixed (upperSupport n m) (upperSupport n m \ K.1)
  enough : (upperSupport n m \ K.1).card ≤ m - 1
  gaps : PositiveGapsOn (Option ↑(upperSupport n m)) (m - 1)
    (fixedGapLabels (upperSupport n m) K.1)

/-- The lower values in their forced decreasing order. -/
def lowerDescending (m : ℕ) : List ℕ := (List.range' 1 (m - 1)).reverse

/-- The list produced by the decorated construction (2.3). -/
def twelveList {n m k : ℕ} (d : TwelveData n m k) : List ℕ :=
  let sizes := gapSizes (upperSupport n m) d.sigma.1 d.gaps.1
  let blocks := sizes.splitLengths (lowerDescending m)
  blocks.headD [] ++ m :: afterBlocks d.sigma.1.1 blocks.tail

/-- The decorated construction uses every value of `[n]` exactly once. -/
theorem twelveList_perm {n m k : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (d : TwelveData n m k) :
    (twelveList d).Perm (List.range' 1 n) := by
  let H := upperSupport n m
  let sizes := gapSizes H d.sigma.1 d.gaps.1
  let blocks := sizes.splitLengths (lowerDescending m)
  have hsizes := gapSizes_length_sum H d.sigma.1 d.gaps.1
  have hHcard : H.card = n - m := by
    simp [H, upperSupport, List.toFinset_card_of_nodup List.nodup_range']
  have hsigmaLen : d.sigma.1.1.length = H.card := by
    have hp : d.sigma.1.1.Perm H.toList := by
      simpa [words, List.mem_permutations] using d.sigma.1.2
    simpa using hp.length_eq
  have hsizesLen : sizes.length = H.card + 1 := hsizes.1
  have hsizesSum : sizes.sum = m - 1 := hsizes.2
  have hlowLen : (lowerDescending m).length = m - 1 := by simp [lowerDescending]
  have hblocksLen : blocks.length = H.card + 1 := by
    simpa [blocks] using hsizesLen
  have htailLen : blocks.tail.length = d.sigma.1.1.length := by
    rw [List.length_tail, hblocksLen, hsigmaLen]
    omega
  have hflatten : blocks.flatten = lowerDescending m := by
    exact List.flatten_splitLengths _ _ (by rw [hlowLen, hsizesSum])
  have hinterleave := afterBlocks_perm htailLen
  have hblocks : blocks.headD [] ++ blocks.tail.flatten = lowerDescending m := by
    rw [← hflatten]
    rcases blocks with _ | ⟨b, bs⟩
    · simp at hblocksLen
    · simp
  have hfirst : (twelveList d).Perm
      (m :: d.sigma.1.1 ++ lowerDescending m) := by
    change (blocks.headD [] ++ m :: afterBlocks d.sigma.1.1 blocks.tail).Perm _
    have h1 := hinterleave.append_left (blocks.headD [] ++ [m])
    have hmove :
        (blocks.headD [] ++ [m] ++ d.sigma.1.1 ++ blocks.tail.flatten).Perm
          (m :: d.sigma.1.1 ++ blocks.headD [] ++ blocks.tail.flatten) := by
      have hs : (blocks.headD [] ++ (m :: d.sigma.1.1)).Perm
          ((m :: d.sigma.1.1) ++ blocks.headD []) := List.perm_append_comm
      simpa [List.append_assoc] using hs.append_right blocks.tail.flatten
    have h12 := h1.trans (by simpa only [List.append_assoc] using hmove)
    simpa only [List.singleton_append, List.append_assoc, hblocks] using h12
  apply hfirst.trans
  have hsigma : d.sigma.1.1.Perm (List.range' (m + 1) (n - m)) := by
    have hp : d.sigma.1.1.Perm H.toList := by
      simpa [words, List.mem_permutations] using d.sigma.1.2
    exact hp.trans (by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact H.nodup_toList
      · exact List.nodup_range'
      · simp [H, upperSupport])
  have hlow : (lowerDescending m).Perm (List.range' 1 (m - 1)) :=
    List.reverse_perm _
  have hpieces :
      (m :: d.sigma.1.1 ++ lowerDescending m).Perm
        (m :: List.range' (m + 1) (n - m) ++ List.range' 1 (m - 1)) :=
    (hsigma.append hlow).cons m
  apply hpieces.trans
  have hfirstNodup :
      (m :: List.range' (m + 1) (n - m) ++ List.range' 1 (m - 1)).Nodup := by
    rw [List.nodup_append']
    constructor
    · rw [List.nodup_cons]
      exact ⟨by simp only [List.mem_range']; omega, List.nodup_range'⟩
    constructor
    · exact List.nodup_range'
    intro x hx1 hx2
    simp [List.mem_range'] at hx1 hx2
    omega
  apply (List.perm_ext_iff_of_nodup hfirstNodup List.nodup_range').mpr
  intro x
  simp only [List.mem_cons, List.mem_append, List.mem_range', one_mul]
  constructor
  · rintro ((h | ⟨i, hi, h⟩) | ⟨i, hi, h⟩)
    · exact ⟨m - 1, by omega, by omega⟩
    · exact ⟨m + i, by omega, by omega⟩
    · exact ⟨i, by omega, h⟩
  · rintro ⟨i, hi, rfl⟩
    by_cases hlow : i < m - 1
    · exact Or.inr ⟨i, hlow, rfl⟩
    by_cases hmid : i = m - 1
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inr ⟨i - m, by omega, by omega⟩)

/-- The distinguished value is a singleton Foata block in every decorated word. -/
theorem twelveList_fixed_m {n m k : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (d : TwelveData n m k) : hat (twelveList d) m = m := by
  let H := upperSupport n m
  let sizes := gapSizes H d.sigma.1 d.gaps.1
  let blocks := sizes.splitLengths (lowerDescending m)
  let u := blocks.headD []
  have hperm := twelveList_perm hm hmn d
  have hnodup : (twelveList d).Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hmem : m ∈ twelveList d := hperm.mem_iff.mpr (by
    simp only [List.mem_range', one_mul]
    exact ⟨m - 1, by omega, by omega⟩)
  rw [← fixedSyntax_iff_hat_fixed hnodup hmem]
  have hsizes := gapSizes_length_sum H d.sigma.1 d.gaps.1
  have hlowLen : (lowerDescending m).length = m - 1 := by simp [lowerDescending]
  have hflatten : blocks.flatten = lowerDescending m := by
    exact List.flatten_splitLengths _ _ (by rw [hlowLen, hsizes.2])
  have hu : ∀ x ∈ u, x < m := by
    intro x hx
    have hxlow : x ∈ lowerDescending m := by
      rw [← hflatten]
      cases hb : blocks with
      | nil => simp [u, hb] at hx
      | cons b bs =>
          change x ∈ (b :: bs).flatten
          simp only [List.flatten_cons, List.mem_append]
          exact Or.inl (by simpa [u, hb] using hx)
    simp only [lowerDescending, List.mem_reverse, List.mem_range', one_mul] at hxlow
    rcases hxlow with ⟨i, hi, heq⟩
    omega
  have hsyntax : FixedSyntax m (twelveList d) ↔
      FixedSyntax m (m :: afterBlocks d.sigma.1.1 blocks.tail) := by
    change FixedSyntax m (u ++ (m :: afterBlocks d.sigma.1.1 blocks.tail)) ↔ _
    exact fixedSyntax_append_small_iff (by simp) hu
  rw [hsyntax]
  have hsigma : d.sigma.1.1.Perm H.toList := by
    simpa [words, List.mem_permutations] using d.sigma.1.2
  cases hs : d.sigma.1.1 with
  | nil => simp [afterBlocks, FixedSyntax]
  | cons x xs =>
      have hxH : x ∈ H := by
        have hx : x ∈ d.sigma.1.1 := by simp [hs]
        exact H.mem_toList.mp (hsigma.mem_iff.mp hx)
      have hmx : m < x := by
        simp [H, upperSupport, List.mem_range'] at hxH
        omega
      cases hb : blocks.tail with
      | nil => simp [hs, hb, afterBlocks, FixedSyntax, hmx]
      | cons b bs => simp [hs, hb, afterBlocks, FixedSyntax, hmx]

/-- Mandatory lower blocks destroy every upper singleton Foata block. -/
theorem twelveList_no_upper_fixed {n m k : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (d : TwelveData n m k) {g : ℕ} (hgH : g ∈ upperSupport n m) :
    hat (twelveList d) g ≠ g := by
  let H := upperSupport n m
  let sizes := gapSizes H d.sigma.1 d.gaps.1
  let blocks := sizes.splitLengths (lowerDescending m)
  let s := d.sigma.1.1
  have hperm := twelveList_perm hm hmn d
  have hnodup : (twelveList d).Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hsigma : s.Perm H.toList := by
    simpa [s, words, List.mem_permutations] using d.sigma.1.2
  have hsNodup : s.Nodup := hsigma.nodup_iff.mpr H.nodup_toList
  have hgs : g ∈ s := hsigma.mem_iff.mpr (by simpa using hgH)
  have hgmem : g ∈ twelveList d := hperm.mem_iff.mpr (by
    simp only [List.mem_range', one_mul]
    simp [upperSupport, List.mem_range'] at hgH
    rcases hgH with ⟨i, hi, heq⟩
    exact ⟨m + i, by omega, by omega⟩)
  have hsizes := gapSizes_length_sum H d.sigma.1 d.gaps.1
  have hlowLen : (lowerDescending m).length = m - 1 := by simp [lowerDescending]
  have hblocksLen : blocks.length = s.length + 1 := by
    rw [List.length_splitLengths, hsizes.1]
    simpa [s] using hsigma.length_eq.symm
  have htailLen : blocks.tail.length = s.length := by
    rw [List.length_tail, hblocksLen]
    omega
  have hflatten : blocks.flatten = lowerDescending m :=
    List.flatten_splitLengths _ _ (by rw [hlowLen, hsizes.2])
  have hblocks : blocks.headD [] ++ blocks.tail.flatten = lowerDescending m := by
    rw [← hflatten]
    cases blocks with
    | nil => simp
    | cons b bs => simp
  have hsmall : ∀ b ∈ blocks.tail, ∀ x ∈ b, x < g := by
    intro b hb x hx
    have hxlow : x ∈ lowerDescending m := by
      rw [← hblocks]
      exact List.mem_append.mpr (Or.inr (List.mem_flatten.mpr ⟨b, hb, hx⟩))
    simp only [lowerDescending, List.mem_reverse, List.mem_range', one_mul] at hxlow
    simp [upperSupport, List.mem_range'] at hgH
    rcases hxlow with ⟨i, hi, heq⟩
    rcases hgH with ⟨j, hj, hgj⟩
    omega
  have hafterMem : g ∈ afterBlocks s blocks.tail :=
    (afterBlocks_perm htailLen).mem_iff.mpr (by simp [hgs])
  have hu : ∀ x ∈ blocks.headD [] ++ [m], x < g := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hxlow : x ∈ lowerDescending m := by
        rw [← hblocks]
        exact List.mem_append.mpr (Or.inl hx)
      simp only [lowerDescending, List.mem_reverse, List.mem_range', one_mul] at hxlow
      simp [upperSupport, List.mem_range'] at hgH
      rcases hxlow with ⟨i, hi, heq⟩
      rcases hgH with ⟨j, hj, hgj⟩
      omega
    · simp only [List.mem_singleton] at hx
      subst x
      simp [upperSupport, List.mem_range'] at hgH
      rcases hgH with ⟨j, hj, hgj⟩
      omega
  have hgapLengths : blocks.tail.map List.length = s.map (gapAt H d.gaps.1) := by
    have h := List.map_splitLengths_length (lowerDescending m) sizes
      (by rw [hlowLen, hsizes.2])
    have ht := congrArg List.tail h
    simpa [blocks, sizes, gapSizes, s] using ht
  have hidx : s.idxOf g < s.length := List.idxOf_lt_length_of_mem hgs
  have hget : s.getD (s.idxOf g) 0 = g := by
    rw [List.getD_eq_getElem (l := s) 0 hidx, List.getElem_idxOf hidx]
  intro hfixed
  have hsyntax := (fixedSyntax_iff_hat_fixed hnodup hgmem).mpr hfixed
  have hprefix : FixedSyntax g (twelveList d) ↔
      FixedSyntax g (afterBlocks s blocks.tail) := by
    change FixedSyntax g (blocks.headD [] ++ m :: afterBlocks s blocks.tail) ↔ _
    simpa only [List.append_assoc, List.singleton_append] using
      (fixedSyntax_append_small_iff hafterMem hu)
  have hpair := (fixedSyntax_afterBlocks_iff hsNodup htailLen hgs hsmall).mp
    (hprefix.mp hsyntax)
  have hgap : g ∈ H \ d.K.1 := (d.sigma.2 g hgH).mp
    ((fixedSyntax_iff_hat_fixed hsNodup hgs).mp hpair.1)
  have hlabel : (some ⟨g, hgH⟩ : Option ↑H) ∈ fixedGapLabels H d.K.1 := by
    apply Finset.mem_map.mpr
    exact ⟨⟨g, hgap⟩, Finset.mem_attach _ _, rfl⟩
  have hpositive : 0 < gapAt H d.gaps.1 g := by
    unfold gapAt
    split_ifs with hx
    · simpa using d.gaps.2 (some ⟨g, hgH⟩) hlabel
    · exact (hx hgH).elim
  have hblockLen : (blocks.tail.getD (s.idxOf g) []).length = gapAt H d.gaps.1 g := by
    have h := congrArg (fun l : List ℕ => l.getD (s.idxOf g) 0) hgapLengths
    have hidxB : s.idxOf g < blocks.tail.length := by omega
    rw [List.getD_eq_getElem (l := blocks.tail.map List.length) 0 (by simpa using hidxB),
      List.getElem_map,
      List.getD_eq_getElem (l := s.map (gapAt H d.gaps.1)) 0 (by simpa using hidx),
      List.getElem_map, List.getElem_idxOf hidx] at h
    rw [List.getD_eq_getElem (l := blocks.tail) [] hidxB]
    exact h
  rw [hpair.2] at hblockLen
  simp at hblockLen
  omega

/-- The decorated construction lands in the first avoidance class. -/
theorem twelveList_avoids {n m k : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (d : TwelveData n m k) : ¬ Contains [1, 2] [(3, 3)] 3 (twelveList d) := by
  let H := upperSupport n m
  let sizes := gapSizes H d.sigma.1 d.gaps.1
  let blocks := sizes.splitLengths (lowerDescending m)
  let s := d.sigma.1.1
  let P : ℕ → Bool := fun x => decide (m ≤ x)
  have hsigma : s.Perm H.toList := by
    simpa [s, words, List.mem_permutations] using d.sigma.1.2
  have hsizes := gapSizes_length_sum H d.sigma.1 d.gaps.1
  have hlowLen : (lowerDescending m).length = m - 1 := by simp [lowerDescending]
  have hblocksLen : blocks.length = s.length + 1 := by
    rw [List.length_splitLengths, hsizes.1]
    simpa [s] using hsigma.length_eq.symm
  have htailLen : blocks.tail.length = s.length := by
    rw [List.length_tail, hblocksLen]
    omega
  have hflatten : blocks.flatten = lowerDescending m :=
    List.flatten_splitLengths _ _ (by rw [hlowLen, hsizes.2])
  have hblocks : blocks.headD [] ++ blocks.tail.flatten = lowerDescending m := by
    rw [← hflatten]
    cases blocks with
    | nil => simp
    | cons b bs => simp
  have hsmall : ∀ b ∈ blocks.tail, ∀ x ∈ b, ¬ P x := by
    intro b hb x hx
    have hxlow : x ∈ lowerDescending m := by
      rw [← hblocks]
      exact List.mem_append.mpr (Or.inr (List.mem_flatten.mpr ⟨b, hb, hx⟩))
    simp only [lowerDescending, List.mem_reverse, List.mem_range', one_mul] at hxlow
    rcases hxlow with ⟨i, hi, heq⟩
    simp only [P, decide_eq_true_eq]
    omega
  have hsu : ∀ x ∈ s, P x := by
    intro x hx
    have hxH : x ∈ H := Finset.mem_toList.mp (hsigma.mem_iff.mp hx)
    simp [P, H, upperSupport, List.mem_range'] at *
    omega
  have huf : (blocks.headD []).filter (fun x => !P x) = blocks.headD [] := by
    apply List.filter_eq_self.mpr
    intro x hx
    have hxlow : x ∈ lowerDescending m := by
      rw [← hblocks]
      exact List.mem_append.mpr (Or.inl hx)
    simp only [lowerDescending, List.mem_reverse, List.mem_range', one_mul] at hxlow
    rcases hxlow with ⟨i, hi, heq⟩
    simp [P]
    omega
  have hfiltered : (twelveList d).filter (fun x => !P x) = lowerDescending m := by
    have hinter := filter_afterBlocks_fillers P htailLen hsu hsmall
    change (blocks.headD [] ++ m :: afterBlocks s blocks.tail).filter (fun x => !P x) = _
    have hPm : (!P m) = false := by simp [P]
    simp only [List.filter_append, List.filter_cons, hPm, Bool.false_eq_true,
      ↓reduceIte, huf, hinter]
    exact hblocks
  intro hcontains
  rcases (contains_twelve_iff _).mp hcontains with
    ⟨a, b, f, hab, hbf, ha, hb, hf, hsub, hfixed⟩
  have hf_le : f ≤ m := by
    by_contra hn
    have hfm : m < f := by omega
    have hfrange : f ∈ List.range' 1 n :=
      (twelveList_perm hm hmn d).mem_iff.mp hf
    have hfH : f ∈ H := by
      simp only [H, upperSupport, List.mem_toFinset, List.mem_range', one_mul]
      simp only [List.mem_range', one_mul] at hfrange
      rcases hfrange with ⟨i, hi, heq⟩
      refine ⟨f - (m + 1), ?_, ?_⟩ <;> omega
    exact twelveList_no_upper_fixed hm hmn d hfH hfixed
  have habm : a < m ∧ b < m := by omega
  have hsub' := hsub.filter (fun x => !P x)
  have hpair : [a, b].Sublist (lowerDescending m) := by
    simpa [P, habm.1, habm.2, hfiltered] using hsub'
  have hdescending : (lowerDescending m).Pairwise (· > ·) := by
    rw [lowerDescending, List.pairwise_reverse]
    exact List.pairwise_lt_range'
  have hbad := hdescending.sublist hpair
  have hgt : a > b := (List.pairwise_cons.mp hbad).1 b (by simp)
  omega

/-- The decorated word as a word on the standard support. -/
def twelveWord {n m k : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (d : TwelveData n m k) : Word (fullSupport n) := by
  refine ⟨twelveList d, ?_⟩
  change twelveList d ∈ words (fullSupport n)
  rw [words, List.mem_toFinset, List.mem_permutations]
  exact (twelveList_perm hm hmn d).trans (by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_range'
    · exact (fullSupport n).nodup_toList
    · simp [fullSupport])

end

end D5.S3.Combinatorics.ArrowWilfTwelveCount
