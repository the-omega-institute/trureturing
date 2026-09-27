/- GID: D5/S3/Combinatorics/ArrowWilfTwelveSurject
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfTwelveSurject
   mirror-E: none(waiver:inverse-gap-construction-for-the-twelve-arrow-pattern)
   anchors: [mathlib/module/Mathlib.Data.Finsupp.Defs]
   utility: none
   digest: Skeleton-indexed lower blocks are converted to labelled gap vectors. -/

import D5.S3.Combinatorics.ArrowWilfTwelveInverse
import Mathlib.Data.Finsupp.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfTwelveSurject

noncomputable section

open D5.S3.Combinatorics.ArrowWilfCountingCore
open D5.S3.Combinatorics.ArrowWilfGapData
open D5.S3.Combinatorics.ArrowWilfTwelveCount
open D5.S3.Combinatorics.ArrowWilfTwelveInverse
open D5.S3.Combinatorics.ArrowWilfFixedInsertion
open D5.S3.Combinatorics.ArrowWilfDefs

/-- Assign a block length to each support value, and the initial length to `none`. -/
def blockLengths (H : Finset ℕ) (s : Word H) (u : List ℕ)
    (bs : List (List ℕ)) : Option ↑H →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun label => match label with
      | none => u.length
      | some x => (bs.getD (s.1.idxOf x.1) []).length)
    (by simp)

/-- The labelled length of a support entry is the length of its aligned block. -/
theorem blockLengths_aligned (H : Finset ℕ) (s : Word H) (u : List ℕ)
    (bs : List (List ℕ)) (hlen : bs.length = s.1.length) :
    s.1.map (fun x => if hx : x ∈ H then
        blockLengths H s u bs (some ⟨x, hx⟩) else 0) = bs.map List.length := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    have hp : s.1.Perm H.toList := by
      simpa [words, List.mem_permutations] using s.2
    have hsi : i < s.1.length := by simpa using hi
    have hbi : i < bs.length := by simpa using hj
    have hx : s.1[i] ∈ H := Finset.mem_toList.mp (hp.mem_iff.mp
      (List.getElem_mem hsi))
    have hidx : s.1.idxOf s.1[i] = i := by
      have hn : s.1.Nodup := hp.nodup_iff.mpr H.nodup_toList
      simpa using List.get_idxOf hn ⟨i, hsi⟩
    simp only [List.getElem_map]
    simp [blockLengths, hx, hidx]
    simp [List.getElem?_eq_getElem hbi]

/-- The labelled block lengths form a weak composition of the total filler length. -/
def gapsOfBlocks (H : Finset ℕ) (s : Word H) (u : List ℕ)
    (bs : List (List ℕ)) (hlen : bs.length = s.1.length) :
    GapsOn (Option ↑H) (u.length + bs.flatten.length) := by
  refine ⟨blockLengths H s u bs, ?_⟩
  rw [Finset.mem_finsuppAntidiag]
  constructor
  · have hp : s.1.Perm H.toList := by
      simpa [words, List.mem_permutations] using s.2
    have halign := blockLengths_aligned H s u bs hlen
    have hsumMap := (hp.map (fun x => if hx : x ∈ H then
      blockLengths H s u bs (some ⟨x, hx⟩) else 0)).sum_eq
    rw [halign] at hsumMap
    have hsumH : (bs.map List.length).sum =
        (∑ x : ↑H, blockLengths H s u bs (some x)) := by
      rw [hsumMap]
      rw [← List.sum_toFinset (fun x => if hx : x ∈ H then
        blockLengths H s u bs (some ⟨x, hx⟩) else 0) H.nodup_toList]
      rw [← Finset.sum_attach]
      rw [Finset.toList_toFinset]
      apply Finset.sum_congr rfl
      intro x hx
      simp
    change (∑ i : Option ↑H, blockLengths H s u bs i) =
      u.length + bs.flatten.length
    rw [Fintype.sum_option, ← hsumH]
    simp [blockLengths]
  · exact Finset.subset_univ _

/-- Filtering a standard-support word above `m` gives a word on the upper support. -/
def upperWord {n m : ℕ} (p : Word (fullSupport n)) : Word (upperSupport n m) := by
  let q := p.1.filter (fun x => decide (m < x))
  refine ⟨q, ?_⟩
  change q ∈ words (upperSupport n m)
  rw [words, List.mem_toFinset, List.mem_permutations]
  have hp : p.1.Perm (List.range' 1 n) := by
    have hp' : p.1.Perm (fullSupport n).toList := by
      simpa [words, List.mem_permutations] using p.2
    apply hp'.trans
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact (fullSupport n).nodup_toList
    · exact List.nodup_range'
    · simp [fullSupport]
  have hqnodup : q.Nodup := (hp.nodup_iff.mpr List.nodup_range').filter _
  apply (List.perm_ext_iff_of_nodup hqnodup
    (upperSupport n m).nodup_toList).mpr
  intro x
  simp only [q, List.mem_filter, decide_eq_true_eq, Finset.mem_toList,
    upperSupport, List.mem_toFinset, List.mem_range', one_mul]
  rw [hp.mem_iff]
  simp only [List.mem_range', one_mul]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hmx⟩
    exact ⟨1 + i - (m + 1), by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨m + i, ?_, ?_⟩, ?_⟩ <;> omega

/-- The lengths of a block partition reconstruct that partition from its flattening. -/
theorem splitLengths_map_length_flatten {α : Type*} (blocks : List (List α)) :
    (blocks.map List.length).splitLengths blocks.flatten = blocks := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
      simp [List.splitLengths_cons, ih]

/-- An upper singleton in the skeleton needs a nonempty following lower block. -/
theorem positive_block_of_no_upper_fixed
    (H : Finset ℕ) (m : ℕ) (s : Word H) (u : List ℕ)
    (bs : List (List ℕ)) (hlen : bs.length = s.1.length)
    (hu : ∀ x ∈ u, x < m)
    (hb : ∀ b ∈ bs, ∀ x ∈ b, x < m)
    (hs : ∀ x ∈ s.1, m < x)
    (hp : (u ++ m :: afterBlocks s.1 bs).Nodup)
    (hno : ∀ g ∈ H, hat (u ++ m :: afterBlocks s.1 bs) g ≠ g)
    (g : ℕ) (hg : g ∈ H) (hfixed : hat s.1 g = g) :
    0 < (bs.getD (s.1.idxOf g) []).length := by
  have hperm : s.1.Perm H.toList := by
    simpa [words, List.mem_permutations] using s.2
  have hsNodup : s.1.Nodup := hperm.nodup_iff.mpr H.nodup_toList
  have hgs : g ∈ s.1 := hperm.mem_iff.mpr (by simpa using hg)
  have haftermem : g ∈ afterBlocks s.1 bs :=
    (afterBlocks_perm hlen).mem_iff.mpr (by simp [hgs])
  have hprefix : ∀ x ∈ u ++ [m], x < g := by
    intro x hx
    rcases List.mem_append.mp hx with hxu | hxm
    · exact lt_trans (hu x hxu) (hs g hgs)
    · have : x = m := by simpa using hxm
      subst x
      exact hs g hgs
  have hsmall : ∀ b ∈ bs, ∀ x ∈ b, x < g := by
    intro b hbb x hx
    exact lt_trans (hb b hbb x hx) (hs g hgs)
  by_contra hpos
  have hempty : bs.getD (s.1.idxOf g) [] = [] := by
    cases hbget : bs.getD (s.1.idxOf g) [] with
    | nil => rfl
    | cons x xs =>
        have : 0 < (bs.getD (s.1.idxOf g) []).length := by
          rw [hbget]
          simp
        exact (hpos this).elim
  have hsyntax : FixedSyntax g (afterBlocks s.1 bs) :=
    (fixedSyntax_afterBlocks_iff hsNodup hlen hgs hsmall).mpr
      ⟨(fixedSyntax_iff_hat_fixed hsNodup hgs).mpr hfixed, hempty⟩
  have hfull : FixedSyntax g (u ++ m :: afterBlocks s.1 bs) := by
    simpa only [List.append_assoc, List.singleton_append] using
      (fixedSyntax_append_small_iff haftermem hprefix).mpr hsyntax
  have hmem : g ∈ u ++ m :: afterBlocks s.1 bs := by simp [haftermem]
  exact (hno g hg) ((fixedSyntax_iff_hat_fixed hp hmem).mp hfull)

/-- Positive prescribed coordinates cannot outnumber the total gap mass. -/
theorem positiveGaps_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℕ} (R : Finset ι) (g : GapsOn ι t)
    (hpositive : ∀ i ∈ R, 0 < g.1 i) : R.card ≤ t := by
  have hsum := (Finset.mem_finsuppAntidiag.mp g.2).1
  calc
    R.card = ∑ i ∈ R, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ R, g.1 i := Finset.sum_le_sum (by
      intro i hi
      exact hpositive i hi)
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), g.1 i :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ R)
    _ = t := hsum

/-- Every twelve avoider with specified largest fixed point is a decorated output. -/
theorem exists_twelveData_of_largest_fixed {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n)
    (p : Word (fullSupport n))
    (havoid : ¬ Contains [1, 2] [(3, 3)] 3 p.1)
    (hfixed : hat p.1 m = m)
    (hmax : ∀ g ∈ upperSupport n m, hat p.1 g ≠ g) :
    ∃ k, ∃ d : TwelveData n m k, twelveList d = p.1 := by
  let H := upperSupport n m
  obtain ⟨u, s, bs, hshape, hs, hblen, hu, hb, hflatten⟩ :=
    avoiding_twelve_normal_form hm hmn p hfixed havoid
  let w : Word H := upperWord p
  have hsw : s = w.1 := hs
  have hlen : bs.length = w.1.length := by rw [← hsw]; exact hblen
  have hwlarge : ∀ x ∈ w.1, m < x := by
    intro x hx
    have hperm : w.1.Perm H.toList := by
      simpa [words, List.mem_permutations] using w.2
    have hxH : x ∈ H := Finset.mem_toList.mp (hperm.mem_iff.mp hx)
    simp only [H, upperSupport, List.mem_toFinset, List.mem_range', one_mul] at hxH
    rcases hxH with ⟨i, hi, heq⟩
    omega
  have hpperm : p.1.Perm (List.range' 1 n) := by
    have hp' : p.1.Perm (fullSupport n).toList := by
      simpa [words, List.mem_permutations] using p.2
    apply hp'.trans
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact (fullSupport n).nodup_toList
    · exact List.nodup_range'
    · simp [fullSupport]
  have hshapeNodup : (u ++ m :: afterBlocks w.1 bs).Nodup := by
    rw [← hsw, ← hshape]
    exact hpperm.nodup_iff.mpr List.nodup_range'
  have hshapeNo : ∀ g ∈ H, hat (u ++ m :: afterBlocks w.1 bs) g ≠ g := by
    intro g hg
    rw [← hsw, ← hshape]
    exact hmax g hg
  let K : Finset ℕ := H.filter (fun g => hat w.1 g ≠ g)
  have hKsub : K ⊆ H := Finset.filter_subset _ _
  let k := K.card
  have hKmem : K ∈ H.powersetCard k := by
    simp [k, Finset.mem_powersetCard, hKsub]
  have hexact : ∀ g ∈ H, hat w.1 g = g ↔ g ∈ H \ K := by
    intro g hg
    simp [K, hg]
  have htotal : u.length + bs.flatten.length = m - 1 := by
    have hh := congrArg List.length hflatten
    simpa [lowerDescending, List.length_append] using hh
  let raw := gapsOfBlocks H w u bs hlen
  let g : GapsOn (Option ↑H) (m - 1) := ⟨raw.1, by
    have hraw := Finset.mem_finsuppAntidiag.mp raw.2
    apply Finset.mem_finsuppAntidiag.mpr
    exact ⟨by rw [← htotal]; exact hraw.1, hraw.2⟩⟩
  have hpositive : ∀ label ∈ fixedGapLabels H K, 0 < g.1 label := by
    intro label hlabel
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_map.mp hlabel
    subst label
    have hxK : x.1 ∈ H \ K := x.2
    have hxH : x.1 ∈ H := (Finset.mem_sdiff.mp hxK).1
    have hxfix : hat w.1 x.1 = x.1 := (hexact x.1 hxH).mpr hxK
    have hblock := positive_block_of_no_upper_fixed H m w u bs hlen
      hu hb hwlarge hshapeNodup hshapeNo x.1 hxH hxfix
    change 0 < g.1 (some ⟨x.1, hxH⟩)
    simpa [g, raw, gapsOfBlocks, blockLengths] using hblock
  have henough : (H \ K).card ≤ m - 1 := by
    have hcard : (fixedGapLabels H K).card = (H \ K).card := by
      simp [fixedGapLabels]
    rw [← hcard]
    exact positiveGaps_card_le (fixedGapLabels H K) g hpositive
  let d : TwelveData n m k :=
    { K := ⟨K, hKmem⟩
      sigma := ⟨w, hexact⟩
      enough := henough
      gaps := ⟨g, hpositive⟩ }
  refine ⟨k, d, ?_⟩
  have hgapSizes : gapSizes H w g = u.length :: bs.map List.length := by
    change gapSizes H w raw = _
    unfold gapSizes
    congr 1
    change w.1.map (fun x => if hx : x ∈ H then
      blockLengths H w u bs (some ⟨x, hx⟩) else 0) = bs.map List.length
    exact blockLengths_aligned H w u bs hlen
  have hblocks : (gapSizes H w g).splitLengths (lowerDescending m) = u :: bs := by
    rw [hgapSizes, ← hflatten]
    simpa using splitLengths_map_length_flatten (u :: bs)
  change ((gapSizes H w g).splitLengths (lowerDescending m)).headD [] ++
    m :: afterBlocks w.1
      ((gapSizes H w g).splitLengths (lowerDescending m)).tail = p.1
  rw [hblocks]
  simpa [hsw] using hshape.symm

end

end D5.S3.Combinatorics.ArrowWilfTwelveSurject
