/- GID: D5/S3/Combinatorics/ArrowWilfTwentyThreeCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfTwentyThreeCount
   mirror-E: none(waiver:decorated-gap-count-for-the-twenty-three-arrow-pattern)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: Avoiders of the twenty-three arrow pattern decompose by their smallest Foata fixed point. -/

import D5.S3.Combinatorics.ArrowWilfTwelveCount
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfTwentyThreeCount

noncomputable section

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowWilfCountingCore
open D5.S3.Combinatorics.ArrowWilfFixedInsertion
open D5.S3.Combinatorics.ArrowWilfGapData
open D5.S3.Combinatorics.ArrowWilfTwelveCount

/-- The decorated objects in the `m,r` summand of Theorem 5.5. -/
structure TwentyThreeData (n m r : ℕ) where
  R : ↑((lowerSupport m).powersetCard r)
  rho : Word R.1
  sigma : NoFixed (lowerSupport m \ R.1)
  gaps : GapsOn ↑(upperSupport n m) r

/-- The forced decreasing sequence of entries larger than `m`. -/
def upperDescending (n m : ℕ) : List ℕ :=
  (List.range' (m + 1) (n - m)).reverse

/-- Read gaps in the order of the decreasing upper skeleton. -/
def upperGapSizes (n m : ℕ) {r : ℕ}
    (g : GapsOn ↑(upperSupport n m) r) : List ℕ :=
  (upperDescending n m).map fun x =>
    if hx : x ∈ upperSupport n m then g.1 ⟨x, hx⟩ else 0

/-- The gaps consume all the chosen lower values. -/
theorem upperGapSizes_length_sum (n m : ℕ) {r : ℕ}
    (g : GapsOn ↑(upperSupport n m) r) :
    (upperGapSizes n m g).length = n - m ∧
      (upperGapSizes n m g).sum = r := by
  let H := upperSupport n m
  let read : ℕ → ℕ := fun x => if hx : x ∈ H then g.1 ⟨x, hx⟩ else 0
  have hperm : (upperDescending n m).Perm H.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_reverse.mpr List.nodup_range'
    · exact H.nodup_toList
    · simp [upperDescending, H, upperSupport]
  constructor
  · simp [upperGapSizes, upperDescending]
  · change ((upperDescending n m).map read).sum = r
    rw [(hperm.map read).sum_eq]
    rw [← List.sum_toFinset read H.nodup_toList, ← Finset.sum_attach]
    have hg := (Finset.mem_finsuppAntidiag.mp g.2).1
    rw [Finset.toList_toFinset]
    calc
      (∑ x ∈ H.attach, read x.1) = ∑ x : ↑H, g.1 x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [read]
      _ = r := hg

/-- The word produced by the decorated construction (3.3). -/
def twentyThreeList {n m r : ℕ} (d : TwentyThreeData n m r) : List ℕ :=
  let blocks := (upperGapSizes n m d.gaps).splitLengths d.rho.1
  d.sigma.1.1 ++ m :: afterBlocks (upperDescending n m) blocks

/-- Every decorated word uses the standard support exactly once. -/
theorem twentyThreeList_perm {n m r : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (d : TwentyThreeData n m r) :
    (twentyThreeList d).Perm (List.range' 1 n) := by
  let L := lowerSupport m \ d.R.1
  let H := upperSupport n m
  let U := upperDescending n m
  let blocks := (upperGapSizes n m d.gaps).splitLengths d.rho.1
  have hRcard : d.R.1.card = r := (Finset.mem_powersetCard.mp d.R.2).2
  have hRsub : d.R.1 ⊆ lowerSupport m :=
    (Finset.mem_powersetCard.mp d.R.2).1
  have hrho : d.rho.1.Perm d.R.1.toList := by
    simpa [words, List.mem_permutations] using d.rho.2
  have hsigma : d.sigma.1.1.Perm L.toList := by
    simpa [words, List.mem_permutations] using d.sigma.1.2
  have hU : U.Perm H.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_reverse.mpr List.nodup_range'
    · exact H.nodup_toList
    · simp [U, upperDescending, H, upperSupport]
  have hgap := upperGapSizes_length_sum n m d.gaps
  have hblocksLen : blocks.length = U.length := by
    simp [blocks, U, upperDescending, hgap.1]
  have hflatten : blocks.flatten = d.rho.1 := by
    apply List.flatten_splitLengths
    simp [hrho.length_eq, hRcard, hgap.2]
  have hinterleave : (afterBlocks U blocks).Perm (U ++ d.rho.1) := by
    simpa [hflatten] using afterBlocks_perm hblocksLen
  have hfirst : (twentyThreeList d).Perm
      (d.sigma.1.1 ++ m :: U ++ d.rho.1) := by
    simpa [twentyThreeList, blocks, U, List.append_assoc] using
      hinterleave.cons m |>.append_left d.sigma.1.1
  have hparts : (d.sigma.1.1 ++ m :: U ++ d.rho.1).Perm
      (L.toList ++ m :: H.toList ++ d.R.1.toList) := by
    simpa only [List.append_assoc, List.cons_append] using
      (hsigma.append ((hU.append hrho).cons m))
  have hpartNodup : (L.toList ++ m :: H.toList ++ d.R.1.toList).Nodup := by
    rw [List.append_assoc]
    rw [List.nodup_append']
    constructor
    · exact L.nodup_toList
    constructor
    · rw [List.cons_append, List.nodup_cons]
      constructor
      · simp [H, upperSupport, lowerSupport, List.mem_range']
        constructor
        · intro i hi
          omega
        · intro hxR
          have := hRsub hxR
          simp [lowerSupport, List.mem_range'] at this
          omega
      · rw [List.nodup_append']
        exact ⟨H.nodup_toList, d.R.1.nodup_toList,
            by
              intro x hxH hxR
              have hxUp : m < x := by
                simp [H, upperSupport, List.mem_range'] at hxH
                omega
              have hxLow : x < m := by
                have := hRsub (Finset.mem_toList.mp hxR)
                simp [lowerSupport, List.mem_range'] at this
                omega
              omega⟩
    intro x hxL hxTail
    have hxLow : x < m := by
      have hx := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hxL)).1
      simp [lowerSupport, List.mem_range'] at hx
      omega
    rcases List.mem_cons.mp hxTail with rfl | hxTail
    · omega
    rcases List.mem_append.mp hxTail with hxH | hxR
    · have hxUp : m < x := by
        simp [H, upperSupport, List.mem_range'] at hxH
        omega
      omega
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hxL)).2
        (Finset.mem_toList.mp hxR)
  apply hfirst.trans (hparts.trans ?_)
  apply (List.perm_ext_iff_of_nodup hpartNodup List.nodup_range').mpr
  intro x
  simp only [List.mem_append, List.mem_cons, Finset.mem_toList,
    List.mem_range', one_mul]
  constructor
  · rintro (((hxL | hxM | hxH) | hxR))
    · have hx := (Finset.mem_sdiff.mp hxL).1
      simp [lowerSupport, List.mem_range'] at hx
      rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i, by omega, rfl⟩
    · exact ⟨m - 1, by omega, by omega⟩
    · simp [H, upperSupport, List.mem_range'] at hxH
      rcases hxH with ⟨i, hi, rfl⟩
      exact ⟨m + i, by omega, by omega⟩
    · have hx := hRsub hxR
      simp [lowerSupport, List.mem_range'] at hx
      rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    by_cases hlow : i < m - 1
    · by_cases hR : i + 1 ∈ d.R.1
      · exact Or.inr (by simpa [Nat.add_comm] using hR)
      · apply Or.inl
        apply Or.inl
        apply Finset.mem_sdiff.mpr
        constructor
        · simp [lowerSupport, List.mem_range', hlow]
        · simpa [Nat.add_comm] using hR
    by_cases hmid : i = m - 1
    · exact Or.inl (Or.inr (Or.inl (by omega)))
    · exact Or.inl (Or.inr (Or.inr (by
        simp [H, upperSupport, List.mem_range']
        exact ⟨i - m, by omega, by omega⟩)))

/-- The decorated word has its distinguished singleton block at `m`. -/
theorem twentyThreeList_fixed_m {n m r : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (d : TwentyThreeData n m r) :
    hat (twentyThreeList d) m = m := by
  have hperm := twentyThreeList_perm hm hmn.le d
  have hnodup : (twentyThreeList d).Nodup :=
    hperm.nodup_iff.mpr List.nodup_range'
  have hmem : m ∈ twentyThreeList d := by
    exact hperm.mem_iff.mpr (by
      simp only [List.mem_range', one_mul]
      exact ⟨m - 1, by omega, by omega⟩)
  rw [← fixedSyntax_iff_hat_fixed hnodup hmem]
  let pre := d.sigma.1.1
  let tail := afterBlocks (upperDescending n m)
    ((upperGapSizes n m d.gaps).splitLengths d.rho.1)
  have hpre : ∀ x ∈ pre, x < m := by
    intro x hx
    have hp : pre.Perm (lowerSupport m \ d.R.1).toList := by
      simpa [pre, words, List.mem_permutations] using d.sigma.1.2
    have hxL := Finset.mem_toList.mp (hp.mem_iff.mp hx)
    have hxLow := (Finset.mem_sdiff.mp hxL).1
    simp [lowerSupport, List.mem_range'] at hxLow
    omega
  have hsyntax : FixedSyntax m (twentyThreeList d) ↔
      FixedSyntax m (m :: tail) := by
    change FixedSyntax m (pre ++ m :: tail) ↔ _
    exact fixedSyntax_append_small_iff (by simp) hpre
  rw [hsyntax]
  have hUlen : (upperDescending n m).length = n - m := by
    simp [upperDescending]
  cases hU : upperDescending n m with
  | nil =>
      simp [hU] at hUlen
      omega
  | cons x xs =>
      have hxH : x ∈ upperSupport n m := by
        have hUperm : (upperDescending n m).Perm (upperSupport n m).toList := by
          apply List.perm_of_nodup_nodup_toFinset_eq
          · exact List.nodup_reverse.mpr List.nodup_range'
          · exact (upperSupport n m).nodup_toList
          · simp [upperDescending, upperSupport]
        exact Finset.mem_toList.mp (hUperm.mem_iff.mp (by simp [hU]))
      have hmx : m < x := by
        simp [upperSupport, List.mem_range'] at hxH
        omega
      cases hb : (upperGapSizes n m d.gaps).splitLengths d.rho.1 with
      | nil => simp [tail, hU, hb, afterBlocks, FixedSyntax, hmx]
      | cons b bs => simp [tail, hU, hb, afterBlocks, FixedSyntax, hmx]

/-- A larger successor preserves the singleton-block status of a prefix entry. -/
theorem fixedSyntax_append_greater_iff {g m : ℕ} (hgm : g < m)
    {u v : List ℕ} (hg : g ∈ u) :
    FixedSyntax g (u ++ m :: v) ↔ FixedSyntax g u := by
  induction u with
  | nil => simp at hg
  | cons a u ih =>
      by_cases hag : a = g
      · subst a
        rcases u with _ | ⟨b, bs⟩
        · simp [FixedSyntax, hgm]
        · simp [FixedSyntax]
      · have hgu : g ∈ u := by
          rcases List.mem_cons.mp hg with h | h
          · exact (hag h.symm).elim
          · exact h
        rcases u with _ | ⟨b, bs⟩
        · simp at hgu
        · simpa only [List.cons_append, FixedSyntax, if_neg hag] using
            (and_congr_right fun _ => ih hgu)

/-- A singleton block below `m` must occur before an earlier `m`. -/
theorem fixedSyntax_append_greater_mem {g m : ℕ} (hgm : g < m)
    (u v : List ℕ) (h : FixedSyntax g (u ++ m :: v)) : g ∈ u := by
  have hlarge : ∀ w : List ℕ, ¬ FixedSyntax g (m :: w) := by
    intro w
    have hne : m ≠ g := (Nat.ne_of_lt hgm).symm
    cases w with
    | nil => simp [FixedSyntax, hne]
    | cons x xs =>
        simp [FixedSyntax, hne, Nat.not_lt_of_ge hgm.le]
  induction u with
  | nil => exact (hlarge v h).elim
  | cons a u ih =>
      by_cases hag : a = g
      · simp [hag]
      · cases u with
        | nil =>
            simp [FixedSyntax, hag] at h
            exact (hlarge v h.2).elim
        | cons b bs =>
            have hh : FixedSyntax g ((b :: bs) ++ m :: v) := by
              have hh' : a < g ∧ FixedSyntax g ((b :: bs) ++ m :: v) := by
                simpa only [List.cons_append, FixedSyntax, if_neg hag] using h
              exact hh'.2
            exact List.mem_cons_of_mem _ (ih hh)

/-- No value below the distinguished point is fixed in a decorated word. -/
theorem twentyThreeList_no_lower_fixed {n m r : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (d : TwentyThreeData n m r) {g : ℕ}
    (hgm : g < m) (hg : g ∈ twentyThreeList d) :
    hat (twentyThreeList d) g ≠ g := by
  have hperm := twentyThreeList_perm hm hmn d
  have hnodup : (twentyThreeList d).Nodup :=
    hperm.nodup_iff.mpr List.nodup_range'
  have hprePerm : d.sigma.1.1.Perm (lowerSupport m \ d.R.1).toList := by
    simpa [words, List.mem_permutations] using d.sigma.1.2
  intro hfix
  have hsyntax := (fixedSyntax_iff_hat_fixed hnodup hg).mpr hfix
  let tail := afterBlocks (upperDescending n m)
    ((upperGapSizes n m d.gaps).splitLengths d.rho.1)
  have hpre : g ∈ d.sigma.1.1 := by
    exact fixedSyntax_append_greater_mem hgm d.sigma.1.1 tail
      (by simpa [twentyThreeList, tail] using hsyntax)
  have hno : hat d.sigma.1.1 g ≠ g := d.sigma.2 g (by
    exact Finset.mem_toList.mp (hprePerm.mem_iff.mp hpre))
  have hpreNodup : d.sigma.1.1.Nodup :=
    hprePerm.nodup_iff.mpr (lowerSupport m \ d.R.1).nodup_toList
  have hprefixSyntax :=
    (fixedSyntax_append_greater_iff hgm hpre).mp hsyntax
  exact hno ((fixedSyntax_iff_hat_fixed hpreNodup hpre).mp hprefixSyntax)

/-- Filtering the decorated word above `m` recovers the decreasing upper skeleton. -/
theorem filter_twentyThreeList_upper {n m r : ℕ}
    (d : TwentyThreeData n m r) :
    (twentyThreeList d).filter (fun x => decide (m < x)) = upperDescending n m := by
  let H := upperSupport n m
  let U := upperDescending n m
  let blocks := (upperGapSizes n m d.gaps).splitLengths d.rho.1
  have hgap := upperGapSizes_length_sum n m d.gaps
  have hlen : blocks.length = U.length := by
    simp [blocks, U, upperDescending, hgap.1]
  have hrho : d.rho.1.Perm d.R.1.toList := by
    simpa [words, List.mem_permutations] using d.rho.2
  have hRcard : d.R.1.card = r := (Finset.mem_powersetCard.mp d.R.2).2
  have hRsub : d.R.1 ⊆ lowerSupport m :=
    (Finset.mem_powersetCard.mp d.R.2).1
  have hflat : blocks.flatten = d.rho.1 := by
    apply List.flatten_splitLengths
    simp [hrho.length_eq, hRcard, hgap.2]
  have hU : ∀ x ∈ U, decide (m < x) := by
    intro x hx
    simp only [decide_eq_true_eq]
    simp [U, upperDescending, List.mem_range'] at hx
    omega
  have hblocks : ∀ b ∈ blocks, ∀ x ∈ b, ¬ decide (m < x) := by
    intro b hb x hx
    have hxrho : x ∈ d.rho.1 := by
      rw [← hflat]
      exact List.mem_flatten.mpr ⟨b, hb, hx⟩
    have hxR := Finset.mem_toList.mp (hrho.mem_iff.mp hxrho)
    have hxLow := hRsub hxR
    simp [lowerSupport, List.mem_range'] at hxLow
    simpa using Nat.not_lt_of_ge (by omega : x ≤ m)
  have hpre : (d.sigma.1.1.filter (fun x => decide (m < x))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hp : d.sigma.1.1.Perm (lowerSupport m \ d.R.1).toList := by
      simpa [words, List.mem_permutations] using d.sigma.1.2
    have hxL := Finset.mem_toList.mp (hp.mem_iff.mp hx)
    have hxLow := (Finset.mem_sdiff.mp hxL).1
    simp [lowerSupport, List.mem_range'] at hxLow
    simpa using Nat.not_lt_of_ge (by omega : x ≤ m)
  have htail := filter_afterBlocks_skeleton (fun x => decide (m < x)) hlen hU hblocks
  simpa [twentyThreeList, U, blocks, hpre] using htail

/-- In the decorated word, larger values cannot occur in increasing order. -/
theorem no_increasing_upper_pair {n m r a b : ℕ}
    (d : TwentyThreeData n m r) (hma : m < a) (hab : a < b) :
    ¬ [a, b].Sublist (twentyThreeList d) := by
  intro hsub
  have hfilter := hsub.filter (fun x => decide (m < x))
  have hfiltered : [a, b].Sublist (upperDescending n m) := by
    simpa [hma, lt_trans hma hab, filter_twentyThreeList_upper d] using hfilter
  have hascending : (List.range' (m + 1) (n - m)).Pairwise (· < ·) := by
    exact List.pairwise_lt_range' (1 : ℕ) (by omega)
  have hdescending : (upperDescending n m).Pairwise (· > ·) := by
    simpa [upperDescending] using hascending.reverse
  have hpair := hdescending.sublist hfiltered
  have hba : b < a := by simpa using hpair
  omega

/-- The decorated construction avoids `(23; 1 -> 1)`. -/
theorem twentyThreeList_avoids {n m r : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (d : TwentyThreeData n m r) :
    ¬ Contains [2, 3] [(1, 1)] 3 (twentyThreeList d) := by
  rw [contains_twenty_three_iff]
  rintro ⟨f, a, b, hfa, hab, hf, ha, hb, hsub, hfix⟩
  have hfg : m ≤ f := by
    by_contra hnot
    have hfm : f < m := by omega
    exact twentyThreeList_no_lower_fixed hm hmn.le d hfm hf hfix
  exact no_increasing_upper_pair d (by omega) hab hsub

/-- The decorated word as an avoiding permutation of the standard support. -/
def twentyThreeAvoider {n m r : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (d : TwentyThreeData n m r) :
    {p : Word (fullSupport n) //
      ¬ Contains [2, 3] [(1, 1)] 3 p.1} := by
  refine ⟨⟨twentyThreeList d, ?_⟩, twentyThreeList_avoids hm hmn d⟩
  change twentyThreeList d ∈ words (fullSupport n)
  rw [words, List.mem_toFinset, List.mem_permutations]
  exact (twentyThreeList_perm hm hmn.le d).trans (by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_range'
    · exact (fullSupport n).nodup_toList
    · simp [fullSupport])

/-- Bundle the four independent choices after the selected lower subset is fixed. -/
def twentyThreeDataEquiv (n m r : ℕ) :
    TwentyThreeData n m r ≃
      Σ R : ↑((lowerSupport m).powersetCard r),
        Word R.1 × NoFixed (lowerSupport m \ R.1) ×
          GapsOn ↑(upperSupport n m) r where
  toFun d := ⟨d.R, d.rho, d.sigma, d.gaps⟩
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d with | mk R rest => cases rest with | mk rho rest =>
    cases rest
    rfl

noncomputable instance (n m r : ℕ) : Fintype (TwentyThreeData n m r) :=
  Fintype.ofEquiv _ (twentyThreeDataEquiv n m r).symm

/-- The decorated family has the `m,r` summand cardinality in (3.1). -/
theorem card_twentyThreeData (n m r : ℕ) :
    Fintype.card (TwentyThreeData n m r) =
      (m - 1).choose r * (n - m + r - 1).choose r *
        r.factorial * numDerangements (m - 1 - r) := by
  rw [Fintype.card_congr (twentyThreeDataEquiv n m r), Fintype.card_sigma]
  have hGap : Fintype.card (GapsOn ↑(upperSupport n m) r) =
      (n - m + r - 1).choose r := by
    rw [Fintype.card_coe]
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    rw [Finset.card_univ, Fintype.card_coe]
    unfold upperSupport
    rw [List.toFinset_card_of_nodup List.nodup_range']
    simp
  have hR : ∀ R : ↑((lowerSupport m).powersetCard r),
      Fintype.card (Word R.1) = r.factorial := by
    intro R
    rw [Fintype.card_coe]
    change (words R.1).card = r.factorial
    unfold words
    rw [List.toFinset_card_of_nodup
      (List.nodup_permutations _ R.1.nodup_toList)]
    have hcard : R.1.card = r := (Finset.mem_powersetCard.mp R.2).2
    simp [List.length_permutations, hcard]
  have hDer : ∀ R : ↑((lowerSupport m).powersetCard r),
      Fintype.card (NoFixed (lowerSupport m \ R.1)) =
        numDerangements (m - 1 - r) := by
    intro R
    rw [card_noFixed]
    have hRsub : R.1 ⊆ lowerSupport m :=
      (Finset.mem_powersetCard.mp R.2).1
    have hRcard : R.1.card = r := (Finset.mem_powersetCard.mp R.2).2
    rw [Finset.card_sdiff_of_subset hRsub, hRcard]
    simp [lowerSupport, List.toFinset_card_of_nodup List.nodup_range']
  simp_rw [Fintype.card_prod, hR, hDer, hGap]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard]
  simp [lowerSupport, List.toFinset_card_of_nodup List.nodup_range']
  ring

/-- The exceptional avoiding stratum has `n` as its only fixed point. -/
abbrev TopAvoiders (n : ℕ) :=
  {p : Word (fullSupport n) //
    ¬ Contains [2, 3] [(1, 1)] 3 p.1 ∧
      hat p.1 n = n ∧
      ∀ g ∈ fullSupport n, g < n → hat p.1 g ≠ g}

noncomputable instance (n : ℕ) : Fintype (TopAvoiders n) := by
  classical exact inferInstance

/-- Exact fixed-point data already counts the exceptional stratum. -/
def topAvoidersEquiv (n : ℕ) (hn : 1 ≤ n) :
    TopAvoiders n ≃ ExactFixed (fullSupport n) {n} where
  toFun p := ⟨p.1, by
    intro g hg
    constructor
    · intro hfix
      by_cases hgn : g = n
      · simp [hgn]
      · have hglt : g < n := by
          have hgRange : g ∈ (List.range' 1 n).toFinset := hg
          simp [List.mem_range'] at hgRange
          omega
        exact (p.2.2.2 g hg hglt hfix).elim
    · intro h
      simp only [Finset.mem_singleton] at h
      subst g
      exact p.2.2.1⟩
  invFun p := ⟨p.1, by
    have hnmem : n ∈ fullSupport n := by
      simp [fullSupport, List.mem_range']
      exact ⟨n - 1, by omega, by omega⟩
    have hnfixed : hat p.1.1 n = n := (p.2 n hnmem).mpr (by simp)
    have hsmall : ∀ g ∈ fullSupport n, g < n → hat p.1.1 g ≠ g := by
      intro g hg hglt hfix
      have := (p.2 g hg).mp hfix
      simp only [Finset.mem_singleton] at this
      omega
    refine ⟨?_, hnfixed, hsmall⟩
    rw [contains_twenty_three_iff]
    rintro ⟨f, a, b, hfa, hab, hf, ha, hb, hsub, hfix⟩
    have hfS : f ∈ fullSupport n := by
      have hp : p.1.1.Perm (fullSupport n).toList := by
        simpa [words, List.mem_permutations] using p.1.2
      exact Finset.mem_toList.mp (hp.mem_iff.mp hf)
    have hfn : f = n := by
      by_contra hne
      have hflt : f < n := by
        have := hfS
        simp [fullSupport, List.mem_range'] at this
        omega
      exact hsmall f hfS hflt hfix
    have haS : a ∈ fullSupport n := by
      have hp : p.1.1.Perm (fullSupport n).toList := by
        simpa [words, List.mem_permutations] using p.1.2
      exact Finset.mem_toList.mp (hp.mem_iff.mp ha)
    simp [fullSupport, List.mem_range'] at haS
    omega⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Every word can be parsed into a leading filler block and blocks after
    the entries selected by a Boolean skeleton predicate. -/
theorem interleave_decompose {α : Type*} (P : α → Bool) (q : List α) :
    ∃ pre bs, (∀ x ∈ pre, ¬ P x) ∧
      bs.length = (q.filter P).length ∧
      (∀ b ∈ bs, ∀ x ∈ b, ¬ P x) ∧
      q = pre ++ afterBlocks (q.filter P) bs := by
  induction q with
  | nil => exact ⟨[], [], by simp, by simp, by simp, by simp [afterBlocks]⟩
  | cons a q ih =>
      rcases ih with ⟨pre, bs, hpre, hlen, hbs, heq⟩
      by_cases ha : P a
      · refine ⟨[], pre :: bs, by simp, ?_, ?_, ?_⟩
        · simp [ha, hlen]
        · intro b hb x hx
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hpre x hx
          · exact hbs b hb x hx
        · conv_lhs => rw [heq]
          simp only [List.filter_cons, if_pos ha, List.nil_append, afterBlocks]
      · refine ⟨a :: pre, bs, ?_, ?_, hbs, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hpre x hx
        · simpa [ha] using hlen
        · conv_lhs => rw [heq]
          simp only [List.filter_cons, if_neg ha, List.cons_append]

/-- The characterization forces the entire upper-value subsequence into the
    unique descending order. -/
theorem upper_filter_eq_of_avoids {n m : ℕ} (hmn : m ≤ n)
    {p : Word (fullSupport n)}
    (havoid : ¬ Contains [2, 3] [(1, 1)] 3 p.1)
    (hm : m ∈ p.1) (hmfixed : hat p.1 m = m) :
    p.1.filter (fun x => decide (m < x)) = upperDescending n m := by
  have hp : p.1.Perm (List.range' 1 n) := by
    have hp' : p.1.Perm (fullSupport n).toList := by
      simpa [words, List.mem_permutations] using p.2
    exact hp'.trans (by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact (fullSupport n).nodup_toList
      · exact List.nodup_range'
      · simp [fullSupport])
  have hnodup : p.1.Nodup := hp.nodup_iff.mpr List.nodup_range'
  let q := p.1.filter (fun x => decide (m < x))
  let U := upperDescending n m
  have hqNodup : q.Nodup := hnodup.filter _
  have hUNodup : U.Nodup := by
    exact List.nodup_reverse.mpr List.nodup_range'
  have hperm : q.Perm U := by
    apply (List.perm_ext_iff_of_nodup hqNodup hUNodup).mpr
    intro x
    simp only [q, U, upperDescending, List.mem_filter, decide_eq_true_eq,
      List.mem_reverse, List.mem_range']
    constructor
    · rintro ⟨hmp, hmx⟩
      have hx := hp.mem_iff.mp hmp
      simp only [List.mem_range', one_mul] at hx
      rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i - m, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      constructor
      · apply hp.mem_iff.mpr
        simp only [List.mem_range', one_mul]
        exact ⟨m + i, by omega, by omega⟩
      · omega
  have hpair : q.Pairwise (· > ·) := by
    rw [List.pairwise_iff_forall_sublist]
    intro a b hab
    have habp : [a, b].Sublist p.1 :=
      hab.trans (by exact List.filter_sublist)
    have haQ : a ∈ q := hab.subset (by simp)
    have hbQ : b ∈ q := hab.subset (by simp)
    have hma : m < a := by simpa [q] using (List.mem_filter.mp haQ).2
    have hmb : m < b := by simpa [q] using (List.mem_filter.mp hbQ).2
    have hne : a ≠ b := by
      intro heq
      subst b
      have hdup : ¬ [a, a].Nodup := by simp
      exact hdup (hnodup.sublist habp)
    by_contra hnot
    have hablt : a < b := by omega
    have hba : [b, a].Sublist p.1 :=
      (avoids_twenty_three_iff hnodup).mp havoid m hm hmfixed a b hma hablt
        ((List.mem_filter.mp haQ).1) ((List.mem_filter.mp hbQ).1)
    exact pair_sublist_asymm hnodup hne ⟨habp, hba⟩
  have hUpair : U.Pairwise (· > ·) := by
    have h : (List.range' (m + 1) (n - m)).Pairwise (· < ·) :=
      List.pairwise_lt_range' (1 : ℕ) (by omega)
    simpa [U, upperDescending] using h.reverse
  exact hperm.eq_of_sortedGE hpair.sortedGT.sortedGE hUpair.sortedGT.sortedGE

/-- A specified list member splits a word into a prefix and a suffix. -/
theorem split_at_member {α : Type*} {x : α} {p : List α} (hx : x ∈ p) :
    ∃ u v, p = u ++ x :: v := by
  induction p with
  | nil => simp at hx
  | cons a p ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨[], p, rfl⟩
      · rcases ih hx with ⟨u, v, rfl⟩
        exact ⟨a :: u, v, rfl⟩

/-- A singleton block at `m` has only smaller entries before it, and the
    next entry, when present, is larger than `m`. -/
theorem fixedSyntax_split {m : ℕ} {u v : List ℕ}
    (hnot : m ∉ u) (h : FixedSyntax m (u ++ m :: v)) :
    (∀ x ∈ u, x < m) ∧
      (v = [] ∨ ∃ x xs, v = x :: xs ∧ m < x) := by
  induction u with
  | nil =>
      constructor
      · intro x hx; simp at hx
      · cases v with
        | nil => exact Or.inl rfl
        | cons x xs =>
            right
            exact ⟨x, xs, rfl, by simpa [FixedSyntax] using h⟩
  | cons a u ih =>
      have ham : a ≠ m := by
        intro heq
        exact hnot (by simp [heq])
      have hnotu : m ∉ u := by
        intro hmu
        exact hnot (by simp [hmu])
      have hrec : FixedSyntax m (u ++ m :: v) := by
        cases u with
        | nil =>
            have h' : a < m ∧ FixedSyntax m (m :: v) := by
              simpa [FixedSyntax, ham] using h
            exact h'.2
        | cons b bs =>
            have h' : a < m ∧ FixedSyntax m ((b :: bs) ++ m :: v) := by
              simpa only [List.cons_append, FixedSyntax, if_neg ham] using h
            exact h'.2
      have hlt : a < m := by
        cases u with
        | nil =>
            have h' : a < m ∧ FixedSyntax m (m :: v) := by
              simpa [FixedSyntax, ham] using h
            exact h'.1
        | cons b bs =>
            have h' : a < m ∧ FixedSyntax m ((b :: bs) ++ m :: v) := by
              simpa only [List.cons_append, FixedSyntax, if_neg ham] using h
            exact h'.1
      rcases ih hnotu hrec with ⟨hu, hv⟩
      constructor
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlt
        · exact hu x hx
      · exact hv

/-- If a word starts with a selected skeleton entry, its interleaving has no
    leading filler block. -/
theorem interleave_decompose_head {α : Type*} (P : α → Bool)
    {a : α} {q : List α} (ha : P a) :
    ∃ bs, bs.length = ((a :: q).filter P).length ∧
      (∀ b ∈ bs, ∀ x ∈ b, ¬ P x) ∧
      a :: q = afterBlocks ((a :: q).filter P) bs := by
  rcases interleave_decompose P (a :: q) with
    ⟨pre, bs, hpre, hlen, hbs, heq⟩
  cases pre with
  | nil => exact ⟨bs, hlen, hbs, by simpa using heq⟩
  | cons b pre =>
      have hab : a = b := by
        simpa only [List.cons_append, List.head?_cons, Option.some.injEq] using
          congrArg List.head? heq
      exact (hpre b (by simp) (hab ▸ ha)).elim

end

end D5.S3.Combinatorics.ArrowWilfTwentyThreeCount
