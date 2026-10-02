/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv
   mirror-E: none(waiver:minimum-maximum-word-class-correspondence)
   anchors: []
   utility: none
   digest: Minimum and suffix maximum yield reversible encodings of the first and third classes. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenClasses
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenMinimum
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenUnimodal
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWordEncoding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenACEquiv

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open Fishburn.FishburnBasicPrefixes
open FishburnTenSevenWords FishburnTenSevenWords.Letter FishburnTenSevenWordEncoding
open FishburnTenSevenClasses FishburnTenSevenMinimum FishburnTenSevenUnimodal

def ACParameters (third : Bool) (size : ℕ) :=
  Unit ⊕ Σ peak : {peak : ℕ // 2 ≤ peak ∧ peak ≤ size},
    ↥(if third then languageC (peak.val - 2) else languageA (peak.val - 2))

theorem ac_equivalence (third : Bool) (size : ℕ) (hsize : 1 ≤ size) :
    ∃ correspondence :
        (avoiders size (if third then
          [[1, 3, 2, 4], [1, 4, 2, 3], [3, 1, 2, 4]] else
          [[1, 3, 2, 4], [2, 1, 4, 3], [1, 4, 2, 3]])) ≃ ACParameters third size,
      (correspondence.symm (Sum.inl ())).val = (List.range' 1 size).reverse ∧
      ∀ peak word,
        (correspondence.symm (Sum.inr ⟨peak, word⟩)).val =
          reconstruct size (fun index : Fin (peak.val - 2) => word.val.getD index.val d) := by
  classical
  let patterns := if third then
    [[1, 3, 2, 4], [1, 4, 2, 3], [3, 1, 2, 4]] else
    [[1, 3, 2, 4], [2, 1, 4, 3], [1, 4, 2, 3]]
  let language (length : ℕ) := if third then languageC length else languageA length
  let piece (parts : List ℕ × List ℕ × List ℕ) (letter : Letter) :=
    match letter with
    | d => parts.1
    | i => parts.2.1
    | j => parts.2.2
  have hblocks (length : ℕ) (word : Fin length → Letter) (letter : Letter) (value : ℕ) :
      value ∈ piece (blocks word) letter ↔
        ∃ index : Fin length, word index = letter ∧ index.val + 2 = value := by
    cases letter <;> simp [piece, blocks]
  have hblock_index (length : ℕ) (word : Fin length → Letter)
      (letter : Letter) (index : Fin length) :
      index.val + 2 ∈ piece (blocks word) letter ↔ word index = letter := by
    rw [hblocks]
    constructor
    · rintro ⟨other, hletter, heq⟩
      have hsame : other = index := Fin.ext (by omega)
      simpa only [hsame] using hletter
    · exact fun hletter => ⟨index, hletter, rfl⟩
  have hbefore (length : ℕ) (word : Fin length → Letter)
      (earlier later : Letter) (hne : earlier ≠ later) :
      Before earlier later (List.ofFn word) ↔
        ∀ first second : Fin length,
          word first = earlier → word second = later → first.val < second.val := by
    simp only [Before, List.pairwise_ofFn]
    constructor
    · intro hp first second hfirst hsecond
      by_contra hnot
      have hneindex : first.val ≠ second.val := by
        intro heq
        have hsame : first = second := Fin.ext heq
        exact hne (hfirst.symm.trans (hsame ▸ hsecond))
      have hlt : second < first := by change second.val < first.val; omega
      rcases hp hlt with hbad | hbad
      · exact hbad hsecond
      · exact hbad hfirst
    · intro hp first second hlt
      by_cases hfirst : word first = later
      · right
        intro hsecond
        have hreverse := hp second first hsecond hfirst
        change first.val < second.val at hlt
        omega
      · exact Or.inl hfirst
  have hofFn (length : ℕ) (word : List Letter) (hlen : word.length = length) :
      List.ofFn (fun index : Fin length => word.getD index.val d) = word := by
    apply List.ext_getElem (by simp [hlen])
    intro index hleft hright
    simp only [List.getElem_ofFn, List.getD_eq_getElem word d hright]
  have hgetFn (length : ℕ) (word : Fin length → Letter) :
      (fun index : Fin length => (List.ofFn word).getD index.val d) = word := by
    funext index
    rw [List.getD_eq_getElem _ d (by simp)]
    simp
  have hlength (length : ℕ) (word : language length) : word.val.length = length := by
    cases third <;> exact word.property.1
  have hrange_sorted (start length : ℕ) : (List.range' start length).Pairwise (· < ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro first second hfirst hsecond hlt
    simp only [List.getElem_range']
    omega
  have htransport (length : ℕ) (hbound : length + 2 ≤ size)
      (word : Fin length → Letter) :
      reconstruct size word ∈ avoiders size patterns ↔ List.ofFn word ∈ language length := by
    let parts := blocks word
    let upper := (List.range' (length + 3) (size - (length + 2))).reverse
    let decreasing := upper ++ parts.1
    obtain ⟨hperm, hdec, hinc, htrail, hsmall⟩ :=
      (reconstruct_permutation size length hbound).2 word
    have hshape := shape_classes_iff size decreasing parts.2.1 parts.2.2 (length + 2)
      hperm hdec hinc htrail (fun value hv => (hsmall value hv).2)
    have hchain :
        (List.ofFn word).IsChain (fun left right => left ≠ j ∨ right ≠ i) ↔
          ∀ value ∈ parts.2.2, value + 1 ∉ parts.2.1 := by
      constructor
      · intro hc value hvalue hnext
        obtain ⟨first, hfirst, rfl⟩ := (hblocks length word j value).mp hvalue
        obtain ⟨second, hsecond, heq⟩ := (hblocks length word i _).mp hnext
        have hindex : second.val = first.val + 1 := by omega
        have hnextbound : first.val + 1 < (List.ofFn word).length := by
          simp only [List.length_ofFn]
          omega
        have hrel := List.isChain_iff_getElem.mp hc first.val hnextbound
        simp only [List.getElem_ofFn] at hrel
        have hsame : (⟨first.val + 1, by omega⟩ : Fin length) = second :=
          Fin.ext hindex.symm
        simp [hsame, hfirst, hsecond] at hrel
      · intro hc
        apply List.isChain_iff_getElem.mpr
        intro index hindex
        simp only [List.length_ofFn] at hindex
        simp only [List.getElem_ofFn]
        by_cases hj : word ⟨index, by omega⟩ = j
        · right
          intro hi
          apply hc (index + 2)
          · exact (hblock_index length word j ⟨index, by omega⟩).mpr hj
          · have hmem := (hblock_index length word i ⟨index + 1, hindex⟩).mpr hi
            convert hmem using 1
        · exact Or.inl hj
    have hA : Before j d (List.ofFn word) ↔
        ∀ value ∈ parts.2.2, ∀ earlier ∈ decreasing, value < earlier := by
      rw [hbefore length word j d (by decide)]
      constructor
      · intro hp value hvalue earlier hearlier
        obtain ⟨first, hfirst, rfl⟩ := (hblocks length word j value).mp hvalue
        rcases List.mem_append.mp hearlier with hupper | hlow
        · have hu := List.mem_range'_1.mp (List.mem_reverse.mp hupper)
          omega
        · obtain ⟨second, hsecond, rfl⟩ := (hblocks length word d earlier).mp hlow
          have := hp first second hfirst hsecond
          omega
      · intro hp first second hfirst hsecond
        have hj := (hblock_index length word j first).mpr hfirst
        have hd := (hblock_index length word d second).mpr hsecond
        have := hp _ hj _ (List.mem_append_right _ hd)
        omega
    have hC : Before d i (List.ofFn word) ↔
        ∀ value ∈ decreasing, value < length + 2 →
          ∀ later ∈ parts.2.1, value < later := by
      rw [hbefore length word d i (by decide)]
      constructor
      · intro hp value hvalue hlow later hlater
        obtain ⟨second, hsecond, rfl⟩ := (hblocks length word i later).mp hlater
        rcases List.mem_append.mp hvalue with hupper | hsmall
        · have hu := List.mem_range'_1.mp (List.mem_reverse.mp hupper)
          omega
        · obtain ⟨first, hfirst, rfl⟩ := (hblocks length word d value).mp hsmall
          have := hp first second hfirst hsecond
          omega
      · intro hp first second hfirst hsecond
        have hd := (hblock_index length word d first).mpr hfirst
        have hi := (hblock_index length word i second).mpr hsecond
        have := hp _ (List.mem_append_right _ hd) (by omega) _ hi
        omega
    cases third
    · change _ ↔ (List.ofFn word).length = length ∧ _ ∧ _
      simp only [List.length_ofFn, true_and, hchain, hA]
      exact hshape.1
    · change _ ↔ (List.ofFn word).length = length ∧ _ ∧ _
      simp only [List.length_ofFn, true_and, hchain, hC]
      exact hshape.2
  let descending := (List.range' 1 size).reverse
  have hdescending : descending.Pairwise (· > ·) :=
    List.pairwise_reverse.mpr (hrange_sorted 1 size)
  have hdescending_perm : descending.Perm (List.range' 1 size) := List.reverse_perm _
  have hdescending_member : descending ∈ avoiders size patterns := by
    refine ⟨hdescending_perm, ?_, ?_⟩
    · intro first later hgap hbound hbad
      have hlt := List.pairwise_iff_getElem.mp hdescending first (first + 1)
        (by omega) (by omega) (by omega)
      rw [← List.getD_eq_getElem descending 0 (by omega),
        ← List.getD_eq_getElem descending 0 (by omega)] at hlt
      omega
    · have hnot (pattern : List ℕ) (low high : ℕ)
          (hpair : [low, high].Sublist pattern)
          (hlt : ∀ values : ℕ → ℕ,
            (∀ rank, 1 ≤ rank → rank < 4 → values rank < values (rank + 1)) →
              values low < values high) :
          ¬ ArrowWilfDefs.Contains pattern [] 4 descending := by
        rintro ⟨values, hstep, _, hsub, _⟩
        have hp := hdescending.sublist ((hpair.map values).trans hsub)
        have hreverse : values high < values low := by simpa using hp
        have hforward := hlt values hstep
        omega
      intro pattern hpattern
      have h1324 : ¬ NonnestingDefs.Occurs [1, 3, 2, 4] descending := by
        apply hnot _ 1 3 (by simp)
        intro values hs
        exact lt_trans (hs 1 (by omega) (by omega)) (hs 2 (by omega) (by omega))
      have h2143 : ¬ NonnestingDefs.Occurs [2, 1, 4, 3] descending := by
        apply hnot _ 1 4 (by simp)
        intro values hs
        exact lt_trans (hs 1 (by omega) (by omega))
          (lt_trans (hs 2 (by omega) (by omega)) (hs 3 (by omega) (by omega)))
      have h1423 : ¬ NonnestingDefs.Occurs [1, 4, 2, 3] descending := by
        apply hnot _ 1 4 (by simp)
        intro values hs
        exact lt_trans (hs 1 (by omega) (by omega))
          (lt_trans (hs 2 (by omega) (by omega)) (hs 3 (by omega) (by omega)))
      have h3124 : ¬ NonnestingDefs.Occurs [3, 1, 2, 4] descending := by
        apply hnot _ 3 4 (by simp)
        exact fun values hs => hs 3 (by omega) (by omega)
      cases third <;>
        simp only [patterns, Bool.false_eq_true, if_false, if_true,
          List.mem_cons, List.not_mem_nil, or_false] at hpattern <;>
        rcases hpattern with rfl | rfl | rfl
      all_goals assumption
  let peakOf (permutation : List ℕ) :=
    ((permutation.dropWhile (fun value => value != 1)).toFinset).sup id
  have hdrop_construct (length : ℕ) (hb : length + 2 ≤ size)
      (word : Fin length → Letter) :
      (reconstruct size word).dropWhile (fun value => value != 1) =
        1 :: ((blocks word).2.1 ++ (length + 2) :: (blocks word).2.2) := by
    let initial := (List.range' (length + 3) (size - (length + 2))).reverse ++ (blocks word).1
    have hp := ((reconstruct_permutation size length hb).2 word).1
    have hn := hp.nodup_iff.mpr (List.nodup_range' 1)
    change (initial ++ 1 :: ((blocks word).2.1 ++
      (length + 2) :: (blocks word).2.2)).Nodup at hn
    have hnot : 1 ∉ initial := by
      intro hmem
      exact (List.nodup_append.mp hn).2.2 _ hmem _ (by simp) rfl
    have hprefix (value : ℕ) (hvalue : value ∈ initial) : (value != 1) = true := by
      simp only [bne_iff_ne]
      exact fun heq => hnot (heq ▸ hvalue)
    change (initial ++ 1 :: ((blocks word).2.1 ++
      (length + 2) :: (blocks word).2.2)).dropWhile _ = _
    rw [List.dropWhile_append_of_pos hprefix]
    simp
  have hpeak_construct (length : ℕ) (hb : length + 2 ≤ size)
      (word : Fin length → Letter) : peakOf (reconstruct size word) = length + 2 := by
    change ((reconstruct size word).dropWhile _).toFinset.sup id = _
    rw [hdrop_construct length hb word]
    apply le_antisymm
    · apply Finset.sup_le
      intro value hv
      change value ≤ length + 2
      have hmem := List.mem_toFinset.mp hv
      simp only [List.mem_cons, List.mem_append] at hmem
      rcases hmem with rfl | hi | rfl | hj
      · omega
      · exact le_of_lt (((reconstruct_permutation size length hb).2 word).2.2.2.2 _
          (List.mem_append_left _ hi)).2
      · rfl
      · exact le_of_lt (((reconstruct_permutation size length hb).2 word).2.2.2.2 _
          (List.mem_append_right _ hj)).2
    · exact Finset.le_sup (f := id) (b := length + 2)
        (List.mem_toFinset.mpr (by simp))
  have hpeak_descending : peakOf descending = 1 := by
    have hone : 1 ∈ descending := hdescending_perm.mem_iff.mpr
      (List.mem_range'_1.mpr (by omega))
    obtain ⟨initial, tail, heq⟩ := List.mem_iff_append.mp hone
    have htail : tail = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro value hv
      have htail_dec : (1 :: tail).Pairwise (· > ·) :=
        (List.pairwise_append.mp (heq ▸ hdescending)).2.1
      have hdec : value < 1 := (List.pairwise_cons.mp htail_dec).1 value hv
      have hrange := hdescending_perm.mem_iff.mp (heq ▸ List.mem_append_right initial
        (List.mem_cons_of_mem 1 hv))
      have hpos := (List.mem_range'_1.mp hrange).1
      omega
    have hnot : 1 ∉ initial := by
      have hn := hdescending_perm.nodup_iff.mpr (List.nodup_range' 1)
      rw [heq] at hn
      exact fun hmem => (List.nodup_append.mp hn).2.2 _ hmem _ (by simp) rfl
    change (descending.dropWhile _).toFinset.sup id = _
    rw [heq, htail, List.dropWhile_append_of_pos
      (fun value hv => by simp only [bne_iff_ne]; exact fun he => hnot (he ▸ hv))]
    simp
  let realize (data : ACParameters third size) : List ℕ := match data with
    | Sum.inl _ => descending
    | Sum.inr ⟨peak, word⟩ =>
      reconstruct size (fun index : Fin (peak.val - 2) => word.val.getD index.val d)
  have hrealize_member (data : ACParameters third size) :
      realize data ∈ avoiders size patterns := by
    rcases data with trivial | ⟨peak, word⟩
    · exact hdescending_member
    · have hb : peak.val - 2 + 2 ≤ size := by have := peak.property; omega
      apply (htransport _ hb _).mpr
      simpa only [hofFn _ word.val (hlength _ word)] using word.property
  have hrealize_peak (peak : {peak : ℕ // 2 ≤ peak ∧ peak ≤ size})
      (word : language (peak.val - 2)) : peakOf (realize (Sum.inr ⟨peak, word⟩)) = peak.val := by
    have hb : peak.val - 2 + 2 ≤ size := by have := peak.property; omega
    have heq := hpeak_construct _ hb
      (fun index : Fin (peak.val - 2) => word.val.getD index.val d)
    simpa only [realize, Nat.sub_add_cancel peak.property.1] using heq
  have hinjective : Function.Injective realize := by
    rintro (trivial | ⟨⟨peak, hp⟩, word⟩) (other | ⟨⟨top, ht⟩, letters⟩) heq
    · cases trivial
      cases other
      rfl
    · have he := congrArg peakOf heq
      rw [hpeak_descending, hrealize_peak] at he
      change 1 = top at he
      omega
    · have he := congrArg peakOf heq
      rw [hrealize_peak, hpeak_descending] at he
      change peak = 1 at he
      omega
    · have he := congrArg peakOf heq
      rw [hrealize_peak, hrealize_peak] at he
      change peak = top at he
      subst top
      have hb : peak - 2 + 2 ≤ size := by omega
      have hw := congrArg (encodePermutation (size := peak - 2)) heq
      change encodePermutation (reconstruct size _) = encodePermutation (reconstruct size _) at hw
      rw [(reconstruct_permutation size (peak - 2) hb).1 _,
        (reconstruct_permutation size (peak - 2) hb).1 _] at hw
      have hwords : word.val = letters.val := by
        rw [← hofFn _ word.val (hlength _ word), ← hofFn _ letters.val (hlength _ letters)]
        exact congrArg List.ofFn hw
      have hs : word = letters := Subtype.ext hwords
      subst letters
      rfl
  have hsurjective (permutation : List ℕ) (hmember : permutation ∈ avoiders size patterns) :
      ∃ data : ACParameters third size, realize data = permutation := by
    obtain ⟨hperm, hfish, havoid⟩ := hmember
    have h1324 : ¬ NonnestingDefs.Occurs [1, 3, 2, 4] permutation := by
      apply havoid
      cases third <;> simp [patterns]
    have h1423 : ¬ NonnestingDefs.Occurs [1, 4, 2, 3] permutation := by
      apply havoid
      cases third <;> simp [patterns]
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hvalues (value : ℕ) : value ∈ permutation ↔ 1 ≤ value ∧ value ≤ size := by
      rw [hperm.mem_iff, List.mem_range'_1]
      omega
    obtain ⟨before, tail, heq⟩ := List.mem_iff_append.mp ((hvalues 1).mpr (by omega))
    subst permutation
    let suffix := 1 :: tail
    have hbefore_sub : before.Sublist (before ++ suffix) := List.sublist_append_left _ _
    have hsuffix_sub : suffix.Sublist (before ++ suffix) := List.sublist_append_right _ _
    have hsuffix_nodup := hnodup.sublist hsuffix_sub
    have honebound : before.length < (before ++ suffix).length := by simp [suffix]
    have hone : (before ++ suffix).getD before.length 0 = 1 := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [suffix]
    have hdec := prefix_through_one_decreasing size (before ++ suffix) hperm hfish
      before.length honebound hone
    have hbefore_dec : before.Pairwise (· > ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro first second hfirst hsecond hlt
      have hr := hdec first second hlt (by omega)
      rw [List.getD_append before suffix 0 second hsecond,
        List.getD_append before suffix 0 first hfirst,
        List.getD_eq_getElem _ _ hfirst, List.getD_eq_getElem _ _ hsecond] at hr
      exact hr
    by_cases hempty : tail = []
    · subst tail
      have hwhole_dec : (before ++ [1]).Pairwise (· > ·) := by
        apply List.pairwise_iff_getElem.mpr
        intro first second hfirst hsecond hlt
        have hr := hdec first second hlt (by simp at hsecond; omega)
        rw [List.getD_eq_getElem _ _ hfirst, List.getD_eq_getElem _ _ hsecond] at hr
        exact hr
      refine ⟨Sum.inl (), ?_⟩
      exact hdescending.eq_of_mem_iff hwhole_dec (fun value =>
        hdescending_perm.mem_iff.trans hperm.mem_iff.symm)
    have hafter (index : ℕ) :
        (before ++ suffix).getD (before.length + index) 0 = suffix.getD index 0 := by
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    have htests := minimum_pattern_tests size (before ++ suffix) hperm hfish
      before.length honebound hone
    have h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] suffix := by
      change ¬ ArrowWilfDefs.Contains [2, 1, 3] [] 3 suffix
      rintro ⟨values, hstep, _, hsub, _⟩
      obtain ⟨positions, hembed⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let first := positions ⟨0, by simp⟩
      let second := positions ⟨1, by simp⟩
      let last := positions ⟨2, by simp⟩
      have h12 : first.val < second.val :=
        positions.strictMono (by change (0 : ℕ) < 1; omega)
      have h23 : second.val < last.val :=
        positions.strictMono (by change (1 : ℕ) < 2; omega)
      have hfirst : suffix.getD first.val 0 = values 2 := by
        simpa [first, List.getD_eq_getElem] using (hembed ⟨0, by simp⟩).symm
      have hsecond : suffix.getD second.val 0 = values 1 := by
        simpa [second, List.getD_eq_getElem] using (hembed ⟨1, by simp⟩).symm
      have hlast : suffix.getD last.val 0 = values 3 := by
        simpa [last, List.getD_eq_getElem] using (hembed ⟨2, by simp⟩).symm
      have hpos := ((hvalues (values 1)).mp (hsuffix_sub.subset
        (hsub.subset (by simp)))).1
      have hfirst_pos : 0 < first.val := by
        by_contra hnot
        have hz : first.val = 0 := by omega
        have hlt : values 1 < values 2 := hstep 1 (by omega) (by omega)
        rw [hz] at hfirst
        change 1 = values 2 at hfirst
        omega
      apply h1324
      apply htests.1.mpr
      refine ⟨before.length + first.val, before.length + second.val,
        before.length + last.val, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · simpa only [List.length_append] using Nat.add_lt_add_left last.isLt before.length
      · rw [hafter, hafter, hsecond, hfirst]
        exact hstep 1 (by omega) (by omega)
      · rw [hafter, hafter, hfirst, hlast]
        exact hstep 2 (by omega) (by omega)
    have h312 : ¬ NonnestingDefs.Occurs [3, 1, 2] suffix := by
      change ¬ ArrowWilfDefs.Contains [3, 1, 2] [] 3 suffix
      rintro ⟨values, hstep, _, hsub, _⟩
      obtain ⟨positions, hembed⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let first := positions ⟨0, by simp⟩
      let second := positions ⟨1, by simp⟩
      let last := positions ⟨2, by simp⟩
      have h12 : first.val < second.val :=
        positions.strictMono (by change (0 : ℕ) < 1; omega)
      have h23 : second.val < last.val :=
        positions.strictMono (by change (1 : ℕ) < 2; omega)
      have hfirst : suffix.getD first.val 0 = values 3 := by
        simpa [first, List.getD_eq_getElem] using (hembed ⟨0, by simp⟩).symm
      have hsecond : suffix.getD second.val 0 = values 1 := by
        simpa [second, List.getD_eq_getElem] using (hembed ⟨1, by simp⟩).symm
      have hlast : suffix.getD last.val 0 = values 2 := by
        simpa [last, List.getD_eq_getElem] using (hembed ⟨2, by simp⟩).symm
      have hpos := ((hvalues (values 1)).mp (hsuffix_sub.subset
        (hsub.subset (by simp)))).1
      have hfirst_pos : 0 < first.val := by
        by_contra hnot
        have hz : first.val = 0 := by omega
        have hlt : values 1 < values 3 :=
          lt_trans (hstep 1 (by omega) (by omega)) (hstep 2 (by omega) (by omega))
        rw [hz] at hfirst
        change 1 = values 3 at hfirst
        omega
      apply h1423
      apply htests.2.1.mpr
      refine ⟨before.length + first.val, before.length + second.val,
        before.length + last.val, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · simpa only [List.length_append] using Nat.add_lt_add_left last.isLt before.length
      · rw [hafter, hafter, hsecond, hlast]
        exact hstep 1 (by omega) (by omega)
      · rw [hafter, hafter, hlast, hfirst]
        exact hstep 2 (by omega) (by omega)
    have hnonempty : tail.toFinset.Nonempty := by
      obtain ⟨value, hvalue⟩ := List.exists_mem_of_ne_nil tail hempty
      exact ⟨value, List.mem_toFinset.mpr hvalue⟩
    let peak := tail.toFinset.max' hnonempty
    have hpeak_mem : peak ∈ tail := List.mem_toFinset.mp (Finset.max'_mem _ _)
    have hpeak_range := (hvalues peak).mp (hsuffix_sub.subset (List.mem_cons_of_mem 1 hpeak_mem))
    have htail_not_one : 1 ∉ tail := (List.nodup_cons.mp hsuffix_nodup).1
    have hpeak_ge : 2 ≤ peak := by
      have hne : peak ≠ 1 := fun heq => htail_not_one (heq ▸ hpeak_mem)
      omega
    have hpeak_le : peak ≤ size := hpeak_range.2
    have htail_bound (value : ℕ) (hv : value ∈ tail) : value ≤ peak :=
      Finset.le_max' _ _ (List.mem_toFinset.mpr hv)
    obtain ⟨increasing, trailing, htail_eq⟩ := List.mem_iff_append.mp hpeak_mem
    have htail_nodup := (List.nodup_cons.mp hsuffix_nodup).2
    have hpeak_not : peak ∉ increasing ++ trailing := by
      rw [htail_eq] at htail_nodup
      obtain ⟨_, hright, hcross⟩ := List.nodup_append.mp htail_nodup
      intro hmem
      rcases List.mem_append.mp hmem with hleft | hright_mem
      · exact hcross _ hleft _ (by simp) rfl
      · exact (List.nodup_cons.mp hright).1 hright_mem
    have hrest_mem (value : ℕ) (hv : value ∈ increasing ++ trailing) : value ∈ tail := by
      rw [htail_eq]
      rcases List.mem_append.mp hv with hinc | htrail
      · exact List.mem_append_left _ hinc
      · exact List.mem_append_right _ (List.mem_cons_of_mem peak htrail)
    have hsmall (value : ℕ) (hv : value ∈ increasing ++ trailing) : value < peak := by
      have hle := htail_bound value (hrest_mem value hv)
      have hne : value ≠ peak := fun heq => hpeak_not (heq ▸ hv)
      omega
    have hmax (value : ℕ) (hv : value ∈ (1 :: increasing) ++ trailing) : value < peak := by
      simp only [List.cons_append, List.mem_cons] at hv
      rcases hv with rfl | hmem
      · omega
      · exact hsmall value hmem
    have hshape_nodup : ((1 :: increasing) ++ peak :: trailing).Nodup := by
      simpa only [suffix, htail_eq, List.cons_append] using hsuffix_nodup
    have havoids_shape : ¬ NonnestingDefs.Occurs [2, 1, 3]
        ((1 :: increasing) ++ peak :: trailing) ∧
        ¬ NonnestingDefs.Occurs [3, 1, 2] ((1 :: increasing) ++ peak :: trailing) := by
      simpa only [suffix, htail_eq, List.cons_append] using And.intro h213 h312
    obtain ⟨hinc_with_one, htrailing⟩ :=
      (unimodal_iff (1 :: increasing) trailing peak hshape_nodup hmax).mp havoids_shape
    have hincreasing : increasing.Pairwise (· < ·) := hinc_with_one.tail
    let low := before.filter (fun value => decide (value < peak))
    have hlow (value : ℕ) : value ∈ low ↔ value ∈ before ∧ value < peak := by simp [low]
    have hseparate : ∀ value ∈ before, value ∉ suffix := by
      intro value hv hs
      exact (List.nodup_append.mp hnodup).2.2 _ hv _ hs rfl
    have hlow_partition : (low ++ (increasing ++ trailing)).Perm (List.range' 2 (peak - 2)) := by
      have hlow_nodup : low.Nodup := hbefore_dec.nodup.sublist List.filter_sublist
      have hrest_nodup : (increasing ++ trailing).Nodup := by
        have hn := (List.nodup_cons.mp hsuffix_nodup).2
        rw [htail_eq] at hn
        exact hn.sublist ((List.Sublist.refl increasing).append
          ((List.Sublist.refl trailing).cons peak))
      have hpartition_nodup : (low ++ (increasing ++ trailing)).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hlow_nodup, hrest_nodup, ?_⟩
        intro value hv later hlater heq
        apply hseparate value ((hlow value).mp hv).1
        have hm : later ∈ suffix := List.mem_cons_of_mem 1 (hrest_mem later hlater)
        exact heq ▸ hm
      apply (List.perm_ext_iff_of_nodup hpartition_nodup (List.nodup_range' 1)).mpr
      intro value
      rw [List.mem_append, hlow, List.mem_range'_1]
      constructor
      · rintro (⟨hbefore, hlt⟩ | hrest)
        · have hpos := ((hvalues value).mp (hbefore_sub.subset hbefore)).1
          have hne : value ≠ 1 := fun heq => hseparate value hbefore (by simp [suffix, heq])
          omega
        · have hlt := hsmall value hrest
          have hmem : value ∈ suffix := List.mem_cons_of_mem 1 (hrest_mem value hrest)
          have hpos := ((hvalues value).mp (hsuffix_sub.subset hmem)).1
          have hne : value ≠ 1 := by
            intro heq
            apply htail_not_one
            simpa only [heq] using hrest_mem value hrest
          omega
      · intro hb
        have hlt : value < peak := by omega
        have hmem : value ∈ before ++ suffix := (hvalues value).mpr (by omega)
        rcases List.mem_append.mp hmem with hbefore | hrest
        · exact Or.inl ⟨hbefore, hlt⟩
        · right
          simp only [suffix, htail_eq, List.mem_cons, List.mem_append] at hrest
          rcases hrest with he | hi | he | hj
          · omega
          · exact List.mem_append_left _ hi
          · omega
          · exact List.mem_append_right _ hj
    obtain ⟨blockCorrespondence, hblockForward, _⟩ := block_bijection (peak - 2)
    let partition := (low, increasing, trailing)
    have hpartition : partition.1.Pairwise (· > ·) ∧ partition.2.1.Pairwise (· < ·) ∧
        partition.2.2.Pairwise (· > ·) ∧
        (partition.1 ++ (partition.2.1 ++ partition.2.2)).Perm (List.range' 2 (peak - 2)) :=
      ⟨hbefore_dec.filter _, hincreasing, htrailing, hlow_partition⟩
    let letters := blockCorrespondence.symm ⟨partition, hpartition⟩
    have hletters : blocks letters = partition := by
      rw [← hblockForward letters]
      exact congrArg Subtype.val (blockCorrespondence.apply_symm_apply ⟨partition, hpartition⟩)
    have hb : peak - 2 + 2 ≤ size := by omega
    have hpeak_eq : peak - 2 + 2 = peak := by omega
    have hconstructed := (reconstruct_permutation size (peak - 2) hb).2 letters
    have hprefix_eq :
        (List.range' (peak - 2 + 3) (size - (peak - 2 + 2))).reverse ++ low = before := by
      have hsorted : List.Pairwise (· > ·)
          ((List.range' (peak - 2 + 3) (size - (peak - 2 + 2))).reverse ++ low) := by
        simpa only [hletters] using hconstructed.2.1
      apply hsorted.eq_of_mem_iff hbefore_dec
      intro value
      simp only [List.mem_append, List.mem_reverse, List.mem_range'_1, hlow]
      constructor
      · rintro (hupper | ⟨hbefore, _⟩)
        · have hmem : value ∈ before ++ suffix := (hvalues value).mpr (by omega)
          rcases List.mem_append.mp hmem with hbefore | hsuffix
          · exact hbefore
          · simp only [suffix, List.mem_cons] at hsuffix
            rcases hsuffix with rfl | htail
            · omega
            · have := htail_bound value htail
              omega
        · exact hbefore
      · intro hv
        by_cases hlt : value < peak
        · exact Or.inr ⟨hv, hlt⟩
        · left
          have hbound := (hvalues value).mp (hbefore_sub.subset hv)
          have hne : value ≠ peak := fun heq => hseparate value hv
            (List.mem_cons_of_mem 1 (heq ▸ hpeak_mem))
          omega
    have hwhole : reconstruct size letters = before ++ suffix := by
      simp only [reconstruct, hletters, partition]
      rw [hprefix_eq, hpeak_eq]
      simp only [suffix, htail_eq]
    have hword_member : List.ofFn letters ∈ language (peak - 2) :=
      (htransport _ hb letters).mp (hwhole ▸ ⟨hperm, hfish, havoid⟩)
    refine ⟨Sum.inr ⟨⟨peak, hpeak_ge, hpeak_le⟩, ⟨List.ofFn letters, hword_member⟩⟩, ?_⟩
    change reconstruct size (fun index : Fin (peak - 2) =>
      (List.ofFn letters).getD index.val d) = before ++ suffix
    rw [hgetFn]
    exact hwhole
  let forward : ACParameters third size → avoiders size patterns :=
    fun data => ⟨realize data, hrealize_member data⟩
  have hbijective : Function.Bijective forward := by
    constructor
    · intro first second heq
      exact hinjective (congrArg Subtype.val heq)
    · intro permutation
      obtain ⟨data, heq⟩ := hsurjective permutation.val permutation.property
      exact ⟨data, Subtype.ext heq⟩
  refine ⟨(Equiv.ofBijective forward hbijective).symm, ?_, ?_⟩
  · rfl
  · intro peak word
    rfl

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenACEquiv
