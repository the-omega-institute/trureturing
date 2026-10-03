/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152GapCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152GapCount
   mirror-E: none(waiver:gap-suffix-bijection)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.Sym.Card]
   utility: none
   digest: Gap suffixes correspond to subsets or multisets by retaining strict increases. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Left
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sym.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152GapCount

theorem gap_suffix_enumerators (gap : Finset ℕ) (maximum length : ℕ)
    (hgap : ∀ value ∈ gap, value < maximum) :
    Nonempty
      ({word : List ℕ // word.length = length + 1 ∧ word.Pairwise (· < ·) ∧
          ∀ value ∈ word, value ∈ gap} ≃ gap.powersetCard (length + 1)) ∧
    Nonempty
      ({word : List ℕ // word.length = length + 1 ∧
          (∀ value ∈ word, value ∈ gap ∨ value = maximum) ∧
          (word.filter (· ≠ maximum)).Pairwise (· < ·) ∧
          word.getD 0 maximum ≠ maximum} ≃ Sym gap (length + 1)) ∧
    Nat.card {word : List ℕ // word.length = length + 1 ∧ word.Pairwise (· < ·) ∧
        ∀ value ∈ word, value ∈ gap} = gap.card.choose (length + 1) ∧
    Nat.card {word : List ℕ // word.length = length + 1 ∧
        (∀ value ∈ word, value ∈ gap ∨ value = maximum) ∧
        (word.filter (· ≠ maximum)).Pairwise (· < ·) ∧
        word.getD 0 maximum ≠ maximum} = (gap.card + length).choose (length + 1) := by
  classical
  let internal := {word : List ℕ // word.length = length + 1 ∧
    word.Pairwise (· < ·) ∧ ∀ value ∈ word, value ∈ gap}
  let top := {word : List ℕ // word.length = length + 1 ∧
    (∀ value ∈ word, value ∈ gap ∨ value = maximum) ∧
    (word.filter (· ≠ maximum)).Pairwise (· < ·) ∧ word.getD 0 maximum ≠ maximum}
  let weak := {word : List ℕ // word.length = length + 1 ∧
    word.Pairwise (· ≤ ·) ∧ ∀ value ∈ word, value ∈ gap}
  let fill : ℕ → List ℕ → List ℕ := fun previous word =>
    (word.foldr (fun value recur prior =>
      let next := if value = maximum then prior else value
      next :: recur next) (fun _ => [])) previous
  let mark : ℕ → List ℕ → List ℕ := fun previous word =>
    (word.foldr (fun value recur prior =>
      (if value = prior then maximum else value) :: recur value) (fun _ => [])) previous
  have hfillnil (previous : ℕ) : fill previous [] = [] := rfl
  have hfillcons (previous value : ℕ) (rest : List ℕ) :
      fill previous (value :: rest) =
        (if value = maximum then previous else value) ::
          fill (if value = maximum then previous else value) rest := rfl
  have hmarknil (previous : ℕ) : mark previous [] = [] := rfl
  have hmarkcons (previous value : ℕ) (rest : List ℕ) :
      mark previous (value :: rest) =
        (if value = previous then maximum else value) :: mark value rest := rfl
  have hfill : ∀ word : List ℕ, ∀ previous ∈ gap,
      (∀ value ∈ word, value ∈ gap ∨ value = maximum) →
      (word.filter (· ≠ maximum)).Pairwise (· < ·) →
      (∀ value ∈ word, value ≠ maximum → previous < value) →
      (fill previous word).length = word.length ∧
      (fill previous word).Pairwise (· ≤ ·) ∧
      (∀ value ∈ fill previous word, value ∈ gap ∧ previous ≤ value) ∧
      mark previous (fill previous word) = word := by
    intro word
    induction word with
    | nil => intro previous hprevious hvalues hpair hlow; simp [hfillnil, hmarknil]
    | cons value rest ih =>
      intro previous hprevious hvalues hpair hlow
      have hrestvalues : ∀ entry ∈ rest, entry ∈ gap ∨ entry = maximum :=
        fun entry hentry => hvalues entry (List.mem_cons_of_mem _ hentry)
      by_cases heq : value = maximum
      · subst value
        have hrestpair : (rest.filter (· ≠ maximum)).Pairwise (· < ·) := by
          simpa using hpair
        have hrestlow : ∀ entry ∈ rest, entry ≠ maximum → previous < entry :=
          fun entry hentry => hlow entry (List.mem_cons_of_mem _ hentry)
        obtain ⟨hlen, hmono, hentries, hinverse⟩ :=
          ih previous hprevious hrestvalues hrestpair hrestlow
        rw [hfillcons]
        simp only [ite_true]
        refine ⟨by simp [hlen], List.pairwise_cons.mpr
          ⟨fun entry hentry => (hentries entry hentry).2, hmono⟩, ?_, ?_⟩
        · intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact ⟨hprevious, le_rfl⟩
          · exact hentries entry hentry
        · rw [hmarkcons]
          simpa only [ite_true] using congrArg (List.cons maximum) hinverse
      · have hvalue : value ∈ gap := (hvalues value (by simp)).resolve_right heq
        have hlt : previous < value := hlow value (by simp) heq
        have hp : (∀ entry ∈ rest.filter (· ≠ maximum), value < entry) ∧
            (rest.filter (· ≠ maximum)).Pairwise (· < ·) := by
          simpa [heq] using hpair
        have hrestlow : ∀ entry ∈ rest, entry ≠ maximum → value < entry := by
          intro entry hentry hne
          exact hp.1 entry (by simp [hentry, hne])
        obtain ⟨hlen, hmono, hentries, hinverse⟩ :=
          ih value hvalue hrestvalues hp.2 hrestlow
        rw [hfillcons]
        simp only [if_neg heq]
        refine ⟨by simp [hlen], List.pairwise_cons.mpr
          ⟨fun entry hentry => (hentries entry hentry).2, hmono⟩, ?_, ?_⟩
        · intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact ⟨hvalue, Nat.le_of_lt hlt⟩
          · exact ⟨(hentries entry hentry).1, by
              have := (hentries entry hentry).2
              omega⟩
        · rw [hmarkcons]
          simp only [if_neg (by omega : value ≠ previous), hinverse]
  have hmark : ∀ word : List ℕ, ∀ previous ∈ gap,
      word.Pairwise (· ≤ ·) → (∀ value ∈ word, value ∈ gap ∧ previous ≤ value) →
      (mark previous word).length = word.length ∧
      (∀ value ∈ mark previous word, value ∈ gap ∨ value = maximum) ∧
      ((mark previous word).filter (· ≠ maximum)).Pairwise (· < ·) ∧
      (∀ value ∈ mark previous word, value ≠ maximum → previous < value) ∧
      fill previous (mark previous word) = word := by
    intro word
    induction word with
    | nil => intro previous hprevious hpair hvalues; simp [hmarknil, hfillnil]
    | cons value rest ih =>
      intro previous hprevious hpair hvalues
      have hv := hvalues value (by simp)
      have hp := List.pairwise_cons.mp hpair
      have hrestvalues : ∀ entry ∈ rest, entry ∈ gap ∧ value ≤ entry :=
        fun entry hentry =>
          ⟨(hvalues entry (List.mem_cons_of_mem _ hentry)).1, hp.1 entry hentry⟩
      obtain ⟨hlen, hentries, hstrict, hlow, hinverse⟩ :=
        ih value hv.1 hp.2 hrestvalues
      rw [hmarkcons]
      by_cases heq : value = previous
      · subst value
        simp only [ite_true]
        refine ⟨by simp [hlen], ?_, by simpa using hstrict, ?_, ?_⟩
        · intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact Or.inr rfl
          · exact hentries entry hentry
        · intro entry hentry hne
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact (hne rfl).elim
          · exact hlow entry hentry hne
        · rw [hfillcons]
          simpa only [ite_true] using congrArg (List.cons previous) hinverse
      · have hlt : previous < value := by omega
        have hne : value ≠ maximum := Nat.ne_of_lt (hgap value hv.1)
        simp only [if_neg heq]
        refine ⟨by simp [hlen], ?_, ?_, ?_, ?_⟩
        · intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact Or.inl hv.1
          · exact hentries entry hentry
        · simp only [List.filter_cons, ne_eq, hne, not_false_eq_true, decide_true,
            if_pos, List.pairwise_cons]
          refine ⟨?_, hstrict⟩
          intro entry hentry
          have hm := List.mem_filter.mp hentry
          exact hlow entry hm.1 (by simpa using hm.2)
        · intro entry hentry hentryne
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact hlt
          · have := hlow entry hentry hentryne
            omega
        · rw [hfillcons]
          simp only [if_neg hne, hinverse]
  let encode : List ℕ → List ℕ := fun word =>
    match word with
    | [] => []
    | first :: rest => first :: fill first rest
  let decode : List ℕ → List ℕ := fun word =>
    match word with
    | [] => []
    | first :: rest => first :: mark first rest
  have hencode (word : top) :
      (encode word.1).length = length + 1 ∧ (encode word.1).Pairwise (· ≤ ·) ∧
      (∀ value ∈ encode word.1, value ∈ gap) ∧ decode (encode word.1) = word.1 := by
    obtain ⟨word, hlen, hvalues, hpair, hfirst⟩ := word
    cases word with
    | nil => simp at hlen
    | cons first rest =>
      have hne : first ≠ maximum := by simpa using hfirst
      have hmem : first ∈ gap := (hvalues first (by simp)).resolve_right hne
      have hp : (∀ entry ∈ rest.filter (· ≠ maximum), first < entry) ∧
          (rest.filter (· ≠ maximum)).Pairwise (· < ·) := by
        simpa [hne] using hpair
      obtain ⟨hl, hm, he, hi⟩ := hfill rest first hmem
        (fun entry hentry => hvalues entry (List.mem_cons_of_mem _ hentry)) hp.2
        (fun entry hentry hentryne => hp.1 entry (by simp [hentry, hentryne]))
      refine ⟨by simpa [encode, hl] using hlen, ?_, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun entry hentry => (he entry hentry).2, hm⟩
      · intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact hmem
        · exact (he entry hentry).1
      · simp only [encode, decode, hi]
  have hdecode (word : weak) :
      (decode word.1).length = length + 1 ∧
      (∀ value ∈ decode word.1, value ∈ gap ∨ value = maximum) ∧
      ((decode word.1).filter (· ≠ maximum)).Pairwise (· < ·) ∧
      (decode word.1).getD 0 maximum ≠ maximum ∧ encode (decode word.1) = word.1 := by
    obtain ⟨word, hlen, hpair, hvalues⟩ := word
    cases word with
    | nil => simp at hlen
    | cons first rest =>
      have hmem : first ∈ gap := hvalues first (by simp)
      have hne : first ≠ maximum := Nat.ne_of_lt (hgap first hmem)
      have hp := List.pairwise_cons.mp hpair
      obtain ⟨hl, he, hs, hlow, hi⟩ := hmark rest first hmem hp.2
        (fun entry hentry =>
          ⟨hvalues entry (List.mem_cons_of_mem _ hentry), hp.1 entry hentry⟩)
      refine ⟨by simpa [decode, hl] using hlen, ?_, ?_, by simpa [decode], ?_⟩
      · intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact Or.inl hmem
        · exact he entry hentry
      · change ((first :: mark first rest).filter (· ≠ maximum)).Pairwise (· < ·)
        simp only [List.filter_cons, ne_eq, hne, not_false_eq_true, decide_true,
          if_pos, List.pairwise_cons]
        refine ⟨?_, hs⟩
        intro entry hentry
        have hm := List.mem_filter.mp hentry
        exact hlow entry hm.1 (by simpa using hm.2)
      · simp only [decode, encode, hi]
  let topWeak : top ≃ weak :=
    { toFun := fun word => ⟨encode word.1, (hencode word).1,
        (hencode word).2.1, (hencode word).2.2.1⟩
      invFun := fun word => ⟨decode word.1, (hdecode word).1,
        (hdecode word).2.1, (hdecode word).2.2.1, (hdecode word).2.2.2.1⟩
      left_inv := fun word => Subtype.ext (hencode word).2.2.2
      right_inv := fun word => Subtype.ext (hdecode word).2.2.2.2 }
  let sorted : Sym gap (length + 1) → weak := fun collection =>
    ⟨(collection.1.sort (· ≤ ·)).map Subtype.val,
      by simp,
      List.pairwise_map.mpr (Multiset.pairwise_sort collection.1 (· ≤ ·)),
      by
        intro value hvalue
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hvalue
        exact entry.2⟩
  have hsortedbij : Function.Bijective sorted := by
    constructor
    · intro first second heq
      have heqlist := congrArg Subtype.val heq
      have heqmulti := congrArg (fun word : List ℕ => (word : Multiset ℕ)) heqlist
      have hmap : first.1.map Subtype.val = second.1.map Subtype.val := by
        simpa only [sorted, ← Multiset.map_coe, Multiset.sort_eq] using heqmulti
      exact Subtype.ext (Multiset.map_injective Subtype.val_injective hmap)
    · intro word
      let lifted := word.1.attachWith (fun value => value ∈ gap) word.2.2.2
      let collection : Sym gap (length + 1) :=
        ⟨(lifted : Multiset gap), by simp [lifted, word.2.1]⟩
      refine ⟨collection, Subtype.ext ?_⟩
      change ((collection.1.sort (· ≤ ·)).map Subtype.val) = word.1
      have hperm : ((collection.1.sort (· ≤ ·)).map Subtype.val).Perm word.1 := by
        apply Multiset.coe_eq_coe.mp
        rw [← Multiset.map_coe, Multiset.sort_eq]
        change ((lifted : Multiset gap).map Subtype.val) = (word.1 : Multiset ℕ)
        rw [Multiset.map_coe, List.attachWith_map_subtype_val]
      exact hperm.eq_of_pairwise' (sorted collection).2.2.1 word.2.2.1
  let topEquiv : top ≃ Sym gap (length + 1) :=
    topWeak.trans (Equiv.ofBijective sorted hsortedbij).symm
  let internalEquiv : internal ≃ gap.powersetCard (length + 1) :=
    { toFun := fun word => ⟨word.1.toFinset, Finset.mem_powersetCard.mpr
        ⟨by
          intro value hvalue
          exact word.2.2.2 value (List.mem_toFinset.mp hvalue),
        (List.toFinset_card_of_nodup word.2.2.1.nodup).trans word.2.1⟩⟩
      invFun := fun subset => ⟨subset.1.sort (· ≤ ·),
        (Finset.length_sort _).trans (Finset.mem_powersetCard.mp subset.2).2,
        subset.1.sortedLT_sort.pairwise,
        fun value hvalue => (Finset.mem_powersetCard.mp subset.2).1
          ((Finset.mem_sort _).mp hvalue)⟩
      left_inv := fun word => Subtype.ext
        ((List.toFinset_sort (· ≤ ·) word.2.2.1.nodup).mpr
          (word.2.2.1.imp fun hlt => Nat.le_of_lt hlt))
      right_inv := fun subset => Subtype.ext (Finset.sort_toFinset _ _) }
  refine ⟨⟨internalEquiv⟩, ⟨topEquiv⟩, ?_, ?_⟩
  · exact (Nat.card_congr internalEquiv).trans
      ((Nat.card_eq_finsetCard _).trans (Finset.card_powersetCard _ _))
  · rw [Nat.card_congr topEquiv, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
    simp only [Fintype.card_coe]
    congr 1

end D5.S3.Combinatorics.InversionSeq.InversionSeq152GapCount
