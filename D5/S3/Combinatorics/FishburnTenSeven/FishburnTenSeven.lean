/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSeven
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSeven
   mirror-E: none(waiver:triple-avoidance-combinatorial-enumeration)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Reversible decompositions and word recurrences prove all three Fishburn counts. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenDefs
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenACEquiv
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBEquiv
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSeven

open Fishburn.FishburnDefs
open FishburnTenSevenWords FishburnTenSevenWords.Letter
open FishburnTenSevenACEquiv FishburnTenSevenBEquiv FishburnTenSevenBParameters

theorem result : FishburnTenSevenDefs.claim107 := by
  classical
  have hwordcounts (size : ℕ) :
      (languageA size).Finite ∧ (languageC size).Finite ∧
      (languageA size).ncard = 2 ^ (size + 1) - 1 ∧
      (languageC size).ncard = 2 ^ (size + 1) - 1 := by
    classical
    let binary (length : ℕ) : Set (List Letter) :=
      {word | word.length = length ∧ j ∉ word}
    let run (length : ℕ) : Set (List Letter) :=
      {word | j :: word ∈ languageA (length + 1)}
    have hbinary_valid (word : List Letter) (hword : j ∉ word) :
        word.IsChain (fun left right => left ≠ j ∨ right ≠ i) ∧ Before j d word := by
      induction word with
      | nil => simp [Before]
      | cons letter tail ih =>
        have hletter : letter ≠ j := by
          intro heq
          exact hword (by simp [heq])
        have htail : j ∉ tail := fun hmem => hword (List.mem_cons_of_mem _ hmem)
        rcases ih htail with ⟨hchain, hbefore⟩
        refine ⟨hchain.cons (fun _ _ => Or.inl hletter), ?_⟩
        exact List.pairwise_cons.mpr
          ⟨fun next hnext => Or.inr (fun heq => htail (heq ▸ hnext)), hbefore⟩
    have hi (length : ℕ) (word : List Letter) :
        i :: word ∈ languageA (length + 1) ↔ word ∈ languageA length := by
      cases word with
      | nil => simp [languageA, Before, eq_comm]
      | cons letter tail =>
        simp [languageA, Before, List.pairwise_cons, List.isChain_cons_cons]
    have hd (length : ℕ) (word : List Letter) :
        d :: word ∈ languageA (length + 1) ↔ word ∈ binary length := by
      change ((d :: word).length = length + 1 ∧
        (d :: word).IsChain (fun left right => left ≠ j ∨ right ≠ i) ∧
        Before j d (d :: word)) ↔ word.length = length ∧ j ∉ word
      constructor
      · rintro ⟨hlen, _, hbefore⟩
        refine ⟨by simpa using hlen, ?_⟩
        intro hmem
        have hrel := (List.pairwise_cons.mp hbefore).1 j hmem
        simp at hrel
      · rintro ⟨hlen, hnot⟩
        rcases hbinary_valid word hnot with ⟨hchain, hbefore⟩
        refine ⟨by simpa using hlen, hchain.cons (fun _ _ => Or.inl (by decide)), ?_⟩
        exact List.pairwise_cons.mpr
          ⟨fun next hnext => Or.inr (fun heq => hnot (heq ▸ hnext)), hbefore⟩
    have hj (length : ℕ) (word : List Letter) :
        j :: word ∈ languageA (length + 1) ↔
          word ∈ languageA length ∧ word.head? ≠ some i := by
      cases word with
      | nil => simp [languageA, Before, eq_comm]
      | cons letter tail =>
        cases letter <;>
          simp [languageA, Before, List.pairwise_cons, List.isChain_cons_cons]
    have hbinary_step (length : ℕ) :
        binary (length + 1) =
          List.cons d '' binary length ∪ List.cons i '' binary length := by
      ext word
      cases word with
      | nil => simp [binary]
      | cons letter tail => cases letter <;> simp [binary]
    have hrun_step (length : ℕ) :
        run (length + 1) =
          List.cons d '' binary length ∪ List.cons j '' run length := by
      ext word
      change (j :: word ∈ languageA ((length + 1) + 1)) ↔ _
      rw [hj]
      cases word with
      | nil => simp [languageA]
      | cons letter tail => cases letter <;> simp [hi, hd, run]
    have hlanguage_step (length : ℕ) :
        languageA (length + 1) = List.cons i '' languageA length ∪
          (List.cons d '' binary length ∪ List.cons j '' run length) := by
      ext word
      cases word with
      | nil => simp [languageA]
      | cons letter tail => cases letter <;> simp [hi, hd, run]
    have hdisjoint (left right : Letter) (hne : left ≠ right)
        (source target : Set (List Letter)) :
        Disjoint (List.cons left '' source) (List.cons right '' target) := by
      rw [Set.disjoint_left]
      rintro _ ⟨first, _, rfl⟩ ⟨second, _, heq⟩
      exact hne (List.cons.inj heq).1.symm
    have hcard_cons (letter : Letter) (source : Set (List Letter)) :
        (List.cons letter '' source).ncard = source.ncard :=
      Set.ncard_image_of_injective source (fun _ _ heq => (List.cons.inj heq).2)
    have hzero : binary 0 = {[]} ∧ run 0 = {[]} ∧ languageA 0 = {[]} := by
      constructor
      · ext word
        cases word <;> simp [binary]
      constructor
      · ext word
        cases word <;> simp [run, languageA, Before]
      · ext word
        cases word <;> simp [languageA, Before]
    have hinduction (length : ℕ) :
        (binary length).Finite ∧ (run length).Finite ∧ (languageA length).Finite ∧
        (binary length).ncard = 2 ^ length ∧ (run length).ncard = 2 ^ length ∧
        (languageA length).ncard = 2 ^ (length + 1) - 1 := by
      induction length with
      | zero => simp [hzero.1, hzero.2.1, hzero.2.2]
      | succ length ih =>
        rcases ih with ⟨hbinary, hrun, hlanguage, hbinary_count, hrun_count, hlanguage_count⟩
        have hdb := hbinary.image (List.cons d)
        have hib := hbinary.image (List.cons i)
        have hjr := hrun.image (List.cons j)
        have hia := hlanguage.image (List.cons i)
        have hd_i := hdisjoint d i (by decide) (binary length) (binary length)
        have hd_j := hdisjoint d j (by decide) (binary length) (run length)
        have hi_rest : Disjoint (List.cons i '' languageA length)
            (List.cons d '' binary length ∪ List.cons j '' run length) := by
          exact Set.disjoint_union_right.mpr
            ⟨hdisjoint i d (by decide) _ _, hdisjoint i j (by decide) _ _⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hbinary_step]
          exact hdb.union hib
        · rw [hrun_step]
          exact hdb.union hjr
        · rw [hlanguage_step]
          exact hia.union (hdb.union hjr)
        · rw [hbinary_step, Set.ncard_union_eq hd_i hdb hib, hcard_cons, hcard_cons,
            hbinary_count, Nat.pow_succ]
          omega
        · rw [hrun_step, Set.ncard_union_eq hd_j hdb hjr, hcard_cons, hcard_cons,
            hbinary_count, hrun_count, Nat.pow_succ]
          omega
        · rw [hlanguage_step, Set.ncard_union_eq hi_rest hia (hdb.union hjr),
            Set.ncard_union_eq hd_j hdb hjr, hcard_cons, hcard_cons, hcard_cons,
            hlanguage_count, hbinary_count, hrun_count]
          have hpositive := Nat.two_pow_pos (length + 1)
          simp only [Nat.pow_succ] at hpositive ⊢
          omega
    rcases hinduction size with ⟨_, _, hfinite, _, _, hcount⟩
    obtain ⟨correspondence, _⟩ := (word_bijection size).2.2
    have himage : phi '' languageA size = languageC size := by
      ext word
      constructor
      · rintro ⟨original, horiginal, rfl⟩
        exact (word_bijection size).2.1 original |>.mp horiginal
      · intro hword
        refine ⟨phi word, ?_, (word_bijection size).1 word⟩
        apply ((word_bijection size).2.1 (phi word)).mpr
        simpa only [(word_bijection size).1 word] using hword
    refine ⟨hfinite, ?_, hcount, ?_⟩
    · rw [← himage]
      exact hfinite.image phi
    · rw [← Set.ncard_congr' correspondence]
      exact hcount
  
  have hac_count (third : Bool) (size : ℕ) (hsize : 1 ≤ size) :
      Nat.card (ACParameters third size) = 2 ^ size - size := by
    let language (length : ℕ) := if third then languageC length else languageA length
    have hwords (length : ℕ) :
        (language length).Finite ∧ (language length).ncard = 2 ^ (length + 1) - 1 := by
      cases third
      · exact ⟨(hwordcounts length).1, (hwordcounts length).2.2.1⟩
      · exact ⟨(hwordcounts length).2.1, (hwordcounts length).2.2.2⟩
    let (length : ℕ) : Finite (language length) := (hwords length).1.to_subtype
    let (total : ℕ) : Finite {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ total} :=
      (Set.finite_Icc 2 total).to_subtype
    let (total : ℕ) : Fintype {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ total} :=
      Fintype.ofFinite _
    let codes : (Σ maximum : {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ size},
        language (maximum.val - 2)) ≃ Σ index : Fin (size - 1), language index.val := by
      refine
        { toFun := fun ⟨maximum, word⟩ =>
            ⟨⟨maximum.val - 2, by have := maximum.property; omega⟩, word⟩
          invFun := fun ⟨index, word⟩ =>
            ⟨⟨index.val + 2, by have := index.is_lt; omega⟩,
              ⟨word.val, by simpa only [Nat.add_sub_cancel_right] using word.property⟩⟩
          left_inv := ?_
          right_inv := ?_ }
      · rintro ⟨⟨maximum, hmaximum⟩, ⟨word, hword⟩⟩
        dsimp only
        refine Sigma.ext (Subtype.ext (by dsimp; omega)) ?_
        exact (Subtype.heq_iff_coe_eq (fun candidate => by
          simp only [Nat.add_sub_cancel_right])).mpr rfl
      · rintro ⟨⟨index, hindex⟩, ⟨word, hword⟩⟩
        dsimp only
        refine Sigma.ext (Fin.ext (by dsimp; omega)) ?_
        exact (Subtype.heq_iff_coe_eq (fun candidate => by
          simp only [Nat.add_sub_cancel_right])).mpr rfl
    have hcount (length : ℕ) :
        (∑ index ∈ Finset.range length, (2 ^ (index + 1) - 1)) + length + 2 =
          2 ^ (length + 1) := by
      induction length with
      | zero => simp
      | succ length ih =>
        rw [Finset.sum_range_succ]
        have hpositive := Nat.two_pow_pos (length + 1)
        have hpower : 2 ^ (length + 1 + 1) = 2 ^ (length + 1) * 2 := Nat.pow_succ _ _
        omega
    have hcard :
        Nat.card (Unit ⊕ (Σ maximum : {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ size},
          language (maximum.val - 2))) =
        1 + ∑ index ∈ Finset.range (size - 1), (2 ^ (index + 1) - 1) := by
      rw [Nat.card_sum, Nat.card_unique, Nat.card_congr codes, Nat.card_sigma]
      simp_rw [Nat.card_coe_set_eq, (hwords _).2]
      rw [Fin.sum_univ_eq_sum_range (fun index : ℕ => 2 ^ (index + 1) - 1) (size - 1)]
    have hsum := hcount (size - 1)
    have hexponent : size - 1 + 1 = size := by omega
    rw [hexponent] at hsum
    change Nat.card (Unit ⊕ (Σ maximum : {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ size},
      language (maximum.val - 2))) = _
    omega
  intro size hsize
  obtain ⟨firstCorrespondence, _, _⟩ := ac_equivalence false size hsize
  obtain ⟨thirdCorrespondence, _, _⟩ := ac_equivalence true size hsize
  have hfirst :
      (avoiders size [[1, 3, 2, 4], [2, 1, 4, 3], [1, 4, 2, 3]]).ncard =
        2 ^ size - size := by
    change Nat.card (avoiders size [[1, 3, 2, 4], [2, 1, 4, 3], [1, 4, 2, 3]]) = _
    exact (Nat.card_congr firstCorrespondence).trans (hac_count false size hsize)
  have hsecond :
      (avoiders size [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]).ncard =
        2 ^ size - size := by
    change Nat.card (avoiders size [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]) = _
    exact (Nat.card_congr (B_normalForm_equiv size hsize)).trans
      (BParameters_card size hsize).2
  have hthird :
      (avoiders size [[1, 3, 2, 4], [1, 4, 2, 3], [3, 1, 2, 4]]).ncard =
        2 ^ size - size := by
    change Nat.card (avoiders size [[1, 3, 2, 4], [1, 4, 2, 3], [3, 1, 2, 4]]) = _
    exact (Nat.card_congr thirdCorrespondence).trans (hac_count true size hsize)
  exact ⟨hfirst, hsecond, hthird⟩

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSeven
