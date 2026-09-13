/- GID: D5/S3/Factorization/Combinatorics/DistinctPrimePrefixWordCount
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/DistinctPrimePrefixWordCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct prefixes in occupation words have elementary symmetric counts. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.DistinctPrimePrefixWordCount

noncomputable section
open scoped BigOperators
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

/-- The number of words with occupation `a` whose first `j` labels are pairwise distinct. -/
def distinctPrefixCount {q : ℕ} (a : Multiset (Fin q)) (j : ℕ) : ℕ := by
  classical
  exact ((sectorWords a.card a).filter (fun w => ((List.ofFn w).take j).Nodup)).card

/-- The elementary symmetric coefficient of degree `j` in the label multiplicities. -/
def elementary {q : ℕ} (a : Multiset (Fin q)) (j : ℕ) : ℕ :=
  ∑ s ∈ (Finset.univ : Finset (Fin q)).powersetCard j, ∏ i ∈ s, a.count i

/-- Distinct initial labels give the elementary symmetric formula for occupation word counts. -/
theorem distinct_prefix_count_factorial (q : ℕ) (a : Multiset (Fin q)) (j : ℕ)
    (hj : j ≤ a.card) :
    distinctPrefixCount a j * (∏ i : Fin q, (a.count i).factorial) =
      j.factorial * (a.card - j).factorial * elementary a j := by
  classical
  let k := a.card - j
  have ha : a.card = j + k := by dsimp [k]; omega
  let B := (Finset.univ : Finset (Fin q)).powersetCard j
  have hsplit : distinctPrefixCount a j =
      ∑ u : Word (Fin q) j, ∑ v : Word (Fin q) k,
        if occupation u + occupation v = a ∧ (List.ofFn u).Nodup then 1 else 0 := by
    unfold distinctPrefixCount
    rw [ha]
    simp only [sectorWords, Finset.filter_filter, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    rw [← (Fin.appendEquiv j k).sum_comp
      (fun w => if occupation w = a ∧ (List.ofFn w |>.take j).Nodup then 1 else 0),
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    change (if occupation (Fin.append u v) = a ∧
      ((List.ofFn (Fin.append u v)).take j).Nodup then 1 else 0) = _
    simp only [occupation_append, List.ofFn_fin_append]
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  have hterm (u : Word (Fin q) j) (v : Word (Fin q) k) :
      (if occupation u + occupation v = a ∧ (List.ofFn u).Nodup then 1 else 0) =
      ∑ s ∈ B, if occupation u = s.val ∧ occupation v = a - s.val ∧ s.val ≤ a
        then 1 else 0 := by
    by_cases h : occupation u + occupation v = a ∧ (List.ofFn u).Nodup
    · let s : Finset (Fin q) := ⟨occupation u, h.2⟩
      have hs : s ∈ B := by
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, occupation_card u⟩
      have hle : s.val ≤ a := by
        rw [← h.1]
        exact Multiset.le_add_right _ _
      have hv : occupation v = a - s.val := by
        rw [← h.1]
        simp [s]
      rw [Finset.sum_eq_single s]
      · simp [h, s, hv, hle]
      · intro t _ hts
        have hne : occupation u ≠ t.val := by
          intro ht
          apply hts
          exact Finset.val_injective ht.symm
        simp [hne]
      · exact fun hn => (hn hs).elim
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro s _
      have hn : ¬ (occupation u = s.val ∧ occupation v = a - s.val ∧ s.val ≤ a) := by
        rintro ⟨hu, hv, hle⟩
        apply h
        constructor
        · rw [hu, hv, add_comm, Multiset.sub_add_cancel hle]
        · change (occupation u).Nodup
          rw [hu]
          exact s.nodup
      simp [hn]
  have hpartition : distinctPrefixCount a j =
      ∑ s ∈ B, if s.val ≤ a then
        multiplicity j s.val * multiplicity k (a - s.val) else 0 := by
    rw [hsplit]
    simp_rw [hterm]
    rw [show (∑ u : Word (Fin q) j, ∑ v : Word (Fin q) k,
        ∑ s ∈ B, if occupation u = s.val ∧ occupation v = a - s.val ∧ s.val ≤ a
          then 1 else 0) =
        ∑ s ∈ B, ∑ u : Word (Fin q) j, ∑ v : Word (Fin q) k,
          if occupation u = s.val ∧ occupation v = a - s.val ∧ s.val ≤ a
            then 1 else 0 by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Word (Fin q) k))) (t := B)]
      rw [Finset.sum_comm]]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hle : s.val ≤ a
    · simp only [hle, and_true, if_true]
      simp only [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity, sectorWords,
        Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : occupation u = s.val <;> simp [hu]
    · simp [hle]
  have hfactorial (b : Multiset (Fin q)) (n : ℕ) (hb : b.card = n) :
      (∏ i : Fin q, (b.count i).factorial) * multiplicity n b = n.factorial := by
    rw [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity,
      sector_words_card_multinomial b hb, Nat.multinomial_spec,
      Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _), hb]
  have hvalue (s : Finset (Fin q)) (hs : s ∈ B) :
      (if s.val ≤ a then multiplicity j s.val * multiplicity k (a - s.val) else 0) *
        (∏ i : Fin q, (a.count i).factorial) =
        j.factorial * k.factorial * ∏ i ∈ s, a.count i := by
    have hcard : s.val.card = j := (Finset.mem_powersetCard.mp hs).2
    have hcount (i : Fin q) : s.val.count i = if i ∈ s then 1 else 0 :=
      Multiset.count_eq_of_nodup s.nodup
    have hsfac : (∏ i : Fin q, (s.val.count i).factorial) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      rw [hcount]
      split_ifs <;> rfl
    have hsmul : multiplicity j s.val = j.factorial := by
      simpa [hsfac] using hfactorial s.val j hcard
    by_cases hle : s.val ≤ a
    · rw [if_pos hle, hsmul]
      have hc : (a - s.val).card = k := by
        rw [Multiset.card_sub hle, hcard, ha]
        omega
      have hcfac := hfactorial (a - s.val) k hc
      have hchoose : (∏ i : Fin q, (a.count i).choose (s.val.count i)) =
          ∏ i ∈ s, a.count i := by
        simp_rw [hcount]
        simp only [apply_ite, Nat.choose_one_right, Nat.choose_zero_right]
        exact Finset.prod_ite_mem_eq s _
      have hprod : (∏ i ∈ s, a.count i) *
          (∏ i : Fin q, ((a - s.val).count i).factorial) =
          ∏ i : Fin q, (a.count i).factorial := by
        rw [← hchoose, ← one_mul (∏ i : Fin q, ((a - s.val).count i).factorial),
          ← hsfac, ← mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        rw [Multiset.count_sub]
        exact Nat.choose_mul_factorial_mul_factorial (Multiset.count_le_of_le i hle)
      rw [← hprod]
      calc
        j.factorial * multiplicity k (a - s.val) *
            ((∏ i ∈ s, a.count i) * (∏ i : Fin q, ((a - s.val).count i).factorial)) =
            j.factorial * ((∏ i : Fin q, ((a - s.val).count i).factorial) *
              multiplicity k (a - s.val)) * ∏ i ∈ s, a.count i := by ring
        _ = _ := by rw [hcfac]
    · rw [if_neg hle, zero_mul]
      have hz : ∃ i ∈ s, a.count i = 0 := by
        by_contra! hn
        apply hle
        rw [Multiset.le_iff_count]
        intro i
        rw [hcount]
        split_ifs with hi
        · exact Nat.one_le_iff_ne_zero.mpr (hn i hi)
        · exact Nat.zero_le _
      obtain ⟨i, hi, hzero⟩ := hz
      rw [Finset.prod_eq_zero hi hzero, mul_zero]
  rw [hpartition, Finset.sum_mul]
  calc
    _ = ∑ s ∈ B, j.factorial * k.factorial * ∏ i ∈ s, a.count i := by
      apply Finset.sum_congr rfl
      exact hvalue
    _ = _ := by rw [← Finset.mul_sum]; rfl

end

end D5.S3.Factorization.Combinatorics.DistinctPrimePrefixWordCount
