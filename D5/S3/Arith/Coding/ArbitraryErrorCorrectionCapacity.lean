/- GID: D5/S3/Arith/Coding/ArbitraryErrorCorrectionCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/ArbitraryErrorCorrectionCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Correcting e arbitrary residue coordinates requires distance at least 2e+1
     and bounds the message range by the first n-2e moduli. -/

import D5.S3.Arith.Coding.ResidueCodeDynamicRange
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * The current-tree search for residue words, minimum distance, prefix products,
     correction radii, and capacity found the family SSOT in
     `ResidueCodeDynamicRange` and the forward decoding theorem in
     `UniqueDecodingRadius`; this module imports and applies the exact dynamic-range
     equivalence and states correction operationally as disjoint Hamming balls.
   * Pinned Mathlib's `InformationTheory.Hamming` provides `hammingDist_self` and
     `hammingDist_le_card_fintype`, while `Finset.exists_subset_card_eq` and
     `Finset.card_sdiff_of_subset` split a short disagreement set between two balls.
   * Repository and pinned Mathlib searches found no theorem deriving the converse
     distance requirement and mixed-alphabet capacity bound from arbitrary-error
     correction in one public statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.ArbitraryErrorCorrectionCapacity

open D5.S3.Arith.Coding.ResidueCodeDynamicRange

/-- If radius-`e` Hamming balls around the residue codewords are disjoint, then the
code has minimum distance at least `2 * e + 1`; consequently its dynamic range is at
most the product of the first `n - 2 * e` moduli. -/
theorem arbitrary_error_correction_capacity_bound (m : ℕ → ℕ) (n K e : ℕ)
    (hstrict : ∀ i j, i < j → j < n → m i < m j)
    (hmoduli : ∀ i, i < n → 2 ≤ m i)
    (hcoprime : ∀ i j, i < n → j < n → i ≠ j → Nat.Coprime (m i) (m j))
    (hKlower : 2 ≤ K)
    (hcorrects : ∀ x y received, x < K → y < K →
      hammingDist received (residueWord m n x) ≤ e →
      hammingDist received (residueWord m n y) ≤ e → x = y) :
    MinDistanceAtLeast m n K (2 * e + 1) ∧
      K ≤ prefixProduct m (n - 2 * e) := by
  have hminimum : MinDistanceAtLeast m n K (2 * e + 1) := by
    intro x y hxy hyK
    let firstWord := residueWord m n x
    let secondWord := residueWord m n y
    by_contra hnotMinimum
    have hdistanceLe : hammingDist firstWord secondWord ≤ 2 * e := by
      have hdistanceLt : hammingDist firstWord secondWord < 2 * e + 1 :=
        Nat.lt_of_not_ge hnotMinimum
      omega
    by_cases hsmall : hammingDist firstWord secondWord ≤ e
    · have hreceivedFirst :
          hammingDist firstWord (residueWord m n x) ≤ e := by
        simp only [firstWord, hammingDist_self, Nat.zero_le]
      have hreceivedSecond :
          hammingDist firstWord (residueWord m n y) ≤ e := by
        simpa only [firstWord, secondWord] using hsmall
      have hxyEq := hcorrects x y firstWord (hxy.trans hyK) hyK
        hreceivedFirst hreceivedSecond
      exact (Nat.ne_of_lt hxy) hxyEq
    · have heLe : e ≤ hammingDist firstWord secondWord :=
        (Nat.lt_of_not_ge hsmall).le
      let disagreements : Finset (Fin n) :=
        Finset.univ.filter fun i ↦ firstWord i ≠ secondWord i
      have hdisagreements : disagreements.card = hammingDist firstWord secondWord := by
        rfl
      have heLeCard : e ≤ disagreements.card := by
        rw [hdisagreements]
        exact heLe
      obtain ⟨selected, hselectedSubset, hselectedCard⟩ :=
        Finset.exists_subset_card_eq (s := disagreements) (n := e) heLeCard
      let received : Fin n → ℕ := fun i ↦
        if i ∈ selected then secondWord i else firstWord i
      have hfirstFilter :
          Finset.univ.filter (fun i ↦ received i ≠ firstWord i) = selected := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hdiff
          by_contra hi
          simp only [received, if_neg hi] at hdiff
          exact hdiff rfl
        · intro hi
          have hiDisagreements := hselectedSubset hi
          have hdiff : firstWord i ≠ secondWord i := by
            simpa only [disagreements, Finset.mem_filter, Finset.mem_univ,
              true_and] using hiDisagreements
          simp only [received, if_pos hi]
          exact hdiff.symm
      have hsecondFilter :
          Finset.univ.filter (fun i ↦ received i ≠ secondWord i) =
            disagreements \ selected := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        constructor
        · intro hdiff
          have hi : i ∉ selected := by
            intro hi
            simp only [received, if_pos hi] at hdiff
            exact hdiff rfl
          have hwordsDiffer : firstWord i ≠ secondWord i := by
            simpa only [received, if_neg hi] using hdiff
          have hiDisagreements : i ∈ disagreements := by
            simpa only [disagreements, Finset.mem_filter, Finset.mem_univ,
              true_and] using hwordsDiffer
          exact ⟨hiDisagreements, hi⟩
        · rintro ⟨hiDisagreements, hi⟩
          have hwordsDiffer : firstWord i ≠ secondWord i := by
            simpa only [disagreements, Finset.mem_filter, Finset.mem_univ,
              true_and] using hiDisagreements
          simpa only [received, if_neg hi] using hwordsDiffer
      have hreceivedFirst : hammingDist received firstWord ≤ e := by
        rw [hammingDist, hfirstFilter, hselectedCard]
      have hreceivedSecond : hammingDist received secondWord ≤ e := by
        rw [hammingDist, hsecondFilter,
          Finset.card_sdiff_of_subset hselectedSubset, hselectedCard,
          hdisagreements]
        omega
      have hxyEq := hcorrects x y received (hxy.trans hyK) hyK
        hreceivedFirst hreceivedSecond
      exact (Nat.ne_of_lt hxy) hxyEq
  have hdistanceWithinLength : 2 * e + 1 ≤ n := by
    have hzeroOne : 2 * e + 1 ≤
        hammingDist (residueWord m n 0) (residueWord m n 1) :=
      hminimum 0 1 (by omega) (by omega)
    exact hzeroOne.trans (by simpa using
      (hammingDist_le_card_fintype :
        hammingDist (residueWord m n 0) (residueWord m n 1) ≤ Fintype.card (Fin n)))
  have hmonotone : ∀ i j, i ≤ j → j < n → m i ≤ m j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with hijEq | hijLt
    · subst j
      exact le_rfl
    · exact (hstrict i j hijLt hj).le
  have hpositive : ∀ i, i < n → 0 < m i := by
    intro i hi
    exact lt_of_lt_of_le (by decide : 0 < 2) (hmoduli i hi)
  have hcapacity : K ≤ prefixProduct m (n - (2 * e + 1) + 1) :=
    (maximum_dynamic_range_iff_min_distance m n (2 * e + 1) K
      (by omega) hdistanceWithinLength hmonotone hpositive hcoprime).mp hminimum
  have hindex : n - (2 * e + 1) + 1 = n - 2 * e := by omega
  exact ⟨hminimum, by simpa only [hindex] using hcapacity⟩

#print axioms arbitrary_error_correction_capacity_bound

end D5.S3.Arith.Coding.ArbitraryErrorCorrectionCapacity
