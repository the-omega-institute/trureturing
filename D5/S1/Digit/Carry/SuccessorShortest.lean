/- GID: D5/S1/Digit/Carry/SuccessorShortest
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/SuccessorShortest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zeckendorf successor folds give exact bit changes and shortest directed carry paths. -/

import D5.S1.Digit.Carry.Successor
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Dist

set_option autoImplicit false

namespace D5.S1.Digit.Carry.SuccessorShortest

open D5.S1.Digit D5.S1.Digit.Carry.Successor

open private gapCount_spec gapCount_prefix_eq_one carried_original_zero_zero
  carried_original_zero_one carryState_final_canonical carrySteps_to_state_zero
  carrySteps_to_state_one from D5.S1.Digit.Carry.Successor

/-- Every directed carry path has at least the decrease in its total digit multiplicity steps. -/
theorem carry_steps_mass_lower_bound {k : Nat} {r s : RawDigits}
    (path : CarrySteps k r s) : tokenCount r ≤ tokenCount s + k := by
  classical
  induction path with
  | zero => omega
  | @succ k r middle s path step ih =>
    have decrease : tokenCount middle ≤ tokenCount s + 1 := by
      cases step <;> simp [tokenCount, Finsupp.sum_add_index]
    omega


open scoped symmDiff

/-- Hamming distance between the canonical rows of consecutive natural numbers. -/
noncomputable def successorHamming (n : Nat) : Nat :=
  let r := rawOfZeckendorf (Nat.zeckendorf n)
  let s := rawOfZeckendorf (Nat.zeckendorf (n + 1))
  ∑ j ∈ r.support ∪ s.support, Nat.dist (r j) (s j)

/-- The least number of directed carry rewrites after adding the successor input unit. -/
noncomputable def successorRewriteCount (n : Nat) : Nat := by
  classical
  exact Nat.find (show ∃ k, CarrySteps k
      (rawOfZeckendorf (Nat.zeckendorf n) + Finsupp.single 0 1)
      (rawOfZeckendorf (Nat.zeckendorf (n + 1))) from by
    obtain ⟨k, _, path⟩ := zeckendorf_successor_carry_terminates n
    exact ⟨k, path⟩)

/-- The length of the maximal occupied low alternating segment in a canonical row. -/
noncomputable def alternatingLength (n : Nat) : Nat :=
  let r := rawOfZeckendorf (Nat.zeckendorf n)
  gapCount r (if r 0 = 1 then 0 else 1)

/-- The successor erases its maximal low alternating segment, inserts one new bit,
and attains the lower bound on the length of every four-rule carry path. -/
theorem successor_erasure_and_shortest (n : Nat) :
    let r := rawOfZeckendorf (Nat.zeckendorf n)
    let s := rawOfZeckendorf (Nat.zeckendorf (n + 1))
    let offset := if r 0 = 1 then 0 else 1
    let k := alternatingLength n
    let erased := prefixSet offset k
    let inserted := carriedIndex offset k
    (∀ j < k, r (prefixIndex offset j) = 1) ∧
    r (prefixIndex offset k) = 0 ∧
    (r 0 = 0 → r 1 = 0 → k = 0) ∧
    erased ⊆ r.support ∧ erased.card = k ∧ inserted ∉ r.support ∧
    s.support = (r.support \ erased) ∪ {inserted} ∧
    r.support \ s.support = erased ∧ s.support \ r.support = {inserted} ∧
    successorHamming n = k + 1 ∧
    tokenCount s = tokenCount r - k + 1 ∧
    successorHamming n = 2 + tokenCount r - tokenCount s ∧
    successorRewriteCount n = k ∧
    successorRewriteCount n = successorHamming n - 1 ∧
    CarrySteps k (r + Finsupp.single 0 1) s ∧
    (∀ steps, CarrySteps steps (r + Finsupp.single 0 1) s → k ≤ steps) := by
  classical
  let r := rawOfZeckendorf (Nat.zeckendorf n)
  let s := rawOfZeckendorf (Nat.zeckendorf (n + 1))
  let offset := if r 0 = 1 then 0 else 1
  let k := gapCount r offset
  let erased := prefixSet offset k
  let inserted := carriedIndex offset k
  have canonical : CanonicalRaw r :=
    canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)
  have canonicalS : CanonicalRaw s :=
    canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf (n + 1))
  have gap : r (prefixIndex offset k) = 0 := by
    exact gapCount_spec r offset
  have prefix_bits : ∀ j < k, r (prefixIndex offset j) = 1 := by
    intro j hj
    exact gapCount_prefix_eq_one canonical offset j hj
  have offset_cases : offset = 0 ∨ offset = 1 := by
    dsimp [offset]
    split <;> simp
  have positive : offset = 0 → 0 < k := by
    intro ho
    have hzero : r 0 = 1 := by
      by_contra h
      simp [offset, h] at ho
    by_contra hk
    have hk0 : k = 0 := by omega
    simp [ho, hk0, prefixIndex, hzero] at gap
  have new_bit : r inserted = 0 := by
    by_cases hz : r 0 = 1
    · have ho : offset = 0 := by simp [offset, hz]
      change r (carriedIndex offset (gapCount r offset)) = 0
      rw [ho]
      exact carried_original_zero_zero canonical hz
    · have hz0 : r 0 = 0 := by have := canonical.1 0; omega
      have ho : offset = 1 := by simp [offset, hz]
      change r (carriedIndex offset (gapCount r offset)) = 0
      rw [ho]
      exact carried_original_zero_one canonical hz0
  have targetCanonical : CanonicalRaw (carryState r offset k) := by
    exact carryState_final_canonical canonical offset offset_cases positive new_bit
  have chain : CarrySteps k (r + Finsupp.single 0 1) (carryState r offset k) := by
    rcases offset_cases with ho | ho
    · change CarrySteps (gapCount r offset) _ (carryState r offset (gapCount r offset))
      rw [ho]
      exact carrySteps_to_state_zero canonical le_rfl
    · change CarrySteps (gapCount r offset) _ (carryState r offset (gapCount r offset))
      rw [ho]
      exact carrySteps_to_state_one canonical le_rfl
  have target : carryState r offset k = s := by
    apply canonicalRaw_unique targetCanonical canonicalS
    rw [← rawValue_carrySteps chain]
    change rawValue (rawOfZeckendorf (Nat.zeckendorf n) + Finsupp.single 0 1) =
      rawValue (rawOfZeckendorf (Nat.zeckendorf (n + 1)))
    rw [rawValue_add, rawValue_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n),
      rawValue_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf (n + 1))]
    simp only [Nat.sum_zeckendorf_fib, rawValue_single]
    norm_num [D5.S0.Conventions.wValue]
  have subset : erased ⊆ r.support := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjk : j < k := Finset.mem_range.mp hj
    exact Finsupp.mem_support_iff.mpr (by rw [prefix_bits j hjk]; omega)
  have card : erased.card = k := by
    dsimp [erased, prefixSet]
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      dsimp [prefixIndex] at hab
      omega), Finset.card_range]
  have new_not : inserted ∉ r.support := by
    simpa only [Finsupp.mem_support_iff, not_not] using new_bit
  have new_not_erased : inserted ∉ erased := fun h => new_not (subset h)
  have support : s.support = (r.support \ erased) ∪ {inserted} := by
    rw [← target]
    change (stripPrefix r offset k + Finsupp.single inserted 1).support = _
    rw [Finsupp.support_add_eq_union]
    simp only [stripPrefix, Finsupp.support_filter,
      Finsupp.support_single inserted (by omega : (1 : Nat) ≠ 0)]
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr (Finset.mem_filter.mp hx)))
      · exact Finset.mem_union.mpr (Or.inr hx)
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr (Finset.mem_sdiff.mp hx)))
      · exact Finset.mem_union.mpr (Or.inr hx)
  have erased_exact : r.support \ s.support = erased := by
    ext x
    by_cases hx : x = inserted
    · subst x
      simp [new_not, new_not_erased]
    · by_cases he : x ∈ erased
      · have hr := subset he
        simp [support, hx, he, hr]
      · simp [support, hx, he]
  have inserted_exact : s.support \ r.support = {inserted} := by
    ext x
    by_cases hx : x = inserted
    · subst x
      simp [support, new_not]
    · simp [support, hx]
      intro h _
      exact h
  have hamming_card : successorHamming n = (r.support ∆ s.support).card := by
    change (∑ j ∈ r.support ∪ s.support, Nat.dist (r j) (s j)) = _
    have distance : ∀ j, Nat.dist (r j) (s j) =
        if j ∈ r.support ∆ s.support then 1 else 0 := by
      intro j
      have hr : r j = 0 ∨ r j = 1 := by have := canonical.1 j; omega
      have hs : s j = 0 ∨ s j = 1 := by have := canonicalS.1 j; omega
      rcases hr with hr | hr <;> rcases hs with hs | hs <;>
        simp [Nat.dist, hr, hs, Finset.mem_symmDiff, Finsupp.mem_support_iff]
    calc
      _ = ∑ j ∈ r.support ∪ s.support,
          if j ∈ r.support ∆ s.support then 1 else 0 :=
        Finset.sum_congr rfl (fun j _ => distance j)
      _ = ((r.support ∪ s.support).filter
          (fun j => j ∈ r.support ∆ s.support)).card := Finset.sum_boole _ _
      _ = (r.support ∆ s.support).card := by
        congr 1
        rw [Finset.filter_mem_eq_inter]
        exact Finset.inter_eq_right.mpr Finset.symmDiff_subset_union
  have hamming : successorHamming n = k + 1 := by
    rw [hamming_card]
    rw [Finset.symmDiff_def, erased_exact, inserted_exact]
    rw [Finset.union_singleton, Finset.card_insert_of_notMem new_not_erased, card]
  have mass_card : ∀ t : RawDigits, CanonicalRaw t → tokenCount t = t.support.card := by
    intro t ht
    unfold tokenCount Finsupp.sum
    calc
      ∑ j ∈ t.support, t j = ∑ _j ∈ t.support, 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        have := ht.1 j
        have := Finsupp.mem_support_iff.mp hj
        omega
      _ = t.support.card := by simp
  have bound : k ≤ r.support.card := by rw [← card]; exact Finset.card_le_card subset
  have mass : tokenCount s = tokenCount r - k + 1 := by
    rw [mass_card s canonicalS, mass_card r canonical, support,
      Finset.union_singleton, Finset.card_insert_of_notMem (by simp [new_not]),
      Finset.card_sdiff_of_subset subset, card]
  have mass_balance : tokenCount s + k = tokenCount r + 1 := by
    rw [← mass_card r canonical] at bound
    omega
  have lower : ∀ steps, CarrySteps steps (r + Finsupp.single 0 1) s → k ≤ steps := by
    intro steps hp
    have hm := carry_steps_mass_lower_bound hp
    have input_mass : tokenCount (r + Finsupp.single 0 1) = tokenCount r + 1 := by
      simp [tokenCount, Finsupp.sum_add_index]
    rw [input_mass] at hm
    omega
  have path : CarrySteps k (r + Finsupp.single 0 1) s := by rwa [target] at chain
  have minimum : successorRewriteCount n = k := by
    have existsPath : ∃ steps, CarrySteps steps (r + Finsupp.single 0 1) s := ⟨k, path⟩
    unfold successorRewriteCount
    apply Nat.le_antisymm
    · exact Nat.find_min' _ path
    · exact lower _ (Nat.find_spec existsPath)
  have empty_case : r 0 = 0 → r 1 = 0 → k = 0 := by
    intro hz h1
    have ho : offset = 1 := by simp [offset, hz]
    have hk : k ≤ 0 := by
      change gapCount r offset ≤ 0
      unfold gapCount
      apply Nat.find_min'
      simpa [ho, prefixIndex] using h1
    omega
  have hamming_mass : successorHamming n = 2 + tokenCount r - tokenCount s := by omega
  have minimum_hamming : successorRewriteCount n = successorHamming n - 1 := by omega
  exact ⟨prefix_bits, gap, empty_case, subset, card, new_not, support, erased_exact,
    inserted_exact, hamming, mass, hamming_mass, minimum, minimum_hamming, path, lower⟩

end D5.S1.Digit.Carry.SuccessorShortest
