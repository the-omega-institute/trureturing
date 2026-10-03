/- GID: D5/S1/Words/Patterns/Separable/ActualCardinality
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/ActualCardinality
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Schroder]
   utility: none
   digest: Minimum-cut partitions identify actual avoider and indecomposable cardinalities. -/

import D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
import Mathlib.Combinatorics.Enumerative.Schroder

namespace D5.S1.Words.Patterns.Separable.ActualCardinality

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.ProperCut
open D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)
open scoped BigOperators

abbrev ProperSigned (sign : Bool) (length : ℕ) :=
  {π : Avoider length // HasProperCut sign π.val}

open Classical in
theorem actual_signed_cut_enumeration (sign : Bool) (length : ℕ) :
    (∃ equivalence : ProperSigned sign length ≃
      Σ cut : ↥(Finset.Ioo 0 length),
        Indecomposable sign cut.val × Avoider (length - cut.val),
      ∀ π, MinimumCut sign π.val.val (equivalence π).1.val) ∧
    Nat.card (ProperSigned sign length) =
      ∑ cut ∈ Finset.Ioo 0 length,
        Nat.card (Indecomposable sign cut) * Nat.card (Avoider (length - cut)) := by
  classical
  let fibers (cut : ↥(Finset.Ioo 0 length)) :=
    {π : Avoider length // MinimumCut sign π.val cut.val}
  let forget : (Σ cut, fibers cut) → ProperSigned sign length :=
    fun item => ⟨item.2.val, item.1.val,
      (Finset.mem_Ioo.mp item.1.property).1,
      (Finset.mem_Ioo.mp item.1.property).2, item.2.property.1⟩
  have bijective : Function.Bijective forget := by
    constructor
    · rintro ⟨firstCut, firstPermutation⟩ ⟨lastCut, lastPermutation⟩ equality
      have samePermutation : firstPermutation.val = lastPermutation.val :=
        congrArg Subtype.val equality
      have sameValue : firstCut.val = lastCut.val := by
        rcases lt_trichotomy firstCut.val lastCut.val with smaller | equal | larger
        · exact False.elim (lastPermutation.property.2 firstCut.val
            (Finset.mem_Ioo.mp firstCut.property).1 smaller
            (samePermutation ▸ firstPermutation.property.1))
        · exact equal
        · exact False.elim (firstPermutation.property.2 lastCut.val
            (Finset.mem_Ioo.mp lastCut.property).1 larger
            (samePermutation.symm ▸ lastPermutation.property.1))
      have sameCut : firstCut = lastCut := Subtype.ext sameValue
      subst lastCut
      congr 1
      exact Subtype.ext samePermutation
    · intro π
      have existsCut : ∃ cut, 0 < cut ∧ cut < length ∧ Cut sign π.val.val cut :=
        π.property
      let cut := Nat.find existsCut
      have chosen := Nat.find_spec existsCut
      refine ⟨⟨⟨cut, Finset.mem_Ioo.mpr ⟨chosen.1, chosen.2.1⟩⟩,
        π.val, chosen.2.2, ?_⟩, rfl⟩
      intro smaller positive below comparison
      exact Nat.find_min existsCut below ⟨positive, lt_trans below chosen.2.1, comparison⟩
  let partition := Equiv.ofBijective forget bijective
  let factorEquivalence (cut : ↥(Finset.Ioo 0 length)) :
      fibers cut ≃ Indecomposable sign cut.val × Avoider (length - cut.val) := by
    have positive := (Finset.mem_Ioo.mp cut.property).1
    have below := (Finset.mem_Ioo.mp cut.property).2
    have lengthEquality : cut.val + (length - cut.val) = length := by omega
    let transport : MinimumFiber sign cut.val (length - cut.val) ≃ fibers cut :=
      Equiv.cast (congrArg
        (fun size => {π : Avoider size // MinimumCut sign π.val cut.val}) lengthEquality)
    exact transport.symm.trans
      (Classical.choose (minimum_cut_cartesian_kernel sign cut.val (length - cut.val)
        positive (by omega))).symm
  refine ⟨⟨partition.symm.trans (Equiv.sigmaCongrRight factorEquivalence), ?_⟩, ?_⟩
  · intro π
    have minimal := (partition.symm π).2.property
    have reconstruction : (partition.symm π).2.val = π.val :=
      congrArg Subtype.val (partition.apply_symm_apply π)
    exact reconstruction ▸ minimal
  · calc
    Nat.card (ProperSigned sign length) = Nat.card (Σ cut, fibers cut) :=
      Nat.card_congr partition.symm
    _ = ∑ cut : ↥(Finset.Ioo 0 length), Nat.card (fibers cut) := Nat.card_sigma
    _ = ∑ cut : ↥(Finset.Ioo 0 length),
        Nat.card (Indecomposable sign cut.val) * Nat.card (Avoider (length - cut.val)) := by
      apply Finset.sum_congr rfl
      intro cut _
      rw [Nat.card_congr (factorEquivalence cut), Nat.card_prod]
    _ = _ := Finset.sum_coe_sort (Finset.Ioo 0 length)
      (fun cut => Nat.card (Indecomposable sign cut) * Nat.card (Avoider (length - cut)))

open Classical in
theorem actual_schroder_cardinality :
    Nat.card (Avoider 0) = 1 ∧
    (∀ length, 0 < length → Nat.card (Avoider length) = Nat.largeSchroder (length - 1)) ∧
    (∀ sign length, Nat.card (Indecomposable sign length) = Nat.smallSchroder length) ∧
    (∀ sign length, 2 ≤ length →
      2 * Nat.card (Indecomposable sign length) = Nat.card (Avoider length)) ∧
    (∀ sign length, 2 ≤ length →
      Nat.card (ProperSigned sign length) = Nat.card (Indecomposable (!sign) length)) ∧
    (∀ sign length, length ≤ 1 → Nat.card (ProperSigned sign length) = 0) := by
  classical
  have noCut (sign : Bool) (length : ℕ) (small : length ≤ 1)
      (π : Avoider length) : ¬HasProperCut sign π.val := by
    rintro ⟨cut, positive, below, _⟩
    omega
  have tiny (length : ℕ) (small : length ≤ 1) :
      Nat.card (Avoider length) = 1 ∧
        ∀ sign, Nat.card (Indecomposable sign length) = 1 := by
    let : Subsingleton (Fin length) := ⟨fun first last => Fin.ext (by omega)⟩
    exact ⟨Nat.card_of_subsingleton (identityAvoider length),
      fun sign => Nat.card_of_subsingleton
        (⟨identityAvoider length, noCut sign length small _⟩ : Indecomposable sign length)⟩
  have signedOpposite (sign : Bool) (length : ℕ) (large : 2 ≤ length) :
      Nat.card (ProperSigned sign length) = Nat.card (Indecomposable (!sign) length) := by
    obtain ⟨_, _, _, _, _, _, _, _, signLaw⟩ :=
      endpoint_history_count_kernel (EndpointHistory.stop none length)
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun π => (signLaw sign large π).symm))
  have symmetry (sign : Bool) (length : ℕ) :
      Nat.card (Indecomposable sign length) = Nat.card (Indecomposable (!sign) length) := by
    have firstPattern : ∀ position, (pattern2413 position).rev = pattern3142 position := by
      decide
    have secondPattern : ∀ position, (pattern3142 position).rev = pattern2413 position := by
      decide
    let flip (π : Avoider length) : Avoider length :=
      ⟨π.val.trans Fin.revPerm, by
        constructor
        · rintro ⟨embedding, order⟩
          apply π.property.2
          refine ⟨embedding, fun first last => ?_⟩
          rw [← firstPattern first, ← firstPattern last, Fin.rev_lt_rev]
          simpa only [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev] using order last first
        · rintro ⟨embedding, order⟩
          apply π.property.1
          refine ⟨embedding, fun first last => ?_⟩
          rw [← secondPattern first, ← secondPattern last, Fin.rev_lt_rev]
          simpa only [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev] using order last first⟩
    have involutive : Function.Involutive flip := by
      intro π
      apply Subtype.ext
      ext position
      simp [flip, Equiv.trans_apply]
    let equivalence : Avoider length ≃ Avoider length :=
      ⟨flip, flip, involutive, involutive⟩
    have cutFlip (π : Avoider length) (cut : ℕ) :
        Cut (!sign) (flip π).val cut ↔ Cut sign π.val cut := by
      cases sign <;> simp [Cut, flip, Equiv.trans_apply, Fin.rev_lt_rev]
    have properFlip (π : Avoider length) :
        HasProperCut (!sign) (flip π).val ↔ HasProperCut sign π.val := by
      unfold HasProperCut
      simp only [cutFlip]
    exact Nat.card_congr (Equiv.subtypeEquiv equivalence
      (fun π => (properFlip π).not.symm))
  have half (sign : Bool) (length : ℕ) (large : 2 ≤ length) :
      2 * Nat.card (Indecomposable sign length) = Nat.card (Avoider length) := by
    have split : Nat.card (Avoider length) =
        Nat.card (ProperSigned sign length) + Nat.card (Indecomposable sign length) := by
      rw [← Nat.card_congr (Equiv.sumCompl
        (fun π : Avoider length => HasProperCut sign π.val)), Nat.card_sum]
    rw [signedOpposite sign length large, ← symmetry sign length] at split
    omega
  have recurrence (length : ℕ) (large : 2 ≤ length) :
      Nat.card (Avoider length) = 2 * Nat.card (Avoider (length - 1)) +
        ∑ cut ∈ Finset.Ioo 1 length,
          Nat.card (Avoider cut) * Nat.card (Avoider (length - cut)) := by
    have interval : Finset.Ioo 0 length = Finset.Ico 1 length := by
      ext cut
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      omega
    calc
      Nat.card (Avoider length) = 2 * Nat.card (Indecomposable false length) :=
        (half false length large).symm
      _ = 2 * Nat.card (ProperSigned false length) := by
        rw [signedOpposite false length large, ← symmetry false length]
      _ = 2 * ∑ cut ∈ Finset.Ioo 0 length,
          Nat.card (Indecomposable false cut) * Nat.card (Avoider (length - cut)) := by
        rw [(actual_signed_cut_enumeration false length).2]
      _ = 2 * Nat.card (Avoider (length - 1)) +
          2 * ∑ cut ∈ Finset.Ioo 1 length,
            Nat.card (Indecomposable false cut) * Nat.card (Avoider (length - cut)) := by
        rw [interval, ← Finset.add_sum_Ioo_eq_sum_Ico (by omega : 1 < length),
          (tiny 1 (by omega)).2 false, one_mul, Nat.mul_add]
      _ = _ := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro cut member
        rw [← Nat.mul_assoc, half false cut (by
          have := (Finset.mem_Ioo.mp member).1
          omega)]
  have largeCounts : ∀ length, 0 < length →
      Nat.card (Avoider length) = Nat.largeSchroder (length - 1) := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length induction =>
      intro positive
      by_cases singleton : length = 1
      · subst length
        simpa using (tiny 1 (by omega)).1
      have large : 2 ≤ length := by omega
      rw [recurrence length large, induction (length - 1) (by omega) (by omega)]
      have sumEquality :
          (∑ cut ∈ Finset.Ioo 1 length,
            Nat.card (Avoider cut) * Nat.card (Avoider (length - cut))) =
          ∑ index ∈ Finset.Ioc 0 (length - 2),
            Nat.largeSchroder index * Nat.largeSchroder (length - 2 - index) := by
        refine Finset.sum_bij (fun cut _ => cut - 1) ?_ ?_ ?_ ?_
        · intro cut member
          simp only [Finset.mem_Ioo, Finset.mem_Ioc] at member ⊢
          omega
        · intro first firstMember last lastMember same
          simp only [Finset.mem_Ioo] at firstMember lastMember
          omega
        · intro index member
          refine ⟨index + 1, ?_, by omega⟩
          simp only [Finset.mem_Ioc, Finset.mem_Ioo] at member ⊢
          omega
        · intro cut member
          have bounds := Finset.mem_Ioo.mp member
          rw [induction cut bounds.2 (by omega),
            induction (length - cut) (by omega) (by omega)]
          congr 2
          omega
      rw [sumEquality]
      conv_rhs => rw [show length - 1 = (length - 2) + 1 by omega, Nat.largeSchroder_succ]
      rw [← Finset.Icc_bot]
      change _ = Nat.largeSchroder (length - 2) +
        ∑ index ∈ Finset.Icc 0 (length - 2),
          Nat.largeSchroder index * Nat.largeSchroder (length - 2 - index)
      rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le (length - 2))]
      simp only [Nat.largeSchroder_zero, one_mul, Nat.sub_zero]
      rw [show length - 1 - 1 = length - 2 by omega]
      omega
  have smallCounts (sign : Bool) (length : ℕ) :
      Nat.card (Indecomposable sign length) = Nat.smallSchroder length := by
    by_cases small : length ≤ 1
    · rw [(tiny length small).2 sign]
      interval_cases length <;> simp
    · have large : 2 ≤ length := by omega
      apply Nat.mul_left_cancel (by omega : 0 < 2)
      rw [half sign length large, largeCounts length (by omega)]
      have shift := Nat.two_mul_smallSchroder_succ (n := length - 1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ length)] using shift.symm
  refine ⟨(tiny 0 (by omega)).1, largeCounts, smallCounts, half, signedOpposite, ?_⟩
  intro sign length small
  have : IsEmpty (ProperSigned sign length) :=
    ⟨fun π => noCut sign length small π.val π.property⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

#print axioms actual_signed_cut_enumeration
#print axioms actual_schroder_cardinality

end D5.S1.Words.Patterns.Separable.ActualCardinality
