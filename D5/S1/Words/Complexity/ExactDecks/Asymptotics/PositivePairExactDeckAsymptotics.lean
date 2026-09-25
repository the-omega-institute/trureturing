/- GID: D5/S1/Words/Complexity/ExactDecks/Asymptotics/PositivePairExactDeckAsymptotics
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/Asymptotics/PositivePairExactDeckAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact k-deck images have the full weighted-Lyndon asymptotic exponent. -/

/-
proof_shape: content. The public conclusion uses a new finite-coordinate injection:
  one actual Lyndon coordinate is erased, its singleton count is recovered from
  the common source length, and unconditional Lyndon recovery then identifies
  the complete exact deck.
Direct unfrozen dependencies: the split Lyndon, positive-pair, growth, and
  upper-bound providers ending in FullLyndonRecovery. Source acceptance is not freeze status.
escape_witness: the proof-local injection from exact-deck images into the
  dependent retained-coordinate box is live in the upper asymptotic bound and
  is not supplied by any provider or pinned Mathlib declaration.
admission_basis: open-problem-resolution; preregistration #9512.
utility: none; this is a general structural and asymptotic theorem, not a finite
  enumeration, checker, numeric reduction, or certified instance.
Library search: no project declaration packages the exact upper injection or
  IsTheta endpoint. Pinned Mathlib supplies Nat.choose_le_pow,
  Fintype.card_pi, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, and
  Asymptotics.isBigO_iff'. Loogle confirmed Fintype.card_pi; LeanSearch's
  queried API route returned HTTP 404, so it supplied no additional result.
-/


import D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckLowerBound
import D5.S1.Words.Complexity.ExactDecks.UpperBound.FullLyndonRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.Asymptotics.PositivePairExactDeckAsymptotics

open scoped BigOperators
open Filter _root_.Asymptotics
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections
open D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall
open D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
open D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckLowerBound
open D5.S1.Words.Complexity.ExactDecks.UpperBound.FullLyndonRecovery

open private scatteredCount_singleton_eq_count letterActualLyndonEquiv from
  D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall
open private scatteredCount_eq_count_sublistsLen from
  D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore

variable {A : Type*}

/-- For every positive deck length over a finite ordered alphabet with at least
two letters, the number of actual exact `k`-decks of length-`n` words has the
source-faithful weighted-Lyndon exponent, with the single fixed-length relation
removing exactly one degree of freedom. -/
theorem actual_exactKDeckImage_weightedLyndon_isTheta
    [Fintype A] [LinearOrder A] (hq : 2 ≤ Fintype.card A)
    (k : ℕ) (hk : 1 ≤ k) :
    (fun n : ℕ => ((exactKDeckImage (A := A) k n).card : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^
        (weightedLyndonExponent (A := A) k - 1)) := by
  classical
  let a0 : A :=
    Classical.choice (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card A))
  let Coordinate := Σ j : Fin k, ActualLyndonWord A (j.val + 1)
  let missing : Coordinate :=
    ⟨⟨0, hk⟩, ⟨[a0], by
      refine ⟨by simp, ?_⟩
      refine ⟨by simp, ?_⟩
      intro u v hu hv huv
      have hlen := congrArg List.length huv
      simp only [List.length_singleton, List.length_append] at hlen
      have huPos : 0 < u.length := List.length_pos_of_ne_nil hu
      have hvPos : 0 < v.length := List.length_pos_of_ne_nil hv
      omega⟩⟩
  let retained : Finset Coordinate := Finset.univ.erase missing
  have actualLyndonCount_one :
      actualLyndonCount (A := A) 1 = Fintype.card A := by
    unfold actualLyndonCount
    exact (Fintype.card_congr letterActualLyndonEquiv).symm
  have fullWeight :
      (∑ coordinate : Coordinate, coordinate.2.1.length) =
        weightedLyndonExponent (A := A) k := by
    change (∑ coordinate : Σ j : Fin k,
        ActualLyndonWord A (j.val + 1), coordinate.2.1.length) = _
    rw [Fintype.sum_sigma]
    simp_rw [show ∀ (j : Fin k) (word : ActualLyndonWord A (j.val + 1)),
        word.1.length = j.val + 1 by intro j word; exact word.2.1]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    simp_rw [mul_comm]
    unfold weightedLyndonExponent
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_mul]
    rw [← Fin.sum_univ_eq_sum_range]
    simp [actualLyndonCount]
  have exponent_pos :
      1 ≤ weightedLyndonExponent (A := A) k := by
    have hcount : 1 ≤ actualLyndonCount (A := A) 1 := by
      rw [actualLyndonCount_one]
      omega
    have hone : 1 ∈ Finset.range (k + 1) := by simp; omega
    unfold weightedLyndonExponent
    exact hcount.trans (by
      simpa using Finset.single_le_sum
        (fun i _ => Nat.zero_le
          (i * actualLyndonCount (A := A) i)) hone)
  have retainedWeight :
      (∑ coordinate : ↑retained, coordinate.1.2.1.length) =
        weightedLyndonExponent (A := A) k - 1 := by
    let weight : Coordinate → ℕ := fun coordinate => coordinate.2.1.length
    have hmissing : weight missing = 1 := by simp [weight, missing]
    have herase := Finset.sum_erase_add
      (s := (Finset.univ : Finset Coordinate))
      (f := weight)
      (Finset.mem_univ missing)
    have hattached :
        (∑ coordinate : ↑retained, weight coordinate.1) =
          ∑ coordinate ∈ retained, weight coordinate := by
      rw [Finset.univ_eq_attach retained]
      exact Finset.sum_attach retained weight
    have hfullWeight :
        (∑ coordinate : Coordinate, weight coordinate) =
          weightedLyndonExponent (A := A) k := by
      simpa only [weight] using fullWeight
    change (∑ coordinate : ↑retained, weight coordinate.1) = _
    rw [hattached]
    have hsum :
        (∑ coordinate ∈ Finset.univ.erase missing, weight coordinate) + 1 =
          weightedLyndonExponent (A := A) k := by
      simpa only [hmissing, hfullWeight] using herase
    dsimp only [retained]
    omega
  have mem_exactKDeckImage_iff (n : ℕ)
      (deck : {pattern : List A // pattern.length = k} → ℕ) :
      deck ∈ exactKDeckImage (A := A) k n ↔
        ∃ source : List A,
          source.length = n ∧ exactKDeck k source = deck := by
    simp [exactKDeckImage]
  let representative (n : ℕ)
      (deck : ↑(exactKDeckImage (A := A) k n)) : List A :=
    Classical.choose ((mem_exactKDeckImage_iff n deck.1).mp deck.2)
  have representative_length (n : ℕ)
      (deck : ↑(exactKDeckImage (A := A) k n)) :
      (representative n deck).length = n :=
    (Classical.choose_spec
      ((mem_exactKDeckImage_iff n deck.1).mp deck.2)).1
  have representative_deck (n : ℕ)
      (deck : ↑(exactKDeckImage (A := A) k n)) :
      exactKDeck k (representative n deck) = deck.1 :=
    (Classical.choose_spec
      ((mem_exactKDeckImage_iff n deck.1).mp deck.2)).2
  have coordinate_bound (n : ℕ)
      (deck : ↑(exactKDeckImage (A := A) k n))
      (coordinate : ↑retained) :
      scatteredCount coordinate.1.2.1 (representative n deck) ≤
        n ^ coordinate.1.2.1.length := by
    rw [scatteredCount_eq_count_sublistsLen]
    calc
      ((representative n deck).sublistsLen
          coordinate.1.2.1.length).count coordinate.1.2.1 ≤
          ((representative n deck).sublistsLen
            coordinate.1.2.1.length).length := List.count_le_length
      _ = Nat.choose (representative n deck).length
          coordinate.1.2.1.length :=
        List.length_sublistsLen coordinate.1.2.1.length
          (representative n deck)
      _ = Nat.choose n coordinate.1.2.1.length := by
        rw [representative_length]
      _ ≤ n ^ coordinate.1.2.1.length := Nat.choose_le_pow _ _
  let coordinateCode (n : ℕ)
      (deck : ↑(exactKDeckImage (A := A) k n)) :
      (coordinate : ↑retained) → Fin (n ^ coordinate.1.2.1.length + 1) :=
    fun coordinate =>
      ⟨scatteredCount coordinate.1.2.1 (representative n deck),
        Nat.lt_succ_of_le (coordinate_bound n deck coordinate)⟩
  have sum_letter_counts (source : List A) :
      (∑ a : A, source.count a) = source.length := by
    rw [← List.sum_toFinset_count_eq_length source]
    symm
    apply Finset.sum_subset (Finset.subset_univ source.toFinset)
    intro a _ ha
    exact List.count_eq_zero.mpr (by simpa using ha)
  have coordinateCode_injective (n : ℕ) :
      Function.Injective (coordinateCode n) := by
    intro left right hcode
    let leftSource := representative n left
    let rightSource := representative n right
    have retained_count_eq (coordinate : Coordinate)
        (hcoordinate : coordinate ∈ retained) :
        scatteredCount coordinate.2.1 leftSource =
          scatteredCount coordinate.2.1 rightSource := by
      let retainedCoordinate : ↑retained := ⟨coordinate, hcoordinate⟩
      have hvalue := congrArg
        (fun code => (code retainedCoordinate).val) hcode
      exact hvalue
    have other_singleton_count_eq (a : A) (ha : a ≠ a0) :
        leftSource.count a = rightSource.count a := by
      let coordinate : Coordinate :=
        ⟨⟨0, hk⟩, ⟨[a], by
          refine ⟨by simp, ?_⟩
          refine ⟨by simp, ?_⟩
          intro u v hu hv huv
          have hlen := congrArg List.length huv
          simp only [List.length_singleton, List.length_append] at hlen
          have huPos : 0 < u.length := List.length_pos_of_ne_nil hu
          have hvPos : 0 < v.length := List.length_pos_of_ne_nil hv
          omega⟩⟩
      have hne : coordinate ≠ missing := by
        intro heq
        have hword := congrArg (fun x : Coordinate => x.2.1) heq
        simp only [coordinate, missing] at hword
        exact ha (List.singleton_injective hword)
      have hmem : coordinate ∈ retained := by
        simp [retained, hne]
      simpa only [coordinate, scatteredCount_singleton_eq_count] using
        retained_count_eq coordinate hmem
    have missing_singleton_count_eq :
        leftSource.count a0 = rightSource.count a0 := by
      have hother :
          (∑ a ∈ (Finset.univ : Finset A).erase a0, leftSource.count a) =
            ∑ a ∈ (Finset.univ : Finset A).erase a0,
              rightSource.count a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact other_singleton_count_eq a (Finset.mem_erase.mp ha).1
      have hleftTotal := sum_letter_counts leftSource
      have hrightTotal := sum_letter_counts rightSource
      rw [← Finset.sum_erase_add (s := (Finset.univ : Finset A))
          (f := fun a => leftSource.count a) (Finset.mem_univ a0),
        hother, representative_length n left] at hleftTotal
      rw [← Finset.sum_erase_add (s := (Finset.univ : Finset A))
          (f := fun a => rightSource.count a) (Finset.mem_univ a0),
        representative_length n right] at hrightTotal
      omega
    have lyndon_count_eq (word : List A) (hword : IsLyndon word)
        (hwordLength : word.length ≤ k) :
        scatteredCount word leftSource = scatteredCount word rightSource := by
      have hwordPos : 0 < word.length := List.length_pos_of_ne_nil hword.1
      let j : Fin k := ⟨word.length - 1, by omega⟩
      let actual : ActualLyndonWord A (j.val + 1) :=
        ⟨word, by simp only [j]; exact ⟨by omega, hword⟩⟩
      let coordinate : Coordinate := ⟨j, actual⟩
      by_cases hmissing : coordinate = missing
      · have hwordMissing := congrArg (fun x : Coordinate => x.2.1) hmissing
        change word = [a0] at hwordMissing
        subst word
        simpa only [scatteredCount_singleton_eq_count] using
          missing_singleton_count_eq
      · exact retained_count_eq coordinate (by simp [retained, hmissing])
    have hallCounts := scatteredCount_eq_of_lyndon_coordinates
      k leftSource rightSource lyndon_count_eq
    apply Subtype.ext
    rw [← representative_deck n left, ← representative_deck n right]
    funext pattern
    have hdec : LinearOrder.toDecidableEq = Classical.decEq A :=
      Subsingleton.elim _ _
    rw [hdec] at hallCounts
    simpa only [exactKDeck] using
      hallCounts pattern.1 (by rw [pattern.2])
  have upper_card (n : ℕ) (hn : 1 ≤ n) :
      (exactKDeckImage (A := A) k n).card ≤
        2 ^ Fintype.card ↑retained *
          n ^ (weightedLyndonExponent (A := A) k - 1) := by
    have hinjection := Fintype.card_le_of_injective
      (coordinateCode n) (coordinateCode_injective n)
    have hbox :
        Fintype.card ((coordinate : ↑retained) →
          Fin (n ^ coordinate.1.2.1.length + 1)) =
          ∏ coordinate : ↑retained,
            (n ^ coordinate.1.2.1.length + 1) := by
      simp only [Fintype.card_pi, Fintype.card_fin]
    rw [Fintype.card_coe, hbox] at hinjection
    calc
      (exactKDeckImage (A := A) k n).card ≤
          ∏ coordinate : ↑retained,
            (n ^ coordinate.1.2.1.length + 1) := hinjection
      _ ≤ ∏ coordinate : ↑retained,
          (2 * n ^ coordinate.1.2.1.length) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro coordinate _
        have hpow : 1 ≤ n ^ coordinate.1.2.1.length :=
          Nat.one_le_pow coordinate.1.2.1.length n (by omega)
        omega
      _ = 2 ^ Fintype.card ↑retained *
          n ^ (∑ coordinate : ↑retained,
            coordinate.1.2.1.length) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        simp
      _ = 2 ^ Fintype.card ↑retained *
          n ^ (weightedLyndonExponent (A := A) k - 1) := by
        rw [retainedWeight]
  constructor
  · rw [isBigO_iff']
    refine ⟨(2 ^ Fintype.card ↑retained : ℝ), by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hcardNonneg :
        (0 : ℝ) ≤ ((exactKDeckImage (A := A) k n).card : ℝ) := by
      positivity
    have hpowNonneg :
        (0 : ℝ) ≤ (n : ℝ) ^
          (weightedLyndonExponent (A := A) k - 1) := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hcardNonneg,
      Real.norm_eq_abs, abs_of_nonneg hpowNonneg]
    exact_mod_cast upper_card n hn
  · obtain ⟨C, N, hC, hlower⟩ :=
      actual_exactKDeckImage_weightedLyndon_lower_bound
        (A := A) hq k hk
    rw [isBigO_iff']
    refine ⟨(C : ℝ), by exact_mod_cast hC, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpowNonneg :
        (0 : ℝ) ≤ (n : ℝ) ^
          (weightedLyndonExponent (A := A) k - 1) := by
      positivity
    have hcardNonneg :
        (0 : ℝ) ≤ ((exactKDeckImage (A := A) k n).card : ℝ) := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpowNonneg,
      Real.norm_eq_abs, abs_of_nonneg hcardNonneg]
    exact_mod_cast hlower n hn

#print axioms actual_exactKDeckImage_weightedLyndon_isTheta

end D5.S1.Words.Complexity.ExactDecks.Asymptotics.PositivePairExactDeckAsymptotics
