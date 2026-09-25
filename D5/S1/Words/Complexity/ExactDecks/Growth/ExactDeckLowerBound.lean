/- GID: D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckLowerBound
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/Growth/ExactDeckLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-length padding loses exactly one degree in the exact-deck lower bound. -/

import D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
import D5.S1.Words.Complexity.ExactDecks.Growth.PositivePairBallGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckLowerBound

open scoped BigOperators
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections
open D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall
open D5.S1.Words.Complexity.ExactDecks.Growth.PositivePairBallGrowth
open D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore

variable {A : Type*}

theorem actual_exactKDeckImage_weightedLyndon_lower_bound
    [Fintype A] [LinearOrder A] (hq : 2 ≤ Fintype.card A)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C N : ℕ, 0 < C ∧
      ∀ n, N ≤ n →
        n ^ (weightedLyndonExponent (A := A) k - 1) ≤
          C * (exactKDeckImage (A := A) k n).card := by
  classical
  have mem_positiveWordBall_iff (n : ℕ) (x : CutoffCoefficients A k) :
      x ∈ positiveWordBall (A := A) k n ↔
        ∃ source : List A,
          source.length ≤ n ∧ cutoffMagnus k source = x := by
    simp [positiveWordBall]
  have mem_exactKDeckImage_iff (n : ℕ)
      (deck : {pattern : List A // pattern.length = k} → ℕ) :
      deck ∈ exactKDeckImage (A := A) k n ↔
        ∃ source : List A,
          source.length = n ∧ exactKDeck k source = deck := by
    simp [exactKDeckImage]
  let ballRepresentative (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) : List A :=
    Classical.choose ((mem_positiveWordBall_iff n x.1).mp x.2)
  have ballRepresentative_length (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) :
      (ballRepresentative n x).length ≤ n :=
    (Classical.choose_spec
      ((mem_positiveWordBall_iff n x.1).mp x.2)).1
  have ballRepresentative_cutoff (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) :
      cutoffMagnus k (ballRepresentative n x) = x.1 :=
    (Classical.choose_spec
      ((mem_positiveWordBall_iff n x.1).mp x.2)).2
  let fixedLetter : A :=
    Classical.choice (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card A))
  let paddedWord (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) : List A :=
    ballRepresentative n x ++
      List.replicate (n - (ballRepresentative n x).length) fixedLetter
  have paddedWord_length (n : ℕ)
      (x : ↑(positiveWordBall (A := A) k n)) :
      (paddedWord n x).length = n := by
    dsimp only [paddedWord]
    rw [List.length_append, List.length_replicate]
    have hlength := ballRepresentative_length n x
    omega
  have cutoffMagnus_append (r : ℕ) (left right : List A) :
      cutoffMagnus r (left ++ right) =
        cutoffMul r (cutoffMagnus r left) (cutoffMagnus r right) := by
    simp only [cutoffMagnus, magnusPolynomial_append, map_mul,
      cutoffRestriction_mul]
  have cutoffMagnus_empty_coeff (r : ℕ) (source : List A) :
      cutoffMagnus r source ⟨1, by simp⟩ = 1 := by
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom]
    change ((magnusPolynomial source).coeff (FreeMonoid.ofList []) : ℚ) = 1
    rw [magnusPolynomial_coeff_scatteredCount source []]
    norm_num [scatteredCount]
  have cutoffMagnus_tail_vanishes (r : ℕ) (source : List A) :
      VanishesBelow r 1 (cutoffMagnus r source - cutoffOne r) := by
    intro word hword
    have hlength : FreeMonoid.length word.1 = 0 := by omega
    have hempty : word.1 = 1 := by
      apply FreeMonoid.toList.injective
      apply List.length_eq_zero_iff.mp
      simpa [FreeMonoid.length] using hlength
    have hwordSubtype : word = ⟨1, by simp⟩ := Subtype.ext hempty
    rw [hwordSubtype]
    simp [cutoffMagnus_empty_coeff, cutoffOne, cutoffRestriction]
  have cutoffMagnus_eq_one_add_tail (r : ℕ) (source : List A) :
      cutoffMagnus r source =
        cutoffOne r + (cutoffMagnus r source - cutoffOne r) := by
    abel
  have cutoffRightUnit (r : ℕ) (p : CutoffCoefficients A r) :
      cutoffMul r p (cutoffOne r) = p := by
    have hrestrict : cutoffRestriction r (cutoffLift r p) = p := by
      funext w
      simp [cutoffRestriction, cutoffLift,
        Finsupp.mapDomain_apply Subtype.val_injective]
    calc
      _ = cutoffMul r (cutoffRestriction r (cutoffLift r p))
          (cutoffRestriction r 1) := by rw [cutoffOne, hrestrict]
      _ = cutoffRestriction r (cutoffLift r p * 1) :=
        (cutoffRestriction_mul r (cutoffLift r p) 1).symm
      _ = p := by simpa using hrestrict
  have cutoffAssoc (r : ℕ) (p q s : CutoffCoefficients A r) :
      cutoffMul r (cutoffMul r p q) s = cutoffMul r p (cutoffMul r q s) := by
    have hrestrict (x : CutoffCoefficients A r) :
        cutoffRestriction r (cutoffLift r x) = x := by
      funext w
      simp [cutoffRestriction, cutoffLift,
        Finsupp.mapDomain_apply Subtype.val_injective]
    have hp := hrestrict p
    have hq := hrestrict q
    have hs := hrestrict s
    calc
      _ = cutoffRestriction r
          ((cutoffLift r p * cutoffLift r q) * cutoffLift r s) := by
            rw [cutoffRestriction_mul, cutoffRestriction_mul, hp, hq, hs]
      _ = cutoffRestriction r
          (cutoffLift r p * (cutoffLift r q * cutoffLift r s)) := by rw [mul_assoc]
      _ = _ := by rw [cutoffRestriction_mul, cutoffRestriction_mul, hp, hq, hs]
  have cutoffMagnus_cancel_right (r : ℕ)
      (left right suffixLeft suffixRight : List A)
      (hsuffix : cutoffMagnus r suffixLeft = cutoffMagnus r suffixRight)
      (h : cutoffMagnus r (left ++ suffixLeft) =
        cutoffMagnus r (right ++ suffixRight)) :
      cutoffMagnus r left = cutoffMagnus r right := by
    rw [cutoffMagnus_append, cutoffMagnus_append, hsuffix] at h
    let tail := cutoffMagnus r suffixRight - cutoffOne r
    let inverse := cutoffGeometricInverse r tail
    have htail : VanishesBelow r 1 tail :=
      cutoffMagnus_tail_vanishes r suffixRight
    have hinverse : cutoffMul r (cutoffMagnus r suffixRight) inverse =
        cutoffOne r := by
      rw [cutoffMagnus_eq_one_add_tail r suffixRight]
      exact cutoffMul_geometricInverse r tail htail
    have h' := congrArg (fun x ↦ cutoffMul r x inverse) h
    simpa only [cutoffAssoc, hinverse, cutoffRightUnit] using h'
  have ball_card_le_exact (n : ℕ) (hkn : k ≤ n) :
      (positiveWordBall (A := A) k n).card ≤
        (n + 1) * (exactKDeckImage (A := A) k n).card := by
    let embed : ↑(positiveWordBall (A := A) k n) →
        Fin (n + 1) × ↑(exactKDeckImage (A := A) k n) :=
      fun x ↦
        (⟨(ballRepresentative n x).length,
            Nat.lt_succ_of_le (ballRepresentative_length n x)⟩,
          ⟨exactKDeck k (paddedWord n x),
            (mem_exactKDeckImage_iff n _).2
              ⟨paddedWord n x, paddedWord_length n x, rfl⟩⟩)
    have hinjective : Function.Injective embed := by
      intro left right heq
      have hlength : (ballRepresentative n left).length =
          (ballRepresentative n right).length :=
        congrArg (fun output ↦ output.1.val) heq
      have hdeck : exactKDeck k (paddedWord n left) =
          exactKDeck k (paddedWord n right) :=
        congrArg (fun output ↦ output.2.val) heq
      have hpaddedCutoff :=
        (exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length
          k n (paddedWord n left) (paddedWord n right)
          (paddedWord_length n left) (paddedWord_length n right) hkn).mp hdeck
      have hsuffixWords :
          List.replicate (n - (ballRepresentative n left).length) fixedLetter =
            List.replicate
              (n - (ballRepresentative n right).length) fixedLetter := by
        rw [hlength]
      have hsuffixCutoff :
          cutoffMagnus k
              (List.replicate
                (n - (ballRepresentative n left).length) fixedLetter) =
            cutoffMagnus k
              (List.replicate
                (n - (ballRepresentative n right).length) fixedLetter) := by
        rw [hsuffixWords]
      dsimp only [paddedWord] at hpaddedCutoff
      have hrepresentatives := cutoffMagnus_cancel_right k
        (ballRepresentative n left) (ballRepresentative n right)
        (List.replicate
          (n - (ballRepresentative n left).length) fixedLetter)
        (List.replicate
          (n - (ballRepresentative n right).length) fixedLetter)
        hsuffixCutoff hpaddedCutoff
      apply Subtype.ext
      rw [← ballRepresentative_cutoff n left,
        ← ballRepresentative_cutoff n right]
      exact hrepresentatives
    have hcard := Fintype.card_le_of_injective embed hinjective
    simpa only [Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe] using hcard
  have exponent_pos :
      1 ≤ weightedLyndonExponent (A := A) k := by
    have hcountOne : 1 ≤ actualLyndonCount (A := A) 1 := by
      unfold actualLyndonCount
      have hpos : 0 < Fintype.card (ActualLyndonWord A 1) :=
        Fintype.card_pos_iff.mpr ⟨⟨[fixedLetter], by
          refine ⟨rfl, ?_⟩
          refine ⟨by simp, ?_⟩
          intro u v hu hv huv
          have hlen := congrArg List.length huv
          simp only [List.length_singleton, List.length_append] at hlen
          have huPos : 0 < u.length := List.length_pos_of_ne_nil hu
          have hvPos : 0 < v.length := List.length_pos_of_ne_nil hv
          omega⟩⟩
      omega
    have hone_mem : 1 ∈ Finset.range (k + 1) := by simp; omega
    have hterm : 1 * actualLyndonCount (A := A) 1 ≤
        ∑ i ∈ Finset.range (k + 1),
          i * actualLyndonCount (A := A) i := by
      exact Finset.single_le_sum
        (fun i _ ↦ Nat.zero_le
          (i * actualLyndonCount (A := A) i)) hone_mem
    unfold weightedLyndonExponent
    exact hcountOne.trans (by simpa using hterm)
  obtain ⟨C, N, hC, hball⟩ :=
    actual_positiveWordBall_weightedLyndon_lower_bound
      (A := A) hq k hk
  refine ⟨2 * C, max N (max k 1), by positivity, ?_⟩
  intro n hn
  have hnN : N ≤ n := (Nat.le_max_left N (max k 1)).trans hn
  have hnk : k ≤ n :=
    (Nat.le_max_right N (max k 1)).trans hn |>.trans' (Nat.le_max_left k 1)
  have hnpos : 0 < n := by
    have : 1 ≤ n :=
      (Nat.le_max_right N (max k 1)).trans hn |>.trans' (Nat.le_max_right k 1)
    omega
  have hballBound := hball n hnN
  have hcard := ball_card_le_exact n hnk
  have hcancel :
      n ^ (weightedLyndonExponent (A := A) k - 1) * n ≤
        ((2 * C) * (exactKDeckImage (A := A) k n).card) * n := by
    calc
      n ^ (weightedLyndonExponent (A := A) k - 1) * n =
          n ^ (weightedLyndonExponent (A := A) k - 1 + 1) := by
        rw [pow_succ]
      _ = n ^ weightedLyndonExponent (A := A) k := by
        rw [Nat.sub_add_cancel exponent_pos]
      _ ≤ C * (positiveWordBall (A := A) k n).card := hballBound
      _ ≤ C * ((n + 1) * (exactKDeckImage (A := A) k n).card) :=
        Nat.mul_le_mul_left C hcard
      _ ≤ C * ((2 * n) * (exactKDeckImage (A := A) k n).card) := by
        gcongr
        omega
      _ = ((2 * C) * (exactKDeckImage (A := A) k n).card) * n := by
        ring
  exact Nat.le_of_mul_le_mul_right hcancel hnpos

#print axioms exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length
#print axioms actual_exactKDeckImage_weightedLyndon_lower_bound


end D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckLowerBound
