/- GID: D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Multi-scale central digits are injective with exact length control. -/

import D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitInjection

open scoped BigOperators
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairLeadingCoefficients
open D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyHomogeneity
open D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution
open D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections
open D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords
open private exists_actual_independent_directions from
  D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections
open private rationalMagnus repeatedWord from
  D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords
open private degreeDifference multiScaleWord_central_data from
  D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitData

variable {A : Type*}

private theorem multiScaleWord_cutoff_injective
    [Fintype A] [LinearOrder A] (r t : ℕ) (hr : 2 ≤ r) :
    Function.Injective (fun digits : DigitArray (A := A) r t ↦
      cutoffMagnus r (multiScaleWord (A := A) r t digits)) := by
  classical
  intro left right hequal
  let vectors := fun direction : Fin (actualLyndonCount (A := A) r) ↦
    actualLeadingDifference r (selectedDirection (A := A) r direction)
  let coefficient := fun direction : Fin (actualLyndonCount (A := A) r) ↦
    (digitValue (A := A) r t left direction : ℚ) -
      (digitValue (A := A) r t right direction : ℚ)
  have hrelation : ∑ direction, coefficient direction • vectors direction = 0 := by
    ext word
    by_cases hle : FreeMonoid.length word ≤ r
    · rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
          MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
          Finsupp.zero_apply]
        apply Finset.sum_eq_zero
        intro direction _
        have hlower := literalPowerSubstitution_actual_positivePair
          (A := A) 1 r (selectedDirection (A := A) r direction)
          |>.2.2.2.2.1 (FreeMonoid.toList word) (by
            simpa [FreeMonoid.length] using hlt)
        let index := selectedDirection (A := A) r direction
        let bounded : CutoffWord A r := ⟨word, hle⟩
        have hactual : (actualLeadingDifference r index).coeff bounded.1 =
            (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
                (FreeMonoid.toList bounded.1) (positivePairWords r index).1 : ℚ) -
              (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
                (FreeMonoid.toList bounded.1) (positivePairWords r index).2 : ℚ) := by
          have hcoeffAt : (actualLeadingDifference r index).coeff bounded.1 =
              (cutoffMagnus r (positivePairWords r index).1 -
                cutoffMagnus r (positivePairWords r index).2) bounded := by
            simp [actualLeadingDifference, cutoffRestriction, cutoffLift,
              Finsupp.mapDomain_apply Subtype.val_injective]
          rw [hcoeffAt]
          simpa [cutoffMagnus, cutoffRestriction] using
            (full_positivePair_coefficient_checkpoint r index).2 bounded
        have hzero : (vectors direction).coeff word = 0 := by
          rw [hactual]
          apply sub_eq_zero.mpr
          exact_mod_cast (by simpa [literalPowerWord] using hlower)
        simp [hzero]
      · have hlength : (FreeMonoid.toList word).length = r := by
          simpa [FreeMonoid.length] using heq
        have hleft := multiScaleWord_central_data (A := A) r t left
          |>.2 (FreeMonoid.toList word) hlength
        have hright := multiScaleWord_central_data (A := A) r t right
          |>.2 (FreeMonoid.toList word) hlength
        have hcut := congrFun hequal ⟨word, hle⟩
        have hcoeff :
            (rationalMagnus (multiScaleWord (A := A) r t left)).coeff word =
              (rationalMagnus (multiScaleWord (A := A) r t right)).coeff word := by
          simpa [cutoffMagnus, cutoffRestriction, rationalMagnus] using hcut
        simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
          MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
          Finsupp.zero_apply]
        change ∑ direction, coefficient direction * (vectors direction).coeff word = 0
        calc
          _ = (∑ direction,
                (digitValue (A := A) r t left direction : ℚ) *
                  (vectors direction).coeff word) -
              (∑ direction,
                (digitValue (A := A) r t right direction : ℚ) *
                  (vectors direction).coeff word) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro direction _
                simp [coefficient]
                ring
          _ = degreeDifference (FreeMonoid.toList word)
                (multiScaleWord (A := A) r t left,
                  referenceWord (A := A) r t) -
              degreeDifference (FreeMonoid.toList word)
                (multiScaleWord (A := A) r t right,
                  referenceWord (A := A) r t) := by
                have hleft' : degreeDifference (FreeMonoid.toList word)
                    (multiScaleWord (A := A) r t left,
                      referenceWord (A := A) r t) =
                    ∑ direction,
                      (digitValue (A := A) r t left direction : ℚ) *
                        (vectors direction).coeff word := by
                  simpa [vectors, FreeMonoid.ofList_toList] using hleft
                have hright' : degreeDifference (FreeMonoid.toList word)
                    (multiScaleWord (A := A) r t right,
                      referenceWord (A := A) r t) =
                    ∑ direction,
                      (digitValue (A := A) r t right direction : ℚ) *
                        (vectors direction).coeff word := by
                  simpa [vectors, FreeMonoid.ofList_toList] using hright
                rw [hleft', hright']
          _ = 0 := by
                simp [degreeDifference, FreeMonoid.ofList_toList, hcoeff]
    · simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
        Finsupp.zero_apply]
      apply Finset.sum_eq_zero
      intro direction _
      have houtside : (vectors direction).coeff word = 0 := by
        simp only [vectors, actualLeadingDifference, cutoffLift,
          MonoidAlgebra.coeff_ofCoeff]
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨bounded, rfl⟩
        exact hle bounded.2
      simp [houtside]
  have hcoeffZero : ∀ direction, coefficient direction = 0 :=
    Fintype.linearIndependent_iff.mp
      (Classical.choose_spec (exists_actual_independent_directions (A := A) r))
      coefficient hrelation
  have hvalue : ∀ direction,
      digitValue (A := A) r t left direction =
        digitValue (A := A) r t right direction := by
    intro direction
    exact_mod_cast sub_eq_zero.mp (hcoeffZero direction)
  funext direction scale
  have hbase : 1 < digitBase r := by
    exact Nat.one_lt_pow (by omega) (by omega)
  have hlists := Nat.injOn_ofDigits hbase t
    (show (List.ofFn fun scale : Fin t ↦
        (left direction scale : ℕ)) ∈
        {digits | digits.length = t ∧
          ∀ digit ∈ digits, digit < digitBase r} by
      simp)
    (show (List.ofFn fun scale : Fin t ↦
        (right direction scale : ℕ)) ∈
        {digits | digits.length = t ∧
          ∀ digit ∈ digits, digit < digitBase r} by
      simp)
    (hvalue direction)
  have hfunctions :
      (fun scale : Fin t ↦ (left direction scale : ℕ)) =
        (fun scale : Fin t ↦ (right direction scale : ℕ)) :=
    List.ofFn_injective hlists
  exact Fin.ext (congrFun hfunctions scale)

/-- The actual recursive positive-pair family supplies a full multi-scale
central digit system: its selected directions are independent, every digit
word has the same lower cutoff and exact length, and the cutoff images are
injective with the expected finite cardinality. -/
theorem actual_positivePair_multiScale_central_digits
    [Fintype A] [LinearOrder A] (r t : ℕ) (hr : 2 ≤ r) :
    LinearIndependent ℚ
        (fun direction : Fin (actualLyndonCount (A := A) r) ↦
          actualLeadingDifference r
            (selectedDirection (A := A) r direction)) ∧
    (∀ direction : Fin (actualLyndonCount (A := A) r),
      (positivePairWords r
          (selectedDirection (A := A) r direction)).1 ≠ [] ∧
      (positivePairWords r
          (selectedDirection (A := A) r direction)).2 ≠ [] ∧
      (positivePairWords r
          (selectedDirection (A := A) r direction)).1.length =
        (positivePairWords r
          (selectedDirection (A := A) r direction)).2.length) ∧
    (∀ (digits : DigitArray (A := A) r t) (pattern : List A),
      pattern.length < r →
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (multiScaleWord (A := A) r t digits) =
        D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (referenceWord (A := A) r t)) ∧
    (∀ (digits : DigitArray (A := A) r t) (pattern : List A),
      pattern.length = r →
      (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (multiScaleWord (A := A) r t digits) : ℚ) -
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (referenceWord (A := A) r t) : ℚ) =
        ∑ direction : Fin (actualLyndonCount (A := A) r),
          (digitValue (A := A) r t digits direction : ℚ) *
            (actualLeadingDifference r
              (selectedDirection (A := A) r direction)).coeff
                (FreeMonoid.ofList pattern)) ∧
    Function.Injective (fun digits : DigitArray (A := A) r t ↦
      cutoffMagnus r (multiScaleWord (A := A) r t digits)) ∧
    Fintype.card (DigitArray (A := A) r t) =
      digitBase r ^ (t * actualLyndonCount (A := A) r) ∧
    ∀ digits : DigitArray (A := A) r t,
      (multiScaleWord (A := A) r t digits).length =
        baseLength (A := A) r * (2 ^ t - 1) := by
  classical
  refine ⟨Classical.choose_spec (exists_actual_independent_directions (A := A) r),
    ?_, ?_, ?_,
    multiScaleWord_cutoff_injective (A := A) r t hr, ?_, ?_⟩
  · intro direction
    exact (full_positivePair_coefficient_checkpoint r
      (selectedDirection (A := A) r direction)).1 hr
  · intro digits pattern hpattern
    have h := (multiScaleWord_central_data (A := A) r t digits).1
      pattern hpattern
    have hq :
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (multiScaleWord (A := A) r t digits) : ℚ) =
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (referenceWord (A := A) r t) : ℚ) := by
      simpa [rationalMagnus, toRationalWordPolynomial,
        magnusPolynomial_coeff_scatteredCount] using h
    exact_mod_cast hq
  · intro digits pattern hpattern
    have h := (multiScaleWord_central_data (A := A) r t digits).2
      pattern hpattern
    simpa [degreeDifference, rationalMagnus, toRationalWordPolynomial,
      magnusPolynomial_coeff_scatteredCount] using h
  · simp [DigitArray, pow_mul]
  · have digitBlock_length
        (direction : Fin (actualLyndonCount (A := A) r)) (scale : Fin t)
        (digit : Fin (digitBase r)) :
        (digitBlock (A := A) r direction scale digit).length =
          (digitBase r - 1) *
            (positivePairWords r
              (selectedDirection (A := A) r direction)).1.length *
                2 ^ (scale : ℕ) := by
      let pair := positivePairWords r (selectedDirection (A := A) r direction)
      have hpair := (full_positivePair_coefficient_checkpoint r
        (selectedDirection (A := A) r direction)).1 hr
      have hdigit : (digit : ℕ) ≤ digitBase r - 1 := by omega
      have hrepeated (n : ℕ) (word : List A) :
          (repeatedWord n word).length = n * word.length := by
        simp [repeatedWord]
      have hpower (m : ℕ) (word : List A) :
          (literalPowerWord m word).length = word.length * m := by
        induction word with
        | nil => simp [literalPowerWord]
        | cons a word ih => simp [literalPowerWord, Nat.add_mul, Nat.add_comm]
      simp only [digitBlock, List.length_append, hrepeated, hpower]
      rw [← hpair.2.2]
      calc
        (digit : ℕ) * (pair.1.length * 2 ^ (scale : ℕ)) +
            (digitBase r - 1 - (digit : ℕ)) *
              (pair.1.length * 2 ^ (scale : ℕ)) =
          ((digit : ℕ) + (digitBase r - 1 - (digit : ℕ))) *
            (pair.1.length * 2 ^ (scale : ℕ)) := (Nat.add_mul _ _ _).symm
        _ = (digitBase r - 1) * pair.1.length * 2 ^ (scale : ℕ) := by
          rw [Nat.add_sub_of_le hdigit, Nat.mul_assoc]
    have multiScaleWord_length (digits : DigitArray (A := A) r t) :
        (multiScaleWord (A := A) r t digits).length =
          baseLength (A := A) r * (2 ^ t - 1) := by
      simp only [multiScaleWord, List.length_flatten, List.map_ofFn,
        List.sum_ofFn, Function.comp_apply, digitBlock_length]
      have hgeom : ∑ scale : Fin t, 2 ^ (scale : ℕ) = 2 ^ t - 1 := by
        rw [Fin.sum_univ_eq_sum_range]
        simpa using Nat.geomSum_eq (m := 2) (by omega) t
      simp_rw [← Finset.mul_sum, hgeom]
      rw [← Finset.sum_mul]
      unfold baseLength
      rw [Finset.mul_sum]
    exact multiScaleWord_length



end D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitInjection
