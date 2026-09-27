/- GID: D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitData
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Digits/CentralDigitData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal digit blocks preserve lower coefficients and expose leading coordinates. -/

import D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitData

open scoped BigOperators
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairLeadingCoefficients
open D5.S1.Words.Complexity.PositivePairs.Span.FullFamilyHomogeneity
open D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution
open D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections
open D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords
open private AgreesBelow agreesBelow_append_and_degree_add directionWord
  rationalMagnus repeatedWord repeatedWord_central_data zeroDigit from
  D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords

variable {A : Type*}

private theorem digitBlock_central_data
    [Fintype A] [LinearOrder A] (r t : ℕ)
    (direction : Fin (actualLyndonCount (A := A) r)) (scale : Fin t)
    (digit : Fin (digitBase r)) :
    AgreesBelow r (digitBlock (A := A) r direction scale digit)
        (digitBlock (A := A) r direction scale 0) ∧
      ∀ pattern : List A, pattern.length = r →
        (rationalMagnus (digitBlock (A := A) r direction scale digit)).coeff
              (FreeMonoid.ofList pattern) -
            (rationalMagnus (digitBlock (A := A) r direction scale 0)).coeff
              (FreeMonoid.ofList pattern) =
          (digit : ℚ) * ((digitBase r : ℕ) ^ (scale : ℕ) : ℚ) *
            (actualLeadingDifference r
              (selectedDirection (A := A) r direction)).coeff
                (FreeMonoid.ofList pattern) := by
  classical
  have poweredPair_central_data (scale' : ℕ) :
      let pair := positivePairWords r (selectedDirection (A := A) r direction)
      let u := literalPowerWord (2 ^ scale') pair.1
      let v := literalPowerWord (2 ^ scale') pair.2
      AgreesBelow r u v ∧
        ∀ pattern : List A, pattern.length = r →
          (rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
              (rationalMagnus v).coeff (FreeMonoid.ofList pattern) =
            ((digitBase r : ℕ) ^ scale' : ℚ) *
              (actualLeadingDifference r
                (selectedDirection (A := A) r direction)).coeff
                  (FreeMonoid.ofList pattern) := by
    dsimp only
    let index := selectedDirection (A := A) r direction
    let pair := positivePairWords r index
    have hpower := literalPowerSubstitution_actual_positivePair
      (A := A) (2 ^ scale') r index
    constructor
    · intro pattern hp
      simp only [rationalMagnus, toRationalWordPolynomial,
        MonoidAlgebra.coeff_mapRingHom, magnusPolynomial_coeff_scatteredCount]
      change
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern (literalPowerWord (2 ^ scale') pair.1) : ℚ) =
          (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern (literalPowerWord (2 ^ scale') pair.2) : ℚ)
      exact_mod_cast hpower.2.2.2.2.1 pattern hp
    · intro pattern hp
      simp only [rationalMagnus, toRationalWordPolynomial,
        MonoidAlgebra.coeff_mapRingHom, magnusPolynomial_coeff_scatteredCount]
      have hdegree := hpower.2.2.2.2.2 pattern hp
      let bounded : CutoffWord A r :=
        ⟨FreeMonoid.ofList pattern, by simpa [FreeMonoid.length, hp]⟩
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
        simp only [Pi.sub_apply, cutoffMagnus, cutoffRestriction,
          toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom]
        rw [show bounded.1 = FreeMonoid.ofList (FreeMonoid.toList bounded.1) by
          exact (FreeMonoid.ofList_toList bounded.1).symm,
          magnusPolynomial_coeff_scatteredCount,
          magnusPolynomial_coeff_scatteredCount]
        norm_num
      rw [show ((2 ^ scale' : ℕ) : ℚ) ^ r =
          ((digitBase r : ℕ) ^ scale' : ℚ) by
        norm_num [digitBase, ← pow_mul, Nat.mul_comm]] at hdegree
      have hactual' :
          (actualLeadingDifference r index).coeff (FreeMonoid.ofList pattern) =
            (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
                pattern pair.1 : ℚ) -
              (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
                pattern pair.2 : ℚ) := by
        simpa [bounded, pair, FreeMonoid.ofList_toList] using hactual
      rw [hactual']
      exact hdegree
  let pair := positivePairWords r (selectedDirection (A := A) r direction)
  let u := literalPowerWord (2 ^ (scale : ℕ)) pair.1
  let v := literalPowerWord (2 ^ (scale : ℕ)) pair.2
  have hp := poweredPair_central_data (scale : ℕ)
  have hrep := repeatedWord_central_data r (digit : ℕ) hp.1
  have htail : AgreesBelow r
      (repeatedWord (digitBase r - 1 - (digit : ℕ)) v)
      (repeatedWord (digitBase r - 1 - (digit : ℕ)) v) := by
    intro pattern _
    rfl
  have happ := agreesBelow_append_and_degree_add r hrep.1 htail
  have hdigitLe : (digit : ℕ) ≤ digitBase r - 1 := by
    have hdigit : (digit : ℕ) < digitBase r := digit.isLt
    omega
  have hrepeatAdd (m n : ℕ) (word : List A) :
      repeatedWord m word ++ repeatedWord n word = repeatedWord (m + n) word := by
    unfold repeatedWord
    rw [List.replicate_add, List.flatten_append]
  have href : repeatedWord (digit : ℕ) v ++
      repeatedWord (digitBase r - 1 - (digit : ℕ)) v =
        digitBlock (A := A) r direction scale 0 := by
    rw [hrepeatAdd, Nat.add_sub_of_le hdigitLe]
    simp [digitBlock, pair, v, repeatedWord]
  constructor
  · simpa [digitBlock, pair, u, v, href] using happ.1
  · intro pattern hpattern
    have hdegree := happ.2 pattern hpattern
    rw [hrep.2 pattern hpattern] at hdegree
    simpa [digitBlock, pair, u, v, href, hp.2 pattern hpattern,
      mul_assoc] using hdegree

private noncomputable def degreeDifference (pattern : List A)
    (words : List A × List A) : ℚ :=
  (rationalMagnus words.1).coeff (FreeMonoid.ofList pattern) -
    (rationalMagnus words.2).coeff (FreeMonoid.ofList pattern)

private theorem flatten_central_data
    (r : ℕ) (words : List (List A × List A))
    (hbelow : ∀ words' ∈ words, AgreesBelow r words'.1 words'.2) :
    AgreesBelow r (words.map Prod.fst).flatten
        (words.map Prod.snd).flatten ∧
      ∀ pattern : List A, pattern.length = r →
        degreeDifference pattern
            ((words.map Prod.fst).flatten, (words.map Prod.snd).flatten) =
          (words.map (degreeDifference pattern)).sum := by
  classical
  induction words with
  | nil =>
      constructor
      · intro pattern _
        rfl
      · intro pattern _
        simp [degreeDifference]
  | cons head tail ih =>
      have hhead : AgreesBelow r head.1 head.2 := hbelow head (by simp)
      have htail : ∀ words' ∈ tail, AgreesBelow r words'.1 words'.2 := by
        intro words' hwords'
        exact hbelow words' (by simp [hwords'])
      have htailData := ih htail
      have happ := agreesBelow_append_and_degree_add r hhead htailData.1
      constructor
      · simpa using happ.1
      · intro pattern hpattern
        have hdegree := happ.2 pattern hpattern
        change degreeDifference pattern
              (head.1 ++ (tail.map Prod.fst).flatten,
                head.2 ++ (tail.map Prod.snd).flatten) =
            degreeDifference pattern head +
              degreeDifference pattern
                ((tail.map Prod.fst).flatten, (tail.map Prod.snd).flatten) at hdegree
        rw [htailData.2 pattern hpattern] at hdegree
        simpa only [List.map_cons, List.flatten_cons, List.sum_cons] using hdegree

private theorem directionWord_central_data
    [Fintype A] [LinearOrder A] (r t : ℕ)
    (digits : DigitArray (A := A) r t)
    (direction : Fin (actualLyndonCount (A := A) r)) :
    AgreesBelow r (directionWord (A := A) r t digits direction)
        (directionWord (A := A) r t (fun _ _ ↦ zeroDigit r) direction) ∧
      ∀ pattern : List A, pattern.length = r →
        degreeDifference pattern
            (directionWord (A := A) r t digits direction,
              directionWord (A := A) r t (fun _ _ ↦ zeroDigit r) direction) =
          (digitValue (A := A) r t digits direction : ℚ) *
            (actualLeadingDifference r
              (selectedDirection (A := A) r direction)).coeff
                (FreeMonoid.ofList pattern) := by
  classical
  let words : List (List A × List A) :=
    List.ofFn fun scale : Fin t ↦
      (digitBlock (A := A) r direction scale (digits direction scale),
        digitBlock (A := A) r direction scale 0)
  have hbelow : ∀ words' ∈ words,
      AgreesBelow r words'.1 words'.2 := by
    intro words' hwords'
    rcases List.mem_ofFn.mp hwords' with ⟨scale, rfl⟩
    exact (digitBlock_central_data (A := A) r t direction scale
      (digits direction scale)).1
  have hdata := flatten_central_data (A := A) r words hbelow
  have hvalueSum : (digitValue (A := A) r t digits direction : ℚ) =
      ∑ scale : Fin t, (digits direction scale : ℚ) *
        ((digitBase r : ℕ) ^ (scale : ℕ) : ℚ) := by
    have hnat : digitValue (A := A) r t digits direction =
        ∑ scale : Fin t,
          (digits direction scale : ℕ) * digitBase r ^ (scale : ℕ) := by
      simp [digitValue, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn,
        List.sum_ofFn]
    exact_mod_cast hnat
  constructor
  · simpa [words, directionWord, zeroDigit, Function.comp_def] using hdata.1
  · intro pattern hpattern
    calc
      degreeDifference pattern
          (directionWord (A := A) r t digits direction,
            directionWord (A := A) r t (fun _ _ ↦ zeroDigit r) direction) =
          (words.map (degreeDifference pattern)).sum := by
            simpa [words, directionWord, zeroDigit, Function.comp_def] using
              hdata.2 pattern hpattern
      _ = ∑ scale : Fin t,
            (digits direction scale : ℚ) *
                ((digitBase r : ℕ) ^ (scale : ℕ) : ℚ) *
              (actualLeadingDifference r
                (selectedDirection (A := A) r direction)).coeff
                  (FreeMonoid.ofList pattern) := by
            rw [show words.map (degreeDifference pattern) =
                List.ofFn (fun scale : Fin t ↦
                  degreeDifference pattern
                    (digitBlock (A := A) r direction scale
                        (digits direction scale),
                      digitBlock (A := A) r direction scale 0)) by
              simp [words, Function.comp_def], List.sum_ofFn]
            apply Finset.sum_congr rfl
            intro scale _
            exact digitBlock_central_data (A := A) r t direction scale
              (digits direction scale) |>.2 pattern hpattern
      _ = (digitValue (A := A) r t digits direction : ℚ) *
            (actualLeadingDifference r
              (selectedDirection (A := A) r direction)).coeff
                (FreeMonoid.ofList pattern) := by
            rw [hvalueSum]
            rw [Finset.sum_mul]

private theorem multiScaleWord_central_data
    [Fintype A] [LinearOrder A] (r t : ℕ)
    (digits : DigitArray (A := A) r t) :
    AgreesBelow r (multiScaleWord (A := A) r t digits)
        (referenceWord (A := A) r t) ∧
      ∀ pattern : List A, pattern.length = r →
        degreeDifference pattern
            (multiScaleWord (A := A) r t digits,
              referenceWord (A := A) r t) =
          ∑ direction : Fin (actualLyndonCount (A := A) r),
            (digitValue (A := A) r t digits direction : ℚ) *
              (actualLeadingDifference r
                (selectedDirection (A := A) r direction)).coeff
                  (FreeMonoid.ofList pattern) := by
  classical
  let words : List (List A × List A) :=
    List.ofFn fun direction : Fin (actualLyndonCount (A := A) r) ↦
      (directionWord (A := A) r t digits direction,
        directionWord (A := A) r t (fun _ _ ↦ zeroDigit r) direction)
  have hbelow : ∀ words' ∈ words,
      AgreesBelow r words'.1 words'.2 := by
    intro words' hwords'
    rcases List.mem_ofFn.mp hwords' with ⟨direction, rfl⟩
    exact (directionWord_central_data (A := A) r t digits direction).1
  have hdata := flatten_central_data (A := A) r words hbelow
  constructor
  · simpa [words, multiScaleWord, referenceWord, directionWord,
      Function.comp_def] using hdata.1
  · intro pattern hpattern
    calc
      degreeDifference pattern
          (multiScaleWord (A := A) r t digits,
            referenceWord (A := A) r t) =
          (words.map (degreeDifference pattern)).sum := by
            simpa [words, multiScaleWord, referenceWord, directionWord,
              Function.comp_def] using hdata.2 pattern hpattern
      _ = ∑ direction : Fin (actualLyndonCount (A := A) r),
            (digitValue (A := A) r t digits direction : ℚ) *
              (actualLeadingDifference r
                (selectedDirection (A := A) r direction)).coeff
                  (FreeMonoid.ofList pattern) := by
            rw [show words.map (degreeDifference pattern) =
                List.ofFn (fun direction :
                    Fin (actualLyndonCount (A := A) r) ↦
                  degreeDifference pattern
                    (directionWord (A := A) r t digits direction,
                      directionWord (A := A) r t
                        (fun _ _ ↦ zeroDigit r) direction)) by
              simp [words, Function.comp_def], List.sum_ofFn]
            apply Finset.sum_congr rfl
            intro direction _
            exact directionWord_central_data (A := A) r t digits direction
              |>.2 pattern hpattern


end D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitData
