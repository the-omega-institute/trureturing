/- GID: D5/S1/Depth/TwelveScaleReduction
   generality: I
   mirror-B: D5/B/S1/Depth/TwelveScaleReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact finite-sample reduction from nonzero multiples of twelve to the twelve scale. -/

import D5.S1.Phase.SeatTowerArithmetic
import D5.S1.Phase.ZeroOrbitCongruence
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

namespace D5.S1.Depth.TwelveScaleReduction

open D5.S1.Phase.SeatTowerArithmetic
open D5.S1.Phase.ZeroOrbitCongruence

/-- A finite simple continued fraction with integer partial quotients. -/
structure FiniteContinuedFraction where
  head : Int
  partialQuotients : List Int
  deriving DecidableEq, Repr

private def evaluatePartialQuotients : List Int → Rat
  | [] => 0
  | quotient :: rest => 1 / (quotient + evaluatePartialQuotients rest)

private def partialQuotientPair (quotient : Int) : GenContFract.Pair Rat :=
  ⟨1, (quotient : Rat)⟩

/-- The rational value represented by a finite simple continued fraction. -/
def FiniteContinuedFraction.value (fraction : FiniteContinuedFraction) : Rat :=
  fraction.head + evaluatePartialQuotients fraction.partialQuotients

private def FiniteContinuedFraction.toGenContFract
    (fraction : FiniteContinuedFraction) : GenContFract Rat :=
  ⟨fraction.head,
    Stream'.Seq.ofList (fraction.partialQuotients.map partialQuotientPair)⟩

private theorem evaluate_partial_quotients_eq_convs_aux (quotients : List Int) :
    GenContFract.convs'Aux
        (Stream'.Seq.ofList (quotients.map partialQuotientPair))
        quotients.length =
      evaluatePartialQuotients quotients := by
  induction quotients with
  | nil => rfl
  | cons quotient rest ih =>
      simp [GenContFract.convs'Aux, evaluatePartialQuotients, partialQuotientPair, ih]

private theorem finite_continued_fraction_value_eq_convs
    (fraction : FiniteContinuedFraction) :
    fraction.value = fraction.toGenContFract.convs' fraction.partialQuotients.length := by
  simp [FiniteContinuedFraction.value, FiniteContinuedFraction.toGenContFract,
    GenContFract.convs', evaluate_partial_quotients_eq_convs_aux]

private theorem continued_fraction_sequence_terminates (q : Rat) :
    (GenContFract.IntFractPair.seq1 q).snd.Terminates := by
  rcases GenContFract.terminates_of_rat q with ⟨n, hn⟩
  exact ⟨n, GenContFract.of_terminatedAt_iff_intFractPair_seq1_terminatedAt.mp hn⟩

/-- The partial quotients produced directly by Mathlib's Euclidean continued-fraction algorithm. -/
def euclideanPartialQuotients (q : Rat) : List Int :=
  ((GenContFract.IntFractPair.seq1 q).snd.toList
      (continued_fraction_sequence_terminates q)).map (·.b)

private def euclideanContinuedFraction (q : Rat) : FiniteContinuedFraction :=
  ⟨⌊q⌋, euclideanPartialQuotients q⟩

private theorem euclidean_continued_fraction_to_gen_cont_fract (q : Rat) :
    (euclideanContinuedFraction q).toGenContFract = GenContFract.of q := by
  apply GenContFract.ext
  · rfl
  · ext n
    simp [euclideanContinuedFraction, FiniteContinuedFraction.toGenContFract,
      euclideanPartialQuotients, partialQuotientPair, GenContFract.of,
      GenContFract.IntFractPair.seq1, Stream'.Seq.map_get?]

private theorem euclidean_continued_fraction_value (q : Rat) :
    (euclideanContinuedFraction q).value = q := by
  rw [finite_continued_fraction_value_eq_convs,
    euclidean_continued_fraction_to_gen_cont_fract]
  rw [← GenContFract.of_convs_eq_convs']
  exact (GenContFract.of_correctness_of_terminatedAt
    (by
      rw [← euclidean_continued_fraction_to_gen_cont_fract q]
      simpa [FiniteContinuedFraction.toGenContFract, GenContFract.TerminatedAt] using
        Stream'.Seq.terminatedAt_ofList
          ((euclideanContinuedFraction q).partialQuotients.map partialQuotientPair))).symm

private def oddLengthNormalization (quotients : List Int) : List Int :=
  if Odd quotients.length then
    quotients
  else
    match quotients.reverse with
    | [] => []
    | last :: initial => (1 :: (last - 1) :: initial).reverse

private theorem evaluate_partial_quotients_terminal_split
    (initial : List Int) (last : Int) :
    evaluatePartialQuotients (initial ++ [last - 1, 1]) =
      evaluatePartialQuotients (initial ++ [last]) := by
  induction initial with
  | nil => simp [evaluatePartialQuotients]
  | cons quotient rest ih => simp [evaluatePartialQuotients, ih]

private theorem evaluate_odd_length_normalization (quotients : List Int) :
    evaluatePartialQuotients (oddLengthNormalization quotients) =
      evaluatePartialQuotients quotients := by
  by_cases hOdd : Odd quotients.length
  · simp [oddLengthNormalization, hOdd]
  · simp only [oddLengthNormalization, hOdd, ↓reduceIte]
    cases hReverse : quotients.reverse with
    | nil =>
        have hQuotients : quotients = [] := by
          simpa using congrArg List.reverse hReverse
        simp [hQuotients, evaluatePartialQuotients]
    | cons last initial =>
        have hQuotients : quotients = initial.reverse ++ [last] := by
          simpa using congrArg List.reverse hReverse
        rw [hQuotients]
        simpa using evaluate_partial_quotients_terminal_split initial.reverse last

/-- The Euclidean partial quotients under the odd-length terminal convention. -/
def canonicalPartialQuotients (q : Rat) : List Int :=
  oddLengthNormalization (euclideanPartialQuotients q)

private theorem odd_length_normalization_empty_or_odd (quotients : List Int) :
    oddLengthNormalization quotients = [] ∨
      Odd (oddLengthNormalization quotients).length := by
  by_cases hOdd : Odd quotients.length
  · exact Or.inr (by simp [oddLengthNormalization, hOdd])
  · cases hReverse : quotients.reverse with
    | nil => exact Or.inl (by simp [oddLengthNormalization, hOdd, hReverse])
    | cons last initial =>
        right
        have hLength : quotients.length = initial.length + 1 := by
          simpa using congrArg List.length hReverse
        have hEven : Even (initial.length + 1) := by
          rw [← hLength]
          exact Nat.not_odd_iff_even.mp hOdd
        simp only [oddLengthNormalization, hOdd, ↓reduceIte, hReverse, List.length_reverse,
          List.length_cons]
        simpa [Nat.add_assoc] using hEven.add_one

/-- The extracted sequence is empty for an integral sample or has the required odd length. -/
theorem canonical_partial_quotients_empty_or_odd (q : Rat) :
    canonicalPartialQuotients q = [] ∨ Odd (canonicalPartialQuotients q).length := by
  exact odd_length_normalization_empty_or_odd (euclideanPartialQuotients q)

/-- The canonical odd-length finite continued fraction extracted from a rational sample. -/
def canonicalContinuedFraction (q : Rat) : FiniteContinuedFraction :=
  ⟨⌊q⌋, canonicalPartialQuotients q⟩

/-- The canonical extracted continued fraction reconstructs its rational sample exactly. -/
theorem canonical_continued_fraction_value (q : Rat) :
    (canonicalContinuedFraction q).value = q := by
  simpa [canonicalContinuedFraction, FiniteContinuedFraction.value,
    canonicalPartialQuotients, euclideanContinuedFraction] using
    (congrArg (fun tail => (⌊q⌋ : Rat) + tail)
      (evaluate_odd_length_normalization (euclideanPartialQuotients q))).trans
      (euclidean_continued_fraction_value q)

/-- The largest partial quotient of the canonical continued fraction of a rational sample. -/
def maximumPartialQuotient (q : Rat) : Int :=
  (canonicalPartialQuotients q).foldr max 0

/-- The absolute integer reading normalized by the sample's largest partial quotient. -/
def normalizedMagnitude (psi : Int) (q : Rat) : Rat :=
  ((|psi| : Int) : Rat) / (maximumPartialQuotient q : Rat)

/-- The finite set of normalized magnitudes generated by an integer sample. -/
def normalizedSample (sample : Finset Int) (q : Rat) : Finset Rat :=
  sample.image fun psi => normalizedMagnitude psi q

/-- A member of the normalized sample that is no greater than any other member. -/
def IsNormalizedMinimum (sample : Finset Int) (q value : Rat) : Prop :=
  value ∈ normalizedSample sample q ∧
    ∀ other ∈ normalizedSample sample q, value ≤ other

/-- The least normalized magnitude of a nonempty integer sample. -/
def normalizedSampleFloor (sample : Finset Int) (q : Rat) (hSample : sample.Nonempty) : Rat :=
  (normalizedSample sample q).min' (hSample.image fun psi => normalizedMagnitude psi q)

/-- Every nonzero multiple of twelve lies above the normalized twelve scale. -/
theorem twelve_scale_le_normalized_magnitude
    (psi : Int) (q : Rat) (haMax : 0 < maximumPartialQuotient q)
    (hDiv : (12 : Int) ∣ psi) (hNe : psi ≠ 0) :
    12 / (maximumPartialQuotient q : Rat) ≤ normalizedMagnitude psi q := by
  have haMaxRat : (0 : Rat) < (maximumPartialQuotient q : Rat) := by
    exact_mod_cast haMax
  have hAbs : (12 : Int) ≤ |psi| :=
    twelve_le_abs_of_dvd_of_ne_zero psi hDiv hNe
  apply (div_le_div_iff_of_pos_right haMaxRat).2
  exact_mod_cast hAbs

/-- Equality with the normalized twelve scale is exactly the absolute-value-twelve case. -/
theorem normalized_magnitude_eq_twelve_scale_iff
    (psi : Int) (q : Rat) (haMax : 0 < maximumPartialQuotient q) :
    normalizedMagnitude psi q = 12 / (maximumPartialQuotient q : Rat) ↔ |psi| = 12 := by
  have haMaxRat : (0 : Rat) < (maximumPartialQuotient q : Rat) := by
    exact_mod_cast haMax
  constructor
  · intro h
    have hCast : (((|psi| : Int) : Rat)) = 12 := by
      simp only [normalizedMagnitude] at h
      field_simp [ne_of_gt haMaxRat] at h
      exact h
    exact_mod_cast hCast
  · intro h
    simp [normalizedMagnitude, h]

/-- A finite sample of nonzero multiples of twelve has exact normalized minimum
once a member of absolute value twelve is supplied. -/
theorem twelve_scale_is_normalized_sample_minimum
    (sample : Finset Int) (witness : Int) (q : Rat)
    (haMax : 0 < maximumPartialQuotient q)
    (hWitness : witness ∈ sample) (hWitnessAbs : |witness| = 12)
    (hSample : ∀ psi ∈ sample, (12 : Int) ∣ psi ∧ psi ≠ 0) :
    IsNormalizedMinimum sample q (12 / (maximumPartialQuotient q : Rat)) := by
  refine ⟨?_, ?_⟩
  · simp only [normalizedSample, Finset.mem_image]
    exact ⟨witness, hWitness,
      (normalized_magnitude_eq_twelve_scale_iff witness q haMax).2 hWitnessAbs⟩
  · intro other hOther
    simp only [normalizedSample, Finset.mem_image] at hOther
    rcases hOther with ⟨psi, hPsi, rfl⟩
    exact twelve_scale_le_normalized_magnitude psi q haMax
      (hSample psi hPsi).1 (hSample psi hPsi).2

/-- Membership plus the lower-bound property determines a finite-sample minimum uniquely. -/
theorem normalized_sample_minimum_unique
    (sample : Finset Int) (q first second : Rat)
    (hFirst : IsNormalizedMinimum sample q first)
    (hSecond : IsNormalizedMinimum sample q second) :
    first = second := by
  exact le_antisymm (hFirst.2 second hSecond.1) (hSecond.2 first hFirst.1)

/-- The actual finite-sample floor is twelve divided by the extracted maximum partial quotient. -/
theorem normalized_sample_floor_eq_twelve_over_maximum_partial_quotient
    (sample : Finset Int) (witness : Int) (q : Rat)
    (haMax : 0 < maximumPartialQuotient q)
    (hWitness : witness ∈ sample) (hWitnessAbs : |witness| = 12)
    (hSample : ∀ psi ∈ sample, (12 : Int) ∣ psi ∧ psi ≠ 0) :
    normalizedSampleFloor sample q ⟨witness, hWitness⟩ =
      12 / (maximumPartialQuotient q : Rat) := by
  unfold normalizedSampleFloor
  rw [Finset.min'_eq_iff]
  exact twelve_scale_is_normalized_sample_minimum sample witness q haMax
    hWitness hWitnessAbs hSample

/-- Membership in the explicit thirty-six sampling grid. -/
def OnThirtySixGrid (m : Nat) : Prop :=
  ∃ index, m = 36 * index

/-- The local zero-family candidates that survive the Eisenstein-norm condition
lie on the explicit thirty-six grid. -/
theorem zero_family_lies_on_thirty_six_grid
    (m : Nat) (x y : ZMod 3)
    (hLocal : m % 36 = 0 ∨ m % 36 = 8)
    (hNorm : (m : ZMod 3) = x ^ 2 - x * y + y ^ 2) :
    OnThirtySixGrid m := by
  exact thirty_six_dvd_of_local_candidates_and_eisenstein_norm m x y hLocal hNorm

end D5.S1.Depth.TwelveScaleReduction
