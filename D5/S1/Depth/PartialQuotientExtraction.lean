/- GID: D5/S1/Depth/PartialQuotientExtraction
   generality: I
   mirror-B: D5/B/S1/Depth/PartialQuotientExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Endogenous continued-fraction maximum and exact finite-sample twelve-scale floor. -/

import D5.S1.Depth.TwelveScaleReduction
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Data.List.MinMax

namespace D5.S1.Depth.PartialQuotientExtraction

open D5.S1.Depth.TwelveScaleReduction

private theorem partial_denominators_terminate (q : Rat) :
    (GenContFract.of q).partDens.Terminates := by
  unfold GenContFract.partDens
  exact Stream'.Seq.terminates_map_iff.mpr (GenContFract.terminates_of_rat q)

private def euclideanPartialQuotients (q : Rat) : List Nat :=
  ((GenContFract.of q).partDens.toList (partial_denominators_terminate q)).map
    fun quotient => (⌊quotient⌋ : Int).toNat

private def oddLengthNormalization (quotients : List Nat) : List Nat :=
  if Odd quotients.length then
    quotients
  else
    match quotients.reverse with
    | [] => []
    | last :: initial => (1 :: (last - 1) :: initial).reverse

/-- The finite regular continued-fraction tail computed from `q` itself.

`GenContFract.of` keeps the integer head `⌊q⌋` separately, so this list contains only the positive
tail denominators. Mathlib's rational termination theorem makes that stream finite. Following the
odd-tail convention, an even nonempty tail ending in `n` is represented instead by the equivalent
terminal pair `n - 1, 1`; an integral rational has an empty tail. -/
def partialQuotients (q : Rat) : List Nat :=
  oddLengthNormalization (euclideanPartialQuotients q)

/-- The largest mechanically extracted partial quotient, with zero only for an empty tail. -/
def aMax (q : Rat) : Nat :=
  (partialQuotients q).foldr max 0

private theorem partial_denominators_head
    (q : Rat) (hq : q ∉ Set.range fun z : Int => (z : Rat)) :
    (GenContFract.of q).partDens.head =
      some ((⌊(Int.fract q)⁻¹⌋ : Int) : Rat) := by
  have hFract : Int.fract q ≠ 0 := Int.fract_ne_zero_iff.mpr hq
  simpa [GenContFract.partDens, Stream'.Seq.head, Stream'.Seq.map_get?] using
    congrArg (Option.map GenContFract.Pair.b) (GenContFract.of_s_head hFract)

private theorem euclidean_partial_quotients_head
    (q : Rat) (hq : q ∉ Set.range fun z : Int => (z : Rat)) :
    (euclideanPartialQuotients q)[0]? =
      some (⌊(Int.fract q)⁻¹⌋ : Int).toNat := by
  simp only [euclideanPartialQuotients, List.getElem?_map,
    Stream'.Seq.getElem?_toList]
  rw [show (GenContFract.of q).partDens.get? 0 =
      some ((⌊(Int.fract q)⁻¹⌋ : Int) : Rat) by
    simpa [Stream'.Seq.head] using partial_denominators_head q hq]
  rfl

private theorem euclidean_partial_quotients_nonempty
    (q : Rat) (hq : q ∉ Set.range fun z : Int => (z : Rat)) :
    euclideanPartialQuotients q ≠ [] := by
  intro hEmpty
  have hHead := euclidean_partial_quotients_head q hq
  rw [hEmpty] at hHead
  simp at hHead

private theorem odd_length_normalization_nonempty
    (quotients : List Nat) (hQuotients : quotients ≠ []) :
    oddLengthNormalization quotients ≠ [] := by
  by_cases hOdd : Odd quotients.length
  · simpa [oddLengthNormalization, hOdd] using hQuotients
  · cases hReverse : quotients.reverse with
    | nil =>
        exfalso
        apply hQuotients
        simpa using congrArg List.reverse hReverse
    | cons last initial =>
        simp [oddLengthNormalization, hOdd, hReverse]

/-- A nonintegral rational has at least one mechanically extracted tail partial quotient. -/
theorem partialQuotients_nonempty
    (q : Rat) (hq : q ∉ Set.range fun z : Int => (z : Rat)) :
    partialQuotients q ≠ [] := by
  exact odd_length_normalization_nonempty _ (euclidean_partial_quotients_nonempty q hq)

private theorem euclidean_partial_quotient_head_pos
    (q : Rat) (hq : q ∉ Set.range fun z : Int => (z : Rat)) :
    0 < (⌊(Int.fract q)⁻¹⌋ : Int).toNat := by
  have hDenominator : (GenContFract.of q).partDens.get? 0 =
      some ((⌊(Int.fract q)⁻¹⌋ : Int) : Rat) := by
    simpa [Stream'.Seq.head] using partial_denominators_head q hq
  have hRat : (1 : Rat) ≤ ((⌊(Int.fract q)⁻¹⌋ : Int) : Rat) :=
    GenContFract.of_one_le_get?_partDen hDenominator
  have hInt : (1 : Int) ≤ ⌊(Int.fract q)⁻¹⌋ := by
    exact_mod_cast hRat
  omega

/-- The maximum extracted partial quotient is positive for every nonintegral rational. -/
theorem aMax_pos
    (q : Rat) (hq : q ∉ Set.range fun z : Int => (z : Rat)) :
    0 < aMax q := by
  let first := (⌊(Int.fract q)⁻¹⌋ : Int).toNat
  have hFirstPos : 0 < first := euclidean_partial_quotient_head_pos q hq
  have hFirstGet : (euclideanPartialQuotients q)[0]? = some first :=
    euclidean_partial_quotients_head q hq
  have hFirstMem : first ∈ euclideanPartialQuotients q := List.mem_of_getElem? hFirstGet
  have hPositiveMember : ∃ quotient ∈ partialQuotients q, 0 < quotient := by
    by_cases hOdd : Odd (euclideanPartialQuotients q).length
    · exact ⟨first, by simpa [partialQuotients, oddLengthNormalization, hOdd] using hFirstMem,
        hFirstPos⟩
    · cases hReverse : (euclideanPartialQuotients q).reverse with
      | nil =>
          exfalso
          exact (euclidean_partial_quotients_nonempty q hq) <| by
            simpa using congrArg List.reverse hReverse
      | cons last initial =>
          refine ⟨1, ?_, Nat.zero_lt_one⟩
          simp [partialQuotients, oddLengthNormalization, hOdd, hReverse]
  rcases hPositiveMember with ⟨quotient, hMem, hPos⟩
  have hBound : 1 ≤ (partialQuotients q).foldr max 0 :=
    List.le_max_of_le' 0 hMem hPos
  simpa [aMax] using lt_of_lt_of_le Nat.zero_lt_one hBound

/-- The exact twelve-scale floor after substituting the maximum extracted from `q`.

The public signature exposes no scale parameter and accepts no external collection of partial
quotients: the denominator is definitionally `aMax q`. -/
theorem twelve_scale_is_extracted_normalized_sample_minimum
    (q : Rat) (hq : q ∉ Set.range fun z : Int => (z : Rat))
    (sample : Finset Int)
    (hSample : ∀ psi ∈ sample, (12 : Int) ∣ psi ∧ psi ≠ 0)
    (hWitness : ∃ witness ∈ sample, |witness| = 12) :
    IsNormalizedMinimum sample ((aMax q : Nat) : Rat)
      (12 / ((aMax q : Nat) : Rat)) := by
  rcases hWitness with ⟨witness, hWitnessMem, hWitnessAbs⟩
  apply twelve_scale_is_normalized_sample_minimum sample witness
    ((aMax q : Nat) : Rat)
  · exact_mod_cast aMax_pos q hq
  · exact hWitnessMem
  · exact hWitnessAbs
  · exact hSample

-- These #guard checks are build-time executable contracts and do not enter the axiom closure.
-- In-domain: the one-term odd tail for 1/2 is preserved.
#guard partialQuotients (1 / 2 : Rat) == [2]

-- In-domain: the even Euclidean tail for 2/3 is normalized to odd length.
#guard partialQuotients (2 / 3 : Rat) == [1, 1, 1]

-- Tail-only: the integer head of 34/10 is excluded before odd-tail normalization.
#guard partialQuotients (34 / 10 : Rat) == [2, 1, 1]

-- Integer boundary: an integral rational has no tail partial quotients.
#guard partialQuotients (3 : Rat) == []

-- Negative nonintegral: floor-based extraction still records only the positive tail.
#guard partialQuotients (-3 / 2 : Rat) == [2]

-- In-domain maximum: the sole tail quotient of 1/2 fixes aMax at 2.
#guard aMax (1 / 2 : Rat) == 2

-- Odd-tail maximum: normalization of 2/3 fixes aMax at 1.
#guard aMax (2 / 3 : Rat) == 1

-- Tail-only maximum: the excluded integer head of 34/10 does not affect aMax.
#guard aMax (34 / 10 : Rat) == 2

end D5.S1.Depth.PartialQuotientExtraction
