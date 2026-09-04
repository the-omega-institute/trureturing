/- GID: D5/S3/Observer/Chronology/PrimeGoldenBidegreePhaseSeparation
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One scalar phase sample may alias prime-golden bidegrees, while the complete time trajectory faithfully recovers the bidegree. -/

import D5.S3.Observer.Chronology.PrimeGoldenBidegreeFrequencyRigidity
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Prime-golden bidegree phase separation

A single terminal unit-circle sample can alias distinct bidegrees. At time zero
all bidegrees have phase one. The complete real-time phase trajectory is
faithful: the frequency-rigidity theorem supplies a nonzero frequency gap, and
the pair-specific half-beat time sends that gap to `exp (pi i) = -1`.

This separates three levels of information. One sample can alias. The full
scalar trajectory recovers the two counting coordinates. Neither scalar
object recovers the chronological order retained by Magnus or Hopf data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeGoldenBidegreePhaseSeparation

open D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
open D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature
open D5.S3.Observer.Chronology.PrimeGoldenBidegreeFrequencyRigidity

noncomputable section

/-- Pair-dependent half-beat time for two bidegree frequencies. -/
def bidegreeSeparatingTime
    (prime : Nat.Primes)
    (left right : PrimeGoldenBidegree) : Real :=
  Real.pi /
    (bidegreeFrequency prime left - bidegreeFrequency prime right)

@[simp]
theorem bidegree_phase_zero_time
    (prime : Nat.Primes) (degree : PrimeGoldenBidegree) :
    bidegreePhase 0 prime degree = 1 := by
  simp [bidegreePhase]

/-- Time zero is an explicit scalar aliasing sample for distinct bidegrees. -/
theorem zero_time_bidegree_phase_not_injective (prime : Nat.Primes) :
    ¬Function.Injective (fun degree : PrimeGoldenBidegree =>
      bidegreePhase 0 prime degree) := by
  intro hinjective
  let zeroDegree : PrimeGoldenBidegree := ⟨0, 0⟩
  let oneDegree : PrimeGoldenBidegree := ⟨1, 0⟩
  have hphase :
      bidegreePhase 0 prime zeroDegree =
        bidegreePhase 0 prime oneDegree := by
    simp
  have hequal := hinjective hphase
  have hfactor := congrArg PrimeGoldenBidegree.factorDegree hequal
  change 0 = 1 at hfactor
  omega

/-- Distinct bidegrees are separated by the half-beat time of their nonzero
frequency difference. -/
theorem bidegree_phase_separated_at_half_beat
    (prime : Nat.Primes)
    {left right : PrimeGoldenBidegree}
    (hne : left ≠ right) :
    bidegreePhase (bidegreeSeparatingTime prime left right) prime left ≠
      bidegreePhase (bidegreeSeparatingTime prime left right) prime right := by
  have hfrequency :
      bidegreeFrequency prime left ≠ bidegreeFrequency prime right := by
    intro hequal
    exact hne (bidegree_frequency_injective prime hequal)
  have hgap :
      bidegreeFrequency prime left - bidegreeFrequency prime right ≠ 0 :=
    sub_ne_zero.mpr hfrequency
  intro hphase
  let time := bidegreeSeparatingTime prime left right
  change bidegreePhase time prime left =
    bidegreePhase time prime right at hphase
  have hunit :
      Complex.exp
          ((((time *
            (bidegreeFrequency prime left -
              bidegreeFrequency prime right) : Real) : Complex) * Complex.I)) =
        1 := by
    calc
      Complex.exp
          ((((time *
            (bidegreeFrequency prime left -
              bidegreeFrequency prime right) : Real) : Complex) * Complex.I)) =
        bidegreePhase time prime left *
          Complex.exp
            (-(((time * bidegreeFrequency prime right : Real) : Complex) *
              Complex.I)) := by
          unfold bidegreePhase
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
      _ = bidegreePhase time prime right *
          Complex.exp
            (-(((time * bidegreeFrequency prime right : Real) : Complex) *
              Complex.I)) := by rw [hphase]
      _ = 1 := by
          unfold bidegreePhase
          rw [← Complex.exp_add]
          have hcancel :
              (((time * bidegreeFrequency prime right : Real) : Complex) *
                  Complex.I) +
                -(((time * bidegreeFrequency prime right : Real) : Complex) *
                  Complex.I) = 0 := by ring
          rw [hcancel, Complex.exp_zero]
  have hhalfBeat :
      time *
          (bidegreeFrequency prime left -
            bidegreeFrequency prime right) = Real.pi := by
    dsimp [time, bidegreeSeparatingTime]
    exact div_mul_cancel₀ Real.pi hgap
  have hminus :
      Complex.exp
          ((((time *
            (bidegreeFrequency prime left -
              bidegreeFrequency prime right) : Real) : Complex) * Complex.I)) =
        -1 := by
    rw [hhalfBeat]
    simpa using Complex.exp_pi_mul_I
  rw [hminus] at hunit
  norm_num at hunit

/-- The complete time-indexed phase trajectory is faithful on bidegrees. -/
theorem bidegree_phase_trajectory_injective (prime : Nat.Primes) :
    Function.Injective
      (fun degree : PrimeGoldenBidegree =>
        fun time : Real => bidegreePhase time prime degree) := by
  intro left right htrajectory
  by_contra hne
  exact bidegree_phase_separated_at_half_beat prime hne
    (congrFun htrajectory (bidegreeSeparatingTime prime left right))

/-- Complete scalar trajectories of two fixed-prime words recover their count
ledgers, even though chronology inside the common bidegree remains outside the
scalar readout. -/
theorem single_prime_phase_trajectory_recovers_bidegree
    (prime : Nat.Primes)
    (left right : List PrimeGoldenStepEvent)
    (hLeft : IsSinglePrimeWord prime left)
    (hRight : IsSinglePrimeWord prime right)
    (htrajectory : ∀ time : Real,
      scalarStepEndpoint time left = scalarStepEndpoint time right) :
    primeGoldenBidegree left = primeGoldenBidegree right := by
  apply bidegree_phase_trajectory_injective prime
  funext time
  change
    bidegreePhase time prime (primeGoldenBidegree left) =
      bidegreePhase time prime (primeGoldenBidegree right)
  rw [← scalar_step_endpoint_eq_bidegree_phase_of_single_prime
      time prime left hLeft,
    ← scalar_step_endpoint_eq_bidegree_phase_of_single_prime
      time prime right hRight]
  exact htrajectory time

/-- Headline boundary between single-sample aliasing and trajectory recovery. -/
theorem prime_golden_phase_observation_boundary (prime : Nat.Primes) :
    ¬Function.Injective (fun degree : PrimeGoldenBidegree =>
        bidegreePhase 0 prime degree) ∧
      Function.Injective
        (fun degree : PrimeGoldenBidegree =>
          fun time : Real => bidegreePhase time prime degree) :=
  ⟨zero_time_bidegree_phase_not_injective prime,
    bidegree_phase_trajectory_injective prime⟩

#print axioms zero_time_bidegree_phase_not_injective
#print axioms bidegree_phase_separated_at_half_beat
#print axioms bidegree_phase_trajectory_injective
#print axioms single_prime_phase_trajectory_recovers_bidegree
#print axioms prime_golden_phase_observation_boundary

end

end D5.S3.Observer.Chronology.PrimeGoldenBidegreePhaseSeparation
