/- GID: D5/S3/AnalyticClosure/PrimeReciprocalLogApproximation
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/PrimeReciprocalLogApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bertrand primes give reciprocal-log approximations with quadratic error. -/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.Bertrand
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace D5.S3.AnalyticClosure.PrimeReciprocalLogApproximation

open Filter Set
open scoped Topology

/-- The real spectrum obtained by reading a prime through reciprocal logarithmic precision. -/
def primeReciprocalLogSpectrum : Set Real :=
  {x | exists q : Nat, q.Prime ∧ x = 1 / Real.log (q : Real)}

/-- Every positive offset has a prime reciprocal-logarithm witness with the explicit
Bertrand interval, logarithmic window, and quadratic error bound. Consequently the
distance to the prime reciprocal-logarithm spectrum is `O(delta^2)` from the right at zero. -/
theorem prime_reciprocal_log_quadratic_approximation :
    (forall delta : Real, 0 < delta ->
      exists (Y : Real) (N q : Nat),
        Y = Real.exp (1 / delta) ∧
        N = Nat.ceil Y ∧
        q.Prime ∧
        N < q ∧
        q <= 2 * N ∧
        (((2 * N : Nat) : Real) <= 4 * Y) ∧
        1 / delta < Real.log (q : Real) ∧
        Real.log (q : Real) <= 1 / delta + Real.log 4 ∧
        0 <= delta - 1 / Real.log (q : Real) ∧
        delta - 1 / Real.log (q : Real) < Real.log 4 * delta ^ 2) ∧
      (fun delta : Real => Metric.infDist delta primeReciprocalLogSpectrum)
        =O[nhdsWithin 0 (Ioi 0)] (fun delta : Real => delta ^ 2) := by
  have hpoint : forall delta : Real, 0 < delta ->
      exists (Y : Real) (N q : Nat),
        Y = Real.exp (1 / delta) ∧
        N = Nat.ceil Y ∧
        q.Prime ∧
        N < q ∧
        q <= 2 * N ∧
        (((2 * N : Nat) : Real) <= 4 * Y) ∧
        1 / delta < Real.log (q : Real) ∧
        Real.log (q : Real) <= 1 / delta + Real.log 4 ∧
        0 <= delta - 1 / Real.log (q : Real) ∧
        delta - 1 / Real.log (q : Real) < Real.log 4 * delta ^ 2 := by
    intro delta hdelta
    let Y : Real := Real.exp (1 / delta)
    let N : Nat := Nat.ceil Y
    have hYpos : 0 < Y := by
      change 0 < Real.exp (1 / delta)
      exact Real.exp_pos _
    have hYone : 1 < Y := by
      change 1 < Real.exp (1 / delta)
      rw [Real.one_lt_exp_iff]
      exact one_div_pos.mpr hdelta
    have hNne : N ≠ 0 := by
      have hNpos : 1 <= N := by
        change 1 <= Nat.ceil Y
        exact Nat.one_le_ceil_iff.mpr hYpos
      omega
    obtain ⟨q, hqprime, hNq, hqN⟩ := Nat.exists_prime_lt_and_le_two_mul N hNne
    have hYleN : Y <= (N : Real) := by
      change Y <= (Nat.ceil Y : Real)
      exact Nat.le_ceil Y
    have hNcastLt : (N : Real) < Y + 1 := by
      change (Nat.ceil Y : Real) < Y + 1
      exact Nat.ceil_lt_add_one hYpos.le
    have htwoN : (((2 * N : Nat) : Real) <= 4 * Y) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
    have hNqReal : (N : Real) < (q : Real) := by exact_mod_cast hNq
    have hqTwoNReal : (q : Real) <= ((2 * N : Nat) : Real) := by exact_mod_cast hqN
    have hYq : Y < (q : Real) := hYleN.trans_lt hNqReal
    have hqFourY : (q : Real) <= 4 * Y := hqTwoNReal.trans htwoN
    have hqpos : 0 < (q : Real) := by exact_mod_cast hqprime.pos
    have hlogLower : 1 / delta < Real.log (q : Real) := by
      calc
        1 / delta = Real.log Y := by
          change 1 / delta = Real.log (Real.exp (1 / delta))
          rw [Real.log_exp]
        _ < Real.log (q : Real) := Real.log_lt_log hYpos hYq
    have hlogUpper : Real.log (q : Real) <= 1 / delta + Real.log 4 := by
      calc
        Real.log (q : Real) <= Real.log (4 * Y) :=
          Real.log_le_log hqpos hqFourY
        _ = Real.log 4 + Real.log Y := by
          rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0) hYpos.ne']
        _ = 1 / delta + Real.log 4 := by
          change Real.log 4 + Real.log (Real.exp (1 / delta)) = _
          rw [Real.log_exp]
          ring
    have hdeltaInv : 0 < 1 / delta := one_div_pos.mpr hdelta
    have hlogPos : 0 < Real.log (q : Real) := hdeltaInv.trans hlogLower
    have hreciprocalLe : 1 / Real.log (q : Real) <= delta := by
      have h := one_div_le_one_div_of_le hdeltaInv hlogLower.le
      simpa [one_div] using h
    have herrorNonneg : 0 <= delta - 1 / Real.log (q : Real) := sub_nonneg.mpr hreciprocalLe
    have hdeltaLog : 1 < delta * Real.log (q : Real) := by
      have h := (div_lt_iff₀ hdelta).mp hlogLower
      nlinarith
    have hdeltaCancel : delta * (1 / delta) = 1 := by
      field_simp
    have hleftBound : delta * Real.log (q : Real) - 1 <= Real.log 4 * delta := by
      have h := mul_le_mul_of_nonneg_left hlogUpper hdelta.le
      nlinarith
    have hlogFourPos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hrightStrict : Real.log 4 * delta <
        Real.log 4 * delta ^ 2 * Real.log (q : Real) := by
      calc
        Real.log 4 * delta = (Real.log 4 * delta) * 1 := by ring
        _ < (Real.log 4 * delta) * (delta * Real.log (q : Real)) :=
          mul_lt_mul_of_pos_left hdeltaLog (mul_pos hlogFourPos hdelta)
        _ = Real.log 4 * delta ^ 2 * Real.log (q : Real) := by ring
    have herrorLt : delta - 1 / Real.log (q : Real) < Real.log 4 * delta ^ 2 := by
      rw [show delta - 1 / Real.log (q : Real) =
          (delta * Real.log (q : Real) - 1) / Real.log (q : Real) by
        field_simp [hlogPos.ne']]
      exact (div_lt_iff₀ hlogPos).mpr (hleftBound.trans_lt hrightStrict)
    exact ⟨Y, N, q, rfl, rfl, hqprime, hNq, hqN, htwoN,
      hlogLower, hlogUpper, herrorNonneg, herrorLt⟩
  refine ⟨hpoint, ?_⟩
  apply Asymptotics.IsBigO.of_bound (Real.log 4)
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  obtain ⟨Y, N, q, hY, hN, hqprime, hNq, hqN, htwoN,
      hlogLower, hlogUpper, herrorNonneg, herrorLt⟩ := hpoint delta hdelta
  have hmem : 1 / Real.log (q : Real) ∈ primeReciprocalLogSpectrum := by
    exact ⟨q, hqprime, rfl⟩
  calc
    ‖Metric.infDist delta primeReciprocalLogSpectrum‖ =
        Metric.infDist delta primeReciprocalLogSpectrum := by
      rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg]
    _ <= dist delta (1 / Real.log (q : Real)) := Metric.infDist_le_dist_of_mem hmem
    _ = delta - 1 / Real.log (q : Real) := by
      rw [Real.dist_eq, abs_of_nonneg herrorNonneg]
    _ <= Real.log 4 * ‖delta ^ 2‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg delta)]
      exact herrorLt.le

/-- Fidelity probe: the quantified real domain is inhabited. -/
example : Real := 1

/-- Fidelity probe: the positive-offset hypothesis is satisfiable. -/
example : 0 < (1 : Real) := by norm_num

#print axioms prime_reciprocal_log_quadratic_approximation

end D5.S3.AnalyticClosure.PrimeReciprocalLogApproximation
