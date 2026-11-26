/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialAsymptotic
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/FactorialAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact logarithmic rate of the strict distinct-prime tail at fixed factorial order. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialLower
import D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve
import D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper

/-! Matching bounds for the strict factorial tail at the original counting cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Finset Real
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic

open FactorialReserve (centeredThreshold threshold tailCount cutoff safeReserve
  factorial_reserve factorial_far_deletion continuousReserve continuous_reserve_limit)
open FactorialLower (factorial_tail_lower)
open RankinUpper (factorial_sharp_upper_bound)
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)

private theorem eventual_prime_base (r : ℕ) (hr : 2 ≤ r) :
    ∃ base : ℝ → Finset ℕ, ∀ᶠ P : ℝ in atTop,
      base P ⊆ Nat.primesLE ⌊P⌋₊ ∧
      centeredThreshold r P < ((base P).card : ℝ) ∧
      (∑ p ∈ base P, log (p : ℝ)) ≤ P - safeReserve r P ∧
      (∀ p : ℕ, Nat.Prime p → 3 * P / 4 < (p : ℝ) → (p : ℝ) ≤ P → p ∈ base P) := by
  let admissible (P : ℝ) (S : Finset ℕ) : Prop :=
    S ⊆ Nat.primesLE ⌊P⌋₊ ∧
    centeredThreshold r P < (S.card : ℝ) ∧
    (∑ p ∈ S, log (p : ℝ)) ≤ P - safeReserve r P ∧
    (∀ p : ℕ, Nat.Prime p → 3 * P / 4 < (p : ℝ) → (p : ℝ) ≤ P → p ∈ S)
  have hbase : ∀ᶠ P : ℝ in atTop, ∃ S, admissible P S := by
    filter_upwards [factorial_far_deletion r hr, eventually_gt_atTop (1 : ℝ)] with P hfar hP
    obtain ⟨R, hR, hcard⟩ := hfar.1
    obtain ⟨hdeleted, S, hS, hsize, hprime, _, hbudget⟩ := hfar.2 R hR hcard
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · rw [hS]
      exact sdiff_subset
    · rw [hsize, cutoff, Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one _
    · rw [log_prod (fun p hp => Nat.cast_ne_zero.mpr (hprime p hp).1.ne_zero)] at hbudget
      exact hbudget
    · intro p hp hlow hhigh
      rw [hS]
      refine mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff (by linarith : 0 ≤ P)).mpr hhigh, hp⟩, ?_⟩
      intro hpR
      have hupper := (hdeleted p hpR).2.1
      linarith
  classical
  refine ⟨fun P => if h : ∃ S, admissible P S then h.choose else ∅, ?_⟩
  filter_upwards [hbase] with P hP
  simpa only [dite_eq_left hP] using hP.choose_spec

/-- For each fixed order at least two, the strict factorial tail is eventually
nonempty and has the stated exact normalized logarithmic counting rate. -/
theorem factorial_tail_asymptotic (r : ℕ) (hr : 2 ≤ r) :
    (∀ᶠ x : ℝ in atTop, 0 < tailCount r x) ∧
    Tendsto (fun x : ℝ =>
      log (tailCount r x : ℝ) / (log x / log (log x) ^ (((r : ℝ) + 1) / 2)))
      atTop (𝓝 (π * sqrt (2 * (r.factorial : ℝ) / 3))) := by
  obtain ⟨base, hbase⟩ := eventual_prime_base r hr
  have hlower (ε : ℝ) (hε : 0 < ε) :=
    factorial_tail_lower r hr ε hε base (safeReserve r) (factorial_reserve r).2.2.2 hbase
  have hupper (ε : ℝ) (hε : 0 < ε) :=
    factorial_sharp_upper_bound r hr (centeredThreshold r)
      (by simpa only [continuousReserve] using continuous_reserve_limit r) ε hε
  let C (P : ℝ) := tailCount r (exp P)
  let Z (P : ℝ) := P / log P ^ (((r : ℝ) + 1) / 2)
  let K : ℝ := π * sqrt (2 * (r.factorial : ℝ) / 3)
  have hC (P : ℝ) : C P =
      ((Icc 1 ⌊exp P⌋₊).filter (fun n : ℕ =>
        centeredThreshold r P < (ArithmeticFunction.cardDistinctFactors n : ℝ))).card := by
    simp only [C, tailCount, threshold, log_exp]
  have hnonempty : ∀ᶠ P : ℝ in atTop, 0 < C P := by
    filter_upwards [hlower 1 zero_lt_one] with P hP
    rw [hC]
    exact hP.1
  have hlimit : Tendsto (fun P : ℝ => log (C P : ℝ) / Z P) atTop (𝓝 K) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    filter_upwards [hlower (ε / 2) hhalf, hupper (ε / 2) hhalf,
      eventually_gt_atTop (1 : ℝ)] with P hlo hup hP
    have hcount : 0 < C P := by
      rw [hC]
      exact hlo.1
    have hloC : (K - ε / 2) * Z P ≤ log (C P : ℝ) := by
      rw [hC]
      exact hlo.2
    have hupC : (C P : ℝ) < exp ((K + ε / 2) * Z P) := by
      rw [hC]
      exact hup
    have hZ : 0 < Z P :=
      div_pos (zero_lt_one.trans hP) (rpow_pos_of_pos (log_pos hP) _)
    have hpos : 0 < (C P : ℝ) := by exact_mod_cast hcount
    have hlog := log_lt_log hpos hupC
    rw [log_exp] at hlog
    have hlo' := (le_div_iff₀ hZ).mpr hloC
    have hup' := (div_lt_iff₀ hZ).mpr hlog
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  constructor
  · filter_upwards [tendsto_log_atTop.eventually hnonempty, eventually_gt_atTop (0 : ℝ)]
      with x hx hxpos
    simpa only [C, exp_log hxpos] using hx
  · apply (hlimit.comp tendsto_log_atTop).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_def, C, exp_log hx, Z]

end D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic
