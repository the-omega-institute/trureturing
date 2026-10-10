/- GID: D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/ActualReserve/HarmonicReference
   mirror-E: none(waiver:general-real-price)
   anchors: []
   utility: none
   digest: The inclusive finite harmonic prime-power cutoff maximizes the reference objective. -/

import D5.S3.Arith.GoldenResource.ReferencePrefixDominance
import D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import D5.S3.Arith.GoldenLocalThreshold
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/- The original theory §§87.2–87.5 supplies this ordinary argument. The searched
   original D5 public AND private actual-layer optimizers do not optimize the
   harmonic reference. Reuse Nat.log's Galois connection and the original whole-
   prefix theorem; no local marginal-by-marginal comparison is assumed.
   New witness: the exact reference gain sign and its inclusive finite maximum.
   Every helper below is consumed by ActualReservePrimeMask. Arbitrary real x,
   unbounded exponents and actual primes: computational content is none.
   Registration boundary: linked issue #5214; see delivery evidence for the
   original telescopes and missing source-binding/variation evidence. -/

namespace D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference

open Finset
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResource.PrefixDeficitKernel (Q S)
open D5.S3.Arith.GoldenResource.ReferencePrefixDominance

noncomputable section

/-- The reference price, used also by the unrestricted actual pressure. -/
def referencePrice (x : ℝ) : ℝ := 1 / (x * Real.log x)

/-- Nat.log makes the inclusive cutoff finite without an assumed support bound. -/
def referenceCutoff (x : ℝ) (p : ℕ) : ℕ := Nat.log p ⌊x⌋₊

/-- The complete harmonic-prefix objective, including exponent zero. -/
def referenceObjective (x : ℝ) (p a : ℕ) : ℝ :=
  Q a (p : ℝ)⁻¹ - referencePrice x * a * Real.log p

/-- Exactly the actual primes p <= x. -/
def referencePrimes (x : ℝ) : Finset ℕ :=
  (Icc 2 ⌊x⌋₊).filter Nat.Prime

/-- The inclusive finite harmonic prime-power mass. -/
def harmonicMass (x : ℝ) : ℝ :=
  ∑ p ∈ referencePrimes x, Q (referenceCutoff x p) (p : ℝ)⁻¹

/-- Each inclusive prime-power layer contributes log p. -/
def referencePsi (x : ℝ) : ℝ :=
  ∑ p ∈ referencePrimes x, (referenceCutoff x p : ℝ) * Real.log p

/-- The same reference F = P - lambda psi from the original theory. -/
def referencePressure (x : ℝ) : ℝ :=
  harmonicMass x - referencePrice x * referencePsi x

/-- All layers, including a zero-gain equality layer, are retained precisely. -/
theorem reference_cutoff_spec {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (k : ℕ) : k ≤ referenceCutoff x p ↔ (p : ℝ) ^ k ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have hfloor : ⌊x⌋₊ ≠ 0 := by
    have h : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx.le
    omega
  rw [referenceCutoff, Nat.le_log_iff_pow_le hp.one_lt hfloor,
    Nat.le_floor_iff hx0, Nat.cast_pow]

private theorem reference_step (x : ℝ) (p a : ℕ) :
    referenceObjective x p (a + 1) - referenceObjective x p a =
      (p : ℝ)⁻¹ ^ (a + 1) / (a + 1 : ℕ) - referencePrice x * Real.log p := by
  simp only [referenceObjective, Q, sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

/-- The harmonic gain sign is exactly the inclusive prime-power cutoff. -/
theorem reference_gain_nonneg_iff {x : ℝ} (hx : 1 < x) {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) :
    0 ≤ (p : ℝ)⁻¹ ^ k / k - referencePrice x * Real.log p ↔
      (p : ℝ) ^ k ≤ x := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hpow : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  have harith : (p : ℝ)⁻¹ ^ k / k = 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
    rw [inv_pow]
    field_simp [hp0.ne', hk0.ne'] <;> ring
  have hprice : referencePrice x * Real.log p = Real.log p / (x * Real.log x) := by
    unfold referencePrice
    ring
  rw [sub_nonneg, harith, hprice,
    div_le_div_iff₀ (mul_pos hx0 hlog) (mul_pos hk0 (pow_pos hp0 k))]
  have hpowlog : (p : ℝ) ^ k * Real.log ((p : ℝ) ^ k) =
      Real.log p * ((k : ℝ) * (p : ℝ) ^ k) := by
    rw [Real.log_pow]
    ring
  rw [one_mul, ← hpowlog]
  have he : Real.exp (-1 : ℝ) < 1 := by
    simpa using (Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num))
  have hmono := Real.mul_log_strictMonoOn
  constructor
  · intro h
    by_contra hpx
    have hxp : x < (p : ℝ) ^ k := lt_of_not_ge hpx
    exact (not_lt_of_ge h) (hmono (he.le.trans hx.le) (he.le.trans hpow.le) hxp)
  · intro hpx
    exact hmono.monotoneOn (he.le.trans hpow.le) (he.le.trans hx.le) hpx

/-- The finite inclusive reference exponent maximizes against every exponent. -/
theorem reference_objective_maximal {x : ℝ} (hx : 1 < x) {p : ℕ}
    (hp : p.Prime) (a : ℕ) :
    referenceObjective x p a ≤ referenceObjective x p (referenceCutoff x p) := by
  let v := referenceCutoff x p
  have up : MonotoneOn (referenceObjective x p) (Set.Iic v) := by
    apply monotoneOn_of_le_add_one Set.ordConnected_Iic
    intro k _ _ hnext
    have hg := (reference_gain_nonneg_iff hx hp (by omega : 1 ≤ k + 1)).mpr
      ((reference_cutoff_spec hx hp (k + 1)).mp hnext)
    rw [← reference_step x p k] at hg
    exact sub_nonneg.mp hg
  have down : AntitoneOn (referenceObjective x p) (Set.Ici v) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Ici
    intro k _ hk _
    have hout : ¬ (p : ℝ) ^ (k + 1) ≤ x := by
      rw [← reference_cutoff_spec hx hp (k + 1)]
      change ¬ k + 1 ≤ v
      omega
    have hg : (p : ℝ)⁻¹ ^ (k + 1) / (k + 1 : ℕ) -
        referencePrice x * Real.log p < 0 := by
      exact lt_of_not_ge (fun h => hout
        ((reference_gain_nonneg_iff hx hp (by omega : 1 ≤ k + 1)).mp h))
    rw [← reference_step x p k] at hg
    exact (sub_neg.mp hg).le
  rcases le_total a v with hav | hva
  · exact up hav (by simp) hav
  · exact down (by simp) hva hva

/-- Whole-prefix comparison followed by the reference maximum; a=0 is included. -/
theorem actual_local_le_reference_maximum {x : ℝ} (hx : 1 < x) {p : ℕ}
    (hp : p.Prime) (a : ℕ) :
    goldenPrimeLocalObjective (referencePrice x) p a ≤
      referenceObjective x p (referenceCutoff x p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hz : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hz1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have hgeom : S a (p : ℝ)⁻¹ =
      (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) := by
    unfold S
    rw [geom_sum_eq hz1.ne]
    apply (div_eq_div_iff (sub_ne_zero.mpr hz1.ne) (sub_ne_zero.mpr hz1.ne')).mpr
    ring
  have hprefix : Real.log (S a (p : ℝ)⁻¹) ≤ Q a (p : ℝ)⁻¹ := by
    by_cases ha : a = 0
    · simp [ha, S, Q]
    · exact (log_geom_prefix_lt_harmonic_prefix (by omega) hz hz1).le
  rw [hgeom] at hprefix
  exact (sub_le_sub_right hprefix (referencePrice x * a * Real.log p)).trans
    (reference_objective_maximal hx hp a)

/-- Extend the exact reference sum to any finite actual-prime superset. -/
theorem reference_pressure_sum_on {x : ℝ} (hx : 1 < x) (U : Finset ℕ)
    (hU : referencePrimes x ⊆ U) (hprime : ∀ p ∈ U, p.Prime) :
    referencePressure x =
      ∑ p ∈ U, referenceObjective x p (referenceCutoff x p) := by
  have hbase : referencePressure x =
      ∑ p ∈ referencePrimes x, referenceObjective x p (referenceCutoff x p) := by
    simp only [referencePressure, harmonicMass, referencePsi, referenceObjective,
      mul_sum, sum_sub_distrib, mul_assoc]
  rw [hbase]
  apply sum_subset hU
  intro p hpU hpout
  have hp : p.Prime := hprime p hpU
  have hv : referenceCutoff x p = 0 := by
    by_contra hv
    have hpx : (p : ℝ) ≤ x := by
      simpa using (reference_cutoff_spec hx hp 1).mp (by omega)
    have hmem : p ∈ referencePrimes x := by
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,
        (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr hpx⟩, hp⟩
    exact hpout hmem
  simp [hv, referenceObjective, Q]

end

#print axioms reference_cutoff_spec
#print axioms reference_gain_nonneg_iff
#print axioms reference_objective_maximal
#print axioms actual_local_le_reference_maximum
#print axioms reference_pressure_sum_on

end D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
