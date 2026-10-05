/- GID: D5/S3/Arith/GoldenResource/ReferenceReserve
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/ReferenceReserve
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: The reference prime objective controls the optimizer reserve independently of ties. -/

import D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import D5.S3.Arith.GoldenResource.ReferencePrefixDominance
import D5.S3.Arith.GoldenLocalThreshold
import D5.S3.Arith.GoldenLayerMarginalDecay
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.GoldenResource.ReferenceReserve

open Finset Set Real
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay

local notation "Q" => PrefixDeficitKernel.Q
local notation "S" => PrefixDeficitKernel.S
local notation "D" => PrefixDeficitKernel.D

/-- The price associated to a real reference scale. -/
def scalePrice (x : ℝ) : ℝ := 1 / (x * Real.log x)

/-- The exponent of the largest prime power not exceeding the reference scale. -/
def referenceExponent (x : ℝ) (p : ℕ) : ℕ := ⌊Real.log x / Real.log p⌋₊

/-- Harmonic-prefix benefit less the logarithmic exponent cost. -/
def referenceObjective (x : ℝ) (p a : ℕ) : ℝ :=
  Q a (p : ℝ)⁻¹ - scalePrice x * a * Real.log p

/-- The prime reserve compares the reference value with the actual supremum.
It is zero on nonprime indices so that its total uses a natural-number sum. -/
def reserve (x : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then referenceObjective x p (referenceExponent x p) -
    sSup (Set.range (goldenPrimeLocalObjective (scalePrice x) p)) else 0

private theorem prime_bounds {p : ℕ} (hp : p.Prime) :
    0 < (p : ℝ) ∧ 1 < (p : ℝ) ∧ 0 < Real.log p ∧
      0 < (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ < 1 := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h0 : (0 : ℝ) < p := by linarith
  exact ⟨h0, h1, Real.log_pos h1, inv_pos.mpr h0, (inv_lt_one₀ h0).mpr h1⟩

private theorem exponent_spec {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ referenceExponent x p ≤ x ∧
      x < (p : ℝ) ^ (referenceExponent x p + 1) := by
  obtain ⟨hp0, _, hlog, _, _⟩ := prime_bounds hp
  have hx0 : 0 < x := by linarith
  have hquot : 0 ≤ Real.log x / Real.log p := div_nonneg (Real.log_pos hx).le hlog.le
  have hlo := Nat.floor_le hquot
  have hhi := Nat.lt_floor_add_one (Real.log x / Real.log p)
  constructor
  · apply (Real.log_le_log_iff (pow_pos hp0 _) hx0).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hlog).mp hlo
  · apply (Real.log_lt_log_iff hx0 (pow_pos hp0 _)).mp
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
    exact (div_lt_iff₀ hlog).mp hhi

private theorem reference_step (x : ℝ) (p a : ℕ) :
    referenceObjective x p (a + 1) - referenceObjective x p a =
      (p : ℝ)⁻¹ ^ (a + 1) / (a + 1) - scalePrice x * Real.log p := by
  unfold referenceObjective PrefixDeficitKernel.Q
  rw [sum_range_succ]
  push_cast
  ring

private theorem reference_increment_sign {x : ℝ} (hx : 1 < x) {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) :
    (0 ≤ (p : ℝ)⁻¹ ^ k / k - scalePrice x * Real.log p ↔ (p : ℝ) ^ k ≤ x) := by
  obtain ⟨hp0, hp1, hlog, _, _⟩ := prime_bounds hp
  have hx0 : 0 < x := by linarith
  have hxlog := Real.log_pos hx
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpow0 := pow_pos hp0 k
  have hpow1 : 1 ≤ (p : ℝ) ^ k := one_le_pow₀ hp1.le
  have hlogpow : Real.log ((p : ℝ) ^ k) = (k : ℝ) * Real.log p := Real.log_pow _ _
  have hmono := Real.mul_log_strictMonoOn
  have he : Real.exp (-1) ≤ (1 : ℝ) := (Real.exp_lt_one_iff.mpr (by norm_num)).le
  have hdomainX : x ∈ Set.Ici (Real.exp (-1)) := le_trans he hx.le
  have hdomainP : (p : ℝ) ^ k ∈ Set.Ici (Real.exp (-1)) := le_trans he hpow1
  have heq : (0 ≤ (p : ℝ)⁻¹ ^ k / k - scalePrice x * Real.log p) ↔
      (p : ℝ) ^ k * Real.log ((p : ℝ) ^ k) ≤ x * Real.log x := by
    have hi : (p : ℝ)⁻¹ ^ k / k = 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
      rw [inv_pow]
      field_simp
    have hc : scalePrice x * Real.log p = Real.log p / (x * Real.log x) := by
      unfold scalePrice
      ring
    rw [sub_nonneg, hi, hc, div_le_div_iff₀ (mul_pos hx0 hxlog) (mul_pos hk0 hpow0),
      one_mul, hlogpow]
    congr 1 using (by ring : Real.log (p : ℝ) * ((k : ℝ) * (p : ℝ) ^ k) =
      (p : ℝ) ^ k * ((k : ℝ) * Real.log p))
  rw [heq]
  exact hmono.le_iff_le hdomainP hdomainX

private theorem reference_maximal {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    ∀ a, referenceObjective x p a ≤ referenceObjective x p (referenceExponent x p) := by
  let v := referenceExponent x p
  obtain ⟨hlo, hhi⟩ := exponent_spec hx hp
  obtain ⟨hp0, hp1, _, _, _⟩ := prime_bounds hp
  have hup : MonotoneOn (referenceObjective x p) (Set.Iic v) := by
    apply monotoneOn_of_le_add_one Set.ordConnected_Iic
    intro k _ _ hkv
    have hpow : (p : ℝ) ^ (k + 1) ≤ x :=
      (pow_le_pow_right₀ hp1.le hkv).trans hlo
    have hs := (reference_increment_sign hx hp (k := k + 1) (by omega)).mpr hpow
    rw [← reference_step] at hs
    exact sub_nonneg.mp hs
  have hdown : AntitoneOn (referenceObjective x p) (Set.Ici v) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Ici
    intro k _ hvk _
    have hpow : x < (p : ℝ) ^ (k + 1) :=
      hhi.trans_le (pow_le_pow_right₀ hp1.le (Nat.succ_le_succ hvk))
    have hs : (p : ℝ)⁻¹ ^ (k + 1) / (k + 1) - scalePrice x * Real.log p < 0 :=
      lt_of_not_ge (fun h => not_le_of_gt hpow
        ((reference_increment_sign hx hp (by omega)).mp h))
    rw [← reference_step] at hs
    exact (sub_neg.mp hs).le
  intro a
  rcases le_total a v with h | h
  · exact hup h (by simp) h
  · exact hdown (by simp) h h

private theorem actual_eq_prefix (lambda : ℝ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    goldenPrimeLocalObjective lambda p a =
      Real.log (S a (p : ℝ)⁻¹) - lambda * a * Real.log p := by
  obtain ⟨_, _, _, _, hi⟩ := prime_bounds hp
  unfold goldenPrimeLocalObjective PrefixDeficitKernel.S
  congr 2
  rw [geom_sum_eq hi.ne]
  apply (div_eq_div_iff (sub_ne_zero.mpr hi.ne') (sub_ne_zero.mpr hi.ne)).mpr
  ring

private theorem actual_le_reference (x : ℝ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    goldenPrimeLocalObjective (scalePrice x) p a ≤ referenceObjective x p a := by
  rw [actual_eq_prefix _ hp]
  apply sub_le_sub_right
  by_cases ha : a = 0
  · simp [ha, PrefixDeficitKernel.S, PrefixDeficitKernel.Q]
  · obtain ⟨_, _, _, hi0, hi1⟩ := prime_bounds hp
    exact (ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix
      (by omega) hi0 hi1).le

private theorem actual_bounded {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    BddAbove (Set.range (goldenPrimeLocalObjective (scalePrice x) p)) := by
  refine ⟨referenceObjective x p (referenceExponent x p), ?_⟩
  rintro y ⟨a, rfl⟩
  exact (actual_le_reference x hp a).trans (reference_maximal hx hp a)

/-- The reserve is nonnegative, bounded by the matching finite-prefix deficit,
and vanishes beyond the reference scale. -/
theorem result {x : ℝ} (hx : 1 < x) :
    (∀ p : ℕ, p.Prime → 0 ≤ reserve x p ∧
      reserve x p ≤ D (referenceExponent x p) (p : ℝ)⁻¹) := by
  intro p hp
  have hb := actual_bounded hx hp
  have hsup := csSup_le (Set.range_nonempty _) (by
    rintro y ⟨a, rfl⟩
    exact (actual_le_reference x hp a).trans (reference_maximal hx hp a))
  have hval := le_csSup hb (Set.mem_range_self (referenceExponent x p))
  rw [actual_eq_prefix _ hp] at hval
  simp only [reserve, if_pos hp, referenceObjective, PrefixDeficitKernel.D] at *
  constructor <;> linarith

end D5.S3.Arith.GoldenResource.ReferenceReserve
