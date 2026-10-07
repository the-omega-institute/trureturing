/- GID: D5/S3/Arith/FibonacciAtomic/DivisorLogEnvelope
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/DivisorLogEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Moebius logarithmic divisor sum has a sharp positive envelope. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Arith.FibonacciAtomic.DivisorLogEnvelope

/-- The finite signed logarithmic sum over the actual positive divisors of `R`. -/
noncomputable def moebiusLogSum (R : ℕ) (t : ℝ) : ℝ :=
  ∑ d ∈ R.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (1 + t ^ d)

/-- The actual Möbius logarithmic divisor sum for all positive natural numbers. -/
theorem full_log_envelope (R : ℕ) (t : ℝ) (hR : 0 < R)
    (ht : 0 < t) (htmax : t ≤ (2 : ℝ) / 5) :
    0 < moebiusLogSum R t ∧ moebiusLogSum R t ≤ Real.log (1 + t) ∧
      (moebiusLogSum R t = Real.log (1 + t) ↔ R = 1) := by
  classical
  have log_lower {u : ℝ} (hu : 0 < u) :
      u / (1 + u) ≤ Real.log (1 + u) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + u by linarith)
    have he : u / (1 + u) = 1 - (1 + u)⁻¹ := by
      field_simp
      ring
    rwa [← he] at h
  have finite_moebius_log_tail (s : Finset ℕ) (k : ℕ) {t : ℝ}
      (ht : 0 < t) (ht1 : t < 1) (hs : ∀ d ∈ s, k ≤ d) :
      |∑ d ∈ s, (ArithmeticFunction.moebius d : ℝ) * Real.log (1 + t ^ d)|
        ≤ t ^ k / (1 - t) := by
    have hsub : s ⊆ Ico k (s.sup id + 1) := by
      intro d hd
      exact mem_Ico.mpr ⟨hs d hd, Nat.lt_succ_of_le (Finset.le_sup (f := id) hd)⟩
    calc
      _ ≤ ∑ d ∈ s, |(ArithmeticFunction.moebius d : ℝ) * Real.log (1 + t ^ d)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ s, t ^ d := by
        apply sum_le_sum
        intro d hd
        have hp : 0 ≤ t ^ d := pow_nonneg ht.le d
        have hl : 0 ≤ Real.log (1 + t ^ d) := Real.log_nonneg (by linarith)
        have hm : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        have hu := Real.log_le_sub_one_of_pos (show 0 < 1 + t ^ d by linarith)
        rw [abs_mul, abs_of_nonneg hl]
        calc
          _ ≤ 1 * Real.log (1 + t ^ d) := mul_le_mul_of_nonneg_right hm hl
          _ ≤ t ^ d := by linarith
      _ ≤ ∑ d ∈ Ico k (s.sup id + 1), t ^ d :=
        sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => pow_nonneg ht.le d)
      _ ≤ t ^ k / (1 - t) := geom_sum_Ico_le_of_lt_one ht.le ht1
  have prime_tail {t : ℝ} (ht : 0 < t) (htmax : t ≤ (2 : ℝ) / 5)
      {p : ℕ} (hp : 0 < p) :
      t ^ (p + 1) / (1 - t) < t ^ p / (1 + t ^ p) := by
    have ht1 : t ≤ 1 := by linarith
    have hp0 : 0 < t ^ p := pow_pos ht p
    have hpt : t ^ p ≤ t := pow_le_of_le_one ht.le ht1 (Nat.ne_of_gt hp)
    have hq : t ^ 2 ≤ (4 : ℝ) / 25 := by
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htmax)]
    have hb : t * (1 + t ^ p) < 1 - t := by
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hpt)]
    apply (div_lt_div_iff₀ (by linarith : 0 < 1 - t)
      (by positivity : 0 < 1 + t ^ p)).mpr
    rw [pow_succ]
    have h := mul_lt_mul_of_pos_left hb hp0
    nlinarith
  have hR0 : R ≠ 0 := Nat.ne_of_gt hR
  have ht1 : t < 1 := by linarith
  have h1 : 1 ∈ R.divisors := Nat.one_mem_divisors.mpr hR0
  have hsplit : moebiusLogSum R t =
      (∑ d ∈ R.divisors.erase 1,
        (ArithmeticFunction.moebius d : ℝ) * Real.log (1 + t ^ d)) +
        Real.log (1 + t) := by
    have h := sum_erase_add R.divisors
      (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log (1 + t ^ d)) h1
    simpa [moebiusLogSum] using h.symm
  have hsupport : ∀ d ∈ R.divisors.erase 1, 2 ≤ d := by
    intro d hd
    obtain ⟨hd1, hdR⟩ := mem_erase.mp hd
    have hdvd := Nat.dvd_of_mem_divisors hdR
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hR
    omega
  have htail := finite_moebius_log_tail (R.divisors.erase 1) 2 ht ht1 hsupport
  have hsmall : t ^ 2 / (1 - t) < t / (1 + t) := by
    simpa using (prime_tail ht htmax (p := 1) (by decide))
  have hlog := log_lower ht
  have hpositive : 0 < moebiusLogSum R t := by
    have hlo := (abs_le.mp htail).1
    rw [hsplit]
    linarith
  have hstrict : R ≠ 1 → moebiusLogSum R t < Real.log (1 + t) := by
    intro hne
    let p := R.minFac
    have hprime : Nat.Prime p := Nat.minFac_prime hne
    have hp1 : p ≠ 1 := hprime.ne_one
    have hp0 : 0 < p := hprime.pos
    have hpR : p ∈ R.divisors := Nat.mem_divisors.mpr ⟨Nat.minFac_dvd R, hR0⟩
    have hpe : p ∈ R.divisors.erase 1 := mem_erase.mpr ⟨hp1, hpR⟩
    have hs : ∀ d ∈ (R.divisors.erase 1).erase p, p + 1 ≤ d := by
      intro d hd
      obtain ⟨hdp, hd⟩ := mem_erase.mp hd
      obtain ⟨hd1, hdR⟩ := mem_erase.mp hd
      have hdvd := Nat.dvd_of_mem_divisors hdR
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hR
      have hdmin : p ≤ d := Nat.minFac_le_of_dvd (by omega) hdvd
      omega
    have htailp := finite_moebius_log_tail ((R.divisors.erase 1).erase p)
      (p + 1) ht ht1 hs
    have hsmallp := prime_tail ht htmax hp0
    have hlogp := log_lower (pow_pos ht p)
    have hup := (abs_le.mp htailp).2
    have hsplitp : moebiusLogSum R t =
        (∑ d ∈ (R.divisors.erase 1).erase p,
          (ArithmeticFunction.moebius d : ℝ) * Real.log (1 + t ^ d)) -
        Real.log (1 + t ^ p) + Real.log (1 + t) := by
      have h := sum_erase_add (R.divisors.erase 1)
        (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log (1 + t ^ d)) hpe
      rw [ArithmeticFunction.moebius_apply_prime hprime] at h
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at h
      rw [hsplit, ← h]
      ring
    rw [hsplitp]
    linarith
  have hone : moebiusLogSum 1 t = Real.log (1 + t) := by
    simp [moebiusLogSum]
  refine ⟨hpositive, ?_, ?_⟩
  · by_cases he : R = 1
    · simp [he, hone]
    · exact (hstrict he).le
  · constructor
    · intro he
      by_contra hne
      exact (ne_of_lt (hstrict hne)) he
    · intro he
      subst R
      exact hone


end D5.S3.Arith.FibonacciAtomic.DivisorLogEnvelope
