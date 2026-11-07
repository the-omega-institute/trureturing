/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/NormalizedPowerPerturbationAllCutoffKL
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/NormalizedPowerPerturbationAllCutoffKL
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: WIP: normalized countable power perturbations and every finite collapsed cutoff. -/

/-!
WIP source for the E3 atom of
`FIB_ENTROPY_HARMONIC_RENEWAL_STATE_THRESHOLD`.

The target deliberately keeps the infinite normalizers and the complete
`Option (Fin L)` carrier.  `none` is the whole tail `k > L`; a short index
`r : Fin L` denotes the physical count `r.val + 1`.  The theorem is left open
until the two-reference full-series energy estimate and the finite-to-countable
tail Cauchy passage have a kernel proof.  This file is not frozen or deposited.
-/

import D5.S3.Divergence.ClassicalDPI
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CriticalRenewalSource

set_option autoImplicit false

open Filter Finset
open scoped Topology

private lemma power_increment (m k : ℕ) (hm : 1 ≤ m) :
    ((k + 1 : ℕ) : ℝ) ^ (m - 1) ≤
      ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
  have he : m = (m - 1) + 1 := by omega
  have hp : (k : ℝ) ^ (m - 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (m - 1) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.le_succ k) _
  have hh := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) k)
  rw [he, pow_succ, pow_succ]
  push_cast
  nlinarith

private lemma adjacent_power_sum (m : ℕ) (hm : 1 ≤ m)
    (s : ℝ) (hs : 0 < s) :
    powerSum (m - 1) s ≤ (1 - Real.exp (-s)) * powerSum m s := by
  have ha := summable_term m hs
  have hb := summable_term (m - 1) hs
  have hc : Summable (fun k : ℕ => term m s (k + 1)) :=
    (summable_nat_add_iff 1).2 ha
  have hsum : (∑' k : ℕ, term m s (k + 1)) = powerSum m s := by
    simpa [powerSum, term] using ha.tsum_eq_zero_add
  have hshift : ∀ k : ℕ,
      Real.exp (-s) * term m s k =
        (k : ℝ) ^ m * Real.exp (-s * ((k + 1 : ℕ) : ℝ)) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [term, Nat.ne_of_gt hm]
    · simp only [term, hk, ↓reduceIte]
      rw [mul_left_comm, ← Real.exp_add]
      congr 1
      push_cast
      ring
  have hle : ∀ k : ℕ, term (m - 1) s (k + 1) ≤
      term m s (k + 1) - Real.exp (-s) * term m s k := by
    intro k
    rw [hshift]
    simpa [term, Nat.succ_ne_zero, sub_mul] using
      mul_le_mul_of_nonneg_right (power_increment m k hm)
        (Real.exp_pos (-s * ((k + 1 : ℕ) : ℝ))).le
  have hb' : Summable (fun k : ℕ => term (m - 1) s (k + 1)) :=
    (summable_nat_add_iff 1).2 hb
  have h := hb'.tsum_le_tsum hle (hc.sub (ha.mul_left (Real.exp (-s))))
  have hsum' : (∑' k : ℕ, term (m - 1) s (k + 1)) = powerSum (m - 1) s := by
    simpa [powerSum, term] using hb.tsum_eq_zero_add
  rw [hsum', Summable.tsum_sub hc (ha.mul_left _), hsum, tsum_mul_left] at h
  change powerSum (m - 1) s ≤ powerSum m s - Real.exp (-s) * powerSum m s at h
  nlinarith

theorem normalized_power_perturbation_all_cutoff_kl
    (m : ℕ) (hm : 4 ≤ m)
    (d : ℕ → ℝ) (hd0 : d 0 = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hd : ∀ k : ℕ, 0 < k →
      0 ≤ d k ∧ d k ≤ δ * (k : ℝ) ^ (m - 1))
    (s : ℝ) (hs : 0 < s)
    (hZ : (m.factorial : ℝ) / 2 ≤
      s ^ (m + 1) * powerSum m s) :
    let v : Bool → ℕ → ℝ := fun i k =>
      term m s k + if i then d k * Real.exp (-s * (k : ℝ)) else 0
    let Z : Bool → ℝ := fun i => ∑' k : ℕ, v i k
    let p : Bool → ℕ → ℝ := fun i k => v i k / Z i
    let w : ℕ → ℝ := fun k => p true k - p false k
    (∀ i : Bool, HasSum (p i) 1 ∧ p i 0 = 0 ∧
      ∀ k : ℕ, 0 < k → 0 < p i k) ∧
    (∀ j : Bool,
      Summable (fun k : ℕ => (w k) ^ 2 / p j k) ∧
      (∑' k : ℕ, (w k) ^ 2 / p j k) ≤
        4 * δ ^ 2 * (1 - Real.exp (-s)) ^ 2) ∧
    (∀ i : Bool,
      Summable (fun k : ℕ => p i k * Real.log (p i k / p (!i) k)) ∧
      (∑' k : ℕ, p i k * Real.log (p i k / p (!i) k)) ≤
        ∑' k : ℕ, (w k) ^ 2 / p (!i) k) ∧
    (∀ L : ℕ, 1 ≤ L →
      let a : Bool → Option (Fin L) → ℝ := fun i z =>
        match z with
        | some r => p i (r.val + 1)
        | none => 1 - ∑ r : Fin L, p i (r.val + 1)
      ∀ i : Bool,
        klDivergence (a i) (a (!i)) ≤
          4 * δ ^ 2 * s ^ 2 * min 1 ((s * (L : ℝ)) ^ (m - 1))) := by
  have hAdj := adjacent_power_sum m (by omega) s hs
  have hAdj2 := adjacent_power_sum (m - 1) (by omega) s hs
  have hZpos := powerSum_pos m hs
  have hr : 0 < 1 - Real.exp (-s) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -s < 0)
    linarith
  have hTwo : powerSum (m - 2) s ≤
      (1 - Real.exp (-s)) ^ 2 * powerSum m s := by
    have he : m - 1 - 1 = m - 2 := by omega
    rw [he] at hAdj2
    nlinarith [mul_le_mul_of_nonneg_left hAdj hr.le]
  sorry

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution
