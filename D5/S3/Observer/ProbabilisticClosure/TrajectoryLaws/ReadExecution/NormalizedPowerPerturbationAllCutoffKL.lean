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

/-
  Admission record (WIP, therefore no validated status is claimed).
  proof_shape: content (the intended live witness is the two-reference
    countable normalized square-energy estimate).
  escape_witness: the countable bound
    `sum_k (p₁ k - p₀ k)^2 / pⱼ k ≤ 4 δ^2 (1-exp(-s))^2`.
  admission_basis: open pending the kernel proof of that witness.
  Direct frozen dependencies: CriticalRenewalSource.term and powerSum;
    ClassicalDPI.klDivergence.
-/

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
  sorry

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution
