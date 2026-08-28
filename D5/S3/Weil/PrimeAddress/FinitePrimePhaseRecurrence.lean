/- GID: D5/S3/Weil/PrimeAddress/FinitePrimePhaseRecurrence
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeAddress/FinitePrimePhaseRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prime phase vectors return arbitrarily close to the coherent phase. -/

import D5.S3.Weil.PrimeAddress.PrimeLogIndependence
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Sequences

namespace D5.S3.Weil.PrimeAddress.FinitePrimePhaseRecurrence

/-- Every finite family of prime logarithm phases has recurrence times above any real bound. -/
theorem finite_prime_phase_recurrence
    (primes : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ ξ : ℝ, B < ξ ∧ ∀ p ∈ primes,
      ‖Complex.exp (Complex.I * (ξ * Real.log (p : ℕ))) - 1‖ < ε := by
  obtain ⟨c, hc⟩ := exists_nat_gt (max B 0)
  let phase : ℕ → primes → Circle := fun n p =>
    Circle.exp (((n * c : ℕ) : ℝ) * Real.log (p : ℕ))
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq phase
  have hlim_succ :
      Filter.Tendsto (fun k => phase (φ (k + 1))) Filter.atTop (nhds a) := by
    simpa [Function.comp_def] using hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hratio :
      Filter.Tendsto (fun k => phase (φ (k + 1)) * (phase (φ k))⁻¹) Filter.atTop
        (nhds (1 : primes → Circle)) := by
    simpa only [Function.comp_def, mul_inv_cancel] using hlim_succ.mul hlim.inv
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hratio ε hε
  let d := φ (K + 1) - φ K
  let ξ : ℝ := ((d * c : ℕ) : ℝ)
  have hφ_step : φ K < φ (K + 1) := hφ (Nat.lt_succ_self K)
  have hd : 1 ≤ d := by
    simp only [d]
    omega
  have hc_le : c ≤ d * c := by
    simpa only [one_mul] using Nat.mul_le_mul_right c hd
  refine ⟨ξ, ?_, ?_⟩
  · have hc_real : B < (c : ℝ) := (le_max_left B 0).trans_lt hc
    have hc_le_real : (c : ℝ) ≤ ξ := by
      simp only [ξ]
      exact_mod_cast hc_le
    exact hc_real.trans_le hc_le_real
  · intro p hp
    let j : primes := ⟨p, hp⟩
    have hclose := hK K le_rfl
    have hjdist :
        dist ((phase (φ (K + 1)) * (phase (φ K))⁻¹) j) (1 : Circle) < ε :=
      (dist_le_pi_dist
        (phase (φ (K + 1)) * (phase (φ K))⁻¹) (1 : primes → Circle) j).trans_lt hclose
    have hphase :
        (((phase (φ (K + 1)) * (phase (φ K))⁻¹) j : Circle) : ℂ) =
          Complex.exp (Complex.I * (ξ * Real.log (p : ℕ))) := by
      change ((Circle.exp (((φ (K + 1) * c : ℕ) : ℝ) * Real.log (p : ℕ)) *
          (Circle.exp (((φ K * c : ℕ) : ℝ) * Real.log (p : ℕ)))⁻¹ : Circle) : ℂ) = _
      rw [← div_eq_mul_inv, ← Circle.exp_sub, Circle.coe_exp]
      congr 1
      simp only [ξ, d]
      push_cast [Nat.cast_sub hφ_step.le]
      ring
    have hjnorm :
        ‖(((phase (φ (K + 1)) * (phase (φ K))⁻¹) j : Circle) : ℂ) - 1‖ < ε := by
      rw [show dist ((phase (φ (K + 1)) * (phase (φ K))⁻¹) j) (1 : Circle) =
          dist ((((phase (φ (K + 1)) * (phase (φ K))⁻¹) j : Circle) : ℂ)) (1 : ℂ) from rfl,
        dist_eq_norm] at hjdist
      exact hjdist
    rwa [hphase] at hjnorm

#print axioms finite_prime_phase_recurrence

end D5.S3.Weil.PrimeAddress.FinitePrimePhaseRecurrence
