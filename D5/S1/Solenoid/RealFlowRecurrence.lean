/- GID: D5/S1/Solenoid/RealFlowRecurrence
   generality: I
   mirror-B: D5/B/S1/Solenoid/RealFlowRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factorial times recur to zero along the faithful solenoid real flow. -/

/- Library-search audit trail (2026-08-14):
   * `Nat.dvd_factorial` makes each fixed circle coordinate eventually zero.
   * `tendsto_pi_nhds` lifts those coordinate limits to the product topology.
   * `IsEmbedding.tendsto_nhds_iff` and `Nat.self_le_factorial` obstruct an
     embedding by reflecting the recurrence back to the divergent real times.
-/

import D5.S1.Solenoid.RealFlowInjectivity

namespace D5.S1.Solenoid.RealFlowRecurrence

open Filter Topology
open D5.S1.Dynamics

/-- The factorial times return to zero in the universal solenoid. -/
theorem realFlow_factorial_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => UniversalSolenoid.realFlow (Nat.factorial n : ℝ))
      Filter.atTop (nhds 0) := by
  have hinducing :
      IsInducing
        (Subtype.val : UniversalSolenoid → (ℕ+ → AddCircle (1 : ℝ))) := ⟨rfl⟩
  rw [hinducing.tendsto_nhds_iff]
  rw [tendsto_pi_nhds]
  intro m
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop m.1] with n hn
  change 0 = (((n.factorial : ℝ) / m.1 : ℝ) : AddCircle (1 : ℝ))
  symm
  rcases Nat.dvd_factorial m.2 hn with ⟨k, hk⟩
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
  refine ⟨(k : ℤ), ?_⟩
  rw [zsmul_eq_mul]
  norm_num
  rw [show (n.factorial : ℝ) = (m.1 : ℝ) * k by exact_mod_cast hk]
  field_simp [Nat.ne_of_gt m.2]

/-- The faithful universal-solenoid real flow is not a topological embedding. -/
theorem realFlow_injective_not_isEmbedding :
    Function.Injective UniversalSolenoid.realFlow ∧
      ¬ IsEmbedding UniversalSolenoid.realFlow := by
  refine ⟨RealFlowInjectivity.realFlow_injective, ?_⟩
  intro hembedding
  have htime :
      Tendsto (fun n : ℕ => (Nat.factorial n : ℝ)) atTop (nhds 0) := by
    apply (hembedding.tendsto_nhds_iff).2
    change Tendsto
      (fun n : ℕ => UniversalSolenoid.realFlow (Nat.factorial n : ℝ))
      atTop (nhds (UniversalSolenoid.realFlow 0))
    rw [UniversalSolenoid.realFlow_zero]
    exact realFlow_factorial_tendsto_zero
  have htop :
      Tendsto (fun n : ℕ => (Nat.factorial n : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by exact_mod_cast Nat.self_le_factorial n)
      tendsto_natCast_atTop_atTop
  have hlt : ∀ᶠ n : ℕ in atTop, (Nat.factorial n : ℝ) < 1 :=
    htime.eventually (Iio_mem_nhds zero_lt_one)
  have hgt : ∀ᶠ n : ℕ in atTop, (1 : ℝ) < Nat.factorial n :=
    htop.eventually (eventually_gt_atTop 1)
  rcases (hlt.and hgt).exists with ⟨n, hnlt, hngt⟩
  exact lt_asymm hnlt hngt

example : ¬ IsEmbedding UniversalSolenoid.realFlow :=
  realFlow_injective_not_isEmbedding.2

end D5.S1.Solenoid.RealFlowRecurrence
