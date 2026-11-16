/- GID: D5/S3/Arith/Robin/Analytic/RobinThresholdDivergence
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/RobinThresholdDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A local obstruction family forces any eventual threshold to diverge at the endpoint. -/

import Mathlib

/-! A local obstruction family forces any eventual threshold to diverge at the
endpoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.RobinThresholdDivergence

/-! The theorem below is the order-theoretic part of the threshold argument in
the latest LCM/Robin volume. It deliberately takes the local obstruction as a
premise: supplying that obstruction is the separate endpoint problem. -/

theorem threshold_tendsto_atTop_of_local_obstruction
    {a : ℝ} {P : ℝ → ℕ → Prop} {T : ℝ → ℕ}
    (hgood : ∀ {κ : ℝ}, a < κ → ∀ {n : ℕ}, T κ < n → P κ n)
    (hobstruction : ∀ M : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ {κ : ℝ}, a < κ → κ < a + δ →
        ∃ n : ℕ, M < n ∧ ¬ P κ n) :
    Tendsto T (𝓝[>] a) atTop := by
  refine tendsto_atTop.2 (fun M => ?_)
  obtain ⟨δ, hδ, hbad⟩ := hobstruction M
  have hupper : ∀ᶠ κ : ℝ in 𝓝[>] a, κ < a + δ := by
    exact mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (lt_add_of_pos_right a hδ))
  filter_upwards [hupper, self_mem_nhdsWithin] with κ hκupper hκlower
  have hκa : a < κ := hκlower
  obtain ⟨n, hnM, hnfail⟩ := hbad hκa hκupper
  have hTM : M < T κ := by
    by_contra hnot
    have hTle : T κ ≤ M := Nat.le_of_not_gt hnot
    have hPn : P κ n := hgood hκa (lt_of_le_of_lt hTle hnM)
    exact hnfail hPn
  exact hTM.le

end D5.S3.Arith.Robin.Analytic.RobinThresholdDivergence

#print axioms D5.S3.Arith.Robin.Analytic.RobinThresholdDivergence.threshold_tendsto_atTop_of_local_obstruction
