/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vanishing phase error proves unique ergodicity of the actual balanced subshift. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedMeasures
import Mathlib.Analysis.SpecificLimits.Basic

/-! The finite phase error tends to zero for every finite-window event.
Mathlib's measurable cylinders generate the ambient full-shift sigma-algebra;
the measurable subtype embedding transfers their uniqueness to actual points.
Public theorem escape audits remain unfinished under issue #24726. -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced

noncomputable section

local instance (n : ℕ) : NeZero (height n) := ⟨Nat.ne_of_gt (height_pos n)⟩

/-- Two actual invariant probabilities differ on a length-r event by at most
the exact balanced exceptional-phase estimate r/3^n, at every level n. -/
theorem window_event_measure_difference_le
    (μ ν : Measure BalancedPoint) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shiftBalanced 1) μ μ)
    (hν : MeasurePreserving (shiftBalanced 1) ν ν)
    (t : ℤ) (r : ℕ) (C : Set BalancedPoint) (hC : WindowDetermined t r C) (n : ℕ) :
    |μ.real C - ν.real C| ≤ (r : ℝ) / (3 : ℝ) ^ n := by
  obtain ⟨hlμ, huμ⟩ := window_event_measure_squeeze μ hμ n t r C hC
  obtain ⟨hlν, huν⟩ := window_event_measure_squeeze ν hν n t r C hC
  have he : |μ.real C - ν.real C| ≤
      (SparseDisagreement.badPhases
        (SparseDisagreement.wordDisagreements (balancedWord n) (height n)
          (balancedWord_length n)) t r).card / (height n : ℝ) := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  apply he.trans
  apply (div_le_div_iff₀ (by exact_mod_cast height_pos n)
    (pow_pos (by norm_num : (0 : ℝ) < 3) n)).2
  have hc : (3 : ℝ) ^ n *
      (SparseDisagreement.badPhases
        (SparseDisagreement.wordDisagreements (balancedWord n) (height n)
          (balancedWord_length n)) t r).card ≤ (r : ℝ) * height n := by
    exact_mod_cast SparseDisagreement.balanced_badPhases_card_scaled n t r
  nlinarith

/-- The common finite-window event mass follows by taking the phase level to infinity. -/
theorem window_event_measure_eq
    (μ ν : Measure BalancedPoint) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shiftBalanced 1) μ μ)
    (hν : MeasurePreserving (shiftBalanced 1) ν ν)
    (t : ℤ) (r : ℕ) (C : Set BalancedPoint) (hC : WindowDetermined t r C) :
    μ.real C = ν.real C := by
  have ht : Tendsto (fun n : ℕ => (r : ℝ) / (3 : ℝ) ^ n) atTop (𝓝 0) :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).const_div_atTop r
  have hz : |μ.real C - ν.real C| ≤ 0 :=
    ge_of_tendsto ht (Eventually.of_forall
      (window_event_measure_difference_le μ ν hμ hν t r C hC))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

private theorem cylinder_window_determined (I : Finset ℤ)
    (S : Set (I → Bool)) :
    ∃ t : ℤ, ∃ r : ℕ, WindowDetermined t r
      (Subtype.val ⁻¹' (MeasureTheory.cylinder I S)) := by
  let m : ℕ := I.sup Int.natAbs
  refine ⟨-(m : ℤ), 2 * m + 1, ?_⟩
  intro x y hxy
  have heq : I.restrict x.1 = I.restrict y.1 := by
    funext i
    have ha : i.1.natAbs ≤ m := Finset.le_sup i.2
    have hp : i.1 ≤ (i.1.natAbs : ℤ) := Int.le_natAbs
    have hn : -i.1 ≤ (i.1.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -i.1))
    let k : ℕ := (i.1 + (m : ℤ)).toNat
    have hk : k < 2 * m + 1 := by dsimp [k]; omega
    have hi : -(m : ℤ) + (k : ℤ) = i.1 := by dsimp [k]; omega
    change x.1 i.1 = y.1 i.1
    simpa only [hi] using hxy k hk
  change I.restrict x.1 ∈ S ↔ I.restrict y.1 ∈ S
  rw [heq]

/-- All invariant probabilities on the actual balanced subshift coincide. -/
theorem balanced_invariant_probability_unique
    (μ ν : Measure BalancedPoint) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shiftBalanced 1) μ μ)
    (hν : MeasurePreserving (shiftBalanced 1) ν ν) : μ = ν := by
  have hemb : MeasurableEmbedding (Subtype.val : BalancedPoint → ℤ → Bool) :=
    MeasurableEmbedding.subtype_coe balancedSubshift.isClosed.measurableSet
  apply hemb.map_injective
  refine ext_of_generate_finite (measurableCylinders (fun _ : ℤ => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro s hs
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).mp hs
    rw [Measure.map_apply hemb.measurable (hS.cylinder I),
      Measure.map_apply hemb.measurable (hS.cylinder I)]
    apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
    obtain ⟨t, r, hC⟩ := cylinder_window_determined I S
    exact window_event_measure_eq μ ν hμ hν t r _ hC
  · simp [Measure.map_apply hemb.measurable]

/-- The actual nonempty compact balanced subshift is uniquely ergodic. -/
theorem balanced_unique_ergodic :
    ∃! μ : Measure BalancedPoint,
      IsProbabilityMeasure μ ∧ MeasurePreserving (shiftBalanced 1) μ μ := by
  obtain ⟨μ, hμ, hp⟩ := exists_balanced_invariant_probability
  letI := hp
  refine ⟨μ, ⟨hp, hμ⟩, ?_⟩
  intro ν hν
  letI := hν.1
  exact balanced_invariant_probability_unique ν μ hν.2 hμ

end

end D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced
