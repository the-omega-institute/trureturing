/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickInterior
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickInterior
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Removing positivity at a strictly positive overlap optimum. -/

module

import all D5.S3.Quantum.Matrix.RpowPencilTaylor
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Tactic

/-! Positive-interior perturbations in finite matrix overlap problems. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickInterior

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A strictly positive feasible point maximizes the weighted objective over
positive overlaps exactly when it maximizes over all Hermitian overlaps. -/
theorem positive_interior_relaxation (A B W Y₀ : Matrix n n ℂ)
    (hY₀ : Y₀.PosDef) (hA : Y₀ ≤ A) (hB : Y₀ ≤ B) :
    (∀ Y : Matrix n n ℂ, 0 ≤ Y → Y ≤ A → Y ≤ B →
      (W * Y).trace.re ≤ (W * Y₀).trace.re) ↔
    (∀ Y : Matrix n n ℂ, Y.IsHermitian → Y ≤ A → Y ≤ B →
      (W * Y).trace.re ≤ (W * Y₀).trace.re) := by
  constructor
  · intro h Y hY hYA hYB
    by_contra hbad
    have hgt : (W * Y₀).trace.re < (W * Y).trace.re := lt_of_not_ge hbad
    have hp := D5.S3.Quantum.Matrix.RpowPencilTaylor.pencil_posDef_near hY₀ (hY.sub hY₀.isHermitian)
    obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hp
    let θ := min ε 1 / 2
    have hθ : 0 < θ := half_pos (lt_min hε zero_lt_one)
    have hθε : θ < ε := by
      have hm : min ε 1 ≤ ε := min_le_left _ _
      dsimp [θ]
      linarith
    have hθ1 : θ ≤ 1 := by
      have hm : min ε 1 ≤ 1 := min_le_right _ _
      dsimp [θ]
      linarith
    have hpθ : (Y₀ + θ • (Y - Y₀)).PosDef := by
      apply he
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ] using hθε
    have hseg : Y₀ + θ • (Y - Y₀) = (1 - θ) • Y₀ + θ • Y := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    have upper (C : Matrix n n ℂ) (h₀ : Y₀ ≤ C) (h₁ : Y ≤ C) :
        Y₀ + θ • (Y - Y₀) ≤ C := by
      rw [hseg]
      calc
        _ ≤ (1 - θ) • C + θ • C := add_le_add
          (smul_le_smul_of_nonneg_left h₀ (sub_nonneg.mpr hθ1))
          (smul_le_smul_of_nonneg_left h₁ hθ.le)
        _ = C := by rw [← add_smul]; simp
    have hh := h _ hpθ.posSemidef.nonneg (upper A hA hYA) (upper B hB hYB)
    have htrace : (W * (Y₀ + θ • (Y - Y₀))).trace.re =
        (W * Y₀).trace.re + θ * ((W * Y).trace.re - (W * Y₀).trace.re) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_add,
        Matrix.trace_smul, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
        Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    rw [htrace] at hh
    nlinarith
  · intro h Y hY hYA hYB
    exact h Y hY.posSemidef.isHermitian hYA hYB

end D5.S3.Quantum.Divergence.MaximalHockeyStickInterior
