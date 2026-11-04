/- GID: D5/S3/Constants/Moments/CountableHankelNegativeWitness
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/CountableHankelNegativeWitness
   mirror-E: none(waiver:countable-spectrum-classical-analysis)
   anchors: []
   utility: none
   digest: Complete countable conjugate-spectrum integer negative polynomial witnesses. -/

import D5.S3.Constants.NewtonHankelRealRootCriterion
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial Filter
open scoped BigOperators ComplexConjugate Topology

namespace D5.S3.Constants.Moments.CountableHankelNegativeWitness

private theorem eval_bound (p : ℝ[X]) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖p.eval₂ Complex.ofRealHom z‖ ≤ ∑ k ∈ p.support, |p.coeff k| := by
  rw [Polynomial.eval₂_eq_sum]
  calc
    ‖∑ k ∈ p.support, (p.coeff k : ℂ) * z ^ k‖ ≤
        ∑ k ∈ p.support, ‖(p.coeff k : ℂ) * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ p.support, |p.coeff k| := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

private theorem square_summable {ι : Type*} (z w : ι → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hw : Summable (fun i => ‖w i‖)) (p : ℝ[X]) :
    Summable (fun i => w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2) := by
  let C := ∑ k ∈ p.support, |p.coeff k|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply Summable.of_norm_bounded (hw.mul_right (C ^ 2))
  intro i
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (eval_bound p (hz i)) 2)
    (norm_nonneg _)

/-- Strict negativity of a finite real quadratic form survives rational
approximation and clearing a common nonzero integer denominator. -/
theorem exists_integer_negative_quadratic {d : ℕ} (M : Fin d → Fin d → ℝ)
    (u : Fin d → ℝ) (hu : (∑ a, ∑ b, u a * u b * M a b) < 0) :
    ∃ v : Fin d → ℤ, (∑ a, ∑ b, (v a : ℝ) * (v b : ℝ) * M a b) < 0 := by
  classical
  let Q : (Fin d → ℝ) → ℝ := fun x => ∑ a, ∑ b, x a * x b * M a b
  have hQ : Continuous Q := by
    fun_prop
  have hd : DenseRange (fun r : Fin d → ℚ => fun a => (r a : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨x, ⟨r, rfl⟩, hr⟩ := hd.dense.exists_mem_open
    (isOpen_lt hQ continuous_const) ⟨u, hu⟩
  let A : Matrix (Fin d) Unit ℚ := fun a _ => r a
  have hD : (A.den : ℝ) ≠ 0 := by exact_mod_cast A.den_ne_zero
  have hscale (a : Fin d) : (A.num a () : ℝ) = (A.den : ℝ) * (r a : ℝ) := by
    have h := A.num_div_den a ()
    have h' : (A.num a () : ℝ) / (A.den : ℝ) = (r a : ℝ) := by
      exact_mod_cast h
    exact (div_eq_iff hD).mp h' |>.trans (mul_comm _ _)
  refine ⟨fun a => A.num a (), ?_⟩
  simp_rw [hscale]
  have heq : (∑ a, ∑ b, ((A.den : ℝ) * (r a : ℝ)) *
      ((A.den : ℝ) * (r b : ℝ)) * M a b) = (A.den : ℝ) ^ 2 * Q (fun a => (r a : ℝ)) := by
    dsimp [Q]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hD) hr

end D5.S3.Constants.Moments.CountableHankelNegativeWitness
