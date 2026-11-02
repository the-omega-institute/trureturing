/- GID: D5/S3/Quantum/Analysis/SingularGramCommonBranchOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/SingularGramCommonBranchOptimum
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: Finite coherent synthesis has an attained singular Gram constrained minimum. -/

import D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Combination

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Analysis.SingularGramCommonBranchOptimum

open scoped InnerProductSpace BigOperators
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

private theorem constrained_minimizer (V : E →L[ℂ] H) (b : E) (hb : b ≠ 0) :
    let G := gram V
    let p := moorePenroseInverse G b
    let a := (inner ℂ b p).re
    ∃ c : E, inner ℂ b c = 1 ∧
      (∀ d : E, inner ℂ b d = 1 → ‖V c‖ ^ 2 ≤ ‖V d‖ ^ 2) ∧
      (b ∈ G.range → 0 < a ∧ c = (a⁻¹ : ℂ) • p ∧ ‖V c‖ ^ 2 = a⁻¹) ∧
      (b ∉ G.range → c ∈ G.ker ∧ V c = 0) := by
  dsimp only
  let G := gram V
  let p := moorePenroseInverse G b
  have hrange : G.range = V.kerᗮ := by
    change (V.toLinearMap.adjoint ∘ₗ V.toLinearMap).range = _
    rw [V.toLinearMap.range_adjoint_comp_self, ← V.toLinearMap.orthogonal_ker]
    rfl
  by_cases h : b ∈ G.range
  · obtain ⟨u, hu⟩ := h
    have hnormal : G p = b := by
      rw [← hu]
      exact congrArg (fun A : E →ₗ[ℂ] E => A u) (comp_moorePenroseInverse_comp G)
    have henergy : inner ℂ b p = (‖V p‖ ^ 2 : ℝ) := by
      rw [← hnormal]
      change inner ℂ (V.adjoint (V p)) p = _
      rw [V.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
      simp
    have hv : V p ≠ 0 := by
      intro hz
      apply hb
      rw [← hnormal]
      change V.adjoint (V p) = 0
      rw [hz, map_zero]
    have ha : 0 < (inner ℂ b p).re := by
      rw [henergy, Complex.ofReal_re]
      exact sq_pos_of_pos (norm_pos_iff.mpr hv)
    set a : ℝ := (inner ℂ b p).re with hadef
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hinner : inner ℂ b p = (a : ℂ) := by
      rw [hadef, henergy]
      simp
    let c : E := (a⁻¹ : ℂ) • p
    have hc : inner ℂ b c = 1 := by
      simp only [c, inner_smul_right, hinner]
      exact inv_mul_cancel₀ haC
    have hcenergy : ‖V c‖ ^ 2 = a⁻¹ := by
      have hvp : ‖V p‖ ^ 2 = a := by
        simpa [hadef] using (congrArg Complex.re henergy).symm
      rw [show V c = (a⁻¹ : ℂ) • V p by simp [c], norm_smul, mul_pow, hvp]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, sq_abs]
      field_simp
    refine ⟨c, hc, ?_, ?_, ?_⟩
    · intro d hd
      have ho : inner ℂ (V c) (V d - V c) = 0 := by
        rw [← V.adjoint_inner_left, map_smul]
        change inner ℂ ((a⁻¹ : ℂ) • G p) (d - c) = 0
        rw [hnormal, inner_smul_left, inner_sub_right, hd, hc, sub_self, mul_zero]
      have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (V c) (V d - V c) ho
      have hsplit : V c + (V d - V c) = V d := by abel
      rw [hsplit] at he
      nlinarith [sq_nonneg ‖V d - V c‖]
    · intro _
      exact ⟨ha, rfl, hcenergy⟩
    · exact fun hn => (hn h).elim
  · have hn : b ∉ V.kerᗮ := by rwa [← hrange]
    rw [Submodule.mem_orthogonal'] at hn
    push_neg at hn
    obtain ⟨k, hk, hbk⟩ := hn
    let c : E := (inner ℂ b k)⁻¹ • k
    have hc : inner ℂ b c = 1 := by
      simp only [c, inner_smul_right]
      exact inv_mul_cancel₀ hbk
    have hv : V c = 0 := by simp [c, show V k = 0 from hk]
    refine ⟨c, hc, ?_, ?_, ?_⟩
    · intro d _
      rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · exact fun hh => (h hh).elim
    · intro _
      refine ⟨?_, hv⟩
      change V.adjoint (V c) = 0
      rw [hv, map_zero]

end D5.S3.Quantum.Analysis.SingularGramCommonBranchOptimum
