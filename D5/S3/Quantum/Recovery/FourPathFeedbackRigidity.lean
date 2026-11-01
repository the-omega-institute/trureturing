/- GID: D5/S3/Quantum/Recovery/FourPathFeedbackRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathFeedbackRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace saturation forces common-phase polar feedback. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! The finite-dimensional core of Section 9, Theorem 9.4, equations (9.22)--(9.23).
Canonical source atom: 9f4e8ab8a85221187bed0676209bd5de7796bcad65dacfa00d3b7b0bfa8f7df5.
The theorem `trace_saturation_forces_polar_feedback` treats arbitrary positive finite
dimension; the four-path case is n = 3. It does not assert the support or channel
equivalences of the complete atom.
-/

noncomputable section
namespace D5.S3.Quantum.Recovery.FourPathFeedbackRigidity

set_option autoImplicit false

/-- For a vector with no zero coordinate, a unitary attaining the trace upper
bound has precisely one common phase times the coordinatewise polar correction. -/
theorem trace_saturation_forces_polar_feedback (n : ℕ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (v : Fin (n + 1) → ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (hv : ∀ i, v i ≠ 0)
    (hs : ‖Matrix.trace (U * Matrix.diagonal v)‖ = ∑ i, ‖v i‖) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ i j,
      U i j = if i = j then z * star (v i) / (‖v i‖ : ℂ) else 0 := by
  classical
  have norm_square (a : ℂ) : ‖a‖ ^ 2 = a.re * a.re + a.im * a.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have column (j : Fin (n + 1)) : ∑ i, ‖U i j‖ ^ 2 = 1 := by
    simp_rw [norm_square]
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
      (M j j).re) hU.1
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.star_def,
      pow_two] using h
  have entry (i j : Fin (n + 1)) : ‖U i j‖ ≤ 1 := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
      sq_nonneg ‖U k j‖) (Finset.mem_univ i)
    rw [column j] at h
    nlinarith [norm_nonneg (U i j)]
  let L : ℝ := ∑ i, ‖v i‖
  let S : ℂ := Matrix.trace (U * Matrix.diagonal v)
  have Lpos : 0 < L := by
    exact Finset.sum_pos (fun i _ => norm_pos_iff.mpr (hv i)) Finset.univ_nonempty
  have Lne : L ≠ 0 := ne_of_gt Lpos
  have Lcne : (L : ℂ) ≠ 0 := by exact_mod_cast Lne
  have Snorm : ‖S‖ = L := hs
  have Ssum : S = ∑ i, U i i * v i := by
    simp [S, Matrix.trace, Matrix.diag_apply]
  let z : ℂ := S / (L : ℂ)
  have znorm : ‖z‖ = 1 := by
    simp [z, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Lpos, Snorm, Lne]
  have zS : star z * S = (L : ℂ) := by
    rw [show z = S / (L : ℂ) from rfl, star_div₀, Complex.star_def,
      Complex.conj_ofReal, div_mul_eq_mul_div,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Snorm]
    push_cast
    field_simp
  have bound (i : Fin (n + 1)) : ‖star z * (U i i * v i)‖ ≤ ‖v i‖ := by
    simp only [norm_mul, norm_star, znorm, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (entry i i)
  have real_bound (i : Fin (n + 1)) : (star z * (U i i * v i)).re ≤ ‖v i‖ :=
    (Complex.re_le_norm _).trans (bound i)
  have sum_real : ∑ i, (star z * (U i i * v i)).re = ∑ i, ‖v i‖ := by
    rw [← Complex.re_sum, ← Finset.mul_sum, ← Ssum, zS, Complex.ofReal_re]
  have real_eq (i : Fin (n + 1)) : (star z * (U i i * v i)).re = ‖v i‖ := by
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => real_bound k)).mp sum_real i
      (Finset.mem_univ i)
  have aligned (i : Fin (n + 1)) : star z * (U i i * v i) = (‖v i‖ : ℂ) := by
    have hr := real_eq i
    have hb := bound i
    have hsq : ‖star z * (U i i * v i)‖ ^ 2 =
        (star z * (U i i * v i)).re ^ 2 + (star z * (U i i * v i)).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    apply Complex.ext
    · simpa using hr
    · simp only [Complex.ofReal_im]
      nlinarith [norm_nonneg (star z * (U i i * v i)), norm_nonneg (v i),
        sq_nonneg (star z * (U i i * v i)).im]
  have diag_norm (i : Fin (n + 1)) : ‖U i i‖ = 1 := by
    have h := congrArg norm (aligned i)
    simp only [norm_mul, norm_star, znorm, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    exact (mul_right_cancel₀ (norm_ne_zero_iff.mpr (hv i))) (by simpa using h)
  have offdiag (i j : Fin (n + 1)) (hij : i ≠ j) : U i j = 0 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i, j} : Finset (Fin (n + 1))) ⊆ Finset.univ from Finset.subset_univ _)
      (fun k _ _ => sq_nonneg ‖U k j‖)
    rw [Finset.sum_pair hij, column j, diag_norm j] at h
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (U i j)]
  refine ⟨z, znorm, fun i j => ?_⟩
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have hh := congrArg (fun a : ℂ => z * a) (aligned i)
    have zstar : z * star z = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, znorm]
      norm_num
    have phase : U i i * v i = z * (‖v i‖ : ℂ) := by
      simpa only [← mul_assoc, zstar, one_mul] using hh
    have vi : (‖v i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hv i)
    have vv : v i * star (v i) = (‖v i‖ : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    apply (eq_div_iff vi).mpr
    apply (mul_right_cancel₀ (hv i))
    calc
      (U i i * (‖v i‖ : ℂ)) * v i = (U i i * v i) * (‖v i‖ : ℂ) := by ring
      _ = (z * (‖v i‖ : ℂ)) * (‖v i‖ : ℂ) := by rw [phase]
      _ = z * (v i * star (v i)) := by rw [vv]; ring
      _ = (z * star (v i)) * v i := by ring
  · rw [ite_eq_right hij, offdiag i j hij]

end D5.S3.Quantum.Recovery.FourPathFeedbackRigidity
