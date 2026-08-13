/- GID: D5/S3/Zeros/ToySpectrum/OffLineToySpectrum
   generality: I
   mirror-B: D5/B/S3/Zeros/ToySpectrum/OffLineToySpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four off-line points have two symmetries and negative Li coefficient 31. -/

import D5.S3.Zeros.ZeroGeometry
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.BigOperators

namespace D5.S3.Zeros.ToySpectrum.OffLineToySpectrum

open D5.S3.Weil.Convention
open D5.S3.Weil.ReflectionLedger
open Polynomial
open scoped ComplexConjugate

noncomputable def rightUpper : ℂ := ((7 / 10 : ℝ) : ℂ) + 5 * Complex.I
noncomputable def rightLower : ℂ := ((7 / 10 : ℝ) : ℂ) - 5 * Complex.I
noncomputable def leftUpper : ℂ := ((3 / 10 : ℝ) : ℂ) + 5 * Complex.I
noncomputable def leftLower : ℂ := ((3 / 10 : ℝ) : ℂ) - 5 * Complex.I

noncomputable def toySpectrum : Finset ℂ := by
  classical
  exact {rightUpper, rightLower, leftUpper, leftLower}

noncomputable def toyQuartic : ℂ[X] :=
  (X - C rightUpper) * (X - C rightLower) *
    (X - C leftUpper) * (X - C leftLower)

private theorem mirror_rightUpper : mirror rightUpper = leftUpper := by
  apply Complex.ext <;>
    norm_num [mirror, reflection, rightUpper, leftUpper, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

private theorem mirror_rightLower : mirror rightLower = leftLower := by
  apply Complex.ext <;>
    norm_num [mirror, reflection, rightLower, leftLower, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

private theorem mirror_leftUpper : mirror leftUpper = rightUpper := by
  apply Complex.ext <;>
    norm_num [mirror, reflection, leftUpper, rightUpper, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

private theorem mirror_leftLower : mirror leftLower = rightLower := by
  apply Complex.ext <;>
    norm_num [mirror, reflection, leftLower, rightLower, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

private theorem conj_rightUpper : conj rightUpper = rightLower := by
  apply Complex.ext
  · rw [Complex.conj_re]
    norm_num [rightUpper, rightLower]
  · rw [Complex.conj_im]
    norm_num [rightUpper, rightLower]

private theorem conj_rightLower : conj rightLower = rightUpper := by
  apply Complex.ext
  · rw [Complex.conj_re]
    norm_num [rightUpper, rightLower]
  · rw [Complex.conj_im]
    norm_num [rightUpper, rightLower]

private theorem conj_leftUpper : conj leftUpper = leftLower := by
  apply Complex.ext
  · rw [Complex.conj_re]
    norm_num [leftUpper, leftLower]
  · rw [Complex.conj_im]
    norm_num [leftUpper, leftLower]

private theorem conj_leftLower : conj leftLower = leftUpper := by
  apply Complex.ext
  · rw [Complex.conj_re]
    norm_num [leftUpper, leftLower]
  · rw [Complex.conj_im]
    norm_num [leftUpper, leftLower]

private theorem toy_points_pairwise_distinct :
    rightUpper ≠ rightLower ∧ rightUpper ≠ leftUpper ∧ rightUpper ≠ leftLower ∧
      rightLower ≠ leftUpper ∧ rightLower ≠ leftLower ∧ leftUpper ≠ leftLower := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    norm_num [rightUpper, rightLower] at him
  constructor
  · intro h
    have hre := congrArg Complex.re h
    norm_num [rightUpper, leftUpper] at hre
  constructor
  · intro h
    have hre := congrArg Complex.re h
    norm_num [rightUpper, leftLower] at hre
  constructor
  · intro h
    have hre := congrArg Complex.re h
    norm_num [rightLower, leftUpper] at hre
  constructor
  · intro h
    have hre := congrArg Complex.re h
    norm_num [rightLower, leftLower] at hre
  · intro h
    have him := congrArg Complex.im h
    norm_num [leftUpper, leftLower] at him

/-- The displayed spectrum genuinely contains four distinct points. -/
theorem toy_spectrum_cardinality : toySpectrum.card = 4 := by
  rcases toy_points_pairwise_distinct with
    ⟨hruRl, hruLu, hruLl, hrlLu, hrlLl, hluLl⟩
  norm_num [toySpectrum, hruRl, hruLu, hruLl, hrlLu, hrlLl, hluLl]

/-- The explicit spectrum is mirror-invariant although every point is off the critical line. -/
theorem explicit_off_line_j_invariant_four_point_counterexample :
    (∀ s ∈ toySpectrum, mirror s ∈ toySpectrum) ∧
      (∀ s ∈ toySpectrum, s.re ≠ criticalAbscissa) := by
  constructor <;> intro s hs
  · simp only [toySpectrum, Finset.mem_insert, Finset.mem_singleton] at hs ⊢
    rcases hs with rfl | rfl | rfl | rfl
    · simp [mirror_rightUpper]
    · simp [mirror_rightLower]
    · simp [mirror_leftUpper]
    · simp [mirror_leftLower]
  · simp only [toySpectrum, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      norm_num [rightUpper, rightLower, leftUpper, leftLower, criticalAbscissa]

/-- The four displayed points are roots of a monic quartic satisfying reflection and conjugation. -/
theorem toy_spectrum_satisfies_formal_polynomial_symmetries :
    toyQuartic.Monic ∧
      (∀ rho ∈ toySpectrum, toyQuartic.eval rho = 0) ∧
      (∀ s : ℂ, toyQuartic.eval (1 - s) = toyQuartic.eval s) ∧
      (∀ s : ℂ, toyQuartic.eval (conj s) = conj (toyQuartic.eval s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((monic_X_sub_C rightUpper).mul (monic_X_sub_C rightLower)).mul
      (monic_X_sub_C leftUpper)).mul (monic_X_sub_C leftLower)
  · intro rho hrho
    simp only [toySpectrum, Finset.mem_insert, Finset.mem_singleton] at hrho
    rcases hrho with rfl | rfl | rfl | rfl <;> simp [toyQuartic]
  · intro s
    simp [toyQuartic, rightUpper, rightLower, leftUpper, leftLower]
    ring
  · intro s
    simp only [toyQuartic, eval_mul, eval_sub, eval_X, eval_C, map_mul, map_sub]
    rw [conj_rightUpper, conj_rightLower, conj_leftUpper, conj_leftLower]
    ring

/-- The thirty-first Li sum of the explicit toy spectrum has negative real part. -/
theorem li_positivity_distinguishes_the_off_line_toy_spectrum :
    Complex.re (∑ rho ∈ toySpectrum, (1 - (1 - 1 / rho) ^ 31)) < 0 := by
  rcases toy_points_pairwise_distinct with
    ⟨hruRl, hruLu, hruLl, hrlLu, hrlLl, hluLl⟩
  have hru : rightUpper ∉ ({rightLower, leftUpper, leftLower} : Finset ℂ) := by
    simp [hruRl, hruLu, hruLl]
  have hrl : rightLower ∉ ({leftUpper, leftLower} : Finset ℂ) := by
    simp [hrlLu, hrlLl]
  have hlu : leftUpper ∉ ({leftLower} : Finset ℂ) := by
    simp [hluLl]
  rw [show toySpectrum = {rightUpper, rightLower, leftUpper, leftLower} by
    rfl, Finset.sum_insert hru, Finset.sum_insert hrl, Finset.sum_insert hlu,
    Finset.sum_singleton]
  norm_num [rightUpper, rightLower, leftUpper, leftLower, Complex.div_re,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_succ]

end D5.S3.Zeros.ToySpectrum.OffLineToySpectrum
