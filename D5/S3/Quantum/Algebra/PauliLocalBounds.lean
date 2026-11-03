/- GID: D5/S3/Quantum/Algebra/PauliLocalBounds
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PauliLocalBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Exact Euclidean bounds and the action Gram operator of the Pauli perturbation. -/

import D5.S3.Quantum.Algebra.PauliFixedProductFamily
import Mathlib.Tactic.Positivity

noncomputable section
open WithLp
open scoped InnerProductSpace
namespace D5.S3.Quantum.Algebra.PauliFixedProductFamily

private theorem sqrt_two_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- The common attaining direction for the spin product and diagonal defect. -/
def balanced : J := (Real.sqrt 2)⁻¹ • (e 0 + e 1)

private theorem balanced_norm : ‖balanced‖ = 1 := by
  have hn : ‖balanced‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [balanced, e, PiLp.single_apply, Fin.sum_univ_succ]
    field_simp
    nlinarith [sqrt_two_sq]
  nlinarith [norm_nonneg balanced]

private theorem spin_bound (a b : J) : ‖S a b‖ ≤ Real.sqrt 2 * ‖a‖ * ‖b‖ := by
  have hid : ‖S a b‖^2 +
      (a 0*b 0-a 1*b 1-a 2*b 2-a 3*b 3)^2 +
      (a 0*b 1-b 0*a 1)^2 + (a 0*b 2-b 0*a 2)^2 + (a 0*b 3-b 0*a 3)^2 +
      2*((a 1*b 2-a 2*b 1)^2+(a 2*b 3-a 3*b 2)^2+(a 3*b 1-a 1*b 3)^2) =
      2 * ‖a‖^2 * ‖b‖^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, S, spin, Fin.sum_univ_succ]
    <;> ring
  have h : ‖S a b‖^2 ≤ 2*‖a‖^2*‖b‖^2 := by
    nlinarith [sq_nonneg (a 0*b 0-a 1*b 1-a 2*b 2-a 3*b 3),
      sq_nonneg (a 0*b 1-b 0*a 1), sq_nonneg (a 0*b 2-b 0*a 2),
      sq_nonneg (a 0*b 3-b 0*a 3), sq_nonneg (a 1*b 2-a 2*b 1),
      sq_nonneg (a 2*b 3-a 3*b 2), sq_nonneg (a 3*b 1-a 1*b 3)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa [mul_pow, sqrt_two_sq] using h

private theorem d_bound (t : ℝ) (a b : J) :
    ‖D t a b‖ ≤ Real.sqrt (1+t^2) * ‖a‖ * ‖b‖ := by
  let q := a 1^2+a 2^2+(a 3+t*a 0)^2
  have hid : ‖D t a b‖^2 +
      ((a 0-t*a 3)^2+t^2*(a 1^2+a 2^2))*‖b‖^2 +
      q*b 0^2 + (a 1*b 1+a 2*b 2+(a 3+t*a 0)*b 3)^2 =
      (1+t^2)*‖a‖^2*‖b‖^2 := by
    simp [q, EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift,
      Fin.sum_univ_succ]
    <;> ring
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp : 0 ≤ ((a 0-t*a 3)^2+t^2*(a 1^2+a 2^2))*‖b‖^2 := by positivity
  have h : ‖D t a b‖^2 ≤ (1+t^2)*‖a‖^2*‖b‖^2 := by
    nlinarith [mul_nonneg hq (sq_nonneg (b 0)),
      sq_nonneg (a 1*b 1+a 2*b 2+(a 3+t*a 0)*b 3)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa [mul_pow, Real.sq_sqrt (show 0 ≤ 1+t^2 by positivity)] using h

private theorem self_bound (t : ℝ) (a : J) : ‖D t a a‖ ≤ |t|/2*‖a‖^2 := by
  have hid : 4*‖D t a a‖^2 +
      t^2*(a 0^2-a 1^2-a 2^2-a 3^2)^2+4*t^2*a 0^2*a 3^2 =
      t^2*(‖a‖^2)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift,
      Fin.sum_univ_succ]
    <;> ring
  have h : 4*‖D t a a‖^2 ≤ t^2*(‖a‖^2)^2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (a 0^2-a 1^2-a 2^2-a 3^2)),
      mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg (a 0))) (sq_nonneg (a 3))]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have ht : |t|^2 = t^2 := sq_abs t
  nlinarith

private theorem unit_bound (t : ℝ) (b : J) : ‖D t (e 0) b‖ ≤ |t|*‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp [EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift, e,
    PiLp.single_apply, Fin.sum_univ_succ, mul_pow, sq_abs]
  nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (b 0)),
    mul_nonneg (sq_nonneg t) (sq_nonneg (b 3))]

private theorem self_attained (t : ℝ) : ‖D t balanced balanced‖ = |t|/2 := by
  have hsq : ‖D t balanced balanced‖^2 = t^2/4 := by
    simp [EuclideanSpace.real_norm_sq_eq, balanced, D, C, cross, cross_apply,
      shift, e, PiLp.single_apply, Fin.sum_univ_succ]
    field_simp
    nlinarith [sqrt_two_sq]
  have ht : |t|^2 = t^2 := sq_abs t
  nlinarith [norm_nonneg (D t balanced balanced), abs_nonneg t]

private theorem unit_attained (t : ℝ) : ‖D t (e 0) (e 1)‖ = |t| := by
  have heq : D t (e 0) (e 1) = t • e 2 := by
    ext i; fin_cases i <;> simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply]
  rw [heq, norm_smul]
  simp [e]

/-- The original local defect and unit-generator bounds are attained in the same family. -/
theorem exact_defects (t : ℝ) :
    IsGreatest {r : ℝ | ∃ a : J, ‖a‖=1 ∧ r=‖D t a a‖} (|t|/2) ∧
    IsGreatest {r : ℝ | ∃ b : J, ‖b‖=1 ∧ r=‖D t (e 0) b‖} |t| ∧
    (∀ a b : J, ‖S a b‖ ≤ Real.sqrt 2*‖a‖*‖b‖) ∧
    (∀ a b : J, ‖D t a b‖ ≤ Real.sqrt (1+t^2)*‖a‖*‖b‖) := by
  refine ⟨⟨⟨balanced, balanced_norm, (self_attained t).symm⟩, ?_⟩,
    ⟨⟨e 1, by simp [e], (unit_attained t).symm⟩, ?_⟩, spin_bound, d_bound t⟩
  · rintro r ⟨a, ha, rfl⟩
    simpa [ha] using self_bound t a
  · rintro r ⟨b, hb, rfl⟩
    simpa [hb] using unit_bound t b

end D5.S3.Quantum.Algebra.PauliFixedProductFamily
