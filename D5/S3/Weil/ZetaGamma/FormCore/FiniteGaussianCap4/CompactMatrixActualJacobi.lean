/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixActualJacobi
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual positive Mellin scales transport the endpoint-paid Jacobi head. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixActualCoordinates
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfFiniteJacobi

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace FiniteGaussianCap475
open FiniteGaussianCap4
open FiniteGaussianCap4.LaguerreSevenHalf

/-- Detailed balance follows from the existing weight recurrence. -/
theorem weight_jacobi_balance (k : ℕ) :
    weight (k + 1) * jacobiL (k + 1) = weight k * jacobiR k := by
  rw [central_weight_step]
  simp only [jacobiL, jacobiR, Nat.cast_add, Nat.cast_one]
  field_simp [show (k : ℝ) + 1 ≠ 0 by positivity,
    show (k : ℝ) + 11 / 4 ≠ 0 by positivity]
  <;> ring

/-- Positive actual Mellin integrals fix the sign of the Jacobi transport.
Only their already proved squares and the ordinary nonnegative sqrt square
are used; neither Gamma nor a fitted radical normalization is expanded. -/
theorem actualMellinScale_jacobiB (k : ℕ) :
    actualMellinScale k * actualMellinScale (k + 1) * jacobiB k =
      weight k * jacobiR k := by
  have hB : jacobiB k ^ 2 = jacobiR k * jacobiL (k + 1) := by
    rw [jacobiB_eq, mul_pow, Real.sq_sqrt (jacobiR_nonneg k),
      Real.sq_sqrt (jacobiL_nonneg (k + 1))]
  apply (sq_eq_sq₀
    (mul_nonneg (mul_nonneg (actualMellinScale_pos k).le
      (actualMellinScale_pos (k + 1)).le) (jacobiB_nonneg k))
    (mul_nonneg (central_weight_pos k).le (jacobiR_nonneg k))).1
  calc
    (actualMellinScale k * actualMellinScale (k + 1) * jacobiB k) ^ 2 =
        weight k * weight (k + 1) * (jacobiR k * jacobiL (k + 1)) := by
      rw [mul_pow, mul_pow, actualMellinScale_sq, actualMellinScale_sq, hB]
    _ = weight k * (weight (k + 1) * jacobiL (k + 1)) * jacobiR k := by ring
    _ = weight k * (weight k * jacobiR k) * jacobiR k := by rw [weight_jacobi_balance]
    _ = (weight k * jacobiR k) ^ 2 := by ring

private theorem certificate_diagonal_cast (i : Fin 16) :
    (Cap4FiniteCertificate.recurrenceDiagonalQ i : ℝ) = jacobiD i.val := by
  unfold Cap4FiniteCertificate.recurrenceDiagonalQ jacobiD
  push_cast <;> ring

private theorem certificate_edge_cast (i : Fin 16) :
    (Cap4FiniteCertificate.edgeQ i : ℝ) = jacobiR i.val := by
  unfold Cap4FiniteCertificate.edgeQ jacobiR
  push_cast <;> ring

/-- The certificate recurrence is the same weighted real Jacobi form,
including subtraction of the 15/16 edge on the last head diagonal. -/
theorem certificate_recurrence_actual_entry (i j : Fin 16) :
    Cap4FiniteCertificate.recurrence i j =
      if i = j then
        (jacobiD i.val - (if i = 15 then jacobiR i.val else 0)) * weight i.val
      else if i.val + 1 = j.val then weight i.val * jacobiR i.val
      else if j.val + 1 = i.val then weight j.val * jacobiR j.val
      else 0 := by
  have hw (k : Fin 16) : (Cap4FiniteCertificate.weightsQ k : ℝ) = weight k.val := by
    simpa only [Cap4FiniteCertificate.weights] using certificate_weights_eq_weight k
  change (Cap4FiniteCertificate.recurrenceQ i j : ℝ) = _
  simp only [Cap4FiniteCertificate.recurrenceQ, Matrix.of_apply]
  split_ifs <;>
    simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_zero,
      certificate_diagonal_cast, certificate_edge_cast, hw]

/-- A finite algebraic expansion of the stored tridiagonal form. -/
theorem certificate_recurrence_quadratic (u : ℕ → ℝ) :
    (∑ i : Fin 16, ∑ j : Fin 16,
      u i.val * u j.val * Cap4FiniteCertificate.recurrence i j) =
      (∑ k ∈ Finset.range 16, jacobiD k * (weight k * u k ^ 2)) +
        2 * (∑ k ∈ Finset.range 15, (weight k * jacobiR k) * u k * u (k + 1)) -
        jacobiR 15 * (weight 15 * u 15 ^ 2) := by
  simp_rw [certificate_recurrence_actual_entry]
  simp [Fin.sum_univ_succ, Finset.sum_range_succ]
  <;> ring

/-- Congruence by the positive actual Mellin scales is the original paid
head, with its exact last diagonal D15-R15. -/
theorem jacobiPaidHead_actual_coordinates (d : ℕ → ℝ) :
    jacobiPaidHead d =
      ∑ i : Fin 16, ∑ j : Fin 16,
        (d i.val / actualMellinScale i.val) *
          (d j.val / actualMellinScale j.val) * Cap4FiniteCertificate.recurrence i j := by
  have hnorm (k : ℕ) : weight k * (d k / actualMellinScale k) ^ 2 = d k ^ 2 := by
    rw [← actualMellinScale_sq]
    field_simp [(actualMellinScale_pos k).ne']
    <;> ring
  have hedge (k : ℕ) :
      (weight k * jacobiR k) * (d k / actualMellinScale k) *
        (d (k + 1) / actualMellinScale (k + 1)) = jacobiB k * d k * d (k + 1) := by
    rw [← actualMellinScale_jacobiB]
    field_simp [(actualMellinScale_pos k).ne', (actualMellinScale_pos (k + 1)).ne']
    <;> ring
  symm
  rw [certificate_recurrence_quadratic (fun k : ℕ => d k / actualMellinScale k)]
  simp_rw [hnorm, hedge]
  rfl

/-- The recurrence part of the finite certificate acts on the same actual
finite Gaussian coefficients used by its norm, charge, and compact matrix. -/
theorem actual_jacobiPaidHead_coordinates {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    jacobiPaidHead (fun k => finiteGaussianNormalizedCoefficient c site (2 * k)) =
      ∑ i : Fin 16, ∑ j : Fin 16, actualCentralHeadCoordinates c site i *
        actualCentralHeadCoordinates c site j * Cap4FiniteCertificate.recurrence i j := by
  simpa only [actualCentralHeadCoordinates, actualMellinScale] using
    jacobiPaidHead_actual_coordinates
      (fun k => finiteGaussianNormalizedCoefficient c site (2 * k))

end FiniteGaussianCap475
