/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixActualCoordinates
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual Mellin coordinates identify the certificate weights, head norm, and charge. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixActualHead
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4FiniteCertificate

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace FiniteGaussianCap475
open FiniteGaussianCap4
open FiniteGaussianCap4.LaguerreSevenHalf

/-- The positive scale is the actual normalized central Mellin integral. -/
def actualMellinScale (k : ℕ) : ℝ :=
  normalizedCentralMellin (2 * k) / normalizedCentralMellin 0

theorem actualMellinScale_pos (k : ℕ) : 0 < actualMellinScale k :=
  div_pos (normalizedCentralMellin_even_pos k) (normalizedCentralMellin_even_pos 0)

theorem actualMellinScale_sq (k : ℕ) : actualMellinScale k ^ 2 = weight k :=
  (normalizedCentralMellin_weight k).2

/-- The literal rational certificate stores the same existing weight sequence. -/
theorem certificate_weights_eq_weight (i : Fin 16) :
    Cap4FiniteCertificate.weights i = weight i.val := by
  fin_cases i <;>
    norm_num [Cap4FiniteCertificate.weights, Cap4FiniteCertificate.weightsQ, weight, ratio]

theorem certificate_weights_eq_actualMellin_sq (i : Fin 16) :
    Cap4FiniteCertificate.weights i = actualMellinScale i.val ^ 2 := by
  rw [certificate_weights_eq_weight, actualMellinScale_sq]

/-- Exact head norm in the charge coordinates u=d/z, for arbitrary real d. -/
theorem certificate_head_norm_coordinates (d : ℕ → ℝ) :
    (∑ k ∈ Finset.range 16, d k ^ 2) =
      ∑ i : Fin 16, Cap4FiniteCertificate.weights i *
        (d i.val / actualMellinScale i.val) ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => d k ^ 2) 16]
  apply Finset.sum_congr rfl
  intro i _
  rw [certificate_weights_eq_actualMellin_sq]
  field_simp [(actualMellinScale_pos i.val).ne']
  <;> ring

/-- Exact head central charge in the same coordinates. -/
theorem certificate_head_charge_coordinates (d : ℕ → ℝ) :
    (∑ k ∈ Finset.range 16, actualMellinScale k * d k) =
      ∑ i : Fin 16, Cap4FiniteCertificate.weights i *
        (d i.val / actualMellinScale i.val) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => actualMellinScale k * d k) 16]
  apply Finset.sum_congr rfl
  intro i _
  rw [certificate_weights_eq_actualMellin_sq]
  field_simp [(actualMellinScale_pos i.val).ne']
  <;> ring

/-- The head norm of the same actual finite Gaussian source. -/
theorem actual_head_norm_coordinates {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    (∑ k ∈ Finset.range 16, finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) =
      ∑ i : Fin 16, Cap4FiniteCertificate.weights i *
        actualCentralHeadCoordinates c site i ^ 2 := by
  simpa only [actualCentralHeadCoordinates, actualMellinScale] using
    certificate_head_norm_coordinates
      (fun k => finiteGaussianNormalizedCoefficient c site (2 * k))

/-- The head central charge of that source, without a mass or parity premise. -/
theorem actual_head_charge_coordinates {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    (∑ k ∈ Finset.range 16,
      (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
        finiteGaussianNormalizedCoefficient c site (2 * k)) =
      ∑ i : Fin 16, Cap4FiniteCertificate.weights i *
        actualCentralHeadCoordinates c site i := by
  simpa only [actualCentralHeadCoordinates, actualMellinScale] using
    certificate_head_charge_coordinates
      (fun k => finiteGaussianNormalizedCoefficient c site (2 * k))

end FiniteGaussianCap475
