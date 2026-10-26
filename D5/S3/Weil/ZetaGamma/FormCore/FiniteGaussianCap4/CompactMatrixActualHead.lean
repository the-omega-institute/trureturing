/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixActualHead
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: The physical matrix head is the actual finite Gaussian prefix. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixPhysical
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianGraph

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace FiniteGaussianCap475
open FiniteGaussianCap4
open FiniteGaussianCap4.LaguerreSevenHalf

/-- Charge coordinates of the actual normalized source coefficients. -/
def actualCentralHeadCoordinates {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (i : Fin 16) : ℝ :=
  finiteGaussianNormalizedCoefficient c site (2 * i.val) /
    (normalizedCentralMellin (2 * i.val) / normalizedCentralMellin 0)

theorem actualCentralHeadCoordinates_mode {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (i : Fin 16) (x : ℝ) :
    actualCentralHeadCoordinates c site i * centralScaledMode i x =
      finiteGaussianCoefficient c site (2 * i.val) * phi x (2 * i.val) := by
  dsimp only [actualCentralHeadCoordinates, centralScaledMode,
    finiteGaussianNormalizedCoefficient, centralPsi]
  field_simp [(normalizedCentralMellin_even_pos i.val).ne',
    (normalizedCentralMellin_even_pos 0).ne',
    (centralNormalization_pos (2 * i.val)).ne']

private theorem sum_range_even_odd (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), f n) =
      ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- For the same reflected finite source, the matrix head is exactly its
actual thirty-two-mode Gaussian prefix. Normalization is canceled using
positive actual Mellin integrals; odd terms vanish by source reflection. -/
theorem centralHead_actual_prefix {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) (x : ℝ) :
    centralHead (actualCentralHeadCoordinates c site) x =
      finiteGaussianPartialSum c site 32 x := by
  classical
  have hodd (k : ℕ) : finiteGaussianCoefficient c site (2 * k + 1) = 0 :=
    finite_gaussian_odd_coefficient_zero c site reflection hc hs _
      ⟨k, by omega⟩
  calc
    centralHead (actualCentralHeadCoordinates c site) x =
        ∑ i : Fin 16, finiteGaussianCoefficient c site (2 * i.val) *
          phi x (2 * i.val) := by
      unfold centralHead
      exact Finset.sum_congr rfl (fun i _ => actualCentralHeadCoordinates_mode c site i x)
    _ = ∑ k ∈ Finset.range 16,
        finiteGaussianCoefficient c site (2 * k) * phi x (2 * k) := by
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => finiteGaussianCoefficient c site (2 * k) * phi x (2 * k)) 16
    _ = ∑ n ∈ Finset.range 32, finiteGaussianCoefficient c site n * phi x n := by
      rw [show 32 = 2 * 16 by norm_num, sum_range_even_odd]
      simp only [hodd, zero_mul, add_zero]
    _ = finiteGaussianPartialSum c site 32 x :=
      (finiteGaussianPartialSum_eq_modes c site 32 x).symm

end FiniteGaussianCap475
