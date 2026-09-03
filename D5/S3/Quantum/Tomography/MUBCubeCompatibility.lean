/- GID: D5/S3/Quantum/Tomography/MUBCubeCompatibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCubeCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-edge MUB completions factor through an exact cube cross-Gram identity; pointwise cubic orientation does not imply a global orientation. -/

import D5.S3.Quantum.Tomography.MUBHadamardCompatibility
import Mathlib.Tactic

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCubeCompatibility

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility

/-- Flatten the two free coordinates of a factorized Hadamard-cube slice.
The formula mirrors `C_{i,j,k} = H_{i,j} X_{j,k} Y_{i,k}`. -/
def factorizedCubeMatrix
    {ι κ λ : Type*}
    (H : Matrix ι κ ℂ) (X : Matrix κ λ ℂ) (Y : Matrix ι λ ℂ) :
    Matrix (ι × κ) λ ℂ :=
  fun ij k ↦ H ij.1 ij.2 * X ij.2 k * Y ij.1 k

private theorem star_mul_self_of_normSq_one {z : ℂ}
    (hz : Complex.normSq z = 1) : star z * z = 1 := by
  simpa [Complex.star_def, Complex.normSq_eq_conj_mul_self] using
    congrArg (fun a : ℝ ↦ (a : ℂ)) hz

/-- Entrywise cross-Gram factorization for two completions sharing the same
unimodular bottom face. This is the algebraic core of
`Cᴴ D = (Xᴴ X') ∘ (Yᴴ Y')`. -/
theorem factorizedCube_crossGram_apply
    {ι κ λ : Type*}
    [Fintype ι] [Fintype κ]
    (H : Matrix ι κ ℂ)
    (X X' : Matrix κ λ ℂ)
    (Y Y' : Matrix ι λ ℂ)
    (hH : EntrywiseUnit H)
    (k l : λ) :
    ((factorizedCubeMatrix H X Y)ᴴ *
        factorizedCubeMatrix H X' Y') k l =
      ((Xᴴ * X') k l) * ((Yᴴ * Y') k l) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, factorizedCubeMatrix]
  rw [Fintype.sum_prod_type]
  calc
    ∑ i, ∑ j,
        star (H i j * X j k * Y i k) *
          (H i j * X' j l * Y' i l) =
      ∑ i, ∑ j,
        (star (X j k) * X' j l) *
          (star (Y i k) * Y' i l) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hHij : star (H i j) * H i j = 1 :=
          star_mul_self_of_normSq_one (hH i j)
        simp only [map_mul]
        calc
          (star (Y i k) * star (X j k) * star (H i j)) *
              (H i j * X' j l * Y' i l) =
            (star (H i j) * H i j) *
              (star (X j k) * X' j l) *
              (star (Y i k) * Y' i l) := by ring
          _ = (star (X j k) * X' j l) *
              (star (Y i k) * Y' i l) := by rw [hHij]; simp
    _ = ∑ i,
        (∑ j, star (X j k) * X' j l) *
          (star (Y i k) * Y' i l) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
    _ = (∑ j, star (X j k) * X' j l) *
        (∑ i, star (Y i k) * Y' i l) := by
        rw [Finset.mul_sum]
    _ = ((Xᴴ * X') k l) * ((Yᴴ * Y') k l) := by
        rfl

/-- The matrix-valued form of the cube cross-Gram factorization. -/
theorem factorizedCube_crossGram
    {ι κ λ : Type*}
    [Fintype ι] [Fintype κ]
    (H : Matrix ι κ ℂ)
    (X X' : Matrix κ λ ℂ)
    (Y Y' : Matrix ι λ ℂ)
    (hH : EntrywiseUnit H) :
    (factorizedCubeMatrix H X Y)ᴴ * factorizedCubeMatrix H X' Y' =
      fun k l ↦ ((Xᴴ * X') k l) * ((Yᴴ * Y') k l) := by
  ext k l
  exact factorizedCube_crossGram_apply H X X' Y Y' hH k l

/-! ## Orientation logic boundary

The 2026 triplet conjecture gives pointwise products of nonnegative cubic
quantities. A product of the global sums is a strictly stronger statement unless
one separately proves a coherence theorem forcing the same side to vanish at
every orientation. The following two-point witness commits this distinction to
the machine truth source.
-/

/-- Pointwise disjoint support does not force one entire nonnegative family to
vanish. -/
theorem pointwise_product_zero_does_not_force_global_orientation :
    ∃ a b : Fin 2 → ℝ,
      (∀ i, 0 ≤ a i) ∧
      (∀ i, 0 ≤ b i) ∧
      (∀ i, a i * b i = 0) ∧
      (∑ i, a i) * (∑ i, b i) ≠ 0 := by
  refine ⟨![1, 0], ![0, 1], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]

/-- The global one-sided statement does imply pointwise product vanishing for
nonnegative families. This is the safe implication used when a global
orientation certificate has actually been proved. -/
theorem pointwise_product_zero_of_global_sum_product_zero
    {ι : Type*} [Fintype ι]
    (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i)
    (hglobal : (∑ i, a i) * (∑ i, b i) = 0) :
    ∀ i, a i * b i = 0 := by
  rcases mul_eq_zero.mp hglobal with haSum | hbSum
  · have hzero : ∀ i, a i = 0 := by
      intro i
      apply le_antisymm
      · exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ ha j).mp haSum i
          (Finset.mem_univ i)
      · exact ha i
    intro i
    simp [hzero i]
  · have hzero : ∀ i, b i = 0 := by
      intro i
      apply le_antisymm
      · exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hb j).mp hbSum i
          (Finset.mem_univ i)
      · exact hb i
    intro i
    simp [hzero i]

#print axioms factorizedCube_crossGram_apply
#print axioms factorizedCube_crossGram
#print axioms pointwise_product_zero_does_not_force_global_orientation
#print axioms pointwise_product_zero_of_global_sum_product_zero

end D5.S3.Quantum.Tomography.MUBCubeCompatibility
