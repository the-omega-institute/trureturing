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

/-! ## Local rigidity in Zauner's `2 × 2` Fourier-mode factorization

After Fourier diagonalizing the `3 × 3` circulant blocks of a `2`-circulant
unitary, Zauner's construction decomposes the problem into three `2 × 2`
unitaries.  For one such block

`M = 1/2 [[u+v, y(u-v)], [(u-v)/x, y(u+v)/x]]`,

the apparent phase variables `x` and `y` already satisfy quadratic equations
determined by the entries of `M`.  Thus the generic local fibre is discrete.
-/

/-- Polynomial form of the local Zauner parameterization. Division is cleared
so that the statement remains valid without nonzero side conditions. -/
structure ZaunerTwoByTwoFactor (a b c d : ℂ) where
  u : ℂ
  v : ℂ
  x : ℂ
  y : ℂ
  sum_eq : u + v = 2 * a
  y_diff_eq : y * (u - v) = 2 * b
  diff_eq : u - v = 2 * c * x
  y_sum_eq : y * (u + v) = 2 * d * x

/-- In every local Zauner factorization, `x²` is fixed by the matrix entries:
`c d x² = a b`. -/
theorem zaunerTwoByTwo_x_quadratic
    {a b c d : ℂ} (z : ZaunerTwoByTwoFactor a b c d) :
    c * d * z.x ^ 2 = a * b := by
  have hb : b = z.y * c * z.x := by
    calc
      b = (2 : ℂ)⁻¹ * (2 * b) := by ring
      _ = (2 : ℂ)⁻¹ * (z.y * (z.u - z.v)) := by rw [z.y_diff_eq]
      _ = z.y * c * z.x := by rw [z.diff_eq]; ring
  have hdy : d * z.x = a * z.y := by
    have h := z.y_sum_eq
    rw [z.sum_eq] at h
    linarith
  rw [hb]
  calc
    c * d * z.x ^ 2 = c * (d * z.x) * z.x := by ring
    _ = c * (a * z.y) * z.x := by rw [hdy]
    _ = a * (z.y * c * z.x) := by ring

/-- Symmetrically, `y²` is fixed by the matrix entries:
`a c y² = b d`. -/
theorem zaunerTwoByTwo_y_quadratic
    {a b c d : ℂ} (z : ZaunerTwoByTwoFactor a b c d) :
    a * c * z.y ^ 2 = b * d := by
  have hb : b = z.y * c * z.x := by
    calc
      b = (2 : ℂ)⁻¹ * (2 * b) := by ring
      _ = (2 : ℂ)⁻¹ * (z.y * (z.u - z.v)) := by rw [z.y_diff_eq]
      _ = z.y * c * z.x := by rw [z.diff_eq]; ring
  have hdy : d * z.x = a * z.y := by
    have h := z.y_sum_eq
    rw [z.sum_eq] at h
    linarith
  rw [hb]
  calc
    a * c * z.y ^ 2 = c * z.y * (a * z.y) := by ring
    _ = c * z.y * (d * z.x) := by rw [← hdy]
    _ = (z.y * c * z.x) * d := by ring

/-- Two local factorizations of the same generic block can differ in `x` only
by sign.  Nonvanishing of `c*d` lets us cancel the common coefficient. -/
theorem zaunerTwoByTwo_x_eq_or_eq_neg
    {a b c d : ℂ}
    (z w : ZaunerTwoByTwoFactor a b c d)
    (hcd : c * d ≠ 0) :
    w.x = z.x ∨ w.x = -z.x := by
  have hx2 : w.x ^ 2 = z.x ^ 2 := by
    apply (mul_left_cancel₀ hcd)
    calc
      c * d * w.x ^ 2 = a * b := zaunerTwoByTwo_x_quadratic w
      _ = c * d * z.x ^ 2 := (zaunerTwoByTwo_x_quadratic z).symm
  exact (sq_eq_sq_iff_eq_or_eq_neg).mp hx2

/-- The same binary ambiguity holds for `y` when `a*c` is nonzero. -/
theorem zaunerTwoByTwo_y_eq_or_eq_neg
    {a b c d : ℂ}
    (z w : ZaunerTwoByTwoFactor a b c d)
    (hac : a * c ≠ 0) :
    w.y = z.y ∨ w.y = -z.y := by
  have hy2 : w.y ^ 2 = z.y ^ 2 := by
    apply (mul_left_cancel₀ hac)
    calc
      a * c * w.y ^ 2 = b * d := zaunerTwoByTwo_y_quadratic w
      _ = a * c * z.y ^ 2 := (zaunerTwoByTwo_y_quadratic z).symm
  exact (sq_eq_sq_iff_eq_or_eq_neg).mp hy2

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
      have hle : a i ≤ ∑ j, a j :=
        Finset.single_le_sum (fun j _ ↦ ha j) (Finset.mem_univ i)
      exact le_antisymm (by simpa [haSum] using hle) (ha i)
    intro i
    simp [hzero i]
  · have hzero : ∀ i, b i = 0 := by
      intro i
      have hle : b i ≤ ∑ j, b j :=
        Finset.single_le_sum (fun j _ ↦ hb j) (Finset.mem_univ i)
      exact le_antisymm (by simpa [hbSum] using hle) (hb i)
    intro i
    simp [hzero i]

#print axioms factorizedCube_crossGram_apply
#print axioms factorizedCube_crossGram
#print axioms zaunerTwoByTwo_x_quadratic
#print axioms zaunerTwoByTwo_y_quadratic
#print axioms zaunerTwoByTwo_x_eq_or_eq_neg
#print axioms zaunerTwoByTwo_y_eq_or_eq_neg
#print axioms pointwise_product_zero_does_not_force_global_orientation
#print axioms pointwise_product_zero_of_global_sum_product_zero

end D5.S3.Quantum.Tomography.MUBCubeCompatibility
