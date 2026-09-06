/- GID: D5/S3/Quantum/Tomography/ZaunerCompletionFibre
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ZaunerCompletionFibre
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zauner factor branches have structural zero blocks in both the factor-relative and fixed-edge completion-relative directions, obstructing mutual unbiasedness. -/

import D5.S3.Quantum.Tomography.MUBCubeCompatibility

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ZaunerCompletionFibre

open Matrix

/-- The unnormalized block pattern of Zauner's first factor

`[[F, X F], [F, -X F]]`.

The scalar `1 / sqrt 2` is omitted because every zero-pattern statement below
is homogeneous and does not depend on normalization. -/
def zaunerLeftFactor
    {κ : Type*}
    (F : Matrix κ κ ℂ) (x : κ → ℂ) :
    Matrix (Fin 2 × κ) (Fin 2 × κ) ℂ :=
  fun r c ↦
    if c.1 = 0 then
      F r.2 c.2
    else if r.1 = 0 then
      x r.2 * F r.2 c.2
    else
      -(x r.2 * F r.2 c.2)

/-- The upper-right block of the relative Gram matrix between any two Zauner
left factors with the same Fourier block is identically zero. No unitarity or
phase hypothesis is needed for this cancellation. -/
theorem zaunerLeftFactor_crossGram_upperRight_zero
    {κ : Type*} [Fintype κ]
    (F : Matrix κ κ ℂ) (x x' : κ → ℂ) (i j : κ) :
    ((zaunerLeftFactor F x)ᴴ * zaunerLeftFactor F x')
        ((0 : Fin 2), i) ((1 : Fin 2), j) = 0 := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    zaunerLeftFactor, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The lower-left cross block vanishes as well. -/
theorem zaunerLeftFactor_crossGram_lowerLeft_zero
    {κ : Type*} [Fintype κ]
    (F : Matrix κ κ ℂ) (x x' : κ → ℂ) (i j : κ) :
    ((zaunerLeftFactor F x)ᴴ * zaunerLeftFactor F x')
        ((1 : Fin 2), i) ((0 : Fin 2), j) = 0 := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    zaunerLeftFactor, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Consequently the factor-relative Gram matrix of two Zauner left factors
cannot have a fixed nonzero squared modulus at every entry. -/
theorem zaunerLeftFactor_crossGram_not_nonzero_flat
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (F : Matrix κ κ ℂ) (x x' : κ → ℂ) (r : ℝ) (hr : r ≠ 0) :
    ¬ ∀ p q,
      Complex.normSq
        (((zaunerLeftFactor F x)ᴴ * zaunerLeftFactor F x') p q) = r := by
  intro hflat
  let i : κ := Classical.choice inferInstance
  have h := hflat ((0 : Fin 2), i) ((1 : Fin 2), i)
  rw [zaunerLeftFactor_crossGram_upperRight_zero F x x' i i] at h
  simpa using hr h.symm

/-! ## Correct fixed-edge completion direction

If a `2`-circulant edge is factorized as `T = Z₁ᴴ Z₂`, then after fixing the
edge to `(I,T)` the associated third basis is `W = Z₁ᴴ`. Hence two branches
`Z₁,Z₁'` are compared through

`Wᴴ W' = Z₁ Z₁'ᴴ`,

rather than through `Z₁ᴴ Z₁'`. The next statements prove the structural zeros
in this completion-relative direction.
-/

/-- The scalar multiplying one row of the second Zauner block. -/
private def zaunerBlockWeight
    {κ : Type*} (x : κ → ℂ) (r : Fin 2 × κ) (b : Fin 2) : ℂ :=
  if b = 0 then 1 else if r.1 = 0 then x r.2 else -x r.2

private theorem zaunerLeftFactor_apply_eq_weight_mul
    {κ : Type*}
    (F : Matrix κ κ ℂ) (x : κ → ℂ)
    (r : Fin 2 × κ) (b : Fin 2) (j : κ) :
    zaunerLeftFactor F x r (b, j) =
      zaunerBlockWeight x r b * F r.2 j := by
  rcases r with ⟨r, i⟩
  fin_cases r <;> fin_cases b <;>
    simp [zaunerLeftFactor, zaunerBlockWeight]

/-- If the common Fourier block has orthonormal rows, every entry connecting
distinct Fourier modes in `Z₁ Z₁'ᴴ` vanishes. This is the intrinsic sparsity
statement for fixed-edge canonical completions. -/
theorem zaunerLeftFactor_mul_conjTranspose_offMode_zero
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (F : Matrix κ κ ℂ) (x x' : κ → ℂ)
    (hF : F * Fᴴ = (1 : Matrix κ κ ℂ))
    (r s : Fin 2) (i j : κ) (hij : i ≠ j) :
    (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ)
        (r, i) (s, j) = 0 := by
  have hEntry := congrArg (fun M : Matrix κ κ ℂ ↦ M i j) hF
  have hRow : ∑ k, F i k * star (F j k) = 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, hij] using hEntry
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro b hb
  calc
    ∑ k,
        zaunerLeftFactor F x (r, i) (b, k) *
          star (zaunerLeftFactor F x' (s, j) (b, k)) =
      (zaunerBlockWeight x (r, i) b *
          star (zaunerBlockWeight x' (s, j) b)) *
        ∑ k, F i k * star (F j k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [zaunerLeftFactor_apply_eq_weight_mul,
            zaunerLeftFactor_apply_eq_weight_mul]
          simp only [map_mul]
          ring
    _ = 0 := by rw [hRow, mul_zero]

/-- In order six, the correct completion-relative matrix has a structural zero
at every pair of distinct three-cycle modes. Therefore two canonical Zauner
fixed-edge completions cannot have any prescribed nonzero flat modulus. -/
theorem zaunerCanonicalCompletion_crossGram_not_nonzero_flat
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (r : ℝ) (hr : r ≠ 0) :
    ¬ ∀ p q,
      Complex.normSq
        ((zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ) p q) = r := by
  intro hflat
  have h := hflat ((0 : Fin 2), (0 : Fin 3))
    ((0 : Fin 2), (1 : Fin 3))
  rw [zaunerLeftFactor_mul_conjTranspose_offMode_zero
    F x x' hF (0 : Fin 2) (0 : Fin 2)
      (0 : Fin 3) (1 : Fin 3) (by decide)] at h
  have hz : (0 : ℝ) = r := by simpa using h
  exact hr hz.symm

#print axioms zaunerLeftFactor_crossGram_upperRight_zero
#print axioms zaunerLeftFactor_crossGram_lowerLeft_zero
#print axioms zaunerLeftFactor_crossGram_not_nonzero_flat
#print axioms zaunerLeftFactor_mul_conjTranspose_offMode_zero
#print axioms zaunerCanonicalCompletion_crossGram_not_nonzero_flat

end D5.S3.Quantum.Tomography.ZaunerCompletionFibre
