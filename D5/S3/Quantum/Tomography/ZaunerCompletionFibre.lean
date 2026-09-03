/- GID: D5/S3/Quantum/Tomography/ZaunerCompletionFibre
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ZaunerCompletionFibre
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zauner left factors over a common Fourier block have an identically zero cross block, obstructing mutual unbiasedness between canonical completion branches. -/

import D5.S3.Quantum.Tomography.MUBCubeCompatibility

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ZaunerCompletionFibre

open Matrix

/-- The unnormalized block pattern of Zauner's first factor

`[[F, X F], [F, -X F]]`.

The scalar `1 / sqrt 2` is omitted because the zero-block obstruction is
homogeneous and does not depend on normalization. -/
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
left factors with the same Fourier block is identically zero.  No unitarity or
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

/-- Consequently the relative Gram matrix of two canonical Zauner left factors
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

#print axioms zaunerLeftFactor_crossGram_upperRight_zero
#print axioms zaunerLeftFactor_crossGram_lowerLeft_zero
#print axioms zaunerLeftFactor_crossGram_not_nonzero_flat

end D5.S3.Quantum.Tomography.ZaunerCompletionFibre
