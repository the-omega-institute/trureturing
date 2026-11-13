/- GID: D5/S3/Quantum/Lieb/QuadraticPerspective
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/QuadraticPerspective
   mirror-E: none(waiver:schur-complement-finite-matrix-bridge)
   anchors: []
   utility: none
   digest: Joint convexity of the finite-dimensional quadratic operator perspective. -/

import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Lieb.QuadraticPerspective

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/- The Schur complement turns the nonlinear quadratic perspective into an
affine positive-semidefinite block matrix.  The strict-interior lemma keeps
the inverse carrier positive definite; the endpoint cases are identities. -/
private theorem strict_joint_convexity
    (A₀ A₁ B₀ B₁ : Matrix n n ℂ)
    (hA₀ : A₀.IsHermitian) (hA₁ : A₁.IsHermitian)
    (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    let Aₜ := t • A₀ + (1 - t) • A₁
    let Bₜ := t • B₀ + (1 - t) • B₁
    Aₜ * Bₜ⁻¹ * Aₜ ≤
      t • (A₀ * B₀⁻¹ * A₀) + (1 - t) • (A₁ * B₁⁻¹ * A₁) := by
  dsimp
  let Y₀ := A₀ * B₀⁻¹ * A₀
  let Y₁ := A₁ * B₁⁻¹ * A₁
  let Aₜ := t • A₀ + (1 - t) • A₁
  let Bₜ := t • B₀ + (1 - t) • B₁
  let Yₜ := t • Y₀ + (1 - t) • Y₁
  letI iB₀ : Invertible B₀ := hB₀.isUnit.invertible
  letI iB₁ : Invertible B₁ := hB₁.isUnit.invertible
  have hblock₀ : (Matrix.fromBlocks Y₀ A₀ A₀ᴴ B₀).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ Y₀ A₀ hB₀).2
    simpa [Y₀, hA₀.eq] using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  have hblock₁ : (Matrix.fromBlocks Y₁ A₁ A₁ᴴ B₁).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ Y₁ A₁ hB₁).2
    simpa [Y₁, hA₁.eq] using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  have hblock :
      (t • Matrix.fromBlocks Y₀ A₀ A₀ᴴ B₀ +
        (1 - t) • Matrix.fromBlocks Y₁ A₁ A₁ᴴ B₁).PosSemidef :=
    (hblock₀.smul ht₀.le).add (hblock₁.smul (sub_pos.mpr ht₁).le)
  have hblock' :
      (Matrix.fromBlocks Yₜ Aₜ Aₜᴴ Bₜ).PosSemidef := by
    simpa [Matrix.fromBlocks_add, Matrix.fromBlocks_smul, Aₜ, Bₜ, Yₜ,
      map_sub, sub_eq_add_neg] using hblock
  have hBₜ : Bₜ.PosDef := by
    apply Matrix.PosDef.add
    · exact hB₀.smul ht₀
    · exact hB₁.smul (sub_pos.mpr ht₁)
  letI iBₜ : Invertible Bₜ := hBₜ.isUnit.invertible
  have hschur := (Matrix.PosDef.fromBlocks₂₂ Yₜ Aₜ hBₜ).mp hblock'
  have hAₜ : Aₜᴴ = Aₜ := by
    simp [Aₜ, hA₀.eq, hA₁.eq]
  apply Matrix.le_iff.mpr
  simpa [Yₜ, Y₀, Y₁, Aₜ, Bₜ, sub_eq_add_neg, hA₀.eq, hA₁.eq] using hschur

/-- The quadratic perspective `(A, B) ↦ A B⁻¹ A` is jointly convex on
Hermitian `A` and positive-definite `B`, in Loewner order. -/
theorem joint_convexity
    (A₀ A₁ B₀ B₁ : Matrix n n ℂ)
    (hA₀ : A₀.IsHermitian) (hA₁ : A₁.IsHermitian)
    (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    let Aₜ := t • A₀ + (1 - t) • A₁
    let Bₜ := t • B₀ + (1 - t) • B₁
    Aₜ * Bₜ⁻¹ * Aₜ ≤
      t • (A₀ * B₀⁻¹ * A₀) + (1 - t) • (A₁ * B₁⁻¹ * A₁) := by
  by_cases hz : t = 0
  · subst t
    simp
  by_cases ho : t = 1
  · subst t
    simp
  exact strict_joint_convexity A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁
    (lt_of_le_of_ne ht₀ (Ne.symm hz)) (lt_of_le_of_ne ht₁ ho)

end D5.S3.Quantum.Lieb.QuadraticPerspective
