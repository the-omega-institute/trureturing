/- GID: D5/S3/Quantum/Tomography/MUBCompletionGluing
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionGluing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Over a fixed factorized MUB completion, a mutually unbiased second completion is determined by one relative Gram matrix and its entrywise conjugate. -/

import D5.S3.Quantum.Tomography.MUBCubeCompatibility

/- Library-search audit trail (2026-09-03):
   * Reuses `EntrywiseUnit`, `IsComplexHadamard`, and `HadamardUnbiased`
     from `MUBHadamardCompatibility`.
   * Reuses `factorizedCubeMatrix` and
     `factorizedCube_crossGram_apply` from `MUBCubeCompatibility`.
   * Uses the existing matrix multiplication, conjugate-transpose, and scalar
     action APIs. No second unitary predicate, Hadamard-product operation, or
     cube carrier is introduced here.
   * Repository search found no existing theorem eliminating one completion
     factor from the fixed-edge cube cross-Gram equation.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionGluing

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCubeCompatibility

private theorem star_mul_self_of_normSq
    {z : ℂ} {r : ℝ} (hz : Complex.normSq z = r) :
    star z * z = (r : ℂ) := by
  simpa [Complex.star_def, Complex.normSq_eq_conj_mul_self] using
    congrArg (fun a : ℝ ↦ (a : ℂ)) hz

/-- A nonzero squared norm and the matching complex product determine the
second factor as the complex conjugate of the first. -/
theorem partner_eq_star_of_normSq_and_product
    {z w : ℂ} {r : ℝ}
    (hr : r ≠ 0)
    (hz : Complex.normSq z = r)
    (hzw : z * w = (r : ℂ)) :
    w = star z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
    exact hr hz.symm
  apply mul_left_cancel₀ hz0
  calc
    z * w = (r : ℂ) := hzw
    _ = z * star z := by
      simpa [mul_comm] using (star_mul_self_of_normSq hz).symm

/-- If the first relative Gram matrix has the MUB modulus and its pointwise
product with a second relative Gram matrix is the dimension constant, the
second matrix is the entrywise conjugate of the first. -/
theorem relativeGram_partner_eq_entrywiseConj
    {n : Type*} [Fintype n] [Nonempty n]
    (X X' Y Y' : ComplexSquare n)
    (hXX' : HadamardUnbiased X X')
    (hProduct : ∀ k l,
      ((Xᴴ * X') k l) * ((Yᴴ * Y') k l) =
        (Fintype.card n : ℂ)) :
    Yᴴ * Y' = fun k l ↦ star ((Xᴴ * X') k l) := by
  have hcardPos : 0 < Fintype.card n := Fintype.card_pos
  have hcardR : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardPos)
  ext k l
  exact partner_eq_star_of_normSq_and_product
    hcardR (hXX' k l) (hProduct k l)

/-- Multiplying a relative Gram matrix on the left by its Hadamard factor
recovers the second factor, scaled by the finite dimension. -/
theorem left_mul_relativeGram_eq_card_smul
    {n : Type*} [Fintype n] [DecidableEq n]
    (X X' : ComplexSquare n)
    (hX : X * Xᴴ =
      (Fintype.card n : ℂ) • (1 : ComplexSquare n)) :
    X * (Xᴴ * X') = (Fintype.card n : ℂ) • X' := by
  calc
    X * (Xᴴ * X') = (X * Xᴴ) * X' :=
      (Matrix.mul_assoc X Xᴴ X').symm
    _ = ((Fintype.card n : ℂ) • (1 : ComplexSquare n)) * X' := by
      rw [hX]
    _ = (Fintype.card n : ℂ) • X' := by simp

/-- The rationally scaled form of `left_mul_relativeGram_eq_card_smul`.
It avoids introducing square roots into the completion coordinates. -/
theorem invCard_smul_left_mul_relativeGram
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (X X' : ComplexSquare n)
    (hX : X * Xᴴ =
      (Fintype.card n : ℂ) • (1 : ComplexSquare n)) :
    ((Fintype.card n : ℂ)⁻¹) • (X * (Xᴴ * X')) = X' := by
  rw [left_mul_relativeGram_eq_card_smul X X' hX]
  have hcardPos : 0 < Fintype.card n := Fintype.card_pos
  have hcardC : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardPos)
  simp [smul_smul, hcardC]

/-- Fixed-edge double-completion elimination.

For two factorized cube completions sharing an entrywise-unit bottom face,
assume their cube cross-Gram is the constant dimension matrix and the first
relative factor is MUB-flat. Then:

* the second relative Gram is the entrywise conjugate of the first;
* `X'` is recovered rationally from `X` and `Xᴴ X'`;
* `Y'` is recovered rationally from `Y` and the entrywise conjugate of
  `Xᴴ X'`.

Thus one relative Gram matrix carries all remaining gluing freedom. -/
theorem second_completion_determined_by_one_relativeGram
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H X X' Y Y' : ComplexSquare n)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y)
    (hXX' : HadamardUnbiased X X')
    (hCubeCross :
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' =
        fun _ _ ↦ (Fintype.card n : ℂ)) :
    (Yᴴ * Y' = fun k l ↦ star ((Xᴴ * X') k l)) ∧
    (((Fintype.card n : ℂ)⁻¹) •
        (X * (Xᴴ * X')) = X') ∧
    (((Fintype.card n : ℂ)⁻¹) •
        (Y * (fun k l ↦ star ((Xᴴ * X') k l))) = Y') := by
  have hProduct : ∀ k l,
      ((Xᴴ * X') k l) * ((Yᴴ * Y') k l) =
        (Fintype.card n : ℂ) := by
    intro k l
    have hFactor :=
      factorizedCube_crossGram_apply H X X' Y Y' hH k l
    have hConstant := congrFun (congrFun hCubeCross k) l
    exact hFactor.symm.trans hConstant
  have hPartner :
      Yᴴ * Y' = fun k l ↦ star ((Xᴴ * X') k l) :=
    relativeGram_partner_eq_entrywiseConj X X' Y Y' hXX' hProduct
  refine ⟨hPartner, ?_, ?_⟩
  · exact invCard_smul_left_mul_relativeGram X X' hX.2
  · have hRecoverY := invCard_smul_left_mul_relativeGram Y Y' hY.2
    rwa [hPartner] at hRecoverY

#print axioms partner_eq_star_of_normSq_and_product
#print axioms relativeGram_partner_eq_entrywiseConj
#print axioms left_mul_relativeGram_eq_card_smul
#print axioms invCard_smul_left_mul_relativeGram
#print axioms second_completion_determined_by_one_relativeGram

end D5.S3.Quantum.Tomography.MUBCompletionGluing
