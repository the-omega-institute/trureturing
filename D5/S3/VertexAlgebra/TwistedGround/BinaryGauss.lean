/- GID: D5/S3/VertexAlgebra/TwistedGround/BinaryGauss
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BinaryGauss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.LegendreSymbol.ZModChar]
   utility: none
   digest: Binary quadratic Gauss sums detect the determinant character modulo eight. -/

import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Algebra.Ring.Int.Units

/-! The arithmetic of the binary blocks in even-unimodular elimination. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BinaryGauss

open LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

/-- Reduction of the lifted binary coefficients to the charge field. -/
def residue : ZMod 8 →+* F₂ := ZMod.castHom (by decide) F₂

/-- The even integral binary Gram block, reduced modulo eight. -/
def gram (a b c : ZMod 8) : Matrix (Fin 2) (Fin 2) (ZMod 8) :=
  !![2 * a, b; b, 2 * c]

/-- The half-norm of a binary block, reduced modulo two. -/
def quadratic (a b c : ZMod 8) (x : F₂ × F₂) : F₂ :=
  residue a * x.1 ^ 2 + residue b * x.1 * x.2 + residue c * x.2 ^ 2

private theorem odd_square (u : ZMod 8) (hu : residue u = 1) : u ^ 2 = 1 := by
  have table : ∀ u : ZMod 8, residue u = 1 → u ^ 2 = 1 := by decide
  exact table u hu

private theorem block_character (a b c : ZMod 8) (hb : residue b = 1) :
    ZMod.χ₈ (gram a b c).det =
      if residue a * residue c = 0 then 1 else -1 := by
  have table : ∀ a b c : ZMod 8, residue b = 1 →
      ZMod.χ₈ (4 * a * c - b ^ 2) =
        if residue a * residue c = 0 then 1 else -1 := by decide
  have determinant : (gram a b c).det = 4 * a * c - b ^ 2 := by
    simp only [gram, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  rw [determinant]
  exact table a b c hb

private theorem binary_sum (a c : F₂) :
    (∑ x : F₂ × F₂, complexSign (a * x.1 ^ 2 + x.1 * x.2 + c * x.2 ^ 2)) =
      2 * complexSign (a * c) := by
  have table : ∀ a c : F₂,
      (∑ x : F₂ × F₂,
        (if a * x.1 ^ 2 + x.1 * x.2 + c * x.2 ^ 2 = 0 then (1 : ℤ) else -1)) =
          2 * (if a * c = 0 then 1 else -1) := by decide
  have evaluated := congrArg (Int.cast : ℤ → ℂ) (table a c)
  simpa [complexSign] using evaluated

theorem block_sum (a b c : ZMod 8) (hb : residue b = 1) :
    (∑ x : F₂ × F₂, complexSign (quadratic a b c x)) =
      2 * (ZMod.χ₈ (gram a b c).det : ℂ) := by
  simp only [quadratic, hb, one_mul]
  rw [binary_sum, block_character a b c hb]
  simp [complexSign]

private theorem block_product_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c : ι → ZMod 8) (hb : ∀ i, residue (b i) = 1) :
    (∑ x : ι → F₂ × F₂, complexSign (∑ i, quadratic (a i) (b i) (c i) (x i))) =
      (2 : ℂ) ^ Fintype.card ι *
        (ZMod.χ₈ (∏ i, (gram (a i) (b i) (c i)).det) : ℂ) := by
  classical
  simp_rw [LatticeTwistedGroundRealization.sign_sum Finset.univ]
  rw [← Fintype.prod_sum (fun (i : ι) (x : F₂ × F₂) =>
    complexSign (quadratic (a i) (b i) (c i) x))]
  simp_rw [block_sum _ _ _ (hb _)]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, ← Int.cast_prod, ← map_prod]

/-- A binary block decomposition with integral unit determinant has positive Gauss sum.
The odd multiplier is the determinant of the change of coordinates modulo eight.
This does not assert that a supplied lattice admits such a decomposition. -/
theorem binary_gauss_of_integral_unit_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c : ι → ZMod 8) (hb : ∀ i, residue (b i) = 1)
    (d : ℤ) (hd : IsUnit d) (u : ZMod 8) (hu : residue u = 1)
    (congruence : (∏ i, (gram (a i) (b i) (c i)).det) = u ^ 2 * (d : ZMod 8)) :
    (∑ x : ι → F₂ × F₂, complexSign (∑ i, quadratic (a i) (b i) (c i) (x i))) =
      (2 : ℂ) ^ Fintype.card ι := by
  rw [block_product_sum a b c hb, congruence, odd_square u hu, one_mul]
  have character : ZMod.χ₈ (d : ZMod 8) = 1 := by
    rcases Int.isUnit_iff.mp hd with rfl | rfl
    · rfl
    · decide
  rw [character, Int.cast_one, mul_one]

#print axioms binary_gauss_of_integral_unit_congruence

end D5.S3.VertexAlgebra.TwistedGround.BinaryGauss
