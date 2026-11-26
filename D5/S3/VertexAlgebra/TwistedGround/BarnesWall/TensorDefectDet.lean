/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorDefectDet
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorDefectDet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: The defect determinant of an order-four tensor Pauli word gives its ground multiplicity. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorLift
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGramDet

/-! Determinants of order-four defect operators in the Barnes–Wall tensor basis. -/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorDefectDet

open LatticeTwistedGroundRealization.SignQuotient (F₂)
open TailPauliPairing (Word)
open TailPauliQuotientMaps (select selections)
open TensorLift (wordMatrix synthesize_wordMatrix wordMatrix_preserves_gram)
open TensorSubsetRows (synthesize synthesize_injective ambientWord_square rationalSign)
open TensorGram (gram)

variable {ι : Type} [Fintype ι] [LinearOrder ι]

private theorem synthesize_neg (a : Word ι → ℤ) : synthesize (-a) = -synthesize a := by
  funext v
  simp [synthesize, Finset.sum_neg_distrib, neg_mul]

/-- A Pauli word that has odd square exponent squares to negative identity on the lattice. -/
theorem wordMatrix_square_neg (word : List (ι × Bool))
    (hs : ∑ r, selections false word r * selections true word r = (1 : F₂)) :
    wordMatrix word * wordMatrix word = -(1 : Matrix (Word ι) (Word ι) ℤ) := by
  ext i j
  let a : Word ι → ℤ := Pi.single i 1
  have he : (a ᵥ* wordMatrix word) ᵥ* wordMatrix word = -a := by
    apply synthesize_injective
    rw [synthesize_wordMatrix, synthesize_wordMatrix, synthesize_neg]
    funext v
    rw [ambientWord_square, hs]
    have hsign : rationalSign (1 : F₂) = -1 := by decide
    rw [hsign, neg_one_mul]
    rfl
  rw [Matrix.vecMul_vecMul, Matrix.single_vecMul, one_smul] at he
  have hv := congrFun he j
  by_cases hij : i = j <;> simp [Matrix.one_apply, Pi.single_apply, a, hij, eq_comm] at hv ⊢ <;> exact hv

private theorem defect_gram (g G : Matrix (Word ι) (Word ι) ℤ)
    (hsq : g * g = -1) (hisom : g * G * gᵀ = G) :
    (1 - g) * G * (1 - g)ᵀ = (2 : ℤ) • G := by
  have h : G * gᵀ = -(g * G) := by
    have hleft : (g * g) * G * gᵀ = g * G := by
      simpa only [mul_assoc] using congrArg (g * ·) hisom
    rw [hsq, neg_one_mul, neg_mul] at hleft
    simpa only [neg_neg] using congrArg Neg.neg hleft
  rw [Matrix.transpose_sub, Matrix.transpose_one, sub_mul, one_mul, mul_sub, mul_one,
    sub_mul, hisom, h, two_smul]
  abel

/-- For every odd number of tensor slots, the defect of an order-four Pauli word
has determinant of absolute value `2^(2^(m-1))` in the normalized tensor lattice. -/
theorem abs_det_defect (hodd : (Fintype.card ι : F₂) = 1) (word : List (ι × Bool))
    (hs : ∑ r, selections false word r * selections true word r = (1 : F₂)) :
    |(1 - wordMatrix word).det| = (2 : ℤ) ^ (2 ^ (Fintype.card ι - 1)) := by
  let g := wordMatrix word
  let G : Matrix (Word ι) (Word ι) ℤ := Matrix.of gram
  have hg : g * G * gᵀ = G := wordMatrix_preserves_gram hodd word
  have hsquare := wordMatrix_square_neg word hs
  have hG : G.det = 1 := TensorGramDet.gram_det_one hodd
  have hd := congrArg Matrix.det (defect_gram g G hsquare hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, hG, mul_one, mul_one] at hd
  have hm : 1 ≤ Fintype.card ι := by
    by_contra! ha
    have hz : Fintype.card ι = 0 := by omega
    rw [hz, Nat.cast_zero] at hodd
    exact zero_ne_one hodd
  have hcard : Fintype.card (Word ι) = 2 ^ (Fintype.card ι - 1) * 2 := by
    rw [Fintype.card_fun, Fintype.card_bool, ← pow_succ, Nat.sub_add_cancel hm]
  have hp : |(1 - g).det| ^ 2 = ((2 : ℤ) ^ (2 ^ (Fintype.card ι - 1))) ^ 2 := by
    rw [sq_abs, pow_two ((1 - g).det), hd, ← pow_mul, hcard]
  exact (pow_left_inj₀ (abs_nonneg _) (by positivity) (by decide)).mp hp

/-- The three Pauli words in row-action order. The third is the composition
of the first two and represents the product quaternion generator. -/
def quaternionWord (r₁ r₂ : ι) : Fin 3 → List (ι × Bool)
  | 0 => [(r₁, false), (r₁, true)]
  | 1 => [(r₁, false), (r₂, false), (r₂, true)]
  | 2 => [(r₁, false), (r₁, true), (r₁, false), (r₂, false), (r₂, true)]

private theorem square_exponent (r₁ r₂ : ι) (h₁₂ : r₁ ≠ r₂) (r : Fin 3) :
    ∑ a, selections false (quaternionWord r₁ r₂ r) a *
      selections true (quaternionWord r₁ r₂ r) a = (1 : F₂) := by
  classical
  have hterm (a : ι) : ∀ r : Fin 3,
      selections false (quaternionWord r₁ r₂ r) a * selections true (quaternionWord r₁ r₂ r) a =
        if a = (if r = 0 then r₁ else r₂) then 1 else 0 := by
    intro r
    fin_cases r <;> by_cases ha : a = r₁ <;> by_cases hb : a = r₂ <;>
      simp_all [quaternionWord, selections, select, CharTwo.add_self_eq_zero, Pi.add_apply]
  simp_rw [hterm]
  simp

/-- The square-root defect rule fixes the order-four ground multiplicity
in every odd-slot tensor rank. -/
theorem groundMultiplicity_eq (r₁ r₂ : ι) (h₁₂ : r₁ ≠ r₂) (r : Fin 3)
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 2 ≤ Fintype.card ι) (M : ℕ)
    (hM : (M : ℤ) ^ 2 = |(1 - wordMatrix (quaternionWord r₁ r₂ r)).det|) :
    M = 2 ^ (2 ^ (Fintype.card ι - 2)) := by
  have hexp : Fintype.card ι - 1 = (Fintype.card ι - 2) + 1 := by omega
  rw [abs_det_defect hodd _ (square_exponent r₁ r₂ h₁₂ r), hexp, pow_succ (2 : ℕ), pow_mul] at hM
  exact_mod_cast (pow_left_inj₀ (by positivity : 0 ≤ (M : ℤ))
    (by positivity : 0 ≤ (2 : ℤ) ^ (2 ^ (Fintype.card ι - 2))) (by decide : (2 : ℕ) ≠ 0)).mp hM

#print axioms groundMultiplicity_eq

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorDefectDet
