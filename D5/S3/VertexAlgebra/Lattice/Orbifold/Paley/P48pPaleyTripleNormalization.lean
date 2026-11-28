/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyTripleNormalization
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyTripleNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The projective action of SL(2,23) moves every unordered triple to the Paley seed triple. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pPaleyAction
import OmegaBuild.Commands

/-!
# The P48p Paley seed triple

Scale the first two projective rows so that their sum is the third. The inverse
of this row basis sends the three directions to zero, infinity and one. A target
transposition corrects the determinant square class before scalar rescaling.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleyTripleNormalization

open scoped Matrix
open P48pFrameProjectiveAction (Direction F23 SL23 Row normalizedRow projectiveStep)
open P48pPaleyAction (paleyPerm)

open private normalize_smul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pFrameProjectiveAction
open private directionEquiv from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pTernaryPaleyGraph
open private paleyDirection_perm from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pPaleyAction

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

private abbrev Mat := Matrix (Fin 2) (Fin 2) F23

private def rowDet (r s : Row) : F23 := r 0 * s 1 - r 1 * s 0

private theorem rowDet_ne_zero {d e : Direction} (hne : d ≠ e) :
    rowDet (normalizedRow d) (normalizedRow e) ≠ 0 := by
  cases d with
  | none =>
    cases e with
    | none => exact (hne rfl).elim
    | some y => simp [rowDet, normalizedRow]
  | some x =>
    cases e with
    | none => simp [rowDet, normalizedRow]
    | some y =>
      have hyx : y ≠ x := fun h => hne (congrArg some h.symm)
      simpa [rowDet, normalizedRow, sub_eq_zero] using hyx

private theorem exists_normalizing_matrix {d e f : Direction}
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    ∃ (A : Mat) (a b : F23), A.det ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
      normalizedRow d ᵥ* A = a • normalizedRow (some 0) ∧
      normalizedRow e ᵥ* A = b • normalizedRow none ∧
      normalizedRow f ᵥ* A = normalizedRow (some 1) := by
  let r := normalizedRow d
  let s := normalizedRow e
  let t := normalizedRow f
  have hdet : rowDet r s ≠ 0 := rowDet_ne_zero hde
  let α := rowDet t s / rowDet r s
  let β := rowDet r t / rowDet r s
  have hα : α ≠ 0 := div_ne_zero (rowDet_ne_zero (Ne.symm hef)) hdet
  have hβ : β ≠ 0 := div_ne_zero (rowDet_ne_zero hdf) hdet
  have hαdet : α * rowDet r s = rowDet t s := div_mul_cancel₀ _ hdet
  have hβdet : β * rowDet r s = rowDet r t := div_mul_cancel₀ _ hdet
  have ht : t = α • r + β • s := by
    funext i
    change t i = α * r i + β * s i
    apply mul_right_cancel₀ hdet
    rw [add_mul, mul_right_comm α (r i), mul_right_comm β (s i), hαdet, hβdet]
    fin_cases i
    · change t 0 * rowDet r s = rowDet t s * r 0 + rowDet r t * s 0
      unfold rowDet
      ring
    · change t 1 * rowDet r s = rowDet t s * r 1 + rowDet r t * s 1
      unfold rowDet
      ring
  let B : Mat := Matrix.of ![α • r, β • s]
  have hBdet : B.det = α * β * rowDet r s := by
    rw [Matrix.det_fin_two]
    change (α * r 0) * (β * s 1) - (α * r 1) * (β * s 0) = _
    unfold rowDet
    ring
  have hB : IsUnit B.det := by
    rw [hBdet]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero hα hβ) hdet)
  let A : Mat := B⁻¹
  have hBA : B * A = 1 := Matrix.mul_nonsing_inv B hB
  have h0 : (α • r) ᵥ* A = normalizedRow (some 0) := by
    have h := congrArg (fun M : Mat => M 0) hBA
    rw [Matrix.mul_apply_eq_vecMul] at h
    change (α • r) ᵥ* A = (1 : Mat) 0 at h
    rw [h]
    funext i
    fin_cases i <;> simp [Matrix.one_apply, normalizedRow]
  have hInfinity : (β • s) ᵥ* A = normalizedRow none := by
    have h := congrArg (fun M : Mat => M 1) hBA
    rw [Matrix.mul_apply_eq_vecMul] at h
    change (β • s) ᵥ* A = (1 : Mat) 1 at h
    rw [h]
    funext i
    fin_cases i <;> simp [Matrix.one_apply, normalizedRow]
  refine ⟨A, α⁻¹, β⁻¹, (Matrix.isUnit_nonsing_inv_det B hB).ne_zero,
    inv_ne_zero hα, inv_ne_zero hβ, ?_, ?_, ?_⟩
  · change r ᵥ* A = α⁻¹ • normalizedRow (some 0)
    rw [← h0, Matrix.smul_vecMul, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · change s ᵥ* A = β⁻¹ • normalizedRow none
    rw [← hInfinity, Matrix.smul_vecMul, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  · change t ᵥ* A = normalizedRow (some 1)
    rw [ht, Matrix.add_vecMul, h0, hInfinity]
    funext i
    fin_cases i <;> simp [normalizedRow]

private theorem quadraticChar_neg_one_F23 : quadraticChar F23 (-1) = -1 := by
  have hchar : ringChar F23 ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  rw [quadraticChar_eq_pow_of_char_ne_two hchar (neg_ne_zero.mpr one_ne_zero), ZMod.card]
  decide +kernel

private theorem exists_sl_of_square_det (A : Mat) (hne : A.det ≠ 0)
    (hsq : IsSquare A.det) : ∃ (g : SL23) (c : F23), c ≠ 0 ∧ (g : Mat) = c • A := by
  obtain ⟨w, hw⟩ := hsq
  have hwne : w ≠ 0 := by
    intro hz
    apply hne
    rw [hw, hz, zero_mul]
  have hdet : (w⁻¹ • A).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hw, pow_two, mul_mul_mul_comm]
    simp only [inv_mul_cancel₀ hwne, one_mul]
  exact ⟨⟨w⁻¹ • A, hdet⟩, w⁻¹, inv_ne_zero hwne, rfl⟩

private theorem projectiveStep_of_scaled_row {g : SL23} {A : Mat} {c k : F23}
    {d e : Direction} (hg : (g : Mat) = c • A) (hc : c ≠ 0) (hk : k ≠ 0)
    (hrow : normalizedRow d ᵥ* A = k • normalizedRow e) :
    (projectiveStep g d).1 = e := by
  change (P48pFrameProjectiveAction.normalize (normalizedRow d ᵥ* (g : Mat))).1 = e
  rw [hg, Matrix.vecMul_smul, hrow, smul_smul, normalize_smul e (mul_ne_zero hc hk)]

/-- Every three-element set of directions moves to infinity, zero and one. -/
theorem exists_projectiveStep_image_triple (s : Finset Direction) (hs : s.card = 3) :
    ∃ g : SL23, s.image (fun d => (projectiveStep g d).1) = {none, some 0, some 1} := by
  obtain ⟨d, e, f, hde, hdf, hef, rfl⟩ := Finset.card_eq_three.mp hs
  obtain ⟨A, a, b, hA, ha, hb, hd, he, hf⟩ := exists_normalizing_matrix hde hdf hef
  rcases quadraticChar_dichotomy hA with hsq | hnsq
  · obtain ⟨g, c, hc, hg⟩ := exists_sl_of_square_det A hA
      ((quadraticChar_one_iff_isSquare hA).mp hsq)
    have h0 := projectiveStep_of_scaled_row hg hc ha hd
    have hInfinity := projectiveStep_of_scaled_row hg hc hb he
    have hf' : normalizedRow f ᵥ* A = (1 : F23) • normalizedRow (some 1) := by
      rw [one_smul, hf]
    have h1 := projectiveStep_of_scaled_row hg hc one_ne_zero hf'
    refine ⟨g, ?_⟩
    simp only [Finset.image_insert, Finset.image_singleton, h0, hInfinity, h1]
    exact Finset.insert_comm _ _ _
  · let T : Mat := !![1, 1; 0, -1]
    have hTdet : T.det = -1 := by simp [T, Matrix.det_fin_two_of]
    have hT0 : normalizedRow (some 0) ᵥ* T = normalizedRow (some 1) := by
      funext i
      fin_cases i <;> simp [T, normalizedRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have hTInfinity : normalizedRow none ᵥ* T = (-1 : F23) • normalizedRow none := by
      funext i
      fin_cases i <;>
        simp [T, normalizedRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    have hT1 : normalizedRow (some 1) ᵥ* T = normalizedRow (some 0) := by
      funext i
      fin_cases i <;> simp [T, normalizedRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have hAT : (A * T).det ≠ 0 := by
      rw [Matrix.det_mul, hTdet]
      exact mul_ne_zero hA (neg_ne_zero.mpr one_ne_zero)
    have hsq : quadraticChar F23 (A * T).det = 1 := by
      rw [Matrix.det_mul, map_mul, hTdet, hnsq, quadraticChar_neg_one_F23] <;> decide
    obtain ⟨g, c, hc, hg⟩ := exists_sl_of_square_det (A * T) hAT
      ((quadraticChar_one_iff_isSquare hAT).mp hsq)
    have hd' : normalizedRow d ᵥ* (A * T) = a • normalizedRow (some 1) := by
      rw [← Matrix.vecMul_vecMul, hd, Matrix.smul_vecMul, hT0]
    have he' : normalizedRow e ᵥ* (A * T) = (b * -1) • normalizedRow none := by
      rw [← Matrix.vecMul_vecMul, he, Matrix.smul_vecMul, hTInfinity, smul_smul]
    have hf' : normalizedRow f ᵥ* (A * T) = (1 : F23) • normalizedRow (some 0) := by
      rw [← Matrix.vecMul_vecMul, hf, hT1, one_smul]
    have h1 := projectiveStep_of_scaled_row hg hc ha hd'
    have hInfinity := projectiveStep_of_scaled_row hg hc (mul_ne_zero hb (neg_ne_zero.mpr one_ne_zero)) he'
    have h0 := projectiveStep_of_scaled_row hg hc one_ne_zero hf'
    refine ⟨g, ?_⟩
    simp only [Finset.image_insert, Finset.image_singleton, h1, hInfinity, h0]
    rw [Finset.insert_comm (some (1 : F23)) none,
      Finset.pair_comm (some (1 : F23)) (some 0)]

/-- In the actual Paley order, the seed directions have indices `23`, `0` and `1`. -/
theorem exists_paleyPerm_image_triple (s : Finset (Fin 24)) (hs : s.card = 3) :
    ∃ g : SL23, s.image (paleyPerm g) = {23, 0, 1} := by
  have hcard : (s.image directionEquiv).card = 3 :=
    (Finset.card_image_of_injective s directionEquiv.injective).trans hs
  obtain ⟨g, hg⟩ := exists_projectiveStep_image_triple (s.image directionEquiv) hcard
  have haction : (s.image (paleyPerm g)).image directionEquiv =
      (s.image directionEquiv).image (fun d => (projectiveStep g d).1) := by
    simp only [Finset.image_image]
    apply congrArg (fun h : Fin 24 → Direction => s.image h)
    funext d
    exact paleyDirection_perm g d
  have h23 : directionEquiv 23 = none := rfl
  have h0 : directionEquiv 0 = some 0 := rfl
  have h1 : directionEquiv 1 = some 1 := rfl
  refine ⟨g, (Finset.image_inj directionEquiv.injective).mp ?_⟩
  simp only [haction, hg, Finset.image_insert, Finset.image_singleton, h23, h0, h1]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleyTripleNormalization
