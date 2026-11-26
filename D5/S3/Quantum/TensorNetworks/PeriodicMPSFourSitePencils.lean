/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSitePencils
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSitePencils
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Intertwiners and triplet coordinates for the four-site periodic marginal. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteSextic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Compatible four-site flattenings admit a symmetric block and an antisymmetric line. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSitePencils

open PeriodicMPSParentIntersection (Bond)
open PeriodicMPSFourSiteSextic (fourFlattening fourFlattening_entries)
open scoped Matrix

noncomputable section

private lemma flattening_symmetric (A : Fin 2 → Bond) :
    (fourFlattening A).transpose = fourFlattening A := by
  rw [fourFlattening_entries A]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A compatible left flattening intertwines its observed Gram with the transpose Gram.
This holds for every actual competitor giving that observation. -/
theorem intertwines_gram (A : Fin 2 → Bond) (G : Matrix (Fin 4) (Fin 4) ℂ)
    (h : fourFlattening A * (fourFlattening A).conjTranspose = G) :
    G * fourFlattening A = fourFlattening A * G.transpose := by
  let F := fourFlattening A
  have hs : F.transpose = F := flattening_symmetric A
  have hh : F.conjTranspose.transpose = F.conjTranspose := by
    apply Matrix.ext
    intro i j
    exact congrArg star (congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M j i) hs)
  change F * F.conjTranspose = G at h
  change G * F = F * G.transpose
  rw [← h, Matrix.transpose_mul, hs, hh, Matrix.mul_assoc]

section Swap

variable (K : Type*) [Field K] [NeZero (2 : K)]

/-- Columns for the three symmetric vectors followed by the antisymmetric vector. -/
def swapBasis : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 1; 0, 1, 0, -1; 0, 0, 1, 0]

/-- Read the symmetric coefficients and the antisymmetric coefficient. -/
def swapCoordinates : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1 / 2, 1 / 2, 0; 0, 0, 0, 1; 0, 1 / 2, -1 / 2, 0]

private lemma two_nonzero : (2 : K) ≠ 0 := NeZero.ne _

/-- The basis change is invertible, with explicit inverse valid in odd characteristic. -/
theorem swapCoordinates_inverse :
    swapCoordinates K * swapBasis K = 1 ∧ swapBasis K * swapCoordinates K = 1 := by
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [swapCoordinates, swapBasis, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.one_apply] <;> field_simp [two_nonzero K] <;> ring

/-- The triplet block and the singlet coefficient in the unnormalized basis.
The singlet is the middle diagonal of the triplet minus twice its corner. -/
theorem swapCoordinates_cyclic (a b c d e f : K) :
    swapCoordinates K * !![a, b, b, c; b, d, c, e; b, c, d, e; c, e, e, f] * swapBasis K =
      !![a, 2 * b, c, 0; b, c + d, e, 0; c, 2 * e, f, 0; 0, 0, 0, d - c] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [swapCoordinates, swapBasis, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [two_nonzero K] <;> ring

end Swap

/-- Every intertwiner between diagonal matrices with the same three distinct eigenvalues
has diagonal entries given by one quadratic polynomial in the eigenvalues. -/
theorem commute_diagonal_eq_quadratic {K : Type*} [Field K] (values : Fin 3 → K)
    (hvalues : Function.Injective values) (T : Matrix (Fin 3) (Fin 3) K)
    (hT : Matrix.diagonal values * T = T * Matrix.diagonal values) :
    ∃ a b c : K, T = a • (1 : Matrix (Fin 3) (Fin 3) K) +
      b • Matrix.diagonal values + c • (Matrix.diagonal values) ^ 2 := by
  let V := Matrix.vandermonde values
  have hV : IsUnit V.det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hvalues)
  let v : Fin 3 → K := fun i => T i i
  let coeff := V⁻¹ *ᵥ v
  have hcoeff : V *ᵥ coeff = v := by
    change V *ᵥ (V⁻¹ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hV, Matrix.one_mulVec]
  refine ⟨coeff 0, coeff 1, coeff 2, Matrix.ext fun i j => ?_⟩
  rw [Matrix.diagonal_pow]
  by_cases hij : i = j
  · subst j
    have hi := congrFun hcoeff i
    simp only [Matrix.mulVec, dotProduct, V, Matrix.vandermonde_apply,
      Fin.sum_univ_three, v] at hi
    change values i ^ 0 * coeff 0 + values i ^ 1 * coeff 1 +
      values i ^ 2 * coeff 2 = T i i at hi
    simp only [pow_zero, pow_one, one_mul] at hi
    simpa only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq, Pi.pow_apply, smul_eq_mul, mul_one, mul_comm (coeff 1),
      mul_comm (coeff 2)] using hi.symm
  · have hij' := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) hT
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij'
    have hzero : T i j = 0 := by
      apply (mul_eq_zero.mp (show (values i - values j) * T i j = 0 by
        rw [sub_mul, mul_comm (values j), sub_eq_zero]
        exact hij')).resolve_left
      exact sub_ne_zero.mpr (fun h => hij (hvalues h))
    simp [hzero, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

/-- A triplet intertwiner is in the pencil generated by an invertible reference
intertwiner and its first two left translates by the Gram triplet. -/
theorem triplet_intertwiner_pencil {K : Type*} [Field K]
    (G G' F : Matrix (Fin 3) (Fin 3) K) (F₀ S : (Matrix (Fin 3) (Fin 3) K)ˣ)
    (values : Fin 3 → K) (hvalues : Function.Injective values)
    (hG : S.val * Matrix.diagonal values * S.inv = G)
    (hF₀ : G * F₀.val = F₀.val * G') (hF : G * F = F * G') :
    ∃ a b c : K, F = (a • (1 : Matrix (Fin 3) (Fin 3) K) + b • G + c • G ^ 2) * F₀.val := by
  have hS₀ : S.inv * S.val = 1 := S.inv_mul
  have hS₁ : S.val * S.inv = 1 := S.mul_inv
  have hF₁ : F₀.val * F₀.inv = 1 := F₀.mul_inv
  have hF₂ : F₀.inv * F₀.val = 1 := F₀.inv_mul
  let D := Matrix.diagonal values
  let P := F * F₀.inv
  have hrev : G' * F₀.inv = F₀.inv * G := by
    calc
      G' * F₀.inv = F₀.inv * (F₀.val * G' * F₀.inv) := by
        simp only [← mul_assoc, hF₂, one_mul]
      _ = F₀.inv * G := by
        rw [← hF₀, mul_assoc G, hF₁, mul_one]
  have hP : G * P = P * G := by
    dsimp only [P]
    rw [← mul_assoc, hF, mul_assoc, hrev, ← mul_assoc]
  have hl : D * S.inv = S.inv * G := by
    rw [← hG, ← mul_assoc, ← mul_assoc, hS₀, one_mul]
  have hr : S.val * D = G * S.val := by
    rw [← hG, mul_assoc (S.val * D), hS₀, mul_one]
  let T := S.inv * P * S.val
  have ht : D * T = T * D := by
    calc
      D * T = (D * S.inv) * P * S.val := by simp only [T, mul_assoc]
      _ = S.inv * (G * P) * S.val := by rw [hl, mul_assoc (S.inv)]
      _ = S.inv * (P * G) * S.val := by rw [hP]
      _ = (S.inv * P) * (G * S.val) := by simp only [mul_assoc]
      _ = T * D := by rw [← hr]; simp only [T, mul_assoc]
  obtain ⟨a, b, c, hc⟩ := commute_diagonal_eq_quadratic values hvalues T ht
  have hT : S.val * T * S.inv = P := by
    dsimp only [T]
    rw [← mul_assoc (S.val), ← mul_assoc (S.val), hS₁, one_mul,
      mul_assoc P, hS₁, mul_one]
  have hD₂ : S.val * D ^ 2 * S.inv = G ^ 2 := by
    rw [← hG, pow_two, pow_two]
    simp only [D, mul_assoc, ← mul_assoc S.inv,
      hS₀, one_mul]
  have hD₁ : S.val * D * S.inv = G := hG
  have hP' : P = a • (1 : Matrix (Fin 3) (Fin 3) K) + b • G + c • G ^ 2 := by
    rw [← hT, hc]
    change S.val * (a • (1 : Matrix (Fin 3) (Fin 3) K) + b • D + c • D ^ 2) * S.inv = _
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, hS₁, hD₁, hD₂]
  refine ⟨a, b, c, ?_⟩
  rw [← hP']
  simp only [P, mul_assoc, hF₂, mul_one]

/-- If two factors from the compatible triplet pencils multiply to a nonzero
multiple of the observed block, the second polynomial factor is a scalar multiple
of the adjugate of the first. -/
theorem triplet_partner_of_product {K : Type*} [Field K]
    (F₀ H₀ P Q : Matrix (Fin 3) (Fin 3) K) (c : K)
    (hcomm : Commute (F₀ * H₀) P) (hG : IsUnit (F₀ * H₀))
    (hP : P.det ≠ 0) (hprod : (P * F₀) * (H₀ * Q) = c • (F₀ * H₀)) :
    Q = (c / P.det) • P.adjugate := by
  obtain ⟨U, hU⟩ := hG
  have hUinv : U.inv * (↑U : Matrix (Fin 3) (Fin 3) K) = 1 := U.inv_mul
  have hcancel : P * Q = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have he : (F₀ * H₀) * (P * Q) = (F₀ * H₀) * (c • 1) := by
      calc
        (F₀ * H₀) * (P * Q) = ((F₀ * H₀) * P) * Q := by simp only [mul_assoc]
        _ = (P * F₀) * (H₀ * Q) := by rw [hcomm.eq]; simp only [mul_assoc]
        _ = (F₀ * H₀) * (c • 1) := by rw [hprod, Matrix.mul_smul, mul_one]
    rw [← hU] at he
    have hinv := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => U.inv * M) he
    simpa only [← mul_assoc, hUinv, one_mul] using hinv
  have hscale : P.det • Q = c • P.adjugate := by
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => P.adjugate * M) hcancel
    simpa only [← mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, one_mul,
      Matrix.mul_smul, mul_one] using he
  calc
    Q = P.det⁻¹ • (P.det • Q) := by rw [smul_smul, inv_mul_cancel₀ hP, one_smul]
    _ = (c / P.det) • P.adjugate := by rw [hscale, smul_smul, div_eq_mul_inv, mul_comm c]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSitePencils
