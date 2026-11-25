/- GID: D5/S3/Quantum/AURICOmega/RationalUnitTripleGram
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/RationalUnitTripleGram
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Classify rational three-point unit Gram realizations in five coordinates. -/

import D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LinearCombination

open scoped Quaternion
open Quaternion
open D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex (rational_unit_reflection)

namespace D5.S3.Quantum.AURICOmega.RationalUnitTripleGram

private theorem rationalQuaternionGramExtension (x : ℍ[ℚ]) (hx : x ≠ 0) (u k : ℚ) :
    (∃ y : ℍ[ℚ], normSq y = u ∧ (star x * y).re = k) ↔
    (∃ a b c : ℚ, normSq x * u - k^2 = a^2 + b^2 + c^2) := by
  constructor
  · rintro ⟨y, hy, hk⟩
    let q := star x * y
    refine ⟨q.imI, q.imJ, q.imK, ?_⟩
    have hq : normSq q = normSq x * u := by simp [q, map_mul, hy]
    change q.re = k at hk
    rw [Quaternion.normSq_def', hk] at hq
    linarith only [hq]
  · rintro ⟨a, b, c, h⟩
    let q : ℍ[ℚ] := ⟨k, a, b, c⟩
    let y := (star x)⁻¹ * q
    have hn : normSq x ≠ 0 := normSq_ne_zero.mpr hx
    have hq : normSq q = normSq x * u := by
      simp only [q, Quaternion.normSq_def'] at *
      linarith only [h]
    have hs : star x ≠ 0 := fun he => hx (by simpa using congrArg star he)
    refine ⟨y, ?_, ?_⟩
    · rw [show y = (star x)⁻¹ * q from rfl, map_mul, Quaternion.normSq_inv,
        Quaternion.normSq_star, hq, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    · rw [show y = (star x)⁻¹ * q from rfl, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

private theorem rationalQuaternionNorm (t : ℚ) (ht : 0 ≤ t) : ∃ x : ℍ[ℚ], normSq x = t := by
  have hn : 0 ≤ t.num := Rat.num_nonneg.mpr ht
  have hd : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  obtain ⟨i,j,k,l,h⟩ := Nat.sum_four_squares (t.num.toNat * t.den)
  let q : ℍ[ℚ] := ⟨i, j, k, l⟩
  have hq : normSq q = (t.num : ℚ) * (t.den : ℚ) := by
    have h' := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at h'
    rw [show ((t.num.toNat : ℕ) : ℚ) = (t.num : ℚ) by exact_mod_cast Int.toNat_of_nonneg hn] at h'
    simpa [q, normSq_def'] using h'
  refine ⟨(t.den : ℚ)⁻¹ • q, ?_⟩
  rw [normSq_smul, hq]
  conv_rhs => rw [← Rat.num_div_den t]
  field_simp

private theorem rationalAnchoredUnitTriple (a b c : ℚ) (ha : 0 ≤ 1 - a^2) (hb : 0 ≤ 1 - b^2) :
    (∃ x y : ℍ[ℚ], a^2 + normSq x = 1 ∧ b^2 + normSq y = 1 ∧
      a*b + (star x * y).re = c) ↔
    (∃ i j k : ℚ, 1 + 2*a*b*c - a^2 - b^2 - c^2 = i^2 + j^2 + k^2) := by
  let p := 1 - a^2
  let q := 1 - b^2
  let r := c - a*b
  have hdet : p*q - r^2 = 1 + 2*a*b*c - a^2 - b^2 - c^2 := by dsimp [p,q,r]; ring
  rw [← hdet]
  have normalize : (∃ x y : ℍ[ℚ], a^2 + normSq x = 1 ∧ b^2 + normSq y = 1 ∧
      a*b + (star x * y).re = c) ↔
      (∃ x y : ℍ[ℚ], normSq x = p ∧ normSq y = q ∧ (star x * y).re = r) := by
    simp only [p, q, r, eq_sub_iff_add_eq, add_comm]
  rw [normalize]
  by_cases hp : p = 0
  · rw [hp, zero_mul, zero_sub]
    constructor
    · rintro ⟨x, y, hx, _, hxy⟩
      rw [normSq_eq_zero] at hx
      have hr : r = 0 := by simpa [hx] using hxy.symm
      exact ⟨0, 0, 0, by simp [hr]⟩
    · rintro ⟨i, j, k, h⟩
      have hr : r = 0 := by nlinarith [sq_nonneg r, sq_nonneg i, sq_nonneg j, sq_nonneg k]
      obtain ⟨y, hy⟩ := rationalQuaternionNorm q hb
      exact ⟨0, y, map_zero _, hy, by simp [hr]⟩
  · constructor
    · rintro ⟨x,y,hx,hy,hxy⟩
      have hx0 : x ≠ 0 := normSq_ne_zero.mp (hx.symm ▸ hp)
      simpa [hx] using (rationalQuaternionGramExtension x hx0 q r).mp ⟨y,hy,hxy⟩
    · intro h
      obtain ⟨x,hx⟩ := rationalQuaternionNorm p ha
      have hx0 : x ≠ 0 := normSq_ne_zero.mp (hx.symm ▸ hp)
      obtain ⟨y,hy,hxy⟩ := (rationalQuaternionGramExtension x hx0 q r).mpr (by simpa [hx] using h)
      exact ⟨x,y,hx,hy,hxy⟩

open Matrix

private def asQuaternion (v : Fin 5 → ℚ) : ℍ[ℚ] := ⟨v 1, v 2, v 3, v 4⟩

private def fromQuaternion (a : ℚ) (x : ℍ[ℚ]) : Fin 5 → ℚ := ![a, x.re, x.imI, x.imJ, x.imK]

private theorem vector_dot_formula (v w : Fin 5 → ℚ) :
    v ⬝ᵥ w = v 0 * w 0 + (star (asQuaternion v) * asQuaternion w).re := by
  simp [dotProduct, Fin.sum_univ_succ, asQuaternion]
  ring

private theorem asQuaternion_fromQuaternion (a : ℚ) (x : ℍ[ℚ]) :
    asQuaternion (fromQuaternion a x) = x := by
  ext <;> rfl

private def firstBasisVector : Fin 5 → ℚ := fromQuaternion 1 0

private theorem dot_firstBasisVector (v : Fin 5 → ℚ) : firstBasisVector ⬝ᵥ v = v 0 := by
  rw [vector_dot_formula, firstBasisVector, asQuaternion_fromQuaternion]
  simp [fromQuaternion]

/-- Three rational pairwise inner products are realized by unit vectors in five
coordinates exactly when their Gram determinant is a sum of three rational squares. -/
theorem rationalFiveCoordinateUnitTriple (a b c : ℚ) (ha : 0 ≤ 1 - a^2) (hb : 0 ≤ 1 - b^2) :
    (∃ u v w : Fin 5 → ℚ, u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ w ⬝ᵥ w = 1 ∧
      u ⬝ᵥ v = a ∧ u ⬝ᵥ w = b ∧ v ⬝ᵥ w = c) ↔
    (∃ i j k : ℚ, 1 + 2*a*b*c - a^2 - b^2 - c^2 = i^2 + j^2 + k^2) := by
  rw [← rationalAnchoredUnitTriple a b c ha hb]
  have hu0 : firstBasisVector ⬝ᵥ firstBasisVector = 1 :=
    (dot_firstBasisVector _).trans rfl
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩
    obtain ⟨F, hF, h⟩ := rational_unit_reflection u firstBasisVector hu hu0
    have ha0 : F v 0 = a := by simpa [hF, dot_firstBasisVector, huv] using h u v
    have hb0 : F w 0 = b := by simpa [hF, dot_firstBasisVector, huw] using h u w
    refine ⟨asQuaternion (F v), asQuaternion (F w), ?_, ?_, ?_⟩
    · simpa only [vector_dot_formula (F v) (F v), ha0,
        star_mul_self, re_coe, ← pow_two, hv] using h v v
    · simpa only [vector_dot_formula (F w) (F w), hb0,
        star_mul_self, re_coe, ← pow_two, hw] using h w w
    · simpa only [vector_dot_formula (F v) (F w), ha0, hb0, hvw] using h v w
  · rintro ⟨x, y, hx, hy, hxy⟩
    refine ⟨firstBasisVector, fromQuaternion a x, fromQuaternion b y, hu0,
      ?_, ?_, dot_firstBasisVector _, dot_firstBasisVector _, ?_⟩
    · simpa only [vector_dot_formula, asQuaternion_fromQuaternion, star_mul_self, re_coe,
        show fromQuaternion a x 0 = a from rfl, ← pow_two] using hx
    · simpa only [vector_dot_formula, asQuaternion_fromQuaternion, star_mul_self, re_coe,
        show fromQuaternion b y 0 = b from rfl, ← pow_two] using hy
    · simpa only [vector_dot_formula, asQuaternion_fromQuaternion,
        show fromQuaternion a x 0 = a from rfl, show fromQuaternion b y 0 = b from rfl] using hxy

end D5.S3.Quantum.AURICOmega.RationalUnitTripleGram
