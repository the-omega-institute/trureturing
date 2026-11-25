/- GID: D5/S3/Quantum/AURICOmega/RationalUnitTripleGram
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/RationalUnitTripleGram
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Classify rational three-point unit Gram realizations in five coordinates. -/

import D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex
import D5.S3.Quantum.AURICOmega.OmegaShadowBridge
import D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary
import D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LinearCombination
import D5.S0.Algebra.Quaternion

open scoped Quaternion
open Quaternion
open D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex (rational_unit_reflection)
open D5.S3.Quantum.AURICOmega.OmegaShadowBridge
  (toStdInt toStdInt_add toStdInt_mul toStdInt_neg)
open D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary (fromInt to_fromInt)
open D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint (four_rational_squares)

namespace D5.S3.Quantum.AURICOmega.RationalUnitTripleGram

private noncomputable def readQuaternion (x : Omega.Quaternion) : ℍ[ℚ] :=
  ⟨toStdInt x.w, toStdInt x.x, toStdInt x.y, toStdInt x.z⟩

private theorem clearQuaternionDenominators (x : ℍ[ℚ]) :
    ∃ a : Omega.Quaternion, ∃ d : ℚ, x = d⁻¹ • readQuaternion a := by
  let m (q : ℚ) : ℚ := q.den
  have nz (q : ℚ) : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  let d := m x.re * m x.imI * m x.imJ * m x.imK
  let a : Omega.Quaternion :=
    ⟨fromInt (x.re.num * x.imI.den * x.imJ.den * x.imK.den),
     fromInt (x.imI.num * x.re.den * x.imJ.den * x.imK.den),
     fromInt (x.imJ.num * x.re.den * x.imI.den * x.imK.den),
     fromInt (x.imK.num * x.re.den * x.imI.den * x.imJ.den)⟩
  refine ⟨a, d, ?_⟩
  ext <;> simp only [readQuaternion, Quaternion.re_smul, Quaternion.imI_smul,
    Quaternion.imJ_smul, Quaternion.imK_smul, smul_eq_mul, a, to_fromInt, Int.cast_mul,
    Int.cast_natCast] <;> dsimp only [d, m]
  · conv_lhs => rw [← Rat.num_div_den x.re]
    field_simp [nz]
  · conv_lhs => rw [← Rat.num_div_den x.imI]
    field_simp [nz]
  · conv_lhs => rw [← Rat.num_div_den x.imJ]
    field_simp [nz]
  · conv_lhs => rw [← Rat.num_div_den x.imK]
    field_simp [nz]

private theorem readQuaternion_dot (a b : Omega.Quaternion) :
    (toStdInt (a.dot b) : ℚ) = (star (readQuaternion a) * readQuaternion b).re := by
  simp only [Omega.Quaternion.dot, toStdInt_add, toStdInt_mul]
  push_cast
  simp [readQuaternion]
  ring

private theorem readQuaternion_norm (a : Omega.Quaternion) :
    (toStdInt (a.dot a) : ℚ) = normSq (readQuaternion a) := by
  rw [readQuaternion_dot, star_mul_self, re_coe]

private theorem scaledQuaternion_dot (d e : ℚ) (x y : ℍ[ℚ]) :
    (star (d • x) * (e • y)).re = d * e * (star x * y).re := by
  rw [Quaternion.star_smul, smul_mul_assoc, mul_smul_comm, re_smul, re_smul]
  simp [smul_eq_mul, mul_assoc]

private theorem rationalQuaternionGramDet (x y : ℍ[ℚ]) :
    ∃ i j k : ℚ, normSq x * normSq y - (star x * y).re^2 = i^2 + j^2 + k^2 := by
  obtain ⟨a, d, hx⟩ := clearQuaternionDenominators x
  obtain ⟨b, e, hy⟩ := clearQuaternionDenominators y
  let q := a.conj.mul b
  let determinant := ((a.dot a).mul (b.dot b)).sub (Omega.Int.square (a.dot b))
  have hz : determinant =
      ((Omega.Int.square q.x).add (Omega.Int.square q.y)).add (Omega.Int.square q.z) := by
    exact Omega.Eq.rec (motive := fun result _ => determinant = result) rfl
      (Omega.Quaternion.gramDet_eq_imaginary_squares a b)
  have h := congrArg (fun z : Omega.Int => (toStdInt z : ℚ)) hz
  have readSub (u v : Omega.Int) : toStdInt (u.sub v) = toStdInt u - toStdInt v := by
    change toStdInt (u.add v.neg) = _
    rw [toStdInt_add, toStdInt_neg, sub_eq_add_neg]
  simp only [determinant, Omega.Int.square, readSub, toStdInt_add, toStdInt_mul,
    Int.cast_add, Int.cast_mul, Int.cast_sub] at h
  rw [readQuaternion_norm, readQuaternion_norm, readQuaternion_dot] at h
  refine ⟨d⁻¹ * e⁻¹ * toStdInt q.x, d⁻¹ * e⁻¹ * toStdInt q.y, d⁻¹ * e⁻¹ * toStdInt q.z, ?_⟩
  rw [hx, hy, normSq_smul, normSq_smul, scaledQuaternion_dot]
  linear_combination d⁻¹ ^ 2 * e⁻¹ ^ 2 * h

private theorem rationalQuaternionGramExtension (x : ℍ[ℚ]) (hx : x ≠ 0) (u k : ℚ) :
    (∃ y : ℍ[ℚ], normSq y = u ∧ (star x * y).re = k) ↔
    (∃ a b c : ℚ, normSq x * u - k^2 = a^2 + b^2 + c^2) := by
  constructor
  · rintro ⟨y, hy, hk⟩
    simpa only [hy, hk] using rationalQuaternionGramDet x y
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
  obtain ⟨a, b, c, d, h⟩ := four_rational_squares t ht
  exact ⟨⟨a, b, c, d⟩, by simpa only [Quaternion.normSq_def'] using h⟩

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

/-- For rational first-anchor inner products with absolute values at most one,
three rational pairwise inner products are realized by unit vectors in five
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
