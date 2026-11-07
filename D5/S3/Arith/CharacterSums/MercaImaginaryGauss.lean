/- GID: D5/S3/Arith/CharacterSums/MercaImaginaryGauss
   generality: I
   mirror-B: D5/B/S3/Arith/CharacterSums/MercaImaginaryGauss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed Gauss sum at the genuine negative discriminant minus four r. -/

import D5.S3.Arith.CharacterSums.MercaPositiveGauss
import D5.S3.Analytic.Zeta.MercaImaginaryCharacter

/-! The signed composite-conductor Gauss sum factors through literal CRT representatives. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.MercaImaginaryGauss
open D5.S3.Analytic.Zeta MercaImaginaryCharacter PrimeQuadraticLValues

private def param (r : ℕ) (x : ZMod 4 × ZMod r) : ZMod (4 * r) :=
  ((r * x.1.val + 4 * x.2.val : ℕ) : ZMod (4 * r))

private lemma r_mod_four (r : ℕ) (hr : r % 8 = 5) : (r : ZMod 4) = 1 := by
  rw [← ZMod.natCast_mod r 4, show r % 4 = 1 by omega]
  rfl

private def paramEquiv (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    ZMod 4 × ZMod r ≃ ZMod (4 * r) := by
  apply Equiv.ofBijective (param r)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y he
    have h4 := congrArg (ZMod.castHom (dvd_mul_right 4 r) (ZMod 4)) he
    have hr' := congrArg (ZMod.castHom (dvd_mul_left r 4) (ZMod r)) he
    have h2 : (2 : ZMod r) ≠ 0 :=
      Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr (by omega))
    have hfour : (4 : ZMod r) ≠ 0 := by
      convert pow_ne_zero 2 h2 using 1 <;> norm_num
    have hx : x.1 = y.1 := by
      simpa only [param, map_add, map_mul, map_natCast, map_ofNat, Nat.cast_add, Nat.cast_mul, r_mod_four r hr,
        ZMod.natCast_self, one_mul, zero_mul, add_zero, ZMod.natCast_zmod_val] using h4
    have hy : x.2 = y.2 := by
      apply mul_left_cancel₀ hfour
      simpa only [param, map_add, map_mul, map_natCast, map_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self,
        zero_mul, zero_add, ZMod.natCast_zmod_val] using hr'
    exact Prod.ext hx hy
  · simp

private lemma character_param (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (x : ZMod 4) (y : ZMod r) :
    character r (param r (x, y)) =
      (ZMod.χ₄ x : ℂ) * primeCharacter r y := by
  have he : param r (x, y) =
      ((r * x.val + 4 * y.val : ℕ) : ℤ) := by simp [param]
  rw [he, character_int]
  have h4 : ZMod.χ₄ ((r * x.val + 4 * y.val : ℕ) : ℤ) = ZMod.χ₄ x := by
    congr 1
    change ((r * x.val + 4 * y.val : ℕ) : ZMod 4) = x
    simp only [Nat.cast_add, Nat.cast_mul, r_mod_four r hr,
      ZMod.natCast_self, one_mul, zero_mul, add_zero, ZMod.natCast_zmod_val]
  have hleg : legendreSym r ((r * x.val + 4 * y.val : ℕ) : ℤ) =
      quadraticChar (ZMod r) y := by
    simp only [legendreSym, Int.cast_natCast]
    change quadraticChar (ZMod r) (((r * x.val + 4 * y.val : ℕ) : ZMod r)) = _
    simp only [Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self,
      zero_mul, zero_add, ZMod.natCast_zmod_val, map_mul]
    have htwo : (2 : ZMod r) ≠ 0 :=
      Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr (by omega))
    have hfour : quadraticChar (ZMod r) (4 : ZMod r) = 1 := by
      apply (quadraticChar_one_iff_isSquare (by
        convert pow_ne_zero 2 htwo using 1 <;> norm_num)).mpr
      exact ⟨2, by ring⟩
    rw [hfour, one_mul]
  rw [h4, hleg]
  rfl

private lemma additive_param (r : ℕ) [Fact r.Prime]
    (x : ZMod 4) (y : ZMod r) :
    ZMod.stdAddChar (param r (x, y)) =
      ZMod.stdAddChar x * ZMod.stdAddChar y := by
  have he : param r (x, y) =
      ((r * x.val + 4 * y.val : ℕ) : ℤ) := by simp [param]
  rw [he, ZMod.stdAddChar_coe]
  conv_rhs => arg 1; rw [show x = (x.val : ℤ) by simp, ZMod.stdAddChar_coe]
  conv_rhs => arg 2; rw [show y = (y.val : ℤ) by simp, ZMod.stdAddChar_coe]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero]
  <;> ring

private lemma four_gauss :
    (∑ x : ZMod 4, (ZMod.χ₄ x : ℂ) * ZMod.stdAddChar x) = 2 * Complex.I := by
  have h1 : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
    rw [show (1 : ZMod 4) = ((1 : ℤ) : ZMod 4) by norm_num, ZMod.stdAddChar_coe]
    convert Complex.exp_pi_div_two_mul_I using 1 <;> congr 1 <;> ring
  have h3 : ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
    rw [show (3 : ZMod 4) = -1 by decide, AddChar.map_neg_eq_inv, h1]
    simp
  have he (f : ZMod 4 → ℂ) : ∑ x, f x = f 0 + f 1 + f 2 + f 3 :=
    Fin.sum_univ_four f
  rw [he]
  norm_num [ZMod.χ₄, h1, h3]
  ring

/-- The Gauss sum has the positive imaginary sign at the actual conductor 4r. -/
theorem gauss_sum (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    gaussSum (character r) ZMod.stdAddChar =
      2 * Complex.I * (Real.sqrt r : ℂ) := by
  classical
  unfold gaussSum
  rw [← Equiv.sum_comp (paramEquiv r hr)]
  change (∑ x : ZMod 4 × ZMod r,
    character r (param r x) * ZMod.stdAddChar (param r x)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [character_param r hr, additive_param r]
  calc
    _ = (∑ x : ZMod 4, (ZMod.χ₄ x : ℂ) * ZMod.stdAddChar x) *
        (∑ y : ZMod r, primeCharacter r y * ZMod.stdAddChar y) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      rw [four_gauss]
      change (2 * Complex.I) * gaussSum (primeCharacter r) ZMod.stdAddChar = _
      rw [MercaPositiveGauss.prime_gauss_sum r hr]

end D5.S3.Arith.CharacterSums.MercaImaginaryGauss
