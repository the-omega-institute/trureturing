/- GID: D5/S3/Analytic/Zeta/MercaImaginaryCharacter
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/MercaImaginaryCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The genuine primitive odd quadratic character of conductor four times the Merca prime. -/

import D5.S3.Analytic.Zeta.PrimeQuadraticLValues
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
The conductor is proved from coprime local conductors. The discriminant character
is the product of the classical character modulo four and the Legendre character;
its values are not defined from a class number or finite norm checker.
-/
set_option autoImplicit false
noncomputable section

namespace D5.S3.Analytic.Zeta.MercaImaginaryCharacter
open DirichletCharacter PrimeQuadraticLValues

private def fourCharacter : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

private lemma four_odd : fourCharacter.Odd := by
  change ((ZMod.χ₄ (-1) : ℤ) : ℂ) = -1
  rw [show (-1 : ZMod 4) = 3 by decide]
  norm_num [ZMod.χ₄]

private lemma four_primitive : fourCharacter.IsPrimitive := by
  have hc := fourCharacter.conductor_dvd_level
  have hmem : fourCharacter.conductor ∈ Nat.divisors 4 :=
    Nat.mem_divisors.mpr ⟨hc, by decide⟩
  rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hnot (hdc : fourCharacter.conductor ∣ 2) : False := by
    have hf := fourCharacter.factorsThrough_conductor.mono fourCharacter
      hdc (by decide : 2 ∣ 4)
    obtain ⟨hd, χ, he⟩ := hf
    have hv := congrArg (fun ψ : DirichletCharacter ℂ 4 => ψ ((-1 : ℤ) : ZMod 4)) he
    have hodd0 : fourCharacter (-1) = -1 := four_odd
    have hodd : fourCharacter ((-1 : ℤ) : ZMod 4) = -1 := by
      simpa only [Int.cast_neg, Int.cast_one] using hodd0
    rw [hodd, changeLevel_eq_cast_of_dvd' χ hd isCoprime_one_left.neg_left,
      show ((-1 : ℤ) : ZMod 2) = 1 by decide, map_one] at hv
    norm_num at hv
  rcases hmem with h | h | h
  · exact (hnot (by rw [h]; decide)).elim
  · exact (hnot (by rw [h])).elim
  · exact h

private lemma conductor_mul_coprime {N : ℕ} [NeZero N]
    (α β : DirichletCharacter ℂ N) (hc : α.conductor.Coprime β.conductor) :
    (α * β).conductor = α.conductor * β.conductor := by
  have ha := conductor_mul_dvd_lcm_conductor (α * β) β⁻¹
  simp only [mul_inv_cancel_right, conductor_inv] at ha
  have ha' : α.conductor ∣ (α * β).conductor :=
    hc.dvd_of_dvd_mul_right (ha.trans (Nat.lcm_dvd_mul _ _))
  have hb := conductor_mul_dvd_lcm_conductor (α * β) α⁻¹
  have he : (α * β) * α⁻¹ = β := by
    calc
      _ = β * (α * α⁻¹) := by ac_rfl
      _ = β := by rw [mul_inv_cancel, mul_one]
  rw [he, conductor_inv] at hb
  have hb' : β.conductor ∣ (α * β).conductor :=
    hc.symm.dvd_of_dvd_mul_right (hb.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm
    ((conductor_mul_dvd_lcm_conductor α β).trans (hc.lcm_eq_mul ▸ dvd_rfl))
    (hc.mul_dvd_of_dvd_of_dvd ha' hb')

variable (r : ℕ) [Fact r.Prime]

/-- The actual Dirichlet character at modulus four times r. -/
def character : DirichletCharacter ℂ (4 * r) :=
  changeLevel (dvd_mul_right 4 r) fourCharacter *
    changeLevel (dvd_mul_left r 4) (primeCharacter r)

/-- Its literal values at every integer, including all nonunits. -/
theorem character_int (a : ℤ) :
    character r a = (ZMod.χ₄ a : ℂ) * (legendreSym r a : ℂ) := by
  by_cases ha : IsCoprime a (4 * r : ℕ)
  · rw [character, MulChar.mul_apply,
      changeLevel_eq_cast_of_dvd' fourCharacter _ ha,
      changeLevel_eq_cast_of_dvd' (primeCharacter r) _ ha]
    rfl
  · rw [(character r).apply_eq_zero_iff a |>.mpr ha]
    have hsplit : ¬IsCoprime a (4 : ℤ) ∨ ¬IsCoprime a (r : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, IsCoprime.mul_right_iff, not_and_or] using ha
    rcases hsplit with h4 | hr
    · have hz := (fourCharacter.apply_eq_zero_iff a).mpr h4
      change (ZMod.χ₄ a : ℂ) = 0 at hz
      rw [hz, zero_mul]
    · have hz := ((primeCharacter r).apply_eq_zero_iff a).mpr hr
      change (legendreSym r a : ℂ) = 0 at hz
      rw [hz, mul_zero]

/-- Primitive conductor, quadraticity, oddness and nonprincipality on the full domain. -/
theorem character_properties (hr : r % 8 = 5) :
    (character r).IsPrimitive ∧ (character r).IsQuadratic ∧
      (character r).Odd ∧ character r ≠ 1 := by
  have hr2 : r ≠ 2 := by omega
  have hc : Nat.Coprime 4 r := by
    have hc2 : Nat.Coprime 2 r := Nat.coprime_two_left.mpr
      (Nat.odd_iff.mpr (by omega))
    simpa using hc2.pow_left 2
  have hprim : (character r).IsPrimitive := by
    have h4c : fourCharacter.conductor = 4 := four_primitive
    have hrc : (primeCharacter r).conductor = r := primeCharacter_primitive r hr2
    dsimp [character, DirichletCharacter.IsPrimitive]
    rw [conductor_mul_coprime, conductor_changeLevel, conductor_changeLevel,
      h4c, hrc]
    simpa only [conductor_changeLevel, h4c, hrc] using hc
  have hquad : (character r).IsQuadratic := by
    have hfour : fourCharacter ^ 2 = 1 :=
      (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    dsimp [character]
    rw [mul_pow, ← map_pow, ← map_pow,
      hfour,
      (primeCharacter_quadratic r).sq_eq_one, map_one, map_one, one_mul]
  have hodd : (character r).Odd := by
    change character r (-1) = -1
    have hv := character_int r (-1)
    simp only [Int.cast_neg, Int.cast_one] at hv
    rw [hv]
    have h4 : ZMod.χ₄ (-1) = -1 := by
      rw [show (-1 : ZMod 4) = 3 by decide]
      norm_num [ZMod.χ₄]
    have hr4 : r % 4 = 1 := by omega
    have hleg : legendreSym r (-1) = 1 := by
      rw [legendreSym.at_neg_one hr2, ZMod.χ₄_nat_one_mod_four hr4]
    rw [h4, hleg]
    norm_num
  refine ⟨hprim, hquad, hodd, ?_⟩
  intro he
  have hv := hodd
  change character r (-1) = -1 at hv
  rw [he, MulChar.one_apply isUnit_neg_one] at hv
  norm_num at hv

end D5.S3.Analytic.Zeta.MercaImaginaryCharacter
