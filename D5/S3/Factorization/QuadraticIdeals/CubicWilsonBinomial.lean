/- GID: D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wilson's binomial cube determines the conjugate primary cubic symbols. -/

import D5.S3.CharacterSums.CubicEulerWilson
import D5.S3.Factorization.QuadraticIdeals.CubicGaussFrobenius

/-! The imported CubicEulerWilson module supplies
its finite-field sum and factorial-cube identities; none is reproved here.
The actual Jacobi-star reduction and both conjugate-primary symbols are derived
in the original quotient, without a conjugate-field isomorphism.

The arithmetic endpoints require prime residue cardinalities explicitly.
The generic identities retain their own separately stated scopes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Factorization.QuadraticIdeals.CubicWilsonBinomial

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization
open D5.S3.Factorization.QuadraticIdeals.CubicGaussFrobenius
open D5.S3.CharacterSums.CubicEulerWilson

abbrev E := EisensteinOrder

private theorem factorial_cast_ne_zero_of_lt
    {F : Type*} [Field F] (p m : ℕ) [Fact p.Prime] [CharP F p]
    (hmp : m < p) : (m.factorial : F) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ m.factorial := (CharP.cast_eq_zero_iff F p m.factorial).mp hzero
  exact (not_le_of_gt hmp) ((Fact.out : p.Prime).dvd_factorial.mp hdvd)

/-- Reduce the conjugate Jacobi sum in the original quotient E/P.
There is no conjugate-quotient identification in this statement or proof. -/
theorem cubicJacobiSum_star_reduction
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    letI : Fintype (E ⧸ P) := Fintype.ofFinite _
    Ideal.Quotient.mk P
      (star (jacobiSum (cubicResidueMulChar P hcard hthree)
        (cubicResidueMulChar P hcard hthree))) =
      ∑ x : E ⧸ P,
        x ^ (2 * ((Nat.card (E ⧸ P) - 1) / 3)) *
          (1 - x) ^ (2 * ((Nat.card (E ⧸ P) - 1) / 3)) := by
  classical
  let : Field (E ⧸ P) := Ideal.Quotient.field P
  let : Fintype (E ⧸ P) := Fintype.ofFinite _
  let χ := cubicResidueMulChar P hcard hthree
  have hsq : χ⁻¹ = χ ^ 2 := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, cubicResidueMulChar_cube P hcard hthree]
  have hsχ : χ.ringHomComp (starRingEnd E) = χ⁻¹ :=
    cubicResidueMulChar_star P hcard hthree
  have hs : star (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹ := by
    simpa only [starRingEnd_apply, hsχ] using
      (jacobiSum_ringHomComp χ χ (starRingEnd E)).symm
  change Ideal.Quotient.mk P (star (jacobiSum χ χ)) = _
  rw [hs, hsq]
  simp only [jacobiSum, map_sum, map_mul,
    MulChar.pow_apply' χ (by decide : 2 ≠ 0), map_pow]
  dsimp only [χ]
  simp only [cubicResidueMulChar_reduction P hcard hthree, ← pow_mul, Nat.mul_comm]

private theorem cubic_index_even (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    Even ((p - 1) / 3) := by
  have hpne : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hpne
  have hpm : p = 3 * ((p - 1) / 3) + 1 := by omega
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
  omega

/-- The actual primary generator's conjugate is an explicit nonzero-factorial
cube after reduction in P. The Jacobi normalization is consumed internally. -/
theorem primary_conjugate_reduction_eq_factorial_cube
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (p : ℕ) [Fact p.Prime] (hPcard : Nat.card (E ⧸ P) = p) (hp : p % 3 = 1)
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1) :
    letI : Field (E ⧸ P) := Ideal.Quotient.field P
    let m := (p - 1) / 3
    Ideal.Quotient.mk P (star π) = (-((m.factorial : E ⧸ P)⁻¹)) ^ 3 := by
  classical
  let : Field (E ⧸ P) := Ideal.Quotient.field P
  let : Fintype (E ⧸ P) := Fintype.ofFinite _
  let : CharP (E ⧸ P) p :=
    charP_of_card_eq_prime (by simpa only [Fintype.card_eq_nat_card] using hPcard)
  let m := (p - 1) / 3
  have hpm : p = 3 * m + 1 := by dsimp [m]; omega
  have hm : Even m := cubic_index_even p hp
  let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
  have hPmod : Nat.card (E ⧸ P) % 3 = 1 := by omega
  let χ := cubicResidueMulChar P hPmod hPthree
  have HJ : -(jacobiSum χ χ) = π :=
    cubicJacobiSum_eq_primary_generator P hPmod hPthree π hπ hπprimary
  have Hred := cubicJacobiSum_star_reduction P hPmod hPthree
  rw [hPcard] at Hred
  change Ideal.Quotient.mk P (star (jacobiSum χ χ)) =
    ∑ x : E ⧸ P, x ^ (2 * m) * (1 - x) ^ (2 * m) at Hred
  have Hsum := sum_double_cubic_euler (E ⧸ P) m
    (by rw [Fintype.card_eq_nat_card, hPcard, hpm]) hm
  have Hwilson := neg_binomial_eq_inverse_factorial_cube
    (F := E ⧸ P) p m hpm hm
  have Hcube : Ideal.Quotient.mk P (star (jacobiSum χ χ)) =
      ((m.factorial : E ⧸ P)⁻¹) ^ 3 := Hred.trans (Hsum.trans Hwilson)
  rw [← HJ, star_neg, map_neg, Hcube]
  ring

/-- The conjugate-primary symbol is one. The cube witness, its nonvanishing,
and the Jacobi value are all derived, not hypotheses of this endpoint. -/
theorem cubic_character_conjugate_primary_eq_one
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (p : ℕ) [Fact p.Prime] (hPcard : Nat.card (E ⧸ P) = p) (hp : p % 3 = 1)
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1) :
    let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
    let χ := cubicResidueMulChar P (by omega : Nat.card (E ⧸ P) % 3 = 1) hPthree
    χ (Ideal.Quotient.mk P (star π)) = 1 := by
  classical
  let : Field (E ⧸ P) := Ideal.Quotient.field P
  let : Fintype (E ⧸ P) := Fintype.ofFinite _
  let : CharP (E ⧸ P) p :=
    charP_of_card_eq_prime (by simpa only [Fintype.card_eq_nat_card] using hPcard)
  let m := (p - 1) / 3
  let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
  have hPmod : Nat.card (E ⧸ P) % 3 = 1 := by omega
  let χ := cubicResidueMulChar P hPmod hPthree
  have hm3 : 3 * m = p - 1 := by dsimp [m]; omega
  have hmp : m < p := by dsimp [m]; have := (Fact.out : p.Prime).two_le; omega
  have hfac : (m.factorial : E ⧸ P) ≠ 0 :=
    factorial_cast_ne_zero_of_lt p m hmp
  let y : E ⧸ P := -((m.factorial : E ⧸ P)⁻¹)
  have hy : y ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hfac)
  have Hcube := primary_conjugate_reduction_eq_factorial_cube
    P p hPcard hp π hπ hπprimary
  change Ideal.Quotient.mk P (star π) = y ^ 3 at Hcube
  have hinput : Ideal.Quotient.mk P (star π) ≠ 0 := by
    rw [Hcube]
    exact pow_ne_zero _ hy
  have hyfermat : y ^ (p - 1) = 1 := by
    simpa only [Fintype.card_eq_nat_card, hPcard] using
      FiniteField.pow_card_sub_one_eq_one y hy
  have hpower : Ideal.Quotient.mk P (star π) ^ m = 1 := by
    rw [Hcube, ← pow_mul, hm3]
    exact hyfermat
  have Hred := cubicResidueMulChar_reduction P hPmod hPthree
    (Ideal.Quotient.mk P (star π))
  rw [hPcard] at Hred
  change Ideal.Quotient.mk P (χ (Ideal.Quotient.mk P (star π))) =
    Ideal.Quotient.mk P (star π) ^ m at Hred
  have h3 : Ideal.Quotient.mk P (3 : E) ≠ 0 := by
    intro h
    exact hPthree (Ideal.Quotient.eq_zero_iff_mem.mp h)
  apply cubic_roots_injective (Ideal.Quotient.mk P) h3
    (z := χ (Ideal.Quotient.mk P (star π))) (z' := 1)
    (residueCubicValue_mem_roots P hPmod hPthree _ hinput) (Or.inl rfl)
  simpa only [map_one] using Hred.trans hpower

/-- Apply the same-quotient theorem separately at each conjugate generator.
The prime-cardinality data for both quotients is explicit; no transport of
characters or quotient-field isomorphism is used to prove either equality. -/
theorem conjugate_primary_symbol_pair
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (p : ℕ) [Fact p.Prime]
    (hPcard : Nat.card (E ⧸ P) = p) (hQcard : Nat.card (E ⧸ Q) = p)
    (hp : p % 3 = 1) (π : E)
    (hπ : Ideal.span {π} = P) (hQ : Ideal.span {star π} = Q)
    (hπprimary : (3 : E) ∣ π - 1) :
    let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
    let hQthree := three_not_mem_of_residue_prime_card Q p hQcard hp
    let χP := cubicResidueMulChar P (by omega : Nat.card (E ⧸ P) % 3 = 1) hPthree
    let χQ := cubicResidueMulChar Q (by omega : Nat.card (E ⧸ Q) % 3 = 1) hQthree
    χP (Ideal.Quotient.mk P (star π)) = 1 ∧ χQ (Ideal.Quotient.mk Q π) = 1 := by
  classical
  have hbarprimary : (3 : E) ∣ star π - 1 := by
    obtain ⟨z, hz⟩ := hπprimary
    refine ⟨star z, ?_⟩
    have H := congrArg (starRingEnd E) hz
    simpa only [map_sub, map_one, map_mul, map_natCast, map_ofNat, starRingEnd_apply] using H
  constructor
  · exact cubic_character_conjugate_primary_eq_one P p hPcard hp π hπ hπprimary
  · have H := cubic_character_conjugate_primary_eq_one Q p hQcard hp
      (star π) hQ hbarprimary
    simpa only [star_star] using H

end D5.S3.Factorization.QuadraticIdeals.CubicWilsonBinomial
