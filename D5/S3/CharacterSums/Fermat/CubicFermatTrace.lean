/- GID: D5/S3/CharacterSums/Fermat/CubicFermatTrace
   generality: I
   mirror-B: D5/B/S3/CharacterSums/Fermat/CubicFermatTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic Fermat counts equal field size plus one minus the primary trace. -/

import D5.S3.CharacterSums.Fermat.CharacterPointCount
import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.CharP.CharAndCard

/-! # Cubic Fermat point counts and the primary trace

The concrete complex embedding transports the Euler character and the proven
Jacobi normalization to the actual projective point count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.CharacterSums.Fermat.CubicFermatTrace

open D5.S3.CharacterSums.Fermat.CharacterPointCount
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient

abbrev E := EisensteinOrder

private def zeta3 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private theorem zeta3_quad : zeta3 * zeta3 = -1 - zeta3 := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [zeta3, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

/-- A concrete embedding fixes the same orientation throughout the count. -/
def eisensteinComplex : E →+* ℂ :=
  (QuadraticAlgebra.lift (R := ℤ) (a := -1) (b := -1)
    ⟨zeta3, by simpa [sub_eq_add_neg] using zeta3_quad⟩).toRingHom

theorem eisensteinComplex_re (z : E) :
    (eisensteinComplex z).re = (z.re : ℝ) - (z.im : ℝ) / 2 := by
  change (z.re • (1 : ℂ) + z.im • zeta3).re = _
  simp [zeta3, zsmul_eq_mul] <;> ring

theorem eisensteinComplex_im (z : E) :
    (eisensteinComplex z).im = (z.im : ℝ) * (Real.sqrt 3 / 2) := by
  change (z.re • (1 : ℂ) + z.im • zeta3).im = _
  simp [zeta3, zsmul_eq_mul]

theorem eisensteinComplex_injective : Function.Injective eisensteinComplex := by
  intro x y h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  rw [eisensteinComplex_im, eisensteinComplex_im] at hi
  rw [eisensteinComplex_re, eisensteinComplex_re] at hr
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hb : (x.im : ℝ) = (y.im : ℝ) := by nlinarith
  have ha : (x.re : ℝ) = (y.re : ℝ) := by linarith
  apply QuadraticAlgebra.ext
  · exact_mod_cast ha
  · exact_mod_cast hb

theorem twice_re_eisensteinComplex (z : E) :
    2 * (eisensteinComplex z).re = ((QuadraticAlgebra.trace z : ℤ) : ℝ) := by
  rw [eisensteinComplex_re]
  simp only [QuadraticAlgebra.trace_def, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one]
  ring

/-- The degree-three specialization counts the actual projective subtype. -/
theorem cubic_projective_count {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : orderOf χ = 3) :
    (Nat.card (projectivePoints F 3) : ℝ) =
      (Fintype.card F : ℝ) + 1 + 2 * (jacobiSum χ χ).re := by
  have hpow : χ ^ 2 = χ⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ]
    change χ ^ 3 = 1
    rw [← hχ, pow_orderOf_eq_one]
  have hcount := projective_point_count χ (d := 3) (by decide) hχ
  have hs : Finset.Ico 1 3 = ({1, 2} : Finset ℕ) := by decide
  have hc : (Nat.card (projectivePoints F 3) : ℂ) =
      (Fintype.card F : ℂ) + 1 + jacobiSum χ χ + jacobiSum χ⁻¹ χ⁻¹ := by
    simpa [hs, hpow, add_assoc] using hcount
  have hstar : star (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹ := by
    simp [jacobiSum, star_mul, MulChar.star_apply', mul_comm]
  rw [← hstar] at hc
  have hr := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
    Complex.star_def, Complex.conj_re] at hr
  linarith

/-- An integral trace formula for the same Euler character, before choosing a
primary generator.  Substituting the proved normalization J = -π gives the
desired Q + 1 - Tr(π), without switching characters or embeddings. -/
theorem cubic_projective_count_integral {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F E) (hχ : orderOf χ = 3) :
    (Nat.card (projectivePoints F 3) : ℤ) =
      (Fintype.card F : ℤ) + 1 + QuadraticAlgebra.trace (jacobiSum χ χ) := by
  let ψ := χ.ringHomComp eisensteinComplex
  have hc : χ ^ 3 = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
  have hn : χ ≠ 1 := by intro he; simp [he] at hχ
  have hp : ψ ^ 3 = 1 := by
    dsimp [ψ]
    rw [MulChar.ringHomComp_pow, hc, MulChar.ringHomComp_one]
  have hpn : ψ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff eisensteinComplex_injective).mpr hn
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ψ = 3 := orderOf_eq_prime hp hpn
  have H := cubic_projective_count ψ hord
  rw [show jacobiSum ψ ψ = eisensteinComplex (jacobiSum χ χ) from
    jacobiSum_ringHomComp χ χ eisensteinComplex] at H
  rw [twice_re_eisensteinComplex] at H
  exact_mod_cast H

private theorem three_not_mem_of_residue_mod
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (hcard : Nat.card (E ⧸ P) % 3 = 1) : (3 : E) ∉ P := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hmem
  have hz : (3 : E ⧸ P) = 0 := by
    simpa only [map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hchar : ringChar (E ⧸ P) = 3 :=
    CharP.ringChar_of_prime_eq_zero Nat.prime_three hz
  have hdiv : 3 ∣ Fintype.card (E ⧸ P) :=
    (prime_dvd_char_iff_dvd_card (R := E ⧸ P) 3).mp (by simp [hchar])
  have hmod : Nat.card (E ⧸ P) % 3 = 0 := Nat.mod_eq_zero_of_dvd
    (by simpa only [Fintype.card_eq_nat_card] using hdiv)
  omega


/-- For the Euler character belonging to P, the actual cubic Fermat count is
q + 1 - Tr(π). The Jacobi normalization, norm, and ideal direction are discharged
by the companion development, rather than added as premises to this count. -/
theorem cubic_projective_count_primary
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (hcard : Nat.card (E ⧸ P) % 3 = 1)
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1) :
    letI : Field (E ⧸ P) := Ideal.Quotient.field P;
    (Nat.card (projectivePoints (E ⧸ P) 3) : ℤ) =
      (Nat.card (E ⧸ P) : ℤ) + 1 - QuadraticAlgebra.trace π := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  have hthree : (3 : E) ∉ P := three_not_mem_of_residue_mod P hcard
  let χ :=
    D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization.cubicResidueMulChar
      P hcard hthree
  have hχ : orderOf χ = 3 :=
    D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization.cubicResidueMulChar_orderOf
      P hcard hthree
  have H := cubic_projective_count_integral χ hχ
  have HJ : -jacobiSum χ χ = π :=
    D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization.cubicJacobiSum_eq_primary_generator
      P hcard hthree π hπ hπprimary
  have htrace : QuadraticAlgebra.trace (jacobiSum χ χ) =
      -QuadraticAlgebra.trace π := by
    have ht := congrArg (QuadraticAlgebra.trace : E → ℤ) HJ
    rw [map_neg] at ht
    linarith
  rw [Fintype.card_eq_nat_card, htrace] at H
  simpa only [sub_eq_add_neg] using H


end D5.S3.CharacterSums.Fermat.CubicFermatTrace
