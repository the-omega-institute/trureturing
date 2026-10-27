/- GID: D5/S3/Factorization/QuadraticIdeals/CubicSameCharacteristic
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/CubicSameCharacteristic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same-characteristic bridge completes primary cubic reciprocity for finite maximal quotients. -/

import D5.S3.Factorization.QuadraticIdeals.CubicWilsonBinomial
import D5.S3.Factorization.QuadraticIdeals.CubicGaussPrimePower

/- UNCOMPILED research candidate, preserving only the remaining same-
characteristic bridge. No Lean command has been run on this file.

The companion CubicWilsonBinomial and CubicGaussPrimePower modules are
preserved alongside this WIP source. The former supplies the conjugate-prime
Wilson endpoint; the latter supplies primary_generator_three_not_mem,
residue_card_mod_three_of_three_not_mem, and the different-characteristic
endpoint. No proof from either companion is duplicated here.
CubicJacobiNormalization supplies the proved Jacobi value and norm, not
arithmetic hypotheses of this endpoint.

Library-first route: Ideal.mem_span_singleton, QuadraticAlgebra.norm_natCast,
QuadraticAlgebra.isUnit_iff_norm_isUnit, Nat.dvd_prime_pow, and maximality
under the bijective star endomorphism suffice. Full splitting classification,
residue-field conjugation isomorphisms, and character transport are unnecessary.
The norm argument itself excludes the inert case. The total final endpoint
includes the equal-ideal zero branch; cross-nonvanishing is not added to its
assumptions.

No parser/elaborator/kernel, scoped report, axiom-closure, or official CI
acceptance is claimed. This source is preserved as an uncompiled WIP.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.QuadraticIdeals.CubicSameCharacteristic

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization
open D5.S3.Factorization.QuadraticIdeals.CubicGaussPrimePower
open D5.S3.Factorization.QuadraticIdeals.CubicWilsonBinomial

abbrev E := EisensteinOrder

/-- Characteristic p says that the rational integer p belongs to the ideal. -/
private theorem char_mem (P : Ideal E) (p : ℕ) [CharP (E ⧸ P) p] : (p : E) ∈ P := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_natCast] using (CharP.cast_eq_zero (E ⧸ P) p)

/-- Consume the existing normalization internally. No norm or Jacobi value
is a premise of the same-characteristic arithmetic endpoints below. -/
private theorem primary_norm_eq_residue_card
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1) :
    QuadraticAlgebra.norm π = (Nat.card (E ⧸ P) : ℤ) := by
  let hthree := primary_generator_three_not_mem P π hπ hπprimary
  let hmod := residue_card_mod_three_of_three_not_mem P hthree
  have H := cubicJacobiSum_eq_primary_generator P hmod hthree π hπ hπprimary
  rw [← H, QuadraticAlgebra.norm_neg, cubicJacobiSum_norm P hmod hthree]

/-- The only new cardinality argument. Since p = pi*a, the norm of pi divides
p^2. Cross-nonvanishing puts a in Q, excluding the norm-p^2 case because its
remaining factor a would be a unit. Thus an inert residue cardinality cannot
survive in the distinct-ideal same-characteristic branch. -/
theorem residue_card_eq_char_of_cross_nonmem
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)]
    (p : ℕ) [Fact p.Prime] [CharP (E ⧸ P) p] [CharP (E ⧸ Q) p]
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1)
    (hπQ : π ∉ Q) : Nat.card (E ⧸ P) = p := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  have hpπ : (p : E) ∈ Ideal.span {π} := by
    rw [hπ]
    exact char_mem P p
  obtain ⟨a, hpa⟩ := Ideal.mem_span_singleton.mp hpπ
  have hπ0 : Ideal.Quotient.mk Q π ≠ 0 := by
    intro h
    exact hπQ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hprod : Ideal.Quotient.mk Q π * Ideal.Quotient.mk Q a = 0 := by
    rw [← map_mul, ← hpa, map_natCast, CharP.cast_eq_zero]
  have ha0 : Ideal.Quotient.mk Q a = 0 := (mul_eq_zero.mp hprod).resolve_left hπ0
  have hnorm := primary_norm_eq_residue_card P π hπ hπprimary
  have Hnorm := congrArg QuadraticAlgebra.norm hpa
  rw [QuadraticAlgebra.norm_natCast, map_mul, hnorm] at Hnorm
  have hdvdZ : (Nat.card (E ⧸ P) : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) :=
    ⟨QuadraticAlgebra.norm a, by simpa only [Nat.cast_pow] using Hnorm⟩
  have hdvd : Nat.card (E ⧸ P) ∣ p ^ 2 := Int.natCast_dvd_natCast.mp hdvdZ
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have hcardgt : 1 < Nat.card (E ⧸ P) := Finite.one_lt_card
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · simp only [pow_zero] at hcard
    omega
  · simpa only [pow_one] using hcard
  · have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hna : QuadraticAlgebra.norm a = 1 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hpZ)
      calc
        (p : ℤ) ^ 2 * QuadraticAlgebra.norm a = (p : ℤ) ^ 2 := by
          simpa only [hcard, Nat.cast_pow] using Hnorm.symm
        _ = (p : ℤ) ^ 2 * 1 := (mul_one _).symm
    have hua : IsUnit a := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
      (by rw [hna]; exact isUnit_one)
    exact False.elim ((isUnit_iff_ne_zero.mp (hua.map (Ideal.Quotient.mk Q))) ha0)

/-- Star preserves maximality at the ideal level. This uses no identification
of the two quotient fields and transports no multiplicative character. -/
private theorem span_star_isMaximal
    (P : Ideal E) [P.IsMaximal] (π : E) (hπ : Ideal.span {π} = P) :
    (Ideal.span {star π}).IsMaximal := by
  have H := (inferInstance : P.IsMaximal).map_bijective (starRingEnd E)
    (show Function.Bijective (starRingEnd E) from
      ⟨star_involutive.injective, star_involutive.surjective⟩)
  have hmap : Ideal.map (starRingEnd E) P = Ideal.span {star π} := by
    simp only [← hπ, Ideal.map_span, Set.image_singleton, starRingEnd_apply]
  rw [hmap] at H
  exact H

/-- The complete missing bridge to the Wilson endpoint: two distinct finite
maximal quotients of the same characteristic have prime cardinality and
conjugate primary generators. All four conclusions are derived here. -/
theorem same_char_cross_data
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (p : ℕ) [Fact p.Prime] [CharP (E ⧸ P) p] [CharP (E ⧸ Q) p]
    (π ρ : E) (hπ : Ideal.span {π} = P) (hρ : Ideal.span {ρ} = Q)
    (hπprimary : (3 : E) ∣ π - 1) (hρprimary : (3 : E) ∣ ρ - 1)
    (hπQ : π ∉ Q) :
    Nat.card (E ⧸ P) = p ∧ Nat.card (E ⧸ Q) = p ∧
      Ideal.span {star π} = Q ∧ ρ = star π := by
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  have hρP : ρ ∉ P := by
    intro h
    have hle : Q ≤ P := by
      rw [← hρ]
      exact (Ideal.span_singleton_le_iff_mem P).mpr h
    have heq := (inferInstance : Q.IsMaximal).eq_of_le
      (inferInstance : P.IsMaximal).ne_top hle
    apply hπQ
    rw [heq, ← hπ]
    exact Ideal.mem_span_singleton_self π
  have hPcard := residue_card_eq_char_of_cross_nonmem P Q p π hπ hπprimary hπQ
  have hQcard := residue_card_eq_char_of_cross_nonmem Q P p ρ hρ hρprimary hρP
  have hnorm : QuadraticAlgebra.norm π = (p : ℤ) :=
    (primary_norm_eq_residue_card P π hπ hπprimary).trans (congrArg Nat.cast hPcard)
  have hfactor : (p : E) = π * star π := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hnorm]
    rfl
  have hπ0 : Ideal.Quotient.mk Q π ≠ 0 := by
    intro h
    exact hπQ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hprod : Ideal.Quotient.mk Q π * Ideal.Quotient.mk Q (star π) = 0 := by
    rw [← map_mul, ← hfactor, map_natCast, CharP.cast_eq_zero]
  have hbar : star π ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp
    ((mul_eq_zero.mp hprod).resolve_left hπ0)
  have hspan : Ideal.span {star π} = Q :=
    (span_star_isMaximal P π hπ).eq_of_le
      (inferInstance : Q.IsMaximal).ne_top
      ((Ideal.span_singleton_le_iff_mem Q).mpr hbar)
  have hbarprimary : (3 : E) ∣ star π - 1 := by
    obtain ⟨z, hz⟩ := hπprimary
    refine ⟨star z, ?_⟩
    have H := congrArg (starRingEnd E) hz
    simpa only [map_sub, map_one, map_mul, map_natCast, map_ofNat, starRingEnd_apply] using H
  let hQthree := primary_generator_three_not_mem Q ρ hρ hρprimary
  let hQmod := residue_card_mod_three_of_three_not_mem Q hQthree
  have Hρ := cubicJacobiSum_eq_primary_generator Q hQmod hQthree ρ hρ hρprimary
  have Hbar := cubicJacobiSum_eq_primary_generator Q hQmod hQthree
    (star π) hspan hbarprimary
  exact ⟨hPcard, hQcard, hspan, Hρ.symm.trans Hbar⟩

/-- Same-characteristic cross symbols are both one. The Wilson development
is consumed unchanged after deriving its prime-cardinality hypotheses. -/
theorem same_char_primary_cross_symbols_eq_one
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (p : ℕ) [Fact p.Prime] [CharP (E ⧸ P) p] [CharP (E ⧸ Q) p]
    (π ρ : E) (hπ : Ideal.span {π} = P) (hρ : Ideal.span {ρ} = Q)
    (hπprimary : (3 : E) ∣ π - 1) (hρprimary : (3 : E) ∣ ρ - 1)
    (hπQ : π ∉ Q) :
    let hPthree := primary_generator_three_not_mem P π hπ hπprimary
    let hQthree := primary_generator_three_not_mem Q ρ hρ hρprimary
    let χP := cubicResidueMulChar P
      (residue_card_mod_three_of_three_not_mem P hPthree) hPthree
    let χQ := cubicResidueMulChar Q
      (residue_card_mod_three_of_three_not_mem Q hQthree) hQthree
    χQ (Ideal.Quotient.mk Q π) = 1 ∧ χP (Ideal.Quotient.mk P ρ) = 1 := by
  obtain ⟨hPcard, hQcard, hspan, hρbar⟩ :=
    same_char_cross_data P Q p π ρ hπ hρ hπprimary hρprimary hπQ
  let hPthree := primary_generator_three_not_mem P π hπ hπprimary
  have hpmod : p % 3 = 1 := by
    rw [← hPcard]
    exact residue_card_mod_three_of_three_not_mem P hPthree
  have H := conjugate_primary_symbol_pair P Q p hPcard hQcard hpmod
    π hπ hspan hπprimary
  constructor
  · exact H.2
  · rw [hρbar]
    exact H.1

/-- Reciprocity for arbitrary finite maximal quotients in the same
characteristic. Equal ideals are handled by the actual zero extensions. -/
theorem cubic_reciprocity_primary_same_char
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (hchar : ringChar (E ⧸ Q) = ringChar (E ⧸ P))
    (π ρ : E) (hπ : Ideal.span {π} = P) (hρ : Ideal.span {ρ} = Q)
    (hπprimary : (3 : E) ∣ π - 1) (hρprimary : (3 : E) ∣ ρ - 1) :
    let hPthree := primary_generator_three_not_mem P π hπ hπprimary
    let hQthree := primary_generator_three_not_mem Q ρ hρ hρprimary
    let χP := cubicResidueMulChar P
      (residue_card_mod_three_of_three_not_mem P hPthree) hPthree
    let χQ := cubicResidueMulChar Q
      (residue_card_mod_three_of_three_not_mem Q hQthree) hQthree
    χQ (Ideal.Quotient.mk Q π) = χP (Ideal.Quotient.mk P ρ) := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  let hPthree := primary_generator_three_not_mem P π hπ hπprimary
  let hQthree := primary_generator_three_not_mem Q ρ hρ hρprimary
  let χP := cubicResidueMulChar P
    (residue_card_mod_three_of_three_not_mem P hPthree) hPthree
  let χQ := cubicResidueMulChar Q
    (residue_card_mod_three_of_three_not_mem Q hQthree) hQthree
  change χQ (Ideal.Quotient.mk Q π) = χP (Ideal.Quotient.mk P ρ)
  by_cases hπQ : π ∈ Q
  · have hle : P ≤ Q := by
      rw [← hπ]
      exact (Ideal.span_singleton_le_iff_mem Q).mpr hπQ
    have hPQ := (inferInstance : P.IsMaximal).eq_of_le
      (inferInstance : Q.IsMaximal).ne_top hle
    have hρP : ρ ∈ P := by
      rw [hPQ, ← hρ]
      exact Ideal.mem_span_singleton_self ρ
    have hπ0 := Ideal.Quotient.eq_zero_iff_mem.mpr hπQ
    have hρ0 := Ideal.Quotient.eq_zero_iff_mem.mpr hρP
    simp only [hπ0, hρ0, MulChar.map_zero]
  · let p := ringChar (E ⧸ P)
    letI : Fact p.Prime := ⟨CharP.prime_ringChar (E ⧸ P)⟩
    letI : CharP (E ⧸ P) p := inferInstance
    letI : CharP (E ⧸ Q) p :=
      hchar ▸ (inferInstance : CharP (E ⧸ Q) (ringChar (E ⧸ Q)))
    have H := same_char_primary_cross_symbols_eq_one P Q p π ρ
      hπ hρ hπprimary hρprimary hπQ
    exact H.1.trans H.2.symm

/-- Assemble the already authored different-characteristic theorem with the
new same-characteristic bridge. No cross-nonzero, norm, cardinality, Jacobi
value, Gauss value, cube witness, or symbol conclusion is an added premise. -/
theorem cubic_reciprocity_primary_finite_maximal
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (π ρ : E) (hπ : Ideal.span {π} = P) (hρ : Ideal.span {ρ} = Q)
    (hπprimary : (3 : E) ∣ π - 1) (hρprimary : (3 : E) ∣ ρ - 1) :
    let hPthree := primary_generator_three_not_mem P π hπ hπprimary
    let hQthree := primary_generator_three_not_mem Q ρ hρ hρprimary
    let χP := cubicResidueMulChar P
      (residue_card_mod_three_of_three_not_mem P hPthree) hPthree
    let χQ := cubicResidueMulChar Q
      (residue_card_mod_three_of_three_not_mem Q hQthree) hQthree
    χQ (Ideal.Quotient.mk Q π) = χP (Ideal.Quotient.mk P ρ) := by
  by_cases hchar : ringChar (E ⧸ Q) = ringChar (E ⧸ P)
  · exact cubic_reciprocity_primary_same_char P Q hchar π ρ
      hπ hρ hπprimary hρprimary
  · exact cubic_reciprocity_primary_different_char P Q hchar π ρ
      hπ hρ hπprimary hρprimary

/- Acceptance boundary: all new source remains uncompiled. The preceding
final theorem is a candidate proof assembly, not a Lean/kernel/CI acceptance
claim. Existing Wilson and prime-power proofs are imported, not rewritten.
-/

end D5.S3.Factorization.QuadraticIdeals.CubicSameCharacteristic
