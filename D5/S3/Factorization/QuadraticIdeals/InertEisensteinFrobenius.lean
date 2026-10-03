/- GID: D5/S3/Factorization/QuadraticIdeals/InertEisensteinFrobenius
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/InertEisensteinFrobenius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inert Eisenstein quotient and conjugation Frobenius. -/

import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import D5.S3.PrimeForms.Splitting.EisensteinCriterion
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.PrimeForms.Splitting.EisensteinCriterion

namespace D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius

theorem inert_eisenstein_quotient_frobenius (ell : ℕ) [Fact ell.Prime] (hell3 : ell % 3 = 2) :
    let I : Ideal EisensteinOrder := Ideal.span {(ell : EisensteinOrder)}
    I.IsMaximal ∧ Nat.card (EisensteinOrder ⧸ I) = ell ^ 2 ∧
      CharP (EisensteinOrder ⧸ I) ell ∧
      ∃ e : EisensteinOrder ⧸ I ≃+* QuadraticAlgebra (ZMod ell) (-1) (-1),
        (∀ z : EisensteinOrder,
          (e (Ideal.Quotient.mk I z)).re = (z.re : ZMod ell) ∧
          (e (Ideal.Quotient.mk I z)).im = (z.im : ZMod ell)) ∧
        ∀ z : EisensteinOrder,
          (Ideal.Quotient.mk I z) ^ ell = Ideal.Quotient.mk I (star z) := by
  classical
  let I : Ideal EisensteinOrder := Ideal.span {(ell : EisensteinOrder)}
  change I.IsMaximal ∧ Nat.card (EisensteinOrder ⧸ I) = ell ^ 2 ∧
    CharP (EisensteinOrder ⧸ I) ell ∧
    ∃ e : EisensteinOrder ⧸ I ≃+* QuadraticAlgebra (ZMod ell) (-1) (-1),
      (∀ z : EisensteinOrder,
        (e (Ideal.Quotient.mk I z)).re = (z.re : ZMod ell) ∧
        (e (Ideal.Quotient.mk I z)).im = (z.im : ZMod ell)) ∧
      ∀ z : EisensteinOrder,
        (Ideal.Quotient.mk I z) ^ ell = Ideal.Quotient.mk I (star z)
  have hclass :
      I.IsMaximal ∧ Nat.card (EisensteinOrder ⧸ I) = ell ^ 2 ∧
      ∃ e : EisensteinOrder ⧸ I ≃+* QuadraticAlgebra (ZMod ell) (-1) (-1),
        ∀ z : EisensteinOrder,
          (e (Ideal.Quotient.mk I z)).re = (z.re : ZMod ell) ∧
          (e (Ideal.Quotient.mk I z)).im = (z.im : ZMod ell) := by
    classical
    let K := QuadraticAlgebra (ZMod ell) (-1) (-1)
    have hrootFree : ∀ r : ZMod ell,
        r ^ 2 ≠ (-1 : ZMod ell) + (-1 : ZMod ell) * r := by
      intro r hr
      by_cases heq : ell = 2
      · subst ell
        fin_cases r
        · exact (by decide +revert : ¬ ((0 : ZMod 2) ^ 2 = -1 + -1 * 0)) hr
        · exact (by decide +revert : ¬ ((1 : ZMod 2) ^ 2 = -1 + -1 * 1)) hr
      · have hne3 : ell ≠ 3 := by omega
        have hnotSquare : ¬ IsSquare (-3 : ZMod ell) := by
          intro hs
          have h := (neg_three_isSquare_iff ell heq hne3).mp hs
          omega
        apply hnotSquare
        refine ⟨2 * r + 1, ?_⟩
        linear_combination (-4 : ZMod ell) * hr
    letI : Fact (∀ r : ZMod ell,
        r ^ 2 ≠ (-1 : ZMod ell) + (-1 : ZMod ell) * r) := ⟨hrootFree⟩
    letI : Field K := inferInstance
    let reduce : EisensteinOrder →+* K := {
      toFun := fun z => ⟨(z.re : ZMod ell), (z.im : ZMod ell)⟩
      map_zero' := by
        apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
      map_one' := by
        apply QuadraticAlgebra.ext <;>
          simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      map_add' := by
        intro z y
        dsimp [K]
        apply QuadraticAlgebra.ext <;>
          simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;>
          push_cast <;> rfl
      map_mul' := by
        intro z y
        apply QuadraticAlgebra.ext
        · change ((z * y).re : ZMod ell) =
            ((⟨(z.re : ZMod ell), (z.im : ZMod ell)⟩ : K) *
              (⟨(y.re : ZMod ell), (y.im : ZMod ell)⟩ : K)).re
          simp only [QuadraticAlgebra.re_mul]
          push_cast
          ring
        · change ((z * y).im : ZMod ell) =
            ((⟨(z.re : ZMod ell), (z.im : ZMod ell)⟩ : K) *
              (⟨(y.re : ZMod ell), (y.im : ZMod ell)⟩ : K)).im
          simp only [QuadraticAlgebra.im_mul]
          push_cast
          ring
    }
    have hsurj : Function.Surjective reduce := by
      intro z
      obtain ⟨a, ha⟩ := ZMod.intCast_surjective z.re
      obtain ⟨b, hb⟩ := ZMod.intCast_surjective z.im
      refine ⟨⟨a, b⟩, ?_⟩
      apply QuadraticAlgebra.ext <;> simp [reduce, ha, hb]
    have hker : RingHom.ker reduce =
        Ideal.span {(ell : EisensteinOrder)} := by
      ext z
      constructor
      · intro hz
        have hzero : reduce z = 0 := RingHom.mem_ker.mp hz
        have hre : (z.re : ZMod ell) = 0 := congrArg QuadraticAlgebra.re hzero
        have him : (z.im : ZMod ell) = 0 := congrArg QuadraticAlgebra.im hzero
        apply Ideal.mem_span_singleton.mpr
        apply (QuadraticAlgebra.algebraMap_dvd_iff
          (r := (ell : ℤ)) (z := z)).mpr
        exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd z.re ell).mp hre,
          (ZMod.intCast_zmod_eq_zero_iff_dvd z.im ell).mp him⟩
      · intro hz
        obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hz
        apply RingHom.mem_ker.mpr
        change reduce ((ell : EisensteinOrder) * t) = 0
        rw [map_mul, map_natCast]
        have hellK : (ell : K) = 0 := by
          apply QuadraticAlgebra.ext
          · change (ell : ZMod ell) = 0
            exact ZMod.natCast_self ell
          · change (0 : ZMod ell) = 0
            rfl
        rw [hellK]
        exact zero_mul _
    let I : Ideal EisensteinOrder := Ideal.span {(ell : EisensteinOrder)}
    have hmax : I.IsMaximal := by
      change (Ideal.span {(ell : EisensteinOrder)}).IsMaximal
      rw [← hker]
      exact RingHom.ker_isMaximal_of_surjective reduce hsurj
    have hcardK : Nat.card K = ell ^ 2 := by
      calc
        Nat.card K = Nat.card (ZMod ell × ZMod ell) :=
          Nat.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod ell) (-1 : ZMod ell))
        _ = ell ^ 2 := by simp [Nat.card_prod, Nat.card_zmod, pow_two]
    have hcard : Nat.card (EisensteinOrder ⧸ I) = ell ^ 2 := by
      change Nat.card (EisensteinOrder ⧸ Ideal.span {(ell : EisensteinOrder)}) = ell ^ 2
      rw [← hker]
      calc
        Nat.card (EisensteinOrder ⧸ RingHom.ker reduce) = Nat.card K :=
          Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
        _ = ell ^ 2 := hcardK
    have hIker : I = RingHom.ker reduce := hker.symm
    let e : EisensteinOrder ⧸ I ≃+* K :=
      (Ideal.quotEquivOfEq hIker).trans
        (RingHom.quotientKerEquivOfSurjective hsurj)
    have heval (z : EisensteinOrder) : e (Ideal.Quotient.mk I z) = reduce z := by
      simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
    refine ⟨hmax, hcard, e, ?_⟩
    intro z
    rw [heval z]
    exact ⟨rfl, rfl⟩
  obtain ⟨hmax, hcard, e, heval⟩ := hclass
  letI : I.IsMaximal := hmax
  letI : Finite (EisensteinOrder ⧸ I) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : ell.Prime).ne_zero)
  letI : Fintype (EisensteinOrder ⧸ I) := Fintype.ofFinite _
  letI : Field (EisensteinOrder ⧸ I) := Ideal.Quotient.field I
  letI : CharP (EisensteinOrder ⧸ I) ell :=
    charP_of_card_eq_prime_pow (f := 2) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
  have hFrobModel :
      ∀ z : QuadraticAlgebra (ZMod ell) (-1) (-1), z ^ ell = star z := by
    intro z
    let K := QuadraticAlgebra (ZMod ell) (-1) (-1)
    let w : K := QuadraticAlgebra.omega
    letI : CharP K ell :=
      charP_of_injective_ringHom QuadraticAlgebra.algebraMap_injective ell
    have hw : w ^ 2 + w + 1 = 0 := by
      change (QuadraticAlgebra.omega : K) ^ 2 + QuadraticAlgebra.omega + 1 = 0
      rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
      simp
    have hw3 : w ^ 3 = 1 := by
      linear_combination (w - 1) * hw
    have hw2 : w ^ 2 = -1 - w := by
      linear_combination hw
    have hwFrob : w ^ ell = w ^ 2 := by
      have hell : ell = 3 * (ell / 3) + 2 := by omega
      calc
        w ^ ell = w ^ (3 * (ell / 3) + 2) := congrArg (w ^ ·) hell
        _ = w ^ 2 := by rw [pow_add, pow_mul, hw3]; simp
    have hdecomp : z = algebraMap (ZMod ell) K z.re +
        algebraMap (ZMod ell) K z.im * w := by
      simpa only [Algebra.smul_def] using
        (QuadraticAlgebra.mk_eq_add_smul_omega z.re z.im :
          z = algebraMap (ZMod ell) K z.re + z.im • w)
    calc
      z ^ ell = (algebraMap (ZMod ell) K z.re +
          algebraMap (ZMod ell) K z.im * w) ^ ell := by
            conv_lhs => rw [hdecomp]
      _ = (algebraMap (ZMod ell) K z.re) ^ ell +
          (algebraMap (ZMod ell) K z.im * w) ^ ell := add_pow_char _ _ ell
      _ = algebraMap (ZMod ell) K z.re +
          algebraMap (ZMod ell) K z.im * w ^ 2 := by
        rw [mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card, hwFrob]
      _ = star z := by
        rw [hw2]
        apply QuadraticAlgebra.ext
        · dsimp only [K, w]
          simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one,
            QuadraticAlgebra.im_one] <;> ring
        · dsimp only [K, w]
          simp [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one,
            QuadraticAlgebra.im_one] <;> ring
  have hFrob : ∀ z : EisensteinOrder,
      (Ideal.Quotient.mk I z) ^ ell = Ideal.Quotient.mk I (star z) := by
    intro z
    let q : EisensteinOrder →+* EisensteinOrder ⧸ I := Ideal.Quotient.mk I
    have hevalQ (a : EisensteinOrder) :
        (e (q a)).re = (a.re : ZMod ell) ∧
        (e (q a)).im = (a.im : ZMod ell) := by
      simpa only [q] using heval a
    have hstarEval (a : EisensteinOrder) : e (q (star a)) = star (e (q a)) := by
      apply QuadraticAlgebra.ext
      · rw [(hevalQ (star a)).1,
          (QuadraticAlgebra.re_star (e (q a))),
          (hevalQ a).1, (hevalQ a).2,
          (QuadraticAlgebra.re_star a)]
        push_cast
        ring
      · rw [(hevalQ (star a)).2,
          (QuadraticAlgebra.im_star (e (q a))),
          (hevalQ a).2,
          (QuadraticAlgebra.im_star a)]
        push_cast
        ring
    apply e.injective
    calc
      e ((q z) ^ ell) = (e (q z)) ^ ell := map_pow e (q z) ell
      _ = star (e (q z)) := hFrobModel (e (q z))
      _ = e (q (star z)) := (hstarEval z).symm
  exact ⟨hmax, hcard, inferInstance, e, heval, hFrob⟩

#print axioms inert_eisenstein_quotient_frobenius

end D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius
