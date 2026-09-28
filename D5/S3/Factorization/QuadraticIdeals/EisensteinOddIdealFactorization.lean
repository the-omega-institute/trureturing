/- GID: D5/S3/Factorization/QuadraticIdeals/EisensteinOddIdealFactorization
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/EisensteinOddIdealFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit prime-power ideal factorization of odd oriented Eisenstein factors. -/

import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open NumberField

namespace D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization

noncomputable section

private lemma factor_norm [IsDomain EisensteinOrder] [IsPrincipalIdealRing EisensteinOrder]
    (b p : ℕ) (hb : Odd b) (hp : p ∣ blockNorm b) :
    Ideal.absNorm (orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}) = p := by
  obtain ⟨_, e, he⟩ := eisenstein_odd_scalar_quotient b hb
  let q : EisensteinOrder →+* OrientedQuotient b := Ideal.Quotient.mk (orientedIdeal b)
  let f : EisensteinOrder →+* ZMod p :=
    (ZMod.castHom hp (ZMod p)).comp (e.symm.toRingHom.comp q)
  have hscalar (n : ℤ) :
      q (QuadraticAlgebra.C n) = e (n : ZMod (blockNorm b)) := by
    simpa [q, scalarMap, QuadraticAlgebra.C_eq_algebraMap] using (he n).symm
  have hfscalar (n : ℤ) : f (QuadraticAlgebra.C n) = (n : ZMod p) := by
    change (ZMod.castHom hp (ZMod p)) (e.symm (q (QuadraticAlgebra.C n))) = _
    rw [hscalar n, e.symm_apply_apply]
    simp
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := ZMod.castHom_surjective hp y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e z)
    refine ⟨x, ?_⟩
    change (ZMod.castHom hp (ZMod p)) (e.symm (q x)) = y
    rw [hx, e.symm_apply_apply, hz]
  have hker : RingHom.ker f =
      orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective (e.symm (q x))
      have hqx : q x = q (QuadraticAlgebra.C n) := by
        rw [hscalar n]
        calc
          q x = e (e.symm (q x)) := by simp
          _ = e (n : ZMod (blockNorm b)) := by rw [hn]
      have hxI : x - QuadraticAlgebra.C n ∈ orientedIdeal b := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        change q (x - QuadraticAlgebra.C n) = 0
        rw [map_sub, hqx, sub_self]
      have hn0 : (n : ZMod p) = 0 := by
        have hfx : f x = 0 := RingHom.mem_ker.mp hx
        have hfeq : f x = f (QuadraticAlgebra.C n) := by
          change (ZMod.castHom hp (ZMod p)) (e.symm (q x)) =
            (ZMod.castHom hp (ZMod p)) (e.symm (q (QuadraticAlgebra.C n)))
          rw [hqx]
        rw [hfeq, hfscalar] at hfx
        exact hfx
      have hn_div : (p : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp hn0
      have hCn : (QuadraticAlgebra.C n : EisensteinOrder) ∈
          Ideal.span {(p : EisensteinOrder)} := by
        apply Ideal.mem_span_singleton.mpr
        simpa only [QuadraticAlgebra.C_eq_algebraMap, map_natCast] using
          (map_dvd (algebraMap ℤ EisensteinOrder) hn_div)
      have hsum : x = (x - QuadraticAlgebra.C n) + QuadraticAlgebra.C n := by abel
      rw [hsum]
      exact add_mem (Ideal.mem_sup_left hxI) (Ideal.mem_sup_right hCn)
    · apply sup_le
      · intro x hx
        apply RingHom.mem_ker.mpr
        have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
        change (ZMod.castHom hp (ZMod p)) (e.symm (q x)) = 0
        rw [hqx, map_zero, map_zero]
      · apply Ideal.span_le.mpr
        intro x hx
        have hxp : x = (p : EisensteinOrder) := Set.mem_singleton_iff.mp hx
        subst x
        apply RingHom.mem_ker.mpr
        simpa only [QuadraticAlgebra.C_eq_algebraMap, map_natCast,
          ZMod.natCast_self] using hfscalar (p : ℤ)
  let ep : EisensteinOrder ⧸
      (orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}) ≃+* ZMod p :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hfsurj)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr ep.toEquiv).trans (Nat.card_zmod p)

/-- The odd Eisenstein factor has one explicit ideal factor above each prime of its scalar norm. -/
theorem eisenstein_odd_ideal_factorization
    (b : ℕ) (hb : Odd b) :
    orientedIdeal b =
      ∏ p ∈ (blockNorm b).primeFactors,
        (orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}) ^
          (blockNorm b).factorization p := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsPrincipalIdealRing (𝓞 (CyclotomicField 3 ℚ)) :=
    IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
  let φ := Classical.choice eisenstein_cyclotomic_equiv_exists
  letI : IsDomain EisensteinOrder := φ.toRingEquiv.isDomain_iff.mpr inferInstance
  letI : IsPrincipalIdealRing EisensteinOrder :=
    IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
  classical
  let B := blockNorm b
  let I := orientedIdeal b
  let P (p : ℕ) := I ⊔ Ideal.span {(p : EisensteinOrder)}
  have hB0 : B ≠ 0 := by
    dsimp [B, blockNorm]
    omega
  have hnormI : Ideal.absNorm I = B := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    obtain ⟨_, e, _⟩ := eisenstein_odd_scalar_quotient b hb
    rw [Nat.card_congr e.toEquiv.symm, Nat.card_zmod]
  have hnormprod :
      Ideal.absNorm (∏ p ∈ B.primeFactors, P p ^ B.factorization p) = B := by
    calc
      Ideal.absNorm (∏ p ∈ B.primeFactors, P p ^ B.factorization p) =
          ∏ p ∈ B.primeFactors, (Ideal.absNorm (P p)) ^ B.factorization p := by
            simp only [map_prod, map_pow]
      _ = ∏ p ∈ B.primeFactors, p ^ B.factorization p := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [show Ideal.absNorm (P p) = p from
          factor_norm b p hb (Nat.dvd_of_mem_primeFactors hp)]
      _ = B := (Nat.prod_primeFactors_pow_factorization hB0).symm
  have hBmem : (B : EisensteinOrder) ∈ I := by
    have hd := ((eisenstein_odd_scalar_quotient b hb).1 (B : ℤ)).mpr dvd_rfl
    apply Ideal.mem_span_singleton.mpr
    simpa only [I, B, QuadraticAlgebra.C_eq_algebraMap, map_natCast] using hd
  have hprodmem : (∏ p ∈ B.primeFactors, (p : EisensteinOrder) ^ B.factorization p) ∈ I := by
    have hnat := (Nat.prod_primeFactors_pow_factorization hB0).symm
    have hcast := congrArg (fun n : ℕ => (n : EisensteinOrder)) hnat
    norm_cast
    rw [hcast]
    exact hBmem
  have hcont : (∏ p ∈ B.primeFactors, P p ^ B.factorization p) ≤ I := by
    let q : EisensteinOrder →+* EisensteinOrder ⧸ I := Ideal.Quotient.mk I
    have hmap : Ideal.map q (∏ p ∈ B.primeFactors, P p ^ B.factorization p) = ⊥ := by
      rw [show Ideal.map q (∏ p ∈ B.primeFactors, P p ^ B.factorization p) =
          ∏ p ∈ B.primeFactors, Ideal.map q (P p ^ B.factorization p) from
            map_prod (Ideal.mapHom q) _ _]
      simp only [Ideal.map_pow, P, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
      rw [show Ideal.map q I = ⊥ from Ideal.map_quotient_self I]
      simp only [bot_sup_eq, Ideal.span_singleton_pow]
      rw [Ideal.prod_span_singleton]
      apply Ideal.span_singleton_eq_bot.mpr
      have hq : q (∏ p ∈ B.primeFactors, (p : EisensteinOrder) ^ B.factorization p) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hprodmem
      simpa only [map_prod, map_pow] using hq
    simpa only [q, Ideal.mk_ker] using (Ideal.map_eq_bot_iff_le_ker q).mp hmap
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hcont
  have hnormJ : Ideal.absNorm J = 1 := by
    have hm : B * Ideal.absNorm J = B := by
      calc
        B * Ideal.absNorm J = Ideal.absNorm (I * J) := by rw [map_mul, hnormI]
        _ = Ideal.absNorm (∏ p ∈ B.primeFactors, P p ^ B.factorization p) := by rw [← hJ]
        _ = B := hnormprod
    have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
    nlinarith
  have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hnormJ
  change I = ∏ p ∈ B.primeFactors, P p ^ B.factorization p
  rw [hJ, hJtop, Ideal.mul_top]

#print axioms eisenstein_odd_ideal_factorization

end

end D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
