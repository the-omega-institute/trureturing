/- GID: D5/S3/Factorization/QuadraticIdeals/EisensteinCohnReductionCore
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/EisensteinCohnReductionCore
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual Eisenstein prime-power extraction, cubic obstruction and integral coordinates. -/

import D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
import D5.S3.Arith.Congruence.CohnUniformThreeAdic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open NumberField
open scoped QuadraticAlgebra

private theorem z2_two : (2 : ZMod 2) = 0 := by decide
private theorem z2_three : (3 : ZMod 2) = 1 := by decide
private theorem z3_three : (3 : ZMod 3) = 0 := by decide
private theorem z4_four : (4 : ZMod 4) = 0 := by decide
private theorem z4_negthree : (-3 : ZMod 4) = 1 := by decide
attribute [local simp] z2_two z2_three z3_three z4_four z4_negthree


open D5.S3.Arith.Congruence.CohnUniformThreeAdic
open D5.S3.Arith.Congruence.CohnUniformThreeAdic.Exported
open Polynomial

/-- Evaluation of the Cohn polynomial identity at an integer. -/
private theorem cohn_polynomial_eval_power (q : ℕ) (a : ℤ) (hodd : Odd q) :
    (cohnPolynomial q).eval (a ^ 2 - 1) =
      ((⟨a, 1⟩ : QuadraticAlgebra ℤ (-3) 0) ^ q).im := by
  obtain ⟨m, hm⟩ := hodd
  have hq : q = 2 * m + 1 := by omega
  subst q
  have H := congrArg (fun p : ℤ[X] => p.eval a) (polynomial_identification m)
  have H' := congrArg QuadraticAlgebra.im
    ((evalQuadratic a).map_pow (⟨X, 1⟩ : QuadraticAlgebra ℤ[X] (-3) 0) (2 * m + 1))
  have he : (evalQuadratic a) (⟨X, 1⟩ : QuadraticAlgebra ℤ[X] (-3) 0) =
      (⟨a, 1⟩ : QuadraticAlgebra ℤ (-3) 0) := by
    ext <;> simp [evalQuadratic]
  rw [he] at H'
  calc
    (cohnPolynomial (2 * m + 1)).eval (a ^ 2 - 1) =
        (((⟨X, 1⟩ : QuadraticAlgebra ℤ[X] (-3) 0) ^ (2 * m + 1)).im.eval a) := by
      simpa only [eval_comp, eval_sub, eval_pow, eval_X, eval_one, sinePart, z] using H
    _ = _ := H'

abbrev E₂ := QuadraticAlgebra (ZMod 2) (-1) (-1)

def modTwo : EisensteinOrder →+* E₂ where
  toFun z := ⟨(z.re : ZMod 2), (z.im : ZMod 2)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp <;> ring

private theorem f2_sq (a : ZMod 2) : a ^ 2 = a := by
  simpa using FiniteField.pow_card a

private theorem f2_pow (a : ZMod 2) (n : ℕ) (hn : 0 < n) : a ^ n = a := by
  have ha : IsIdempotentElem a := by
    simpa only [IsIdempotentElem, pow_two] using f2_sq a
  exact IsIdempotentElem.pow_eq ha (Nat.ne_of_gt hn)

/-- Integer primitivity is derived from the actual equation, with no sign
assumption on Y and no valuation of zero convention. -/
private theorem primitive_data (x Y : ℤ) (q : ℕ) (hq : 3 ≤ q)
    (heq : x ^ 2 + 3 = Y ^ q) :
    Even x ∧ ¬ (3 : ℤ) ∣ x ∧ IsCoprime (x ^ 2 + 3) (12 : ℤ) := by
  have hxeven : Even x := by
    by_contra hn
    have hxo : Odd x := Int.not_even_iff_odd.mp hn
    have H := congrArg (fun n : ℤ => (n : ZMod 2)) heq
    have hx2 := hxo.intCast_zmod_two
    simp only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] at H
    rw [hx2, f2_pow _ q (by omega)] at H
    have hY2 : (Y : ZMod 2) = 0 := by simpa [one_add_one_eq_two] using H.symm
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd Y 2).mp hY2
    have h8 : (8 : ℤ) ∣ x ^ 2 + 3 := by
      rw [heq, ht, show q = 3 + (q - 3) by omega, pow_add]
      refine ⟨t ^ 3 * (2 * t) ^ (q - 3), ?_⟩
      ring
    obtain ⟨k, hk⟩ := hxo
    have hk2 : ((k ^ 2 + k : ℤ) : ZMod 2) = 0 := by
      push_cast
      rw [f2_sq]
      have htwo : (2 : ZMod 2) = 0 := z2_two
      linear_combination htwo * (k : ZMod 2)
    obtain ⟨l, hl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ 2 + k) 2).mp hk2
    obtain ⟨v, hv⟩ := h8
    have H8 : (8 : ℤ) ∣ 4 := by
      refine ⟨v - l, ?_⟩
      rw [hk] at hv
      norm_num at hl
      nlinarith [sq_nonneg k]
    norm_num at H8
  have hx3 : ¬ (3 : ℤ) ∣ x := by
    intro hx
    obtain ⟨k, hk⟩ := hx
    have H := congrArg (fun n : ℤ => (n : ZMod 3)) heq
    have hx0 : (x : ZMod 3) = 0 := by rw [hk]; push_cast; rw [z3_three, zero_mul]
    simp only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] at H
    rw [hx0] at H
    have hYq : (Y : ZMod 3) ^ q = 0 := by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), z3_three, zero_add] using H.symm
    have hY0 : (Y : ZMod 3) = 0 := (eq_zero_of_pow_eq_zero hYq)
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd Y 3).mp hY0
    have h9 : (9 : ℤ) ∣ Y ^ q := by
      rw [ht, show q = 2 + (q - 2) by omega, pow_add]
      refine ⟨t ^ 2 * (3 * t) ^ (q - 2), ?_⟩
      ring
    have hx9 : (9 : ℤ) ∣ x ^ 2 := by
      refine ⟨k ^ 2, ?_⟩
      rw [hk]
      ring
    have hd : (9 : ℤ) ∣ 3 := by
      have H := dvd_sub (heq.symm ▸ h9) hx9
      rw [show x ^ 2 + 3 - x ^ 2 = (3 : ℤ) by ring] at H
      exact H
    norm_num at hd
  have hcop4 : IsCoprime (x ^ 2 + 3) (4 : ℤ) := by
    obtain ⟨k, hk⟩ := hxeven
    refine ⟨-1, k ^ 2 + 1, ?_⟩
    rw [hk]
    ring
  have hcop3 : IsCoprime (x ^ 2 + 3) (3 : ℤ) := by
    have hx0 : (x : ZMod 3) ≠ 0 := by
      intro h
      exact hx3 ((ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp h)
    have hs : (x : ZMod 3) ^ 2 = 1 := by
      simpa using FiniteField.pow_card_sub_one_eq_one (x : ZMod 3) hx0
    have hN : ((x ^ 2 + 3 : ℤ) : ZMod 3) = 1 := by
      push_cast
      rw [hs, z3_three, add_zero]
    have hd : (3 : ℤ) ∣ (x ^ 2 + 3) - 1 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (x ^ 2 + 3) 3).mp (by simpa using hN.symm)
    obtain ⟨t, ht⟩ := hd
    refine ⟨1, -t, ?_⟩
    nlinarith
  refine ⟨hxeven, hx3, ?_⟩
  simpa using hcop4.mul_right hcop3

/-- The coordinate identity for F₂[ω], without enumerating elements. -/
private theorem modTwo_cube (z : E₂) :
    z ^ 3 = QuadraticAlgebra.C (QuadraticAlgebra.norm z) := by
  have hr := f2_sq z.re
  have ht := f2_sq z.im
  have hr3 : z.re ^ 3 = z.re := by rw [pow_succ, hr, ← pow_two, hr]
  have ht3 : z.im ^ 3 = z.im := by rw [pow_succ, ht, ← pow_two, ht]
  ext
  · simp only [pow_succ, pow_zero, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, mul_one, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.re_C, QuadraticAlgebra.norm_def]
    calc
      _ = z.re ^ 3 - 3 * z.re * z.im ^ 2 + z.im ^ 3 := by ring
      _ = z.re * z.re - z.re * z.im + z.im * z.im := by
        rw [hr3, ht3, ht]
        have htwo : (2 : ZMod 2) = 0 := z2_two
        linear_combination -hr -ht - htwo * (z.re * z.im)
      _ = _ := by ring
  · simp only [pow_succ, pow_zero, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, mul_one, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.im_C]
    calc
      _ = 3 * z.re ^ 2 * z.im - 3 * z.re * z.im ^ 2 := by ring
      _ = 0 := by rw [hr, ht]; ring

private theorem modTwo_cube_of_pow (z : E₂) (n : ℕ) (hn : 0 < n)
    (h : z ^ n = 1) : z ^ 3 = 1 := by
  have hnorm := congrArg (fun w : E₂ => QuadraticAlgebra.norm w) h
  rw [map_pow, QuadraticAlgebra.norm_one, f2_pow _ n hn] at hnorm
  rw [modTwo_cube, hnorm]
  rfl

theorem norm_unit_one (u : EisensteinOrderˣ) :
    QuadraticAlgebra.norm (u : EisensteinOrder) = 1 := by
  have hu : IsUnit (QuadraticAlgebra.norm (u : EisensteinOrder)) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  have hn : 0 ≤ QuadraticAlgebra.norm (u : EisensteinOrder) := by
    simp only [QuadraticAlgebra.norm_def]
    nlinarith [sq_nonneg (2 * (u : EisensteinOrder).re - (u : EisensteinOrder).im),
      sq_nonneg (u : EisensteinOrder).im]
  simpa [abs_of_nonneg hn] using Int.isUnit_iff_abs_eq.mp hu

/-- Uses the existing cyclotomic six-unit classification. No assertion that
an arbitrary chosen equivalence fixes a chosen primitive generator is needed. -/
private theorem unit_six (u : EisensteinOrderˣ) : u ^ 6 = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  let K := CyclotomicField 3 ℚ
  letI : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
  let φ := Classical.choice eisenstein_cyclotomic_equiv_exists
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  let v : (𝓞 K)ˣ := Units.map φ.toRingHom.toMonoidHom u
  have hη3 : η ^ 3 = 1 := by
    apply Units.ext
    change hζ.toInteger ^ 3 = 1
    exact hζ.toInteger_cube_eq_one
  have hη6 : η ^ 6 = 1 := by
    rw [show 6 = 3 * 2 by norm_num, pow_mul, hη3, one_pow]
  have hη26 : (η ^ 2) ^ 6 = 1 := by
    rw [pow_right_comm, hη6, one_pow]
  have hη6val : (η : 𝓞 K) ^ 6 = 1 := by
    exact (Units.val_eq_one (a := η ^ 6)).mpr hη6
  have hv : v ^ 6 = 1 := by
    have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ v
    change v ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h
    · rw [h, one_pow]
    · rw [h]
      apply Units.ext
      change (-1 : 𝓞 K) ^ 6 = 1
      norm_num
    · rw [h]
      exact hη6
    · rw [h]
      apply Units.ext
      change (-(η : 𝓞 K)) ^ 6 = 1
      calc
        _ = (η : 𝓞 K) ^ 6 := by ring
        _ = 1 := hη6val
    · rw [h]
      exact hη26
    · rw [h]
      apply Units.ext
      change (-((η : 𝓞 K) ^ 2)) ^ 6 = 1
      calc
        _ = ((η : 𝓞 K) ^ 6) ^ 2 := by ring
        _ = 1 := by rw [hη6val, one_pow]
  apply Units.ext
  apply φ.injective
  have H := congrArg (fun w : (𝓞 K)ˣ => (w : 𝓞 K)) hv
  simpa [v] using H

/-- A unit in the kernel of reduction modulo two is ±1. This is the
specific coordinate restriction needed at q=3, not a second unit classification. -/
theorem unit_modTwo (u : EisensteinOrderˣ) (hu : modTwo u = 1) :
    (u : EisensteinOrder).im = 0 := by
  have hn := norm_unit_one u
  have hi : ((u : EisensteinOrder).im : ZMod 2) = 0 := by
    simpa [modTwo] using congrArg QuadraticAlgebra.im hu
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hi
  have hb : 3 * (u : EisensteinOrder).im ^ 2 ≤ 4 := by
    simp only [QuadraticAlgebra.norm_def] at hn
    nlinarith [sq_nonneg (2 * (u : EisensteinOrder).re - (u : EisensteinOrder).im)]
  have hb' : -1 ≤ (u : EisensteinOrder).im ∧ (u : EisensteinOrder).im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u : EisensteinOrder).im]
  omega

/-- The primitive actual equation supplies a genuine qth root in the integral
Eisenstein ring; its ω coordinate is even. The q=3 branch is discharged here.
No power-extraction assumption appears among the hypotheses. -/
private theorem primitive_prime_root (x Y : ℤ) (q : ℕ)
    (hxeven : Even x) (hcop : IsCoprime (x ^ 2 + 3) (12 : ℤ))
    (hq : q.Prime) (hqodd : Odd q) (heq : x ^ 2 + 3 = Y ^ q) :
    q ≠ 3 ∧ ∃ γ : EisensteinOrder,
      γ ^ q = (⟨x + 1, 2⟩ : EisensteinOrder) ∧ (2 : ℤ) ∣ γ.im := by
  classical
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
  let α : EisensteinOrder := ⟨x + 1, 2⟩
  let β := star α
  have hn : α * β = ((x ^ 2 + 3 : ℤ) : EisensteinOrder) := by
    ext <;> simp [α, β, pow_two, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] <;> ring
  have h12 : (12 : EisensteinOrder) = -(α - β) ^ 2 := by
    ext <;> simp [α, β, pow_two, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star] <;> ring
  have hc : IsCoprime α β := by
    have H := hcop.intCast (R := EisensteinOrder)
    norm_num only [Int.cast_ofNat] at H
    rw [← hn, h12] at H
    obtain ⟨s, t, hst⟩ := H
    refine ⟨s * β - t * (α - β), t * (α - β), ?_⟩
    linear_combination hst
  have hp : α * β = (Y : EisensteinOrder) ^ q := by
    rw [hn, heq, Int.cast_pow]
  obtain ⟨γ, ε, hγ⟩ := exists_associated_pow_of_mul_eq_pow' hc hp
  -- hγ : γ ^ q * ↑ε = α. This orientation is fixed by Associated's definition.
  have hα2 : modTwo α = 1 := by
    have hx2 : (x : ZMod 2) = 0 := hxeven.intCast_zmod_two
    ext <;> simp [α, modTwo, hx2]
  have hγnorm : ((QuadraticAlgebra.norm γ : ℤ) : ZMod 2) = 1 := by
    have H := congrArg (fun z : EisensteinOrder =>
      ((QuadraticAlgebra.norm z : ℤ) : ZMod 2)) hγ
    have hαnorm : QuadraticAlgebra.norm α = x ^ 2 + 3 := by
      simp only [QuadraticAlgebra.norm_def, α]
      ring
    simp only [map_mul, map_pow, norm_unit_one, mul_one, hαnorm,
      Int.cast_pow, Int.cast_add, Int.cast_ofNat] at H
    rw [hxeven.intCast_zmod_two] at H
    norm_num at H
    rwa [f2_pow _ q hq.pos] at H
  have hγcube : modTwo γ ^ 3 = 1 := by
    rw [modTwo_cube]
    have H : QuadraticAlgebra.norm (modTwo γ) = 1 := by
      simpa [modTwo, QuadraticAlgebra.norm_def, sub_eq_add_neg] using hγnorm
    rw [H]
    rfl
  have hq3 : q ≠ 3 := by
    intro hq3
    have hε2 : modTwo (ε : EisensteinOrder) = 1 := by
      have H := congrArg modTwo hγ
      simpa only [map_mul, map_pow, hq3, hγcube, one_mul, hα2] using H
    have hi := unit_modTwo ε hε2
    have H := congrArg QuadraticAlgebra.im hγ
    have Him : 3 * (γ.re * γ.im * (γ.re - γ.im) * (ε : EisensteinOrder).re) = 2 := by
      simp only [hq3, pow_succ, pow_zero, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, mul_one, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_mul, hi, α, mul_zero, add_zero, zero_mul] at H
      linear_combination H
    have hd : (3 : ℤ) ∣ 2 := ⟨γ.re * γ.im * (γ.re - γ.im) *
      (ε : EisensteinOrder).re, Him.symm⟩
    norm_num at hd
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    norm_num at hqodd
  have hq6 : q.Coprime 6 := by
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    have H : q ∣ 2 ∨ q ∣ 3 := (hq.dvd_mul).mp (show q ∣ 2 * 3 from hd)
    rcases H with h | h
    · rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
      · exact hq.ne_one h
      · exact hq2 h
    · rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
      · exact hq.ne_one h
      · exact hq3 h
  have hεorder : orderOf ε ∣ 6 := orderOf_dvd_of_pow_eq_one (unit_six ε)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := ε)
    (hq6.coprime_dvd_right hεorder)
  let δ : EisensteinOrder := γ * ((ε ^ n : EisensteinOrderˣ) : EisensteinOrder)
  have hδ : δ ^ q = α := by
    dsimp only [δ]
    rw [mul_pow]
    have H : (((ε ^ n : EisensteinOrderˣ) : EisensteinOrder)) ^ q = ε := by
      have H' : (ε ^ n) ^ q = ε := by rw [pow_right_comm]; exact hn
      exact_mod_cast H'
    rw [H]
    exact hγ
  have hδ2 : modTwo δ ^ q = 1 := by
    rw [← map_pow, hδ, hα2]
  have hδcube := modTwo_cube_of_pow (modTwo δ) q hq.pos hδ2
  have hc3 : q.Coprime (orderOf (modTwo δ)) :=
    (hq6.coprime_dvd_right (by norm_num : 3 ∣ 6)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hδcube)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hc3
  have hδone : modTwo δ = 1 := by
    rw [hδ2, one_pow] at hm
    exact hm.symm
  refine ⟨hq3, δ, hδ, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd δ.im 2).mp
  simpa [modTwo] using congrArg QuadraticAlgebra.im hδone


private abbrev Q := QuadraticAlgebra ℤ (-3) 0

/-- The actual integral suborder embedding a+b√(-3) ↦ (a+b)+2bω. -/
private def integralEmbedding : Q →+* EisensteinOrder where
  toFun z := ⟨z.re + z.im, 2 * z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp <;> ring
  map_mul' z w := by ext <;> simp <;> ring

private theorem integralEmbedding_injective : Function.Injective integralEmbedding := by
  intro z w h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  dsimp [integralEmbedding] at hr hi
  ext <;> omega

/-- The coefficient divisibility is an unbounded induction, not a bound on q. -/
private theorem im_dvd_power (z : Q) (n : ℕ) : z.im ∣ (z ^ n).im := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, QuadraticAlgebra.im_mul]
      simp only [zero_mul, add_zero]
      apply dvd_add
      · exact ⟨(z ^ n).re, by ring⟩
      · exact dvd_mul_of_dvd_left ih _

private theorem integral_coordinates (x : ℤ) (q : ℕ) (hq : 0 < q)
    (hxeven : Even x) (hx3 : ¬ (3 : ℤ) ∣ x)
    (γ : EisensteinOrder) (hγ : γ ^ q = (⟨x + 1, 2⟩ : EisensteinOrder))
    (hi : (2 : ℤ) ∣ γ.im) :
    ∃ a b : ℤ, (b = 1 ∨ b = -1) ∧ Even a ∧ ¬ (3 : ℤ) ∣ a ∧
      (⟨a, b⟩ : Q) ^ q = ⟨x, 1⟩ ∧
      (⟨a + b, 2 * b⟩ : EisensteinOrder) ^ q = ⟨x + 1, 2⟩ := by
  obtain ⟨b, hb⟩ := hi
  let a := γ.re - b
  have hγcoords : γ = (⟨a + b, 2 * b⟩ : EisensteinOrder) := by
    ext <;> dsimp [a] <;> omega
  have hQ : (⟨a, b⟩ : Q) ^ q = ⟨x, 1⟩ := by
    apply integralEmbedding_injective
    rw [map_pow]
    change (⟨a + b, 2 * b⟩ : EisensteinOrder) ^ q = ⟨x + 1, 2 * 1⟩
    simpa only [mul_one, ← hγcoords] using hγ
  have hd : b ∣ (1 : ℤ) := by
    have H := im_dvd_power (⟨a, b⟩ : Q) q
    rwa [hQ] at H
  have hbabs : |b| = 1 := Int.isUnit_iff_abs_eq.mp (isUnit_of_dvd_one hd)
  have hbpm : b = 1 ∨ b = -1 := by
    have hlo := neg_abs_le b
    have hhi := le_abs_self b
    have hb0 : b ≠ 0 := by intro h; simp [h] at hbabs
    omega
  have hb2 : b * b = 1 := by
    rcases hbpm with h | h <;> rw [h] <;> norm_num
  have hnorm : (a ^ 2 + 3) ^ q = x ^ 2 + 3 := by
    have H := congrArg (fun z : Q => QuadraticAlgebra.norm z) hQ
    have haNorm : QuadraticAlgebra.norm (⟨a, b⟩ : Q) = a ^ 2 + 3 := by
      simp only [QuadraticAlgebra.norm_def]
      nlinarith [hb2]
    have hxNorm : QuadraticAlgebra.norm (⟨x, 1⟩ : Q) = x ^ 2 + 3 := by
      simp only [QuadraticAlgebra.norm_def]
      ring
    rwa [map_pow, haNorm, hxNorm] at H
  have haeven : Even a := by
    by_contra hn
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hn
    obtain ⟨t, ht⟩ := hxeven
    have ha4 : ((a ^ 2 + 3 : ℤ) : ZMod 4) = 0 := by
      rw [hk]
      push_cast
      ring_nf <;> simp
    have hx4 : ((x ^ 2 + 3 : ℤ) : ZMod 4) = 3 := by
      rw [ht]
      push_cast
      ring_nf <;> simp
    have H := congrArg (fun n : ℤ => (n : ZMod 4)) hnorm
    rw [Int.cast_pow, ha4, hx4, zero_pow (Nat.ne_of_gt hq)] at H
    exact (by decide : (0 : ZMod 4) ≠ 3) H
  have ha3 : ¬ (3 : ℤ) ∣ a := by
    intro ha
    have ha0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mpr ha
    have H := congrArg (fun n : ℤ => (n : ZMod 3)) hnorm
    simp only [Int.cast_pow, Int.cast_add, Int.cast_ofNat] at H
    have hxSq : (x : ZMod 3) ^ 2 = 0 := by
      simpa only [ha0, z3_three,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
        zero_pow (Nat.ne_of_gt hq), add_zero] using H.symm
    have hx0 : (x : ZMod 3) = 0 := eq_zero_of_pow_eq_zero hxSq
    exact hx3 ((ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx0)
  refine ⟨a, b, hbpm, haeven, ha3, hQ, ?_⟩
  simpa only [← hγcoords] using hγ

/-- Every actual integer equation with x≥2 and exponent e≥2 reaches an odd
prime exponent q≥5 and an actual integral root a+b√(-3), where b=±1.
This helper is consumed by the actual Cohn polynomial reduction below. -/
private theorem equation_to_eisenstein_root (x y : ℤ) (e : ℕ)
    (hx : 2 ≤ x) (he : 2 ≤ e) (heq : x ^ 2 + 3 = y ^ e) :
    ∃ q : ℕ, q.Prime ∧ q ∣ e ∧ 5 ≤ q ∧ Odd q ∧
      Even x ∧ ¬ (3 : ℤ) ∣ x ∧
      ∃ a b : ℤ, (b = 1 ∨ b = -1) ∧ Even a ∧ ¬ (3 : ℤ) ∣ a ∧
        (⟨a, b⟩ : QuadraticAlgebra ℤ (-3) 0) ^ q = ⟨x, 1⟩ ∧
        (⟨a + b, 2 * b⟩ : EisensteinOrder) ^ q = ⟨x + 1, 2⟩ := by
  have hneven : ¬ Even e := by
    rintro ⟨k, hk⟩
    have hs : x ^ 2 + 3 = (y ^ k) ^ 2 := by
      rw [heq, hk, pow_add, pow_two]
    have ha : x < |y ^ k| := by
      by_contra hn
      have H := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn))
        (show 0 ≤ x + |y ^ k| by positivity)
      nlinarith [sq_abs (y ^ k)]
    have hb : x + 1 ≤ |y ^ k| := by omega
    have H := mul_nonneg (sub_nonneg.mpr hb)
      (show 0 ≤ |y ^ k| + (x + 1) by positivity)
    nlinarith [sq_abs (y ^ k)]
  obtain ⟨q, hq, hqe⟩ := Nat.exists_prime_and_dvd (show e ≠ 1 by omega)
  have hq2 : q ≠ 2 := by
    intro h
    apply hneven
    exact even_iff_two_dvd.mpr (h ▸ hqe)
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have hqge : 3 ≤ q := hq.odd_iff.mp hqo
  have hprime : x ^ 2 + 3 = (y ^ (e / q)) ^ q := by
    rw [← pow_mul, Nat.div_mul_cancel hqe]
    exact heq
  obtain ⟨hxeven, hx3, hcop⟩ := primitive_data x (y ^ (e / q)) q hqge hprime
  obtain ⟨hq3, γ, hγ, hi⟩ := primitive_prime_root x (y ^ (e / q)) q
    hxeven hcop hq hqo hprime
  have hq5 : 5 ≤ q := by
    have hmod := hq.eq_two_or_odd.resolve_left hq2
    omega
  refine ⟨q, hq, hqe, hq5, hqo, hxeven, hx3, ?_⟩
  exact integral_coordinates x q hq.pos hxeven hx3 γ hγ hi


open D5.S3.Arith.Congruence.CohnUniformThreeAdic
open Polynomial Finset

/-- Actual signed coefficient comparison and residue reduction for arbitrary
odd q≥5. This is not an assumed bridge and uses the supplied polynomial. -/
private theorem integral_root_to_cohn (q : ℕ) (a b x : ℤ)
    (hq : Odd q) (hq5 : 5 ≤ q) (ha : Even a) (ha3 : ¬ (3 : ℤ) ∣ a)
    (hb : b = 1 ∨ b = -1)
    (hpow : (⟨a, b⟩ : QuadraticAlgebra ℤ (-3) 0) ^ q = ⟨x, 1⟩) :
    7 ≤ q ∧ q % 6 = 1 ∧ (3 : ℤ) ∣ a ^ 2 - 1 ∧
      (cohnPolynomial q).eval (a ^ 2 - 1) = 1 := by
  let m := (q - 1) / 2
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp hq
  have hqm : q = 2 * m + 1 := by dsimp [m]; omega
  have heval := cohn_polynomial_eval_power q a hq
  have hsign : (cohnPolynomial q).eval (a ^ 2 - 1) = 1 ∨
      (cohnPolynomial q).eval (a ^ 2 - 1) = -1 := by
    rcases hb with rfl | rfl
    · left
      have H := congrArg QuadraticAlgebra.im hpow
      exact heval.trans H
    · right
      have hbase : (starRingEnd Q) (⟨a, 1⟩ : Q) = ⟨a, -1⟩ := by
        change star (⟨a, 1⟩ : Q) = ⟨a, -1⟩
        ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
      have H := congrArg QuadraticAlgebra.im
        ((starRingEnd Q).map_pow (⟨a, 1⟩ : Q) q)
      rw [hbase, hpow] at H
      have hi : -((⟨a, 1⟩ : Q) ^ q).im = 1 := by
        change (star ((⟨a, 1⟩ : Q) ^ q)).im = 1 at H
        simpa only [QuadraticAlgebra.im_star] using H
      omega
  have hshift : (1 : ℤ) + (a ^ 2 - 1) = a ^ 2 := by ring
  have hEval : (cohnPolynomial q).eval (a ^ 2 - 1) =
      ∑ k ∈ range (m + 1),
        (q.choose (2 * k + 1) : ℤ) * (-3) ^ k * (a ^ 2) ^ (m - k) := by
    simp only [m, cohnPolynomial, eval_finsetSum, eval_mul, eval_C,
      eval_pow, eval_add, eval_one, eval_X, hshift]
  have ha4 : (a : ZMod 4) ^ 2 = 0 := by
    obtain ⟨k, hk⟩ := ha
    rw [hk]
    push_cast
    ring_nf <;> simp
  have hfour : (((cohnPolynomial q).eval (a ^ 2 - 1) : ℤ) : ZMod 4) = 1 := by
    have H := congrArg (fun n : ℤ => (n : ZMod 4)) hEval
    push_cast at H
    rw [H]
    calc
      (∑ k ∈ range (m + 1),
        (q.choose (2 * k + 1) : ZMod 4) * (-3) ^ k *
          ((a : ZMod 4) ^ 2) ^ (m - k)) =
          (q.choose (2 * m + 1) : ZMod 4) * (-3) ^ m *
            ((a : ZMod 4) ^ 2) ^ (m - m) := by
        apply Finset.sum_eq_single
        · intro k hk hkm
          have hlt : k < m := by have := mem_range.mp hk; omega
          rw [ha4, zero_pow (by omega : m - k ≠ 0), mul_zero]
        · intro hn
          exact (hn (mem_range.mpr (by omega))).elim
      _ = 1 := by rw [← hqm, Nat.choose_self, z4_negthree]; simp
  have hP : (cohnPolynomial q).eval (a ^ 2 - 1) = 1 := by
    rcases hsign with h | h
    · exact h
    · rw [h] at hfour
      exact ((by decide : (-1 : ZMod 4) ≠ 1) hfour).elim
  have ha0 : (a : ZMod 3) ≠ 0 := by
    intro h
    exact ha3 ((ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp h)
  have haSq : (a : ZMod 3) ^ 2 = 1 := by
    simpa using FiniteField.pow_card_sub_one_eq_one (a : ZMod 3) ha0
  have hthree : (((cohnPolynomial q).eval (a ^ 2 - 1) : ℤ) : ZMod 3) = (q : ZMod 3) := by
    have H := congrArg (fun n : ℤ => (n : ZMod 3)) hEval
    push_cast at H
    rw [H]
    calc
      (∑ k ∈ range (m + 1),
        (q.choose (2 * k + 1) : ZMod 3) * (-3) ^ k *
          ((a : ZMod 3) ^ 2) ^ (m - k)) =
          (q.choose (2 * 0 + 1) : ZMod 3) * (-3) ^ (0 : ℕ) *
            ((a : ZMod 3) ^ 2) ^ (m - 0) := by
        apply Finset.sum_eq_single
        · intro k _ hk
          simp [show (-3 : ZMod 3) = 0 by rw [z3_three, neg_zero], zero_pow hk]
        · intro hn
          exact (hn (mem_range.mpr (by omega))).elim
      _ = (q : ZMod 3) := by simp [haSq]
  have hqcast : (q : ZMod 3) = 1 := by
    rw [hP] at hthree
    simpa using hthree.symm
  have hq3 : q % 3 = 1 := by
    have H := congrArg ZMod.val hqcast
    simpa [ZMod.val_natCast, ZMod.val_one_eq_one_mod] using H
  have hq6 : q % 6 = 1 := by omega
  have hxi : (3 : ℤ) ∣ a ^ 2 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 - 1) 3).mp
    push_cast
    rw [haSq]
    ring
  exact ⟨by omega, hq6, hxi, hP⟩

/-- Square plus three is not an integer power with exponent at least two when x ≥ 2. -/
theorem int_sq_add_three_not_pow (x y : ℤ) (e : ℕ)
    (hx : 2 ≤ x) (he : 2 ≤ e) : x ^ 2 + 3 ≠ y ^ e := by
  intro heq
  obtain ⟨q, hq, hqe, hq5, hqo, hxeven, hx3, a, b, hb, ha, ha3, hpow, hE⟩ :=
    equation_to_eisenstein_root x y e hx he heq
  obtain ⟨hq7, hq6, hxi, hP⟩ := integral_root_to_cohn q a b x hqo hq5 ha ha3 hb hpow
  exact cohn_polynomial_ne_one q (a ^ 2 - 1) hq7 hq6 hxi hP


end D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
