/- GID: D5/S3/Factorization/QuadraticIdeals/CubicGaussPrimePower
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/CubicGaussPrimePower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-power Frobenius gives cubic reciprocity across distinct residue characteristics. -/

import D5.S3.Factorization.QuadraticIdeals.CubicGaussFrobenius
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.CharAndCard

/-
UNCOMPILED SOURCE-ONLY CANDIDATE. No Lean command has been run on this file.

This independent research draft generalizes the distinct-characteristic Gauss
argument from prime residue cardinalities to arbitrary finite maximal quotients.
In particular, the target cardinal may be r^2 for an inert rational prime r.
It imports the existing normalization and cubic finite-sum development; those
imports and this source still require actual acceptance before any verification claim.

The generic Frobenius statement keeps both characters moving until the full
prime-power exponent has been taken. It does NOT assume r = 1 modulo 3 at an
intermediate Frobenius step. The final arithmetic endpoints assume neither a
Gauss-sum value, a Jacobi value, an algebraic norm, nor a comparison identity.
The existing normalization supplies J_P = -pi and Norm(pi) = N(P).
The cubic-root calculations and arithmetic descent are adapted from the
existing CubicGaussFrobenius source; their provenance is retained here.

Canonical WIP source only, with no build receipt or official acceptance claim.
Its mathematical and API choices have only been inspected as source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Factorization.QuadraticIdeals.CubicGaussPrimePower

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization
open D5.S3.Factorization.QuadraticIdeals.CubicGaussFrobenius

abbrev E := EisensteinOrder

section GenericFrobenius

variable {F K : Type*} [CommRing F] [Fintype F] [CommRing K]

/-- The unrestricted prime-power Frobenius identity. Positivity of r^b is
needed for evaluation of the zero-extended multiplicative character. -/
theorem gaussSum_frob_pow (χ : MulChar F K) (ψ : AddChar F K)
    (r b : ℕ) [Fact r.Prime] [CharP K r] :
    gaussSum χ ψ ^ (r ^ b) = gaussSum (χ ^ (r ^ b)) (ψ ^ (r ^ b)) := by
  have hrb : r ^ b ≠ 0 := pow_ne_zero _ (Fact.out : r.Prime).ne_zero
  calc
    gaussSum χ ψ ^ (r ^ b) =
        (iterateFrobenius K r b) (gaussSum χ ψ) := rfl
    _ = ∑ x : F, χ x ^ (r ^ b) * ψ x ^ (r ^ b) := by
      rw [gaussSum, map_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [map_mul, iterateFrobenius_def, iterateFrobenius_def]
    _ = gaussSum (χ ^ (r ^ b)) (ψ ^ (r ^ b)) := by
      simp only [gaussSum, MulChar.pow_apply' χ hrb, AddChar.pow_apply]

end GenericFrobenius

section CubicFiniteSum

variable {F K : Type*} [Field F] [Fintype F] [Field K]

/-- Fix the cubic character only after taking the full exponent r^b.
This includes r = 2 modulo 3 with b even. -/
theorem cubic_gauss_frobenius_prime_power
    (χ : MulChar F K) (hc : χ ^ 3 = 1) (ψ : AddChar F K)
    (r b : ℕ) [Fact r.Prime] [CharP K r]
    (hq : (r ^ b) % 3 = 1) (hqF : IsUnit ((r ^ b : ℕ) : F)) :
    gaussSum χ ψ ^ (r ^ b) =
      (χ ((r ^ b : ℕ) : F))⁻¹ * gaussSum χ ψ := by
  rw [gaussSum_frob_pow χ ψ r b,
    cubic_character_pow_eq_self χ hc hq, AddChar.pow_mulShift]
  have hshift := gaussSum_mulShift_eq χ ψ hqF.unit
  simpa only [hqF.unit_spec, MulChar.inv_apply_eq_inv'] using hshift

/-- A reusable prime-power comparison; its right side is derived from the
exact cubic Gauss identity rather than supplied as a hypothesis. -/
theorem cubic_gauss_euler_comparison_prime_power
    (χ : MulChar F K) (hχ : orderOf χ = 3)
    (ψ : AddChar F K) (hψ : ψ.IsPrimitive)
    (r b : ℕ) [Fact r.Prime] [CharP K r]
    (hq : (r ^ b) % 3 = 1) (hqF : IsUnit ((r ^ b : ℕ) : F))
    (hcard : (Fintype.card F : K) ≠ 0) :
    (χ ((r ^ b : ℕ) : F))⁻¹ =
      ((Fintype.card F : K) * jacobiSum χ χ) ^ ((r ^ b - 1) / 3) := by
  let G := gaussSum χ ψ
  have hc : χ ^ 3 = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
  have hn : χ ≠ 1 := by intro h; simp [h] at hχ
  have hG : G ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hn hψ
  have hf : G ^ (r ^ b) = (χ ((r ^ b : ℕ) : F))⁻¹ * G :=
    cubic_gauss_frobenius_prime_power χ hc ψ r b hq hqF
  have hqpos : 0 < r ^ b := pow_pos (Fact.out : r.Prime).pos _
  have he : G ^ (r ^ b - 1) = (χ ((r ^ b : ℕ) : F))⁻¹ := by
    apply (mul_left_injective₀ hG)
    change G ^ (r ^ b - 1) * G = (χ ((r ^ b : ℕ) : F))⁻¹ * G
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r ^ b)]
    exact hf
  have hq3 : 3 * ((r ^ b - 1) / 3) = r ^ b - 1 := by omega
  calc
    (χ ((r ^ b : ℕ) : F))⁻¹ = G ^ (r ^ b - 1) := he.symm
    _ = (G ^ 3) ^ ((r ^ b - 1) / 3) := by rw [← pow_mul, hq3]
    _ = _ := by rw [cubic_gauss_cube χ hχ ψ hψ]

end CubicFiniteSum

/-- A finite field's cardinality stays nonzero in every field of different
characteristic, including when its residue degree is greater than one. -/
theorem finite_field_card_cast_ne_zero
    (F T : Type*) [Field F] [Fintype F] [Field T]
    (hchar : ringChar T ≠ ringChar F) : (Fintype.card F : T) ≠ 0 := by
  obtain ⟨a, hs, hF⟩ := FiniteField.card F (ringChar F)
  have hsT : (ringChar F : T) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime T hs hchar
  rw [hF, Nat.cast_pow]
  exact pow_ne_zero _ hsT

/-- The comparison at the cardinality of a finite target field. The target
extension K need not itself be finite. Characteristic and cross-cardinality
nonvanishing are derived from g and the two finite fields. -/
theorem cubic_gauss_euler_comparison_card
    {F T K : Type*} [Field F] [Fintype F] [Field T] [Fintype T] [Field K]
    (χ : MulChar F K) (hχ : orderOf χ = 3)
    (ψ : AddChar F K) (hψ : ψ.IsPrimitive)
    (g : T →+* K) (hchar : ringChar T ≠ ringChar F)
    (hq : Fintype.card T % 3 = 1) :
    (χ (Fintype.card T : F))⁻¹ =
      ((Fintype.card F : K) * jacobiSum χ χ) ^ ((Fintype.card T - 1) / 3) := by
  obtain ⟨b, hr, hT⟩ := FiniteField.card T (ringChar T)
  letI : Fact (ringChar T).Prime := ⟨hr⟩
  letI : CharP K (ringChar T) :=
    charP_of_injective_ringHom g.injective (ringChar T)
  have hKchar : ringChar K ≠ ringChar F := by
    rw [ringChar.eq K (ringChar T)]
    exact hchar
  have hqF : IsUnit (Fintype.card T : F) := isUnit_iff_ne_zero.mpr
    (finite_field_card_cast_ne_zero T F hchar.symm)
  have hcard : (Fintype.card F : K) ≠ 0 :=
    finite_field_card_cast_ne_zero F K hKchar
  have H := cubic_gauss_euler_comparison_prime_power χ hχ ψ hψ
    (ringChar T) (b : ℕ)
    (by simpa only [← hT] using hq)
    (by simpa only [← hT] using hqF) hcard
  simpa only [← hT] using H

/- The next two helpers avoid both a splitting classification and cardinality
primality premises at the public arithmetic endpoint. -/

/-- A primary generator of a proper maximal ideal excludes three from it. -/
theorem primary_generator_three_not_mem
    (P : Ideal E) [P.IsMaximal] (π : E)
    (hπ : Ideal.span {π} = P) (hprimary : (3 : E) ∣ π - 1) :
    (3 : E) ∉ P := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  intro hthree
  have hπmem : π ∈ P := by
    rw [← hπ]
    exact Ideal.mem_span_singleton_self π
  obtain ⟨k, hk⟩ := hprimary
  have hdiff : π - 1 ∈ P := by
    rw [hk]
    exact Ideal.mul_mem_right k P hthree
  have hone : (1 : E) ∈ P := by
    have H := P.sub_mem hπmem hdiff
    simpa only [sub_sub_cancel] using H
  have hz : (1 : E ⧸ P) = 0 := by
    simpa only [map_one] using (Ideal.Quotient.eq_zero_iff_mem.mpr hone)
  exact one_ne_zero hz

private theorem omega_quad : (QuadraticAlgebra.omega : E) ^ 2 +
    QuadraticAlgebra.omega + 1 = 0 := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp

private theorem omega_cube : (QuadraticAlgebra.omega : E) ^ 3 = 1 := by
  linear_combination (QuadraticAlgebra.omega - 1) * omega_quad

/-- Away from three, the quotient contains a unit of exact order three.
Lagrange therefore gives its cardinality modulo three, even for inert ideals. -/
theorem residue_card_mod_three_of_three_not_mem
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (hthree : (3 : E) ∉ P) : Nat.card (E ⧸ P) % 3 = 1 := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let w : E ⧸ P := Ideal.Quotient.mk P QuadraticAlgebra.omega
  have h3 : (3 : E ⧸ P) ≠ 0 := by
    intro h
    exact hthree (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h))
  have hw3 : w ^ 3 = 1 := by
    change Ideal.Quotient.mk P QuadraticAlgebra.omega ^ 3 = 1
    rw [← map_pow, omega_cube, map_one]
  have hwquad : w ^ 2 + w + 1 = 0 := by
    have H := congrArg (Ideal.Quotient.mk P) omega_quad
    simpa only [map_add, map_pow, map_one, map_zero] using H
  have hwne : w ≠ 1 := by
    intro h
    have hz : (3 : E ⧸ P) = 0 := by
      calc
        (3 : E ⧸ P) = w ^ 2 + w + 1 := by rw [h]; ring
        _ = 0 := hwquad
    exact h3 hz
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 3 ≠ 0)] at hw3
    exact zero_ne_one hw3
  let u : (E ⧸ P)ˣ := Units.mk0 w hw0
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    change w ^ 3 = 1
    exact hw3
  have hune : u ≠ 1 := by
    intro h
    apply hwne
    exact congrArg (fun v : (E ⧸ P)ˣ => (v : E ⧸ P)) h
  have huorder : orderOf u = 3 := orderOf_eq_prime hu3 hune
  have hdvd : 3 ∣ Fintype.card (E ⧸ P) - 1 := by
    simpa only [huorder, Fintype.card_units] using (orderOf_dvd_card (x := u))
  have hq : 1 < Fintype.card (E ⧸ P) := Fintype.one_lt_card
  have hmod : Fintype.card (E ⧸ P) % 3 = 1 := by omega
  simpa only [Fintype.card_eq_nat_card] using hmod

/-- The actual transported Euler character satisfies the scalar comparison at
N(Q). The normalization, and not a new hypothesis, supplies J_P = -pi. -/
theorem cubic_gauss_primary_scalar_card
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (hPthree : (3 : E) ∉ P) (hQthree : (3 : E) ∉ Q)
    (hchar : ringChar (E ⧸ Q) ≠ ringChar (E ⧸ P))
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1)
    {K : Type*} [Field K] (g : (E ⧸ Q) →+* K)
    (ψ : AddChar (E ⧸ P) K) (hψ : ψ.IsPrimitive) :
    let f : E →+* K := g.comp (Ideal.Quotient.mk Q)
    let χ := cubicResidueMulChar P
      (residue_card_mod_three_of_three_not_mem P hPthree) hPthree
    (f (χ (Ideal.Quotient.mk P (Nat.card (E ⧸ Q) : E))))⁻¹ =
      f (-(Nat.card (E ⧸ P) : E) * π) ^ ((Nat.card (E ⧸ Q) - 1) / 3) := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : Fintype (E ⧸ Q) := Fintype.ofFinite _
  let f : E →+* K := g.comp (Ideal.Quotient.mk Q)
  let hPmod := residue_card_mod_three_of_three_not_mem P hPthree
  let hQmod := residue_card_mod_three_of_three_not_mem Q hQthree
  let χ := cubicResidueMulChar P hPmod hPthree
  let θ := χ.ringHomComp f
  have h3Q : Ideal.Quotient.mk Q (3 : E) ≠ 0 := by
    intro h
    exact hQthree (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h3 : f 3 ≠ 0 := by
    intro h
    exact h3Q (g.injective (h.trans g.map_zero.symm))
  have hθ : orderOf θ = 3 :=
    residue_character_comp_order_three P hPmod hPthree f h3
  have hJE : jacobiSum χ χ = -π := by
    have H := cubicJacobiSum_eq_primary_generator P hPmod hPthree π hπ hπprimary
    exact neg_eq_iff_eq_neg.mp H
  have hJK : jacobiSum θ θ = f (-π) := by
    rw [jacobiSum_ringHomComp, hJE]
  have H := cubic_gauss_euler_comparison_card θ hθ ψ hψ g hchar
    (by simpa only [Fintype.card_eq_nat_card] using hQmod)
  simp only [Fintype.card_eq_nat_card, hJK] at H
  have hprod : (Nat.card (E ⧸ P) : K) * f (-π) =
      f (-(Nat.card (E ⧸ P) : E) * π) := by
    rw [map_mul, map_neg, map_neg, map_natCast]
    ring
  rw [hprod] at H
  simpa only [θ, MulChar.ringHomComp_apply, map_natCast] using H

private theorem cubic_root_cube {a : E} (ha : IsCubicRoot a) : a ^ 3 = 1 := by
  rcases ha with rfl | rfl | rfl
  · exact one_pow 3
  · exact omega_cube
  · calc
      ((QuadraticAlgebra.omega : E) ^ 2) ^ 3 =
          (QuadraticAlgebra.omega ^ 3) ^ 2 := by ring
      _ = 1 := by rw [omega_cube, one_pow]

private theorem cubic_roots_mul {a b : E} (ha : IsCubicRoot a) (hb : IsCubicRoot b) :
    IsCubicRoot (a * b) := by
  let w : E := QuadraticAlgebra.omega
  change a = 1 ∨ a = w ∨ a = w ^ 2 at ha
  change b = 1 ∨ b = w ∨ b = w ^ 2 at hb
  change a * b = 1 ∨ a * b = w ∨ a * b = w ^ 2
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · left; ring
  · right; left; ring
  · right; right; ring
  · right; left; ring
  · right; right; ring
  · left; calc w * w ^ 2 = w ^ 3 := by ring
               _ = 1 := omega_cube
  · right; right; ring
  · left; calc w ^ 2 * w = w ^ 3 := by ring
               _ = 1 := omega_cube
  · right; left; calc w ^ 2 * w ^ 2 = w ^ 3 * w := by ring
                     _ = w := by rw [show w ^ 3 = 1 from omega_cube, one_mul]

/-- The asymmetric comparison for arbitrary finite maximal quotients of
different characteristics, with no rational-prime cardinality premise. -/
theorem cubic_residue_comparison_different_char
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (hPthree : (3 : E) ∉ P) (hQthree : (3 : E) ∉ Q)
    (hchar : ringChar (E ⧸ Q) ≠ ringChar (E ⧸ P))
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1) :
    let χP := cubicResidueMulChar P
      (residue_card_mod_three_of_three_not_mem P hPthree) hPthree
    let χQ := cubicResidueMulChar Q
      (residue_card_mod_three_of_three_not_mem Q hQthree) hQthree
    χP (Ideal.Quotient.mk P (Nat.card (E ⧸ Q) : E)) =
      χQ (Ideal.Quotient.mk Q π) * χQ (Ideal.Quotient.mk Q (star π)) ^ 2 := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : Fintype (E ⧸ Q) := Fintype.ofFinite _
  let hPmod := residue_card_mod_three_of_three_not_mem P hPthree
  let hQmod := residue_card_mod_three_of_three_not_mem Q hQthree
  let χP := cubicResidueMulChar P hPmod hPthree
  let χQ := cubicResidueMulChar Q hQmod hQthree
  let n := Nat.card (E ⧸ P)
  let q := Nat.card (E ⧸ Q)
  let ψ := AddChar.FiniteField.primitiveChar (E ⧸ P) (E ⧸ Q) hchar
  let K := CyclotomicField ψ.n (E ⧸ Q)
  let g : (E ⧸ Q) →+* K := algebraMap (E ⧸ Q) K
  let f : E →+* K := g.comp (Ideal.Quotient.mk Q)
  have h3Q : Ideal.Quotient.mk Q (3 : E) ≠ 0 := by
    intro h
    exact hQthree (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h3 : f 3 ≠ 0 := by
    intro h
    exact h3Q (g.injective (h.trans g.map_zero.symm))
  have H := cubic_gauss_primary_scalar_card P Q hPthree hQthree hchar
    π hπ hπprimary g ψ.char ψ.prim
  have hnorm : QuadraticAlgebra.norm π = (n : ℤ) := by
    have hj := cubicJacobiSum_eq_primary_generator P hPmod hPthree π hπ hπprimary
    rw [← hj, QuadraticAlgebra.norm_neg, cubicJacobiSum_norm P hPmod hPthree]
  have hn_factor : (n : E) = π * star π := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hnorm]
    rfl
  let a := χP (Ideal.Quotient.mk P (q : E))
  let b := χQ (Ideal.Quotient.mk Q π)
  let c := χQ (Ideal.Quotient.mk Q (star π))
  let d := χQ (Ideal.Quotient.mk Q (-(n : E) * π))
  have hnQ : Ideal.Quotient.mk Q (n : E) ≠ 0 := by
    simpa only [n, map_natCast, Fintype.card_eq_nat_card] using
      finite_field_card_cast_ne_zero (E ⧸ P) (E ⧸ Q) hchar
  have hfactors : Ideal.Quotient.mk Q π * Ideal.Quotient.mk Q (star π) ≠ 0 := by
    rw [← map_mul, ← hn_factor]
    exact hnQ
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := left_ne_zero_of_mul hfactors
  have hbarQ : Ideal.Quotient.mk Q (star π) ≠ 0 := right_ne_zero_of_mul hfactors
  have hqP : Ideal.Quotient.mk P (q : E) ≠ 0 := by
    simpa only [q, map_natCast, Fintype.card_eq_nat_card] using
      finite_field_card_cast_ne_zero (E ⧸ Q) (E ⧸ P) hchar.symm
  have hdQ : Ideal.Quotient.mk Q (-(n : E) * π) ≠ 0 := by
    rw [map_mul, map_neg]
    exact mul_ne_zero (neg_ne_zero.mpr hnQ) hπQ
  have ha : IsCubicRoot a := residueCubicValue_mem_roots P hPmod hPthree _ hqP
  have hb : IsCubicRoot b := residueCubicValue_mem_roots Q hQmod hQthree _ hπQ
  have hc : IsCubicRoot c := residueCubicValue_mem_roots Q hQmod hQthree _ hbarQ
  have hd : IsCubicRoot d := residueCubicValue_mem_roots Q hQmod hQthree _ hdQ
  have hEuler (x : E) :
      f (χQ (Ideal.Quotient.mk Q x)) = f x ^ ((q - 1) / 3) := by
    change g (Ideal.Quotient.mk Q (χQ (Ideal.Quotient.mk Q x))) = _
    rw [cubicResidueMulChar_reduction Q hQmod hQthree, map_pow]
    rfl
  have Had : (f a)⁻¹ = f d := by
    change (f a)⁻¹ = f (χQ (Ideal.Quotient.mk Q (-(n : E) * π)))
    rw [hEuler]
    exact H
  have hfa : f a ≠ 0 := by
    intro hz
    have Hcube := congrArg f (cubic_root_cube ha)
    rw [map_pow, hz, zero_pow (by decide : 3 ≠ 0), map_one] at Hcube
    exact zero_ne_one Hcube
  have had : a * d = 1 := by
    apply cubic_roots_injective f h3 (cubic_roots_mul ha hd) (Or.inl rfl)
    rw [map_mul, map_one, ← Had, mul_inv_cancel₀ hfa]
  have hd_formula : d = b ^ 2 * c := by
    have hinput : Ideal.Quotient.mk Q (-(n : E) * π) =
        (-1 : E ⧸ Q) *
          (Ideal.Quotient.mk Q π ^ 2 * Ideal.Quotient.mk Q (star π)) := by
      rw [hn_factor, map_mul, map_neg, map_mul]
      ring
    change χQ (Ideal.Quotient.mk Q (-(n : E) * π)) = _
    rw [hinput, map_mul, map_mul, map_pow,
      cubic_character_neg_one χQ (cubicResidueMulChar_cube Q hQmod hQthree), one_mul]
  have hbd : (b * c ^ 2) * d = 1 := by
    rw [hd_formula]
    calc
      (b * c ^ 2) * (b ^ 2 * c) = b ^ 3 * c ^ 3 := by ring
      _ = 1 := by rw [cubic_root_cube hb, cubic_root_cube hc, one_mul]
  change a = b * c ^ 2
  calc
    a = a * 1 := (mul_one a).symm
    _ = a * ((b * c ^ 2) * d) := by rw [hbd]
    _ = (a * d) * (b * c ^ 2) := by ring
    _ = b * c ^ 2 := by rw [had, one_mul]

/-- Reciprocity for arbitrary finite maximal quotients of different
characteristics. All cardinality/mod-three and nonvanishing side conditions
are proved internally. This includes inert residue cardinalities r^2. -/
theorem cubic_reciprocity_primary_different_char
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (hchar : ringChar (E ⧸ Q) ≠ ringChar (E ⧸ P))
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
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : Fintype (E ⧸ Q) := Fintype.ofFinite _
  let hPthree := primary_generator_three_not_mem P π hπ hπprimary
  let hQthree := primary_generator_three_not_mem Q ρ hρ hρprimary
  let hPmod := residue_card_mod_three_of_three_not_mem P hPthree
  let hQmod := residue_card_mod_three_of_three_not_mem Q hQthree
  let χP := cubicResidueMulChar P hPmod hPthree
  let χQ := cubicResidueMulChar Q hQmod hQthree
  let A := χQ (Ideal.Quotient.mk Q π)
  let B := χQ (Ideal.Quotient.mk Q (star π))
  let C := χP (Ideal.Quotient.mk P ρ)
  let D := χP (Ideal.Quotient.mk P (star ρ))
  have hn_norm : QuadraticAlgebra.norm π = (Nat.card (E ⧸ P) : ℤ) := by
    have hj := cubicJacobiSum_eq_primary_generator P hPmod hPthree π hπ hπprimary
    rw [← hj, QuadraticAlgebra.norm_neg, cubicJacobiSum_norm P hPmod hPthree]
  have hq_norm : QuadraticAlgebra.norm ρ = (Nat.card (E ⧸ Q) : ℤ) := by
    have hj := cubicJacobiSum_eq_primary_generator Q hQmod hQthree ρ hρ hρprimary
    rw [← hj, QuadraticAlgebra.norm_neg, cubicJacobiSum_norm Q hQmod hQthree]
  have hn_factor : (Nat.card (E ⧸ P) : E) = π * star π := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hn_norm]
    rfl
  have hq_factor : (Nat.card (E ⧸ Q) : E) = ρ * star ρ := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hq_norm]
    rfl
  have hqeval : χP (Ideal.Quotient.mk P (Nat.card (E ⧸ Q) : E)) = C * D := by
    rw [hq_factor, map_mul, map_mul]
  have hneval : χQ (Ideal.Quotient.mk Q (Nat.card (E ⧸ P) : E)) = A * B := by
    rw [hn_factor, map_mul, map_mul]
  have hCD : C * D = A * B ^ 2 := by
    have H := cubic_residue_comparison_different_char P Q hPthree hQthree hchar
      π hπ hπprimary
    change χP (Ideal.Quotient.mk P (Nat.card (E ⧸ Q) : E)) = A * B ^ 2 at H
    rw [hqeval] at H
    exact H
  have hAB : A * B = C * D ^ 2 := by
    have H := cubic_residue_comparison_different_char Q P hQthree hPthree hchar.symm
      ρ hρ hρprimary
    change χQ (Ideal.Quotient.mk Q (Nat.card (E ⧸ P) : E)) = C * D ^ 2 at H
    rw [hneval] at H
    exact H
  have hnQ : Ideal.Quotient.mk Q (Nat.card (E ⧸ P) : E) ≠ 0 := by
    simpa only [map_natCast, Fintype.card_eq_nat_card] using
      finite_field_card_cast_ne_zero (E ⧸ P) (E ⧸ Q) hchar
  have hfactors : Ideal.Quotient.mk Q π * Ideal.Quotient.mk Q (star π) ≠ 0 := by
    rw [← map_mul, ← hn_factor]
    exact hnQ
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := left_ne_zero_of_mul hfactors
  have hbarQ : Ideal.Quotient.mk Q (star π) ≠ 0 := right_ne_zero_of_mul hfactors
  have hA : A ^ 3 = 1 := cubic_root_cube
    (residueCubicValue_mem_roots Q hQmod hQthree _ hπQ)
  have hB : B ^ 3 = 1 := cubic_root_cube
    (residueCubicValue_mem_roots Q hQmod hQthree _ hbarQ)
  exact cubic_reciprocity_algebra A B C D hA hB hCD hAB

/- Acceptance boundary: source preserved only. No parser, elaborator, kernel,
axiom-closure, scoped report, or official CI acceptance has been obtained for
this candidate. It is independent of the current delivery and its cache.
-/

end D5.S3.Factorization.QuadraticIdeals.CubicGaussPrimePower
