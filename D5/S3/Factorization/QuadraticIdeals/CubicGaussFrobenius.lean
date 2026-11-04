/- GID: D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gauss sums and Frobenius prove cubic reciprocity for primary primes. -/

import D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.CharP.CharAndCard

/-! # Cubic reciprocity from Gauss sums and Frobenius

Mathlib convention: gaussSum χ ψ = ∑ x, χ x * ψ x.
`gaussSum_mulShift_eq` therefore has χ⁻¹(a), not χ(a).
The three finite-sum steps below use existing exact upstream identities:
`gaussSum_frob`, `AddChar.pow_mulShift`, `gaussSum_mulShift_eq`, and
`gaussSum_pow_eq_prod_jacobiSum`. No additive character is replaced by ψ⁻¹.

The intended arithmetic application has distinct rational primes p,q ≡ 1 mod 3,
P,Q of residue cardinalities p,q, and a primary generator π of P. The companion
normalization gives J_P=-π and Norm π=p as proved conclusions. Reducing at Q
in a cyclotomic extension gives G³=-pπ and G^q=χ_P(q)⁻¹G; these imply
χ_P(q)=χ_Q(π)χ_Q(star π)². The final transport and reciprocal identities are derived below from the
normalization and finite-sum identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Factorization.QuadraticIdeals.CubicGaussFrobenius

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization

abbrev E := EisensteinOrder

/-- Cubic character values are fixed by the q-th power when q≡1 mod 3. -/
theorem cubic_character_pow_eq_self {F K : Type*}
    [CommMonoid F] [CommMonoidWithZero K] (χ : MulChar F K) (hc : χ ^ 3 = 1)
    {q : ℕ} (hq : q % 3 = 1) : χ ^ q = χ := by
  have hq' : q = 3 * (q / 3) + 1 := by omega
  rw [hq', pow_add, pow_mul, hc, one_pow, pow_one, one_mul]

/-- Every character of exponent dividing three has χ(-1)=1. -/
theorem cubic_character_neg_one {F K : Type*}
    [CommRing F] [CommMonoidWithZero K] (χ : MulChar F K) (hc : χ ^ 3 = 1) :
    χ (-1) = 1 := by
  have hs : χ (-1) ^ 2 = 1 := by
    rw [← map_pow, neg_one_sq, map_one]
  have ht := congrArg (fun η : MulChar F K => η (-1)) hc
  rw [MulChar.pow_apply' χ (by decide : 3 ≠ 0),
    MulChar.one_apply (isUnit_one.neg)] at ht
  calc
    χ (-1) = χ (-1) ^ 3 := by rw [pow_succ, hs, one_mul]
    _ = 1 := ht

section FiniteSum

variable {F K : Type*} [Field F] [Fintype F] [Field K]

/-- Frobenius plus the additive-character shift fixes the inverse direction.
This is valid in every target field of characteristic q. -/
theorem cubic_gauss_frobenius (χ : MulChar F K) (hc : χ ^ 3 = 1)
    (ψ : AddChar F K) (q : ℕ) [Fact q.Prime] [CharP K q]
    (hq : q % 3 = 1) (hqF : IsUnit (q : F)) :
    gaussSum χ ψ ^ q = (χ (q : F))⁻¹ * gaussSum χ ψ := by
  rw [gaussSum_frob q, cubic_character_pow_eq_self χ hc hq,
    AddChar.pow_mulShift]
  have hshift := gaussSum_mulShift_eq χ ψ hqF.unit
  simpa only [hqF.unit_spec, MulChar.inv_apply_eq_inv'] using hshift

/-- The exact cubic Gauss identity. The norm factor is #F, not its inverse. -/
theorem cubic_gauss_cube (χ : MulChar F K) (hχ : orderOf χ = 3)
    (ψ : AddChar F K) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = (Fintype.card F : K) * jacobiSum χ χ := by
  have hc : χ ^ 3 = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
  have H := gaussSum_pow_eq_prod_jacobiSum (χ := χ) (ψ := ψ)
    (by omega : 2 ≤ orderOf χ) hψ
  have hs : Finset.Ico 1 (3 - 1) = ({1} : Finset ℕ) := by decide
  simpa only [hχ, hs, Finset.prod_singleton, pow_one,
    cubic_character_neg_one χ hc, one_mul] using H

/-- Cancellation is justified by the nonzero finite-field cardinal in K.
Neither a cube root nor a Frobenius eigenvalue is introduced as a premise. -/
theorem cubic_gauss_euler_comparison (χ : MulChar F K) (hχ : orderOf χ = 3)
    (ψ : AddChar F K) (hψ : ψ.IsPrimitive)
    (q : ℕ) [Fact q.Prime] [CharP K q]
    (hq : q % 3 = 1) (hqF : IsUnit (q : F))
    (hcard : (Fintype.card F : K) ≠ 0) :
    (χ (q : F))⁻¹ =
      ((Fintype.card F : K) * jacobiSum χ χ) ^ ((q - 1) / 3) := by
  let G := gaussSum χ ψ
  have hc : χ ^ 3 = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
  have hn : χ ≠ 1 := by intro h; simp [h] at hχ
  have hG : G ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hn hψ
  have hf : G ^ q = (χ (q : F))⁻¹ * G :=
    cubic_gauss_frobenius χ hc ψ q hq hqF
  have he : G ^ (q - 1) = (χ (q : F))⁻¹ := by
    apply (mul_left_injective₀ hG)
    change G ^ (q - 1) * G = (χ (q : F))⁻¹ * G
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : q.Prime).one_le]
    exact hf
  have hq3 : 3 * ((q - 1) / 3) = q - 1 := by omega
  calc
    (χ (q : F))⁻¹ = G ^ (q - 1) := he.symm
    _ = (G ^ 3) ^ ((q - 1) / 3) := by rw [← pow_mul, hq3]
    _ = _ := by rw [cubic_gauss_cube χ hχ ψ hψ]

end FiniteSum

/- The following root transport is deliberately restricted to the three cubic
roots. A characteristic-q reduction E→K is never assumed globally injective. -/
def IsCubicRoot (z : E) : Prop :=
  z = 1 ∨ z = QuadraticAlgebra.omega ∨ z = QuadraticAlgebra.omega ^ 2

private theorem omega_quad : (QuadraticAlgebra.omega : E) ^ 2 +
    QuadraticAlgebra.omega + 1 = 0 := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp

private theorem omega_cube : (QuadraticAlgebra.omega : E) ^ 3 = 1 := by
  linear_combination (QuadraticAlgebra.omega - 1) * omega_quad

/-- Reduction away from three is injective on the three actual cubic roots. -/
theorem cubic_roots_injective {K : Type*} [CommRing K] [IsDomain K]
    (f : E →+* K) (h3 : f 3 ≠ 0) {z z' : E}
    (hz : IsCubicRoot z) (hz' : IsCubicRoot z') (heq : f z = f z') : z = z' := by
  let w : E := QuadraticAlgebra.omega
  have hw : w ^ 2 + w + 1 = 0 := omega_quad
  have hw3 : w ^ 3 = 1 := omega_cube
  have hfactor : (1 - w) * (1 - w ^ 2) = (3 : E) := by
    calc
      (1 - w) * (1 - w ^ 2) = 1 - w - w ^ 2 + w ^ 3 := by ring
      _ = 3 := by rw [hw3]; linear_combination -hw
  have hf3 : (f w) ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
  have hf1 : f w ≠ 1 := by
    intro h
    have H : f (3 : E) = 0 := by
      rw [← hfactor, map_mul, map_sub, map_one, h, sub_self, zero_mul]
    exact h3 H
  have hf2 : (f w) ^ 2 ≠ 1 := by
    intro h
    have hh : f w = 1 := by
      calc
        f w = (f w) ^ 2 * f w := by rw [h, one_mul]
        _ = (f w) ^ 3 := by ring
        _ = 1 := hf3
    exact hf1 hh
  have hf12 : f w ≠ (f w) ^ 2 := by
    intro h
    have hh : (f w) ^ 3 = f w := by
      calc
        (f w) ^ 3 = (f w) ^ 2 * f w := by ring
        _ = f w * f w := by rw [← h]
        _ = (f w) ^ 2 := by ring
        _ = f w := h.symm
    exact hf1 (hh.symm.trans hf3)
  change z = 1 ∨ z = w ∨ z = w ^ 2 at hz
  change z' = 1 ∨ z' = w ∨ z' = w ^ 2 at hz'
  rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl
  · rfl
  · exact (hf1 (by simpa only [map_one] using heq.symm)).elim
  · exact (hf2 (by simpa only [map_one, map_pow] using heq.symm)).elim
  · exact (hf1 (by simpa only [map_one] using heq)).elim
  · rfl
  · exact (hf12 (by simpa only [map_pow] using heq)).elim
  · exact (hf2 (by simpa only [map_one, map_pow] using heq)).elim
  · exact (hf12 (by simpa only [map_pow] using heq.symm)).elim
  · rfl

/-- Nontriviality survives characteristic-q transport, although E→K has a kernel. -/
theorem residue_character_comp_order_three
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P)
    {K : Type*} [Field K] (f : E →+* K) (h3 : f 3 ≠ 0) :
    orderOf ((cubicResidueMulChar P hcard hthree).ringHomComp f) = 3 := by
  let χ := cubicResidueMulChar P hcard hthree
  have hc : (χ.ringHomComp f) ^ 3 = 1 := by
    rw [MulChar.ringHomComp_pow, cubicResidueMulChar_cube P hcard hthree,
      MulChar.ringHomComp_one]
  have hn : χ.ringHomComp f ≠ 1 := by
    intro h
    apply cubicResidueMulChar_ne_one P hcard hthree
    apply MulChar.ext
    intro u
    have hu : IsCubicRoot (χ u) :=
      residueCubicValue_mem_roots P hcard hthree (u : E ⧸ P) u.ne_zero
    have hv := congrArg (fun η : MulChar (E ⧸ P) K => η u) h
    rw [MulChar.one_apply_coe]
    change χ (u : E ⧸ P) = 1
    apply cubic_roots_injective f h3 hu (Or.inl rfl)
    simpa only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one] using hv
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hc hn


/-- Distinct prime characteristics give the nonzero casts needed at both places. -/
theorem prime_natCast_ne_zero (F : Type*) [Field F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] [CharP F p] (hpr : p ≠ r) :
    (r : F) ≠ 0 := by
  intro h
  have hd : p ∣ r := (CharP.cast_eq_zero_iff F p r).mp h
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp hd with h | h
  · exact (Fact.out : p.Prime).ne_one h
  · exact hpr h

/-- Prime residue cardinality determines the characteristic and excludes three. -/
theorem three_not_mem_of_residue_prime_card
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (p : ℕ) [Fact p.Prime] (hPcard : Nat.card (E ⧸ P) = p) (hp : p % 3 = 1) :
    (3 : E) ∉ P := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : CharP (E ⧸ P) p :=
    charP_of_card_eq_prime (by simpa only [Fintype.card_eq_nat_card] using hPcard)
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  have H := Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hne := prime_natCast_ne_zero (E ⧸ P) (p := p) (r := 3) (by omega)
  exact hne (by simpa only [map_ofNat, Nat.cast_ofNat] using H)

/-- The actual P-character transported to characteristic q satisfies the Gauss
comparison with -pπ. J=-π is consumed from the preceding normalization proof. -/
theorem cubic_gauss_primary_scalar
    (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 3 = 1) (hq : q % 3 = 1) (hpq : p ≠ q)
    (hPcard : Nat.card (E ⧸ P) = p)
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1)
    {K : Type*} [Field K] [CharP K q]
    (f : E →+* K) (h3 : f 3 ≠ 0)
    (ψ : AddChar (E ⧸ P) K) (hψ : ψ.IsPrimitive) :
    let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
    let χ := cubicResidueMulChar P (by omega : Nat.card (E ⧸ P) % 3 = 1) hPthree
    (f (χ (Ideal.Quotient.mk P (q : E))))⁻¹ =
      f (-(p : E) * π) ^ ((q - 1) / 3) := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : CharP (E ⧸ P) p :=
    charP_of_card_eq_prime (by simpa only [Fintype.card_eq_nat_card] using hPcard)
  let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
  have hPmod : Nat.card (E ⧸ P) % 3 = 1 := by omega
  let χ := cubicResidueMulChar P hPmod hPthree
  let θ := χ.ringHomComp f
  have hθ : orderOf θ = 3 :=
    residue_character_comp_order_three P hPmod hPthree f h3
  have hqF : IsUnit (q : E ⧸ P) := isUnit_iff_ne_zero.mpr
    (prime_natCast_ne_zero (E ⧸ P) hpq)
  have hpK : (Fintype.card (E ⧸ P) : K) ≠ 0 := by
    rw [Fintype.card_eq_nat_card, hPcard]
    exact prime_natCast_ne_zero K hpq.symm
  have hJE : jacobiSum χ χ = -π := by
    have H := cubicJacobiSum_eq_primary_generator P hPmod hPthree π hπ hπprimary
    exact neg_eq_iff_eq_neg.mp H
  have hJK : jacobiSum θ θ = f (-π) := by
    rw [jacobiSum_ringHomComp, hJE]
  have H := cubic_gauss_euler_comparison θ hθ ψ hψ q hq hqF hpK
  rw [Fintype.card_eq_nat_card, hPcard, hJK] at H
  have hprod : (p : K) * f (-π) = f (-(p : E) * π) := by
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

/-- The §58 comparison for the actual residue characters. The finite extension
and primitive additive character are constructed, not assumed. Norm π=p and
J_P=-π are both imported conclusions of the companion normalization. -/
theorem cubic_residue_prime_comparison
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 3 = 1) (hq : q % 3 = 1) (hpq : p ≠ q)
    (hPcard : Nat.card (E ⧸ P) = p) (hQcard : Nat.card (E ⧸ Q) = q)
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1) :
    let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
    let hQthree := three_not_mem_of_residue_prime_card Q q hQcard hq
    let χP := cubicResidueMulChar P (by omega : Nat.card (E ⧸ P) % 3 = 1) hPthree
    let χQ := cubicResidueMulChar Q (by omega : Nat.card (E ⧸ Q) % 3 = 1) hQthree
    χP (Ideal.Quotient.mk P (q : E)) =
      χQ (Ideal.Quotient.mk Q π) * χQ (Ideal.Quotient.mk Q (star π)) ^ 2 := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : Fintype (E ⧸ Q) := Fintype.ofFinite _
  letI : CharP (E ⧸ P) p :=
    charP_of_card_eq_prime (by simpa only [Fintype.card_eq_nat_card] using hPcard)
  letI : CharP (E ⧸ Q) q :=
    charP_of_card_eq_prime (by simpa only [Fintype.card_eq_nat_card] using hQcard)
  have hPmod : Nat.card (E ⧸ P) % 3 = 1 := by omega
  have hQmod : Nat.card (E ⧸ Q) % 3 = 1 := by omega
  let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
  let hQthree := three_not_mem_of_residue_prime_card Q q hQcard hq
  let χP := cubicResidueMulChar P hPmod hPthree
  let χQ := cubicResidueMulChar Q hQmod hQthree
  have hchar : ringChar (E ⧸ Q) ≠ ringChar (E ⧸ P) := by
    rw [ringChar.eq (E ⧸ Q) q, ringChar.eq (E ⧸ P) p]
    exact hpq.symm
  let ψ := AddChar.FiniteField.primitiveChar (E ⧸ P) (E ⧸ Q) hchar
  let K := CyclotomicField ψ.n (E ⧸ Q)
  let g : (E ⧸ Q) →+* K := algebraMap (E ⧸ Q) K
  let f : E →+* K := g.comp (Ideal.Quotient.mk Q)
  letI : CharP K q := charP_of_injective_ringHom g.injective q
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : f 3 ≠ 0 := by
    simpa only [map_ofNat, Nat.cast_ofNat] using
      prime_natCast_ne_zero K (p := q) (r := 3) (by omega)
  have H := cubic_gauss_primary_scalar P p q hp hq hpq hPcard
    π hπ hπprimary f h3 ψ.char ψ.prim
  have hnorm : QuadraticAlgebra.norm π = (p : ℤ) := by
    have hj := cubicJacobiSum_eq_primary_generator P hPmod hPthree π hπ hπprimary
    rw [← hj, QuadraticAlgebra.norm_neg,
      cubicJacobiSum_norm P hPmod hPthree, hPcard]
  have hp_factor : (p : E) = π * star π := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hnorm]
    rfl
  let a := χP (Ideal.Quotient.mk P (q : E))
  let b := χQ (Ideal.Quotient.mk Q π)
  let c := χQ (Ideal.Quotient.mk Q (star π))
  let d := χQ (Ideal.Quotient.mk Q (-(p : E) * π))
  have hpQ : Ideal.Quotient.mk Q (p : E) ≠ 0 := by
    simpa only [map_natCast] using
      prime_natCast_ne_zero (E ⧸ Q) (p := q) (r := p) hpq.symm
  have hfactors : Ideal.Quotient.mk Q π * Ideal.Quotient.mk Q (star π) ≠ 0 := by
    rw [← map_mul, ← hp_factor]
    exact hpQ
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := left_ne_zero_of_mul hfactors
  have hbarQ : Ideal.Quotient.mk Q (star π) ≠ 0 := right_ne_zero_of_mul hfactors
  have hqP : Ideal.Quotient.mk P (q : E) ≠ 0 := by
    simpa only [map_natCast] using prime_natCast_ne_zero (E ⧸ P) hpq
  have hdQ : Ideal.Quotient.mk Q (-(p : E) * π) ≠ 0 := by
    rw [map_mul, map_neg]
    exact mul_ne_zero (neg_ne_zero.mpr hpQ) hπQ
  have ha : IsCubicRoot a := residueCubicValue_mem_roots P hPmod hPthree _ hqP
  have hb : IsCubicRoot b := residueCubicValue_mem_roots Q hQmod hQthree _ hπQ
  have hc : IsCubicRoot c := residueCubicValue_mem_roots Q hQmod hQthree _ hbarQ
  have hd : IsCubicRoot d := residueCubicValue_mem_roots Q hQmod hQthree _ hdQ
  have hEuler (x : E) :
      f (χQ (Ideal.Quotient.mk Q x)) = f x ^ ((q - 1) / 3) := by
    change g (Ideal.Quotient.mk Q (χQ (Ideal.Quotient.mk Q x))) = _
    rw [cubicResidueMulChar_reduction Q hQmod hQthree, hQcard]
    rw [map_pow]
    rfl
  have Had : (f a)⁻¹ = f d := by
    change (f a)⁻¹ = f (χQ (Ideal.Quotient.mk Q (-(p : E) * π)))
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
    have hinput : Ideal.Quotient.mk Q (-(p : E) * π) =
        (-1 : E ⧸ Q) *
          (Ideal.Quotient.mk Q π ^ 2 * Ideal.Quotient.mk Q (star π)) := by
      rw [hp_factor, map_mul, map_neg, map_mul]
      ring
    change χQ (Ideal.Quotient.mk Q (-(p : E) * π)) = _
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



/-- The two Gauss comparisons imply reciprocity using only the two cubic
relations actually needed. The comparison identities are intermediate premises
of this algebra helper; the arithmetic theorem below derives both of them. -/
theorem cubic_reciprocity_algebra {R : Type*} [CommRing R]
    (A B C D : R) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hCD : C * D = A * B ^ 2) (hAB : A * B = C * D ^ 2) : A = C := by
  have hstep : A * B ^ 2 * D = C * D ^ 2 := by rw [← hCD]; ring
  have hBD : B * D = 1 := by
    calc
      B * D = A ^ 3 * B ^ 3 * (B * D) := by rw [hA, hB]; ring
      _ = (A ^ 2 * B ^ 2) * (A * B ^ 2 * D) := by ring
      _ = (A ^ 2 * B ^ 2) * (C * D ^ 2) := by rw [hstep]
      _ = (A ^ 2 * B ^ 2) * (A * B) := by rw [← hAB]
      _ = A ^ 3 * B ^ 3 := by ring
      _ = 1 := by rw [hA, hB, one_mul]
  calc
    A = A * B ^ 3 := by rw [hB, mul_one]
    _ = (A * B ^ 2) * B := by ring
    _ = (C * D) * B := by rw [← hCD]
    _ = C * (B * D) := by ring
    _ = C := by rw [hBD, mul_one]

/-- Cubic reciprocity for the chosen primary generators. Both asymmetric
Gauss comparisons are obtained by applying the preceding theorem in the two
orders. No reciprocity identity, Jacobi value, norm, or conjugate direction is
assumed by this final statement. The residue-cardinality data is exactly the
split-prime data in §58. -/
theorem cubic_reciprocity_primary
    (P Q : Ideal E) [P.IsMaximal] [Q.IsMaximal]
    [Finite (E ⧸ P)] [Finite (E ⧸ Q)]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 3 = 1) (hq : q % 3 = 1) (hpq : p ≠ q)
    (hPcard : Nat.card (E ⧸ P) = p) (hQcard : Nat.card (E ⧸ Q) = q)
    (π ρ : E) (hπ : Ideal.span {π} = P) (hρ : Ideal.span {ρ} = Q)
    (hπprimary : (3 : E) ∣ π - 1) (hρprimary : (3 : E) ∣ ρ - 1) :
    let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
    let hQthree := three_not_mem_of_residue_prime_card Q q hQcard hq
    let χP := cubicResidueMulChar P (by omega : Nat.card (E ⧸ P) % 3 = 1) hPthree
    let χQ := cubicResidueMulChar Q (by omega : Nat.card (E ⧸ Q) % 3 = 1) hQthree
    χQ (Ideal.Quotient.mk Q π) = χP (Ideal.Quotient.mk P ρ) := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : Fintype (E ⧸ Q) := Fintype.ofFinite _
  letI : CharP (E ⧸ Q) q :=
    charP_of_card_eq_prime (by simpa only [Fintype.card_eq_nat_card] using hQcard)
  have hPmod : Nat.card (E ⧸ P) % 3 = 1 := by omega
  have hQmod : Nat.card (E ⧸ Q) % 3 = 1 := by omega
  let hPthree := three_not_mem_of_residue_prime_card P p hPcard hp
  let hQthree := three_not_mem_of_residue_prime_card Q q hQcard hq
  let χP := cubicResidueMulChar P hPmod hPthree
  let χQ := cubicResidueMulChar Q hQmod hQthree
  let A := χQ (Ideal.Quotient.mk Q π)
  let B := χQ (Ideal.Quotient.mk Q (star π))
  let C := χP (Ideal.Quotient.mk P ρ)
  let D := χP (Ideal.Quotient.mk P (star ρ))
  have hp_norm : QuadraticAlgebra.norm π = (p : ℤ) := by
    have hj := cubicJacobiSum_eq_primary_generator P hPmod hPthree π hπ hπprimary
    rw [← hj, QuadraticAlgebra.norm_neg,
      cubicJacobiSum_norm P hPmod hPthree, hPcard]
  have hq_norm : QuadraticAlgebra.norm ρ = (q : ℤ) := by
    have hj := cubicJacobiSum_eq_primary_generator Q hQmod hQthree ρ hρ hρprimary
    rw [← hj, QuadraticAlgebra.norm_neg,
      cubicJacobiSum_norm Q hQmod hQthree, hQcard]
  have hp_factor : (p : E) = π * star π := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hp_norm]
    rfl
  have hq_factor : (q : E) = ρ * star ρ := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hq_norm]
    rfl
  have hqeval : χP (Ideal.Quotient.mk P (q : E)) = C * D := by
    rw [hq_factor, map_mul, map_mul]
  have hpeval : χQ (Ideal.Quotient.mk Q (p : E)) = A * B := by
    rw [hp_factor, map_mul, map_mul]
  have hCD : C * D = A * B ^ 2 := by
    have H := cubic_residue_prime_comparison P Q p q hp hq hpq
      hPcard hQcard π hπ hπprimary
    change χP (Ideal.Quotient.mk P (q : E)) = A * B ^ 2 at H
    rw [hqeval] at H
    exact H
  have hAB : A * B = C * D ^ 2 := by
    have H := cubic_residue_prime_comparison Q P q p hq hp hpq.symm
      hQcard hPcard ρ hρ hρprimary
    change χQ (Ideal.Quotient.mk Q (p : E)) = C * D ^ 2 at H
    rw [hpeval] at H
    exact H
  have hpQ : Ideal.Quotient.mk Q (p : E) ≠ 0 := by
    simpa only [map_natCast] using
      prime_natCast_ne_zero (E ⧸ Q) (p := q) (r := p) hpq.symm
  have hfactors : Ideal.Quotient.mk Q π * Ideal.Quotient.mk Q (star π) ≠ 0 := by
    rw [← map_mul, ← hp_factor]
    exact hpQ
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := left_ne_zero_of_mul hfactors
  have hbarQ : Ideal.Quotient.mk Q (star π) ≠ 0 := right_ne_zero_of_mul hfactors
  have hA : A ^ 3 = 1 := cubic_root_cube
    (residueCubicValue_mem_roots Q hQmod hQthree _ hπQ)
  have hB : B ^ 3 = 1 := cubic_root_cube
    (residueCubicValue_mem_roots Q hQmod hQthree _ hbarQ)
  exact cubic_reciprocity_algebra A B C D hA hB hCD hAB



end D5.S3.Factorization.QuadraticIdeals.CubicGaussFrobenius
