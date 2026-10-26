/- GID: D5/S3/Arith/CharacterSums/KotesovecConjectureOne
   generality: I
   mirror-B: D5/B/S3/Arith/CharacterSums/KotesovecConjectureOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Nonvanishing monomial sums have powerful moduli. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19384
admission_basis: open-problem-resolution (#19241; Proved)
Direct frozen dependency: D5/S3/Arith/Powerful/PowerfulNumber
  Lean name: D5.S3.Arith.Powerful.PowerfulNumber.Powerful
  declaration statement_id: sha256:dba64bfdd5f80d27757ec49e7428404fa5ebcf2dda9d2cad084599c4afb7ecd4
Direct frozen dependency: D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration
  Lean name: D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.finEquiv_eq_natCast
  declaration statement_id: sha256:6062729cd00b090edb5dfcccd635f4a563a8a66f60deb5d1c6d91f2195edc1b1
The source definitions monomialSum, InA368959, InA338325 and claimOne retain their
preregistered expressions. Powerful is the existing frozen predicate.
escape_witness: none. CRT transport is a consumed bind-only helper.
The module uses open-problem resolution for admission.
Per-declaration proof-shape proposals and immediate consumers:
(Names without a module prefix belong to this module.)
definition: monomialSum; consumers: InA368959, good_to_membership, monomialSum_eq_powerSum, result, simple_prime_vanish.
definition: InA368959; consumers: claimOne, family_inclusion, good_to_membership, result, KotesovecConjectureTwo.claimTwo, KotesovecConjectureTwo.result.
definition: InA338325; consumers: family_inclusion, KotesovecConjectureTwo.claimTwo, KotesovecConjectureTwo.result.
definition: claimOne; consumers: result.
definition: powerSum; consumers: Good, good_2401, good_243, good_mul, good_one, good_prime_cube, good_to_membership, high_degree_nonvanishing, monomialSum_eq_powerSum, powerSum_crt, powerSum_ne_zero_of_counts, prime_powerSum_vanish, quadratic_sum_ne_zero, simple_prime_vanish.
definition: leftChar; consumers: good_mul, leftChar_injective, powerSum_crt, simple_prime_vanish.
definition: rightChar; consumers: good_mul, powerSum_crt, rightChar_injective, simple_prime_vanish.
proof_shape: powerSum_crt = bind-only; consumers: good_mul, simple_prime_vanish.
proof_shape: leftChar_injective = bind-only; consumers: good_mul, simple_prime_vanish.
proof_shape: rightChar_injective = bind-only; consumers: good_mul.
proof_shape: prime_powerSum_vanish = bind-only; consumers: simple_prime_vanish.
proof_shape: primitive_char_one = bind-only; consumers: powerSum_ne_zero_of_counts.
proof_shape: monomialSum_eq_powerSum = bind-only; consumers: good_to_membership, simple_prime_vanish.
proof_shape: simple_prime_vanish = bind-only; consumers: result.
proof_shape: result = bind-only; consumers: external conjecture settlement.
proof_shape: geom_mul_coeff = bind-only; consumers: prime_power_coefficient_obstruction.
proof_shape: prime_power_coefficient_obstruction = bind-only; consumers: powerSum_ne_zero_of_counts.
proof_shape: quadratic_sum_ne_zero = bind-only; consumers: good_2401, good_243, good_prime_cube.
proof_shape: high_degree_no_preimage = bind-only; consumers: high_degree_nonvanishing.
definition: powerCount; consumers: countPolynomial_coeff, good_2401, good_243, good_prime_cube, high_degree_nonvanishing, powerCount_eq_rangeCount, powerCount_zero_pos, powerSum_ne_zero_of_counts.
definition: countPolynomial; consumers: countPolynomial_coeff, countPolynomial_degree, countPolynomial_eval, powerSum_ne_zero_of_counts.
proof_shape: countPolynomial_degree = bind-only; consumers: powerSum_ne_zero_of_counts.
proof_shape: countPolynomial_coeff = bind-only; consumers: powerSum_ne_zero_of_counts.
proof_shape: countPolynomial_eval = bind-only; consumers: powerSum_ne_zero_of_counts.
proof_shape: powerCount_zero_pos = bind-only; consumers: high_degree_nonvanishing.
definition: Good; consumers: biquadratefree_good, good_2401, good_243, good_mul, good_one, good_prime_cube, good_prime_square, good_to_membership, KotesovecConjectureTwo.result.
proof_shape: powerSum_ne_zero_of_counts = bind-only; consumers: good_2401, good_243, good_prime_cube, high_degree_nonvanishing.
proof_shape: high_degree_nonvanishing = bind-only; consumers: good_2401, good_243, good_prime_cube, good_prime_square.
proof_shape: good_prime_square = bind-only; consumers: biquadratefree_good, KotesovecConjectureTwo.result.
proof_shape: powerCount_eq_rangeCount = bind-only; consumers: good_2401, good_243, good_prime_cube.
proof_shape: good_prime_cube = content; consumers: biquadratefree_good, KotesovecConjectureTwo.result.
proof_shape: good_one = bind-only; consumers: biquadratefree_good.
proof_shape: good_mul = bind-only; consumers: biquadratefree_good, KotesovecConjectureTwo.result.
proof_shape: biquadratefree_good = content; consumers: family_inclusion.
proof_shape: good_to_membership = bind-only; consumers: family_inclusion, KotesovecConjectureTwo.result.
proof_shape: family_inclusion = content; consumers: KotesovecConjectureTwo.result.
proof_shape: good_243 = content; consumers: KotesovecConjectureTwo.result.
proof_shape: good_2401 = content; consumers: KotesovecConjectureTwo.result.
transitive consumer: monomialSum -> KotesovecConjectureTwo.result.
transitive consumer: powerSum -> KotesovecConjectureTwo.result.
transitive consumer: prime_power_coefficient_obstruction -> KotesovecConjectureTwo.result.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import D5.S3.Arith.Powerful.PowerfulNumber
import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration

open scoped BigOperators
open Polynomial D5.S3.Arith.Powerful.PowerfulNumber

namespace D5.S3.Arith.CharacterSums.KotesovecConjectureOne

/-- `Sum_{k=0..m-1} exp(2πi k^s/m)`. -/
noncomputable def monomialSum (m s : ℕ) : ℂ :=
  ∑ k ∈ Finset.range m, Complex.exp (2 * Real.pi * Complex.I * ((k ^ s : ℕ) : ℂ) / m)

/-- A368959: the positive integers `m` with `Sum_{k=0..m-1} exp(2πi k^s/m) ≠ 0` for all `s ≥ 2`. -/
def InA368959 (m : ℕ) : Prop :=
  0 < m ∧ ∀ s : ℕ, 2 ≤ s → monomialSum m s ≠ 0

/-- A338325: the positive integers whose exponents in their prime factorization are either 2 or 3. -/
def InA338325 (m : ℕ) : Prop :=
  0 < m ∧ ∀ p ∈ m.primeFactors, m.factorization p = 2 ∨ m.factorization p = 3

/-- Conjecture 1: A368959 is a subset of A001694 (the powerful numbers). -/
def claimOne : Prop :=
  ∀ m : ℕ, InA368959 m → Powerful m

open scoped BigOperators

noncomputable def powerSum {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (s : ℕ) : ℂ := ∑ x : R, ψ (x ^ s)

private noncomputable def leftChar {r t : ℕ} (h : r.Coprime t)
    (ψ : AddChar (ZMod (r*t)) ℂ) : AddChar (ZMod r) ℂ :=
  ψ.compAddMonoidHom ((ZMod.chineseRemainder h).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _))

private noncomputable def rightChar {r t : ℕ} (h : r.Coprime t)
    (ψ : AddChar (ZMod (r*t)) ℂ) : AddChar (ZMod t) ℂ :=
  ψ.compAddMonoidHom ((ZMod.chineseRemainder h).symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _))

private theorem powerSum_crt {r t : ℕ} [NeZero r] [NeZero t] (h : r.Coprime t)
    (ψ : AddChar (ZMod (r*t)) ℂ) (s : ℕ) :
    powerSum ψ s = powerSum (leftChar h ψ) s * powerSum (rightChar h ψ) s := by
  classical
  let e := ZMod.chineseRemainder h
  unfold powerSum
  rw [← e.symm.toEquiv.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change ψ ((e.symm (x,y)) ^ s) = ψ (e.symm (x ^ s,0)) * ψ (e.symm (0,y ^ s))
  rw [← ψ.map_add_eq_mul, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]
  exact congrArg ψ (map_pow e.symm (x,y) s).symm

private theorem leftChar_injective {r t : ℕ} (h : r.Coprime t)
    (ψ : AddChar (ZMod (r*t)) ℂ) (hψ : Function.Injective ψ) :
    Function.Injective (leftChar h ψ) := by
  exact hψ.comp ((ZMod.chineseRemainder h).symm.injective.comp (Prod.mk_left_injective (0 : ZMod t)))

private theorem rightChar_injective {r t : ℕ} (h : r.Coprime t)
    (ψ : AddChar (ZMod (r*t)) ℂ) (hψ : Function.Injective ψ) :
    Function.Injective (rightChar h ψ) := by
  exact hψ.comp ((ZMod.chineseRemainder h).symm.injective.comp (Prod.mk_right_injective (0 : ZMod r)))

private theorem prime_powerSum_vanish {p : ℕ} [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) (hψ : Function.Injective ψ) : powerSum ψ p = 0 := by
  classical
  simp only [powerSum, ZMod.pow_card]
  apply AddChar.sum_eq_zero_of_ne_one
  intro h
  have h01 : ψ 0 = ψ 1 := by simp [h]
  exact zero_ne_one (hψ h01)

private theorem primitive_char_one {n : ℕ} [NeZero n]
    (ψ : AddChar (ZMod n) ℂ) (hψ : Function.Injective ψ) : IsPrimitiveRoot (ψ 1) n := by
  rw [IsPrimitiveRoot.iff_orderOf]
  change orderOf (ψ.toMonoidHom (Multiplicative.ofAdd (1 : ZMod n))) = n
  rw [orderOf_injective ψ.toMonoidHom hψ]
  exact ZMod.addOrderOf_one n

private theorem monomialSum_eq_powerSum {m : ℕ} [NeZero m] (s : ℕ) :
    monomialSum m s = powerSum (ZMod.stdAddChar (N := m)) s := by
  have hterm (k : ℕ) : ZMod.stdAddChar ((k : ZMod m)^s) =
      Complex.exp (2 * Real.pi * Complex.I * ((k^s : ℕ) : ℂ) / m) := by
    rw [← Nat.cast_pow, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold monomialSum powerSum
  symm
  calc
    (∑ x : ZMod m, ZMod.stdAddChar (x^s)) =
        ∑ x : ZMod m, Complex.exp (2 * Real.pi * Complex.I * ((x.val^s : ℕ) : ℂ) / m) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa using hterm x.val
    _ = _ := by
      let e : Fin m ≃ ZMod m := (ZMod.finEquiv m).toEquiv
      rw [← e.sum_comp]
      have heval (x : Fin m) : (e x).val = x.val := by
        change (ZMod.finEquiv m x).val = x.val
        rw [D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.finEquiv_eq_natCast,
          ZMod.val_natCast_of_lt x.isLt]
      simp_rw [heval]
      exact Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * ((k^s : ℕ) : ℂ) / (m : ℂ))) m

private theorem simple_prime_vanish {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : p ∣ m) (hp2m : ¬ p^2 ∣ m) : monomialSum m p = 0 := by
  let r := m/p
  have hmr : p*r = m := Nat.mul_div_cancel' hpm
  have hr : 0 < r := (Nat.lt_div_iff_mul_lt' hpm 0).mpr hm
  have hpr : p.Coprime r := hp.coprime_iff_not_dvd.mpr (by
    intro h
    apply hp2m
    rw [← hmr, pow_two]
    exact Nat.mul_dvd_mul_left p h)
  haveI : NeZero r := ⟨hr.ne'⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← hmr, monomialSum_eq_powerSum, powerSum_crt hpr]
  rw [prime_powerSum_vanish _ (leftChar_injective hpr _ ZMod.injective_stdAddChar), zero_mul]

theorem result : claimOne := by
  intro m hm
  refine ⟨hm.1.ne', ?_⟩
  intro p hp hpm
  by_contra hn
  exact hm.2 p hp.two_le (simple_prime_vanish hm.1 hp hpm hn)

open scoped BigOperators
open Polynomial

-- A geometric factor repeats the quotient coefficients below its block size.
private theorem geom_mul_coeff {p h : ℕ} (hp : 2 ≤ p)
    (Q : ℚ[X]) (hQ : Q.natDegree < h) (r : ℕ) (hr : r < h) :
    ((∑ i ∈ Finset.range p, (X ^ h) ^ i) * Q).coeff r =
    ((∑ i ∈ Finset.range p, (X ^ h) ^ i) * Q).coeff (r+h) := by
  classical
  have small (j k : ℕ) (hk : j < h*k) : (X^(h*k)*Q).coeff j = 0 := by
    rw [coeff_X_pow_mul']
    simp [Nat.not_le.mpr hk]
  have low : ((∑ i ∈ Finset.range p, (X ^ h) ^ i) * Q).coeff r = Q.coeff r := by
    rw [Finset.sum_mul, finsetSum_coeff]
    simp_rw [← pow_mul]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b hb hb0
      apply small
      have hb1 : h ≤ h*b := Nat.le_mul_of_pos_right h (Nat.one_le_iff_ne_zero.mpr hb0)
      exact lt_of_lt_of_le hr hb1
    · simp [show 0 < p by exact Nat.zero_lt_of_lt hp]
  have high : ((∑ i ∈ Finset.range p, (X ^ h) ^ i) * Q).coeff (r+h) = Q.coeff r := by
    rw [Finset.sum_mul, finsetSum_coeff]
    simp_rw [← pow_mul]
    rw [Finset.sum_eq_single 1]
    · simp [coeff_X_pow_mul']
    · intro b hb hb1
      by_cases hb0 : b = 0
      · subst b
        simp only [Nat.mul_zero, pow_zero, one_mul]
        exact coeff_eq_zero_of_natDegree_lt (by exact Nat.lt_add_left r hQ)
      · apply small
        have := Nat.mul_le_mul_left h (show 2 ≤ b by omega)
        omega
    · simp [show 1 < p by exact Nat.lt_of_succ_le hp]
  exact low.trans high.symm

-- Exact polynomial obstruction, for arbitrary rational coefficients.
private theorem prime_power_coefficient_obstruction {p a : ℕ} (hp : p.Prime)
    (P : ℚ[X]) (hP : P.degree < (p^(a+1) : ℕ))
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (p^(a+1))) (hz : aeval ζ P = 0)
    (r : ℕ) (hr : r < p^a) : P.coeff r = P.coeff (r+p^a) := by
  classical
  have hd : cyclotomic (p^(a+1)) ℚ ∣ P := by
    rw [cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _)]
    exact minpoly.dvd ℚ ζ hz
  obtain ⟨Q, rfl⟩ := hd
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  have hQ : Q.natDegree < p^a := by
    rw [degree_eq_natDegree (mul_ne_zero (cyclotomic_ne_zero _ _) hQ0),
      natDegree_mul (cyclotomic_ne_zero _ _) hQ0,
      natDegree_cyclotomic, Nat.totient_prime_pow_succ hp a] at hP
    norm_cast at hP
    have hp1 : 1 ≤ p := hp.one_le
    have heq : p^a * (p-1) + p^a = p^(a+1) := by
      calc
        p^a * (p-1) + p^a = p^a * ((p-1)+1) := by exact Eq.symm (Nat.mul_succ (p ^ a) (p - 1))
        _ = p^(a+1) := by rw [Nat.sub_add_cancel hp1, pow_succ]
    omega
  rw [cyclotomic_prime_pow_eq_geom_sum hp]
  exact geom_mul_coeff hp.two_le Q hQ r hr

open scoped BigOperators

private theorem quadratic_sum_ne_zero {n : ℕ} [NeZero n]
    (ψ : AddChar (ZMod n) ℂ) (hψ : Function.Injective ψ)
    (h2 : IsUnit (2 : ZMod n)) : powerSum ψ 2 ≠ 0 := by
  classical
  have hprim : ψ.IsPrimitive := by
    apply AddChar.zmod_char_primitive_of_eq_one_only_at_zero n
    intro a ha
    apply hψ
    simpa using ha
  have hconj (x : ZMod n) : (starRingEnd ℂ) (ψ x) = ψ (-x) :=
    (AddChar.map_neg_eq_conj ψ x).symm
  have hsum (x : ZMod n) : ∑ y : ZMod n, ψ (y * (2*x)) =
      if x = 0 then (n : ℂ) else 0 := by
    rw [AddChar.sum_mulShift _ hprim]
    have hz : (2 : ZMod n)*x = 0 ↔ x = 0 := h2.mul_right_eq_zero
    simp [hz, ZMod.card]
  have heq : powerSum ψ 2 * (starRingEnd ℂ) (powerSum ψ 2) = (n : ℂ) := by
    unfold powerSum
    rw [map_sum]
    simp_rw [hconj]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, ← ψ.map_add_eq_mul]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext y
      rw [← Equiv.sum_comp (Equiv.addRight y) (fun x : ZMod n => ψ (x ^ 2 + -(y ^ 2)))]
    have hpoly (x y : ZMod n) : (x+y)^2 + -(y^2) = x^2 + y*(2*x) := by ring
    simp_rw [Equiv.coe_addRight, hpoly, ψ.map_add_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hsum]
    simp
  intro hz
  rw [hz, zero_mul] at heq
  exact (Nat.cast_ne_zero.mpr (NeZero.ne n)) heq.symm

open scoped BigOperators

private theorem high_degree_no_preimage {p a s : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hs : a+1 ≤ s) (x : ZMod (p^(a+1))) : x^s ≠ (p^a : ℕ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p^(a+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  intro heq
  let f := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p)
  have hpa : f ((p^a : ℕ) : ZMod (p^(a+1))) = 0 := by
    rw [map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_pow_self p (Nat.ne_zero_of_lt ha))
  have hcast : (f x)^s = 0 := by
    rw [← map_pow, heq, hpa]
  have hfx : f x = 0 := (pow_eq_zero_iff (Nat.ne_zero_of_lt hs)).mp hcast
  have hv : p ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have h := congrArg f (ZMod.natCast_zmod_val x)
    simpa only [map_natCast, hfx] using h
  rcases hv with ⟨k,hk⟩
  have hx : x = ((p*k : ℕ) : ZMod (p^(a+1))) := by
    rw [← hk, ZMod.natCast_zmod_val]
  have hzero : x^s = 0 := by
    rw [hx, Nat.cast_mul, mul_pow]
    have hpow : (p : ZMod (p^(a+1)))^s = 0 :=
      ZMod.natCast_pow_eq_zero_of_le p hs
    rw [hpow, zero_mul]
  have hh : ((p^a : ℕ) : ZMod (p^(a+1))) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp h
    have hle := Nat.le_of_dvd (pow_pos hp.pos a) hd
    have hlt : p^a < p^(a+1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self a)
    omega
  exact hh (heq.symm.trans hzero)

open scoped BigOperators
open Polynomial

private noncomputable def powerCount (n s j : ℕ) [NeZero n] : ℕ :=
  (Finset.univ.filter fun x : ZMod n => x^s = (j : ZMod n)).card

private noncomputable def countPolynomial (n s : ℕ) [NeZero n] : ℚ[X] :=
  ∑ x : ZMod n, X ^ (x^s).val

private theorem countPolynomial_degree (n s : ℕ) [NeZero n] :
    (countPolynomial n s).degree < (n : ℕ) := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro x hx
  simpa using (ZMod.val_lt (x^s))

private theorem countPolynomial_coeff {n s j : ℕ} [NeZero n] (hj : j < n) :
    (countPolynomial n s).coeff j = (powerCount n s j : ℚ) := by
  classical
  have hval (x : ZMod n) : (x^s).val = j ↔ x^s = (j : ZMod n) := by
    constructor
    · intro h
      rw [← h, ZMod.natCast_zmod_val]
    · intro h
      rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt hj]
  rw [countPolynomial, finsetSum_coeff, powerCount, Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter, coeff_X_pow]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x^s = (j : ZMod n)
  · simp [h, Nat.mod_eq_of_lt hj]
  · have hv : j ≠ (x^s).val := by
      intro hh
      exact h ((hval x).mp hh.symm)
    simp [h, hv]

private theorem countPolynomial_eval {n s : ℕ} [NeZero n] (ψ : AddChar (ZMod n) ℂ) :
    aeval (ψ 1) (countPolynomial n s) = ∑ x : ZMod n, ψ (x^s) := by
  classical
  simp only [countPolynomial, map_sum, map_pow, aeval_X]
  apply Finset.sum_congr rfl
  intro x _
  rw [← ψ.map_nsmul_eq_pow]
  simp

private theorem powerCount_zero_pos {n s : ℕ} [NeZero n] (hs : 0 < s) :
    0 < powerCount n s 0 := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp [zero_pow hs.ne']

open scoped BigOperators
open Polynomial

def Good (n : ℕ) [NeZero n] : Prop :=
  ∀ (ψ : AddChar (ZMod n) ℂ), Function.Injective ψ → ∀ s : ℕ, 2 ≤ s → powerSum ψ s ≠ 0

private theorem powerSum_ne_zero_of_counts {p a s r : ℕ} (hp : p.Prime)
    [NeZero (p^(a+1))] (ψ : AddChar (ZMod (p^(a+1))) ℂ) (hψ : Function.Injective ψ)
    (hr : r < p^a) (hc : powerCount (p^(a+1)) s r ≠ powerCount (p^(a+1)) s (r+p^a)) :
    powerSum ψ s ≠ 0 := by
  intro hz
  have h := prime_power_coefficient_obstruction hp (countPolynomial (p^(a+1)) s)
    (countPolynomial_degree _ _) (ψ 1) (primitive_char_one ψ hψ)
    (by simpa [powerSum] using (countPolynomial_eval ψ).trans hz) r hr
  have hrq : r < p^(a+1) := lt_of_lt_of_le hr (Nat.pow_le_pow_right hp.pos (by exact Nat.le_add_right a 1))
  have hrhq : r+p^a < p^(a+1) := by
    rw [pow_succ]
    have := Nat.mul_le_mul_left (p^a) hp.two_le
    omega
  rw [countPolynomial_coeff hrq, countPolynomial_coeff hrhq] at h
  apply hc
  exact_mod_cast h

private theorem high_degree_nonvanishing {p a s : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    [NeZero (p^(a+1))] (hs : a+1 ≤ s)
    (ψ : AddChar (ZMod (p^(a+1))) ℂ) (hψ : Function.Injective ψ) : powerSum ψ s ≠ 0 := by
  apply powerSum_ne_zero_of_counts hp ψ hψ (show 0 < p^a from pow_pos hp.pos _)
  have hz : powerCount (p^(a+1)) s (p^a) = 0 := by
    unfold powerCount
    apply Finset.card_eq_zero.mpr
    exact Finset.filter_eq_empty_iff.mpr fun x _ => high_degree_no_preimage hp ha hs x
  simpa only [Nat.zero_add, hz, ne_eq, Nat.pos_iff_ne_zero] using powerCount_zero_pos (lt_of_lt_of_le (Nat.succ_pos a) hs)

theorem good_prime_square {p : ℕ} (hp : p.Prime) [NeZero (p^2)] : Good (p^2) := by
  intro ψ hψ s hs
  exact high_degree_nonvanishing (a := 1) hp (by exact NeZero.one_le) hs ψ hψ

private theorem powerCount_eq_rangeCount (n s j : ℕ) [NeZero n] :
    powerCount n s j = ((Finset.range n).filter fun x => x^s % n = j % n).card := by
  classical
  unfold powerCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hterm (x : ZMod n) :
      (if x^s = (j : ZMod n) then 1 else 0 : ℕ) =
      if x.val^s % n = j % n then 1 else 0 := by
    have hpow : ((x.val^s : ℕ) : ZMod n) = x^s := by simp
    have heq : x^s = (j : ZMod n) ↔ x.val^s % n = j % n := by
      rw [← hpow, ZMod.natCast_eq_natCast_iff']
    simp only [heq]
  simp_rw [hterm]
  let e : Fin n ≃ ZMod n := (ZMod.finEquiv n).toEquiv
  rw [← e.sum_comp]
  have heval (x : Fin n) : (e x).val = x.val := by
    change (ZMod.finEquiv n x).val = x.val
    rw [D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.finEquiv_eq_natCast,
      ZMod.val_natCast_of_lt x.isLt]
  simp_rw [heval]
  exact Fin.sum_univ_eq_sum_range (fun x : ℕ => if x^s % n = j % n then 1 else 0) n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem good_prime_cube {p : ℕ} (hp : p.Prime) [NeZero (p^3)] : Good (p^3) := by
  have count_8_square : ((Finset.range 8).filter fun x => x^2 % 8 = 1 % 8).card = 4 ∧ ((Finset.range 8).filter fun x => x^2 % 8 = 5 % 8).card = 0 := by exact Nat.pair_eq_pair.mp rfl
  intro ψ hψ s hs
  by_cases hs3 : 3 ≤ s
  · exact high_degree_nonvanishing (a := 2) hp (by exact NeZero.one_le) hs3 ψ hψ
  have hs2 : s = 2 := by omega
  subst s
  by_cases hp2 : p = 2
  · subst p
    apply powerSum_ne_zero_of_counts (p := 2) (a := 2) (r := 1) (by exact Nat.prime_two) ψ hψ (by exact Nat.one_lt_two_pow' 1)
    norm_num only [powerCount_eq_rangeCount, count_8_square.1, count_8_square.2]
  · exact quadratic_sum_ne_zero ψ hψ ((ZMod.isUnit_iff_coprime 2 (p^3)).mpr
      (by exact (Nat.Prime.coprime_iff_not_dvd (by exact Nat.prime_two : Nat.Prime 2)).mpr (by
        intro h
        have h2p : 2 ∣ p := (Nat.prime_two.dvd_of_dvd_pow h)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm)))

private theorem good_one : Good 1 := by
  intro ψ hψ s hs
  have heq : powerSum ψ s = 1 := by
    unfold powerSum
    calc
      (∑ x : ZMod 1, ψ (x^s)) = ∑ _x : ZMod 1, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [show x^s = 0 from Subsingleton.elim _ _, ψ.map_zero_eq_one]
      _ = 1 := by exact Fintype.sum_unique fun x => 1
  rw [heq]
  exact one_ne_zero

theorem good_mul {r t : ℕ} [NeZero r] [NeZero t] (h : r.Coprime t)
    (hr : Good r) (ht : Good t) : Good (r*t) := by
  intro ψ hψ s hs
  rw [powerSum_crt h]
  exact mul_ne_zero (hr _ (leftChar_injective h ψ hψ) s hs)
    (ht _ (rightChar_injective h ψ hψ) s hs)

private theorem biquadratefree_good (m : ℕ) : ∀ (hm : 0 < m),
    (∀ p ∈ m.primeFactors, m.factorization p = 2 ∨ m.factorization p = 3) →
    letI : NeZero m := ⟨hm.ne'⟩; Good m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => intro hm; omega
  | one => intro _ _; exact good_one
  | prime_pow p e hp he =>
      intro hm hfac
      haveI : NeZero p := ⟨hp.ne_zero⟩
      have hmem : p ∈ (p^e).primeFactors := hp.mem_primeFactors
        (dvd_pow_self p he.ne') (pow_ne_zero e hp.ne_zero)
      have he23 : e = 2 ∨ e = 3 := by simpa [Nat.factorization_pow, hp.factorization_self] using hfac p hmem
      rcases he23 with rfl | rfl
      · exact good_prime_square hp
      · exact good_prime_cube hp
  | coprime a b ha hb hab iha ihb =>
      intro hm hfac
      haveI : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
      haveI : NeZero b := ⟨Nat.ne_zero_of_lt hb⟩
      apply good_mul hab
      · apply iha (Nat.zero_lt_of_lt ha)
        intro p hp
        have hmem : p ∈ (a*b).primeFactors := by
          rw [Nat.primeFactors_mul (NeZero.ne a) (NeZero.ne b)]
          exact Finset.mem_union_left _ hp
        have heq := Nat.factorization_eq_of_coprime_left hab
          (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)
        simpa [heq] using hfac p hmem
      · apply ihb (Nat.zero_lt_of_lt hb)
        intro p hp
        have hmem : p ∈ (a*b).primeFactors := by
          rw [Nat.primeFactors_mul (NeZero.ne a) (NeZero.ne b)]
          exact Finset.mem_union_right _ hp
        have heq := Nat.factorization_eq_of_coprime_right hab
          (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)
        simpa [heq] using hfac p hmem

theorem good_to_membership (n : ℕ) [NeZero n] (hn : Good n) : InA368959 n := by
  refine ⟨NeZero.pos n, ?_⟩
  intro s hs
  rw [monomialSum_eq_powerSum]
  exact hn ZMod.stdAddChar ZMod.injective_stdAddChar s hs

theorem family_inclusion (m : ℕ) (hm : InA338325 m) : InA368959 m := by
  haveI : NeZero m := ⟨hm.1.ne'⟩
  exact good_to_membership m (biquadratefree_good m hm.1 hm.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem good_243 : Good 243 := by
  have count_243_small :
      ((Finset.range 243).filter fun x => x^3 % 243 = 0 % 243).card = 27 ∧ ((Finset.range 243).filter fun x => x^3 % 243 = 81 % 243).card = 0 ∧
      ((Finset.range 243).filter fun x => x^4 % 243 = 0 % 243).card = 27 ∧ ((Finset.range 243).filter fun x => x^4 % 243 = 81 % 243).card = 54 := by decide
  intro ψ hψ s hs
  by_cases h5 : 5 ≤ s
  · exact high_degree_nonvanishing (p := 3) (a := 4) (by exact Nat.prime_three) (by exact NeZero.one_le) h5 ψ hψ
  interval_cases s
  · exact quadratic_sum_ne_zero ψ hψ ((ZMod.isUnit_iff_coprime _ _).mpr (by exact Nat.coprime_iff_gcd_eq_one.mp rfl))
  · apply powerSum_ne_zero_of_counts (p := 3) (a := 4) (r := 0) (by exact Nat.prime_three) ψ hψ (by exact Nat.zero_lt_succ 80)
    rw [Nat.zero_add, powerCount_eq_rangeCount, powerCount_eq_rangeCount]
    have h := count_243_small
    norm_num only [h.1, h.2.1]
  · apply powerSum_ne_zero_of_counts (p := 3) (a := 4) (r := 0) (by exact Nat.prime_three) ψ hψ (by exact Nat.zero_lt_succ 80)
    rw [Nat.zero_add, powerCount_eq_rangeCount, powerCount_eq_rangeCount]
    have h := count_243_small
    norm_num only [h.2.2.1, h.2.2.2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem good_2401 : Good 2401 := by
  have count_2401_cube : ((Finset.range 2401).filter fun x => x^3 % 2401 = 0 % 2401).card = 49 ∧ ((Finset.range 2401).filter fun x => x^3 % 2401 = 343 % 2401).card = 147 := by exact Nat.pair_eq_pair.mp rfl
  intro ψ hψ s hs
  by_cases h4 : 4 ≤ s
  · exact high_degree_nonvanishing (p := 7) (a := 3) (by exact Nat.prime_seven) (by exact NeZero.one_le) h4 ψ hψ
  interval_cases s
  · exact quadratic_sum_ne_zero ψ hψ ((ZMod.isUnit_iff_coprime _ _).mpr (by exact Nat.coprime_iff_gcd_eq_one.mp rfl))
  · apply powerSum_ne_zero_of_counts (p := 7) (a := 3) (r := 0) (by exact Nat.prime_seven) ψ hψ (by exact Nat.zero_lt_succ 342)
    rw [Nat.zero_add, powerCount_eq_rangeCount, powerCount_eq_rangeCount]
    have h := count_2401_cube
    norm_num only [h.1, h.2]

end D5.S3.Arith.CharacterSums.KotesovecConjectureOne
