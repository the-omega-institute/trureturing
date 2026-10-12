/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream finite-product support used by character APIs. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/Basic/FiniteProducts.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths; direct Mathlib import omits unused upstream metadata.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import Mathlib

open scoped BigOperators Polynomial

namespace LanglandsFirstMainLemma

open Polynomial

/--
Power sums over an injective realization of the multiplicative group of the
prime field.  This form applies both to the usual inclusion in characteristic
`p` and to Teichmüller representatives in mixed characteristic.
-/
theorem sum_primeField (p r : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R]
    (ω : (ZMod p)ˣ →* Rˣ) (hω : Function.Injective ω) :
    (∑ j : (ZMod p)ˣ, ((ω j : R) ^ r)) =
      if p - 1 ∣ r then ((p - 1 : ℕ) : R) else 0 := by
  classical
  let φ : (ZMod p)ˣ →* R :=
    { toFun := fun j => (ω j : R) ^ r
      map_one' := by simp
      map_mul' := by simp [mul_pow] }
  have hφ : φ = 1 ↔ ∀ j : (ZMod p)ˣ, j ^ r = 1 := by
    constructor
    · intro h j
      apply hω
      apply Units.ext
      simpa [φ] using DFunLike.congr_fun h j
    · intro h
      ext j
      simpa [φ] using congrArg ((↑) : Rˣ → R) (congrArg ω (h j))
  have hφdiv : φ = 1 ↔ p - 1 ∣ r := hφ.trans (by
    simpa [ZMod.card] using (FiniteField.forall_pow_eq_one_iff (K := ZMod p) r))
  rw [show (∑ j : (ZMod p)ˣ, ((ω j : R) ^ r)) = ∑ j, φ j from rfl,
    sum_hom_units]
  simp [hφdiv, Fintype.card_units, ZMod.card]

/--
The product of an injectively realized odd prime field's nonzero elements is
`-1`.  In particular, this applies to Teichmüller representatives.
-/
theorem prod_primeField (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {R : Type*} [CommRing R] [IsDomain R]
    (ω : (ZMod p)ˣ →* Rˣ) (hω : Function.Injective ω) :
    (∏ j : (ZMod p)ˣ, (ω j : R)) = -1 := by
  have hpprime : p.Prime := Fact.out
  have hpgt : 2 < p := lt_of_le_of_ne hpprime.two_le hp2.symm
  letI : Fact (2 < p) := ⟨hpgt⟩
  have hωneg_ne : ω (-1) ≠ 1 := by
    intro h
    have hz : (-1 : (ZMod p)ˣ) = 1 := by
      apply hω
      simpa using h
    exact ZMod.neg_one_ne_one (congrArg ((↑) : (ZMod p)ˣ → ZMod p) hz)
  have hval_ne : (ω (-1) : R) ≠ 1 := fun h => hωneg_ne (Units.ext h)
  have hsq : (ω (-1) : R) * (ω (-1) : R) = 1 := by
    simp only [← Units.val_mul, ← map_mul, neg_mul_neg, one_mul, map_one, Units.val_one]
  have hval : (ω (-1) : R) = -1 :=
    (mul_self_eq_one_iff.mp hsq).resolve_left hval_ne
  calc
    (∏ j : (ZMod p)ˣ, (ω j : R)) = ((↑) : Rˣ → R) (∏ j, ω j) := by simp
    _ = ((↑) : Rˣ → R) (ω (∏ j : (ZMod p)ˣ, j)) := by rw [map_prod]
    _ = ((↑) : Rˣ → R) (ω (-1)) := by rw [FiniteField.prod_univ_units_id_eq_neg_one]
    _ = -1 := hval

private theorem prod_X_sub_C_primeField (p : ℕ) [Fact p.Prime] :
    (∏ j : ZMod p, (X - C j)) = (X ^ p - X : (ZMod p)[X]) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hmonic : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hp
  have hfac := (GaloisField.splits_zmod_X_pow_sub_X p).eq_prod_roots_of_monic hmonic
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    convert FiniteField.roots_X_pow_card_sub_X (ZMod p) using 1
    rw [ZMod.card]
  rw [hroots] at hfac
  simpa using hfac.symm

private theorem primeFieldPolynomial (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p] :
    (∏ j : ZMod p, (X + C (ZMod.castHom (dvd_refl p) K j))) =
      (X ^ p - X : K[X]) := by
  let f := ZMod.castHom (dvd_refl p) K
  calc
    (∏ j : ZMod p, (X + C (f j))) =
        ∏ j : ZMod p, (X - C (f (-j))) := by
          apply Finset.prod_congr rfl
          intro j _
          simp [sub_eq_add_neg]
    _ = ∏ j : ZMod p, (X - C (f j)) :=
      Equiv.prod_comp (Equiv.neg (ZMod p))
        (fun j : ZMod p => (X - C (f j) : K[X]))
    _ = (∏ j : ZMod p, (X - C j)).map f := by
      rw [Polynomial.map_prod]
      simp
    _ = (X ^ p - X : (ZMod p)[X]).map f := by rw [prod_X_sub_C_primeField]
    _ = X ^ p - X := by simp

private theorem prod_primeField_sub (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p] (x : K) :
    (∏ j : ZMod p, (x - ZMod.castHom (dvd_refl p) K j)) = x ^ p - x := by
  let f := ZMod.castHom (dvd_refl p) K
  calc
    (∏ j : ZMod p, (x - f j)) =
        Polynomial.eval x ((∏ j : ZMod p, (X - C j)).map f) := by
          rw [Polynomial.map_prod, Polynomial.eval_prod]
          simp
    _ = Polynomial.eval x ((X ^ p - X : (ZMod p)[X]).map f) := by
      rw [prod_X_sub_C_primeField]
    _ = x ^ p - x := by simp

/-- The prime-field factorization `∏ j, (x + j) = x ^ p - x`. -/
theorem prod_primeField_add (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p] (x : K) :
    (∏ j : ZMod p, (x + ZMod.castHom (dvd_refl p) K j)) = x ^ p - x := by
  simpa using (Equiv.prod_comp (Equiv.neg (ZMod p))
    (fun j : ZMod p => x - ZMod.castHom (dvd_refl p) K j)).trans
      (prod_primeField_sub p x)

/-- The scaled prime-field product `∏ j, (1 + jρ) = 1 - ρ ^ (p - 1)`. -/
theorem prod_one_add_primeField (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p] (ρ : K) :
    (∏ j : ZMod p, (1 + ZMod.castHom (dvd_refl p) K j * ρ)) =
      1 - ρ ^ (p - 1) := by
  have hpprime : p.Prime := Fact.out
  have hp1 : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hpprime.one_lt).ne'
  by_cases hρ : ρ = 0
  · simp [hρ, zero_pow hp1]
  have hp0 : 0 < p := hpprime.pos
  calc
    (∏ j : ZMod p, (1 + ZMod.castHom (dvd_refl p) K j * ρ)) =
        ∏ j : ZMod p, ρ * (ρ⁻¹ + ZMod.castHom (dvd_refl p) K j) := by
          apply Finset.prod_congr rfl
          intro j _
          field_simp
    _ = ρ ^ p * ∏ j : ZMod p, (ρ⁻¹ + ZMod.castHom (dvd_refl p) K j) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]
    _ = ρ ^ p * ((ρ⁻¹) ^ p - ρ⁻¹) := by rw [prod_primeField_add]
    _ = 1 - ρ ^ (p - 1) := by
      rw [mul_sub, ← mul_pow, mul_inv_cancel₀ hρ, one_pow]
      congr 1
      rw [← pow_sub_one_mul hp0.ne' ρ, mul_assoc, mul_inv_cancel₀ hρ, mul_one]

private theorem sum_inv_mul_prod {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (f : ι → K) (hf : ∀ i, f i ≠ 0) :
    (∑ i, (f i)⁻¹) * ∏ i, f i = ∑ i, ∏ j ∈ Finset.univ.erase i, f j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  simp [hf i]

/--
The logarithmic derivative of the prime-field factorization, evaluated away
from its roots: `∑ j, (x + j)⁻¹ = (x - x ^ p)⁻¹`.
-/
theorem sum_inv_primeField_add (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p] (x : K) (hx : x ^ p - x ≠ 0) :
    (∑ j : ZMod p, (x + ZMod.castHom (dvd_refl p) K j)⁻¹) =
      (x - x ^ p)⁻¹ := by
  let f : ZMod p → K := fun j => x + ZMod.castHom (dvd_refl p) K j
  have hprod : ∏ j, f j = x ^ p - x := prod_primeField_add p x
  have hf : ∀ j, f j ≠ 0 := by
    intro j hj
    apply hx
    rw [← hprod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  have hderiv : (∑ j : ZMod p, ∏ k ∈ Finset.univ.erase j, f k) = -1 := by
    have h := congrArg (fun q : K[X] => Polynomial.eval x q.derivative)
      (primeFieldPolynomial p (K := K))
    simpa [Polynomial.derivative_prod_finset, Polynomial.derivative_pow,
      Polynomial.eval_finsetSum, Polynomial.eval_prod, f,
      CharP.cast_eq_zero K p] using h
  have hlog := sum_inv_mul_prod f hf
  rw [hprod, hderiv] at hlog
  apply (mul_left_injective₀ hx)
  change (∑ i, (f i)⁻¹) * (x ^ p - x) = (x - x ^ p)⁻¹ * (x ^ p - x)
  rw [hlog]
  rw [show x - x ^ p = -(x ^ p - x) by ring, inv_neg]
  simp [hx]

/-- The zeroth affine logarithmic-derivative sum used in the affine pencil. -/
theorem sum_inv_one_add_primeField (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p] (ρ : K) (hρ : ρ ≠ 0)
    (hden : ρ ^ (p - 1) ≠ 1) :
    (∑ j : ZMod p, (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) =
      ρ ^ (p - 1) / (ρ ^ (p - 1) - 1) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpow : ρ * (ρ⁻¹) ^ p = (ρ ^ (p - 1))⁻¹ := by
    rw [inv_pow, ← pow_sub_one_mul hp0.ne' ρ, mul_inv_rev]
    simp [hρ]
  have hx : (ρ⁻¹) ^ p - ρ⁻¹ ≠ 0 := by
    intro hx
    apply hden
    field_simp at hx
    have hx' : ρ * (ρ⁻¹) ^ p - 1 = 0 := by simpa only [one_div, mul_zero] using hx
    rw [hpow] at hx'
    exact inv_eq_one.mp (sub_eq_zero.mp hx')
  calc
    (∑ j : ZMod p, (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) =
        ∑ j : ZMod p, (ρ⁻¹ + ZMod.castHom (dvd_refl p) K j)⁻¹ * ρ⁻¹ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show 1 + ZMod.castHom (dvd_refl p) K j * ρ =
            (ρ⁻¹ + ZMod.castHom (dvd_refl p) K j) * ρ by field_simp]
          simp [mul_inv_rev, mul_comm]
    _ = (∑ j : ZMod p, (ρ⁻¹ + ZMod.castHom (dvd_refl p) K j)⁻¹) * ρ⁻¹ := by
      rw [Finset.sum_mul]
    _ = (ρ⁻¹ - (ρ⁻¹) ^ p)⁻¹ * ρ⁻¹ := by rw [sum_inv_primeField_add p ρ⁻¹ hx]
    _ = ρ ^ (p - 1) / (ρ ^ (p - 1) - 1) := by
      field_simp
      simp only [one_div]
      rw [hpow]
      field_simp [hden, pow_ne_zero (p - 1) hρ]

/-- The first affine logarithmic-derivative moment used in the affine pencil. -/
theorem sum_primeField_mul_inv_one_add (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p] (ρ : K) (hρ : ρ ≠ 0)
    (hden : ρ ^ (p - 1) ≠ 1) :
    (∑ j : ZMod p, ZMod.castHom (dvd_refl p) K j *
      (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) =
      -ρ ^ (p - 2) / (ρ ^ (p - 1) - 1) := by
  have hpprime : p.Prime := Fact.out
  have hp1 : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hpprime.one_lt).ne'
  have hpow : ρ⁻¹ * ρ ^ (p - 1) = ρ ^ (p - 2) := by
    apply (mul_left_injective₀ hρ)
    change (ρ⁻¹ * ρ ^ (p - 1)) * ρ = ρ ^ (p - 2) * ρ
    calc
      (ρ⁻¹ * ρ ^ (p - 1)) * ρ = ρ ^ (p - 1) := by field_simp
      _ = ρ ^ (p - 2) * ρ := by
        simpa [Nat.sub_sub] using (pow_sub_one_mul hp1 ρ).symm
  have hfac : ∀ j : ZMod p, 1 + ZMod.castHom (dvd_refl p) K j * ρ ≠ 0 := by
    have hprod : (∏ j : ZMod p, (1 + ZMod.castHom (dvd_refl p) K j * ρ)) ≠ 0 := by
      rw [prod_one_add_primeField]
      exact sub_ne_zero.mpr (Ne.symm hden)
    exact fun j => Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
  have hid (j : ZMod p) : ZMod.castHom (dvd_refl p) K j * ρ *
      (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ =
      1 - (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ := by
    calc
      ZMod.castHom (dvd_refl p) K j * ρ *
          (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ =
          ((1 + ZMod.castHom (dvd_refl p) K j * ρ) - 1) *
            (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ := by ring
      _ = 1 - (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ (hfac j), one_mul]
  calc
    (∑ j : ZMod p, ZMod.castHom (dvd_refl p) K j *
      (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) =
        ∑ j : ZMod p, ρ⁻¹ *
          (1 - (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro j _
            simp only [inv_eq_one_div]
            field_simp [hfac j]
            simpa [div_eq_mul_inv] using hid j
    _ = ρ⁻¹ * (∑ j : ZMod p,
        (1 - (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹)) := by
      rw [Finset.mul_sum]
    _ = ρ⁻¹ * (0 - ρ ^ (p - 1) / (ρ ^ (p - 1) - 1)) := by
      rw [Finset.sum_sub_distrib, sum_inv_one_add_primeField p ρ hρ hden]
      congr 2
      simp [ZMod.card]
    _ = -ρ ^ (p - 2) / (ρ ^ (p - 1) - 1) := by
      rw [zero_sub, mul_neg, neg_div, ← mul_div_assoc, hpow]

/--
The second affine logarithmic-derivative moment used in the affine pencil;
the hypothesis `p ≠ 2` is exactly what makes the sum of the prime-field
elements vanish.
-/
theorem sum_primeField_sq_mul_inv_one_add (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Type*} [Field K] [CharP K p] (ρ : K) (hρ : ρ ≠ 0)
    (hden : ρ ^ (p - 1) ≠ 1) :
    (∑ j : ZMod p, (ZMod.castHom (dvd_refl p) K j) ^ 2 *
      (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) =
      ρ ^ (p - 3) / (ρ ^ (p - 1) - 1) := by
  have hpprime : p.Prime := Fact.out
  have hpgt : 2 < p := lt_of_le_of_ne hpprime.two_le hp2.symm
  have hp2pos : 0 < p - 2 := Nat.sub_pos_of_lt hpgt
  have hpow : ρ⁻¹ * ρ ^ (p - 2) = ρ ^ (p - 3) := by
    apply (mul_left_injective₀ hρ)
    change (ρ⁻¹ * ρ ^ (p - 2)) * ρ = ρ ^ (p - 3) * ρ
    calc
      (ρ⁻¹ * ρ ^ (p - 2)) * ρ = ρ ^ (p - 2) := by field_simp
      _ = ρ ^ (p - 3) * ρ := by
        simpa [Nat.sub_sub] using (pow_sub_one_mul hp2pos.ne' ρ).symm
  have hsum : (∑ j : ZMod p, ZMod.castHom (dvd_refl p) K j) = 0 := by
    have hz : (∑ j : ZMod p, j) = 0 := by
      simpa [ZMod.card] using
        (FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 1 (by simp [ZMod.card]; omega))
    simpa using congrArg (ZMod.castHom (dvd_refl p) K) hz
  have hfac : ∀ j : ZMod p, 1 + ZMod.castHom (dvd_refl p) K j * ρ ≠ 0 := by
    have hprod : (∏ j : ZMod p, (1 + ZMod.castHom (dvd_refl p) K j * ρ)) ≠ 0 := by
      rw [prod_one_add_primeField]
      exact sub_ne_zero.mpr (Ne.symm hden)
    exact fun j => Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
  have hid (j : ZMod p) : (ZMod.castHom (dvd_refl p) K j) ^ 2 *
      (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ =
      ρ⁻¹ * ZMod.castHom (dvd_refl p) K j - ρ⁻¹ *
        (ZMod.castHom (dvd_refl p) K j *
          (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) := by
    simp only [inv_eq_one_div]
    field_simp [hfac j]
    have hcore : (ZMod.castHom (dvd_refl p) K j) ^ 2 * ρ *
        (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ =
        ZMod.castHom (dvd_refl p) K j -
          ZMod.castHom (dvd_refl p) K j *
            (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ := by
      calc
        (ZMod.castHom (dvd_refl p) K j) ^ 2 * ρ *
            (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ =
            ZMod.castHom (dvd_refl p) K j *
              ((1 + ZMod.castHom (dvd_refl p) K j * ρ) - 1) *
                (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ := by ring
        _ = ZMod.castHom (dvd_refl p) K j -
            ZMod.castHom (dvd_refl p) K j *
              (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹ := by
                rw [mul_assoc, sub_mul, mul_inv_cancel₀ (hfac j), one_mul]
                ring
    simpa [div_eq_mul_inv, mul_sub] using hcore
  calc
    (∑ j : ZMod p, (ZMod.castHom (dvd_refl p) K j) ^ 2 *
      (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) =
        ∑ j : ZMod p, (ρ⁻¹ * ZMod.castHom (dvd_refl p) K j - ρ⁻¹ *
          (ZMod.castHom (dvd_refl p) K j *
            (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹)) := by
              apply Finset.sum_congr rfl
              intro j _
              exact hid j
    _ = ρ⁻¹ * (∑ j : ZMod p, ZMod.castHom (dvd_refl p) K j) - ρ⁻¹ *
        (∑ j : ZMod p, ZMod.castHom (dvd_refl p) K j *
          (1 + ZMod.castHom (dvd_refl p) K j * ρ)⁻¹) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = ρ⁻¹ * 0 - ρ⁻¹ * (-ρ ^ (p - 2) / (ρ ^ (p - 1) - 1)) := by
      rw [hsum, sum_primeField_mul_inv_one_add p ρ hρ hden]
    _ = ρ ^ (p - 3) / (ρ ^ (p - 1) - 1) := by
      rw [mul_zero, zero_sub, neg_div, mul_neg, neg_neg, ← mul_div_assoc, hpow]

end LanglandsFirstMainLemma
