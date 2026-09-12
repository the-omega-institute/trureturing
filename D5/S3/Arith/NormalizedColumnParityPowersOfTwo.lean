/- GID: D5/S3/Arith/NormalizedColumnParityPowersOfTwo
   generality: I
   mirror-B: D5/B/S3/Arith/NormalizedColumnParityPowersOfTwo
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The zero-constant-coefficient solution of the cubic recorded for A144637 is odd exactly at positive powers of two. -/

import D5.S3.Arith.ArtinSchreierQuadraticRootUniqueness
import D5.S3.Arith.ArtinSchreierTracePowersOfTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped PowerSeries
open Finset Polynomial

namespace D5.S3.Arith.NormalizedColumnParityPowersOfTwo

noncomputable section

private def nextCoeff (n : ℕ) (p : ℤ[X]) : ℤ :=
  if n = 0 then 0
  else
    (if n = 2 then 1 else 0) -
      36 * (p ^ 3).coeff n - 3 * (p ^ 2).coeff n - 6 * p.coeff (n - 1)

private def prefixPolynomial : ℕ → ℤ[X]
  | 0 => 0
  | n + 1 => prefixPolynomial n +
      Polynomial.monomial n (nextCoeff n (prefixPolynomial n))

private def normalizedCoeff (n : ℕ) : ℤ :=
  nextCoeff n (prefixPolynomial n)

/-- The integral zero-constant-term solution of the normalized A144637
generating equation, constructed coefficient by coefficient. -/
def normalizedColumnSeries : ℤ⟦X⟧ := PowerSeries.mk normalizedCoeff

@[simp] private theorem prefixPolynomial_succ (n : ℕ) :
    prefixPolynomial (n + 1) =
      prefixPolynomial n + Polynomial.monomial n (normalizedCoeff n) := by
  simp [prefixPolynomial, normalizedCoeff]

@[simp] private theorem normalizedCoeff_zero : normalizedCoeff 0 = 0 := by
  simp [normalizedCoeff, nextCoeff]

private theorem coeff_prefixPolynomial (n j : ℕ) :
    (prefixPolynomial n).coeff j = if j < n then normalizedCoeff j else 0 := by
  induction n with
  | zero => simp [prefixPolynomial]
  | succ n ih =>
      rw [prefixPolynomial_succ, Polynomial.coeff_add,
        Polynomial.coeff_monomial, ih]
      by_cases h : j = n
      · subst j
        simp
      · by_cases hj : j < n
        · have h' : n ≠ j := Ne.symm h
          simp [h', hj, Nat.lt_succ_of_lt hj]
        · have hnj : n < j := by omega
          have h' : n ≠ j := Ne.symm h
          have hjn : ¬j ≤ n := Nat.not_le.mpr hnj
          simp [h', hj, hjn]

private theorem prefixPolynomial_eq_trunc (n : ℕ) :
    prefixPolynomial n = PowerSeries.trunc n normalizedColumnSeries := by
  ext j
  rw [coeff_prefixPolynomial, PowerSeries.coeff_trunc]
  simp [normalizedColumnSeries]

private theorem coeff_pow_add_monomial_of_constantCoeff_zero
    {R : Type*} [CommRing R] (p : R[X]) (n m : ℕ) (c : R)
    (hn : 0 < n) (hm : 1 < m) (hp0 : p.coeff 0 = 0) :
    ((p + Polynomial.monomial n c) ^ m).coeff n = (p ^ m).coeff n := by
  classical
  rw [add_comm, (Commute.all (Polynomial.monomial n c) p).add_pow,
    Polynomial.finsetSum_coeff]
  let term : ℕ → R := fun k =>
    ((Polynomial.monomial n c) ^ k * p ^ (m - k) *
      Polynomial.C (m.choose k : R)).coeff n
  have hterm0 : term 0 = (p ^ m).coeff n := by
    simp [term]
  have hconst : ∀ k : ℕ, 0 < k → (p ^ k).coeff 0 = 0 := by
    intro k hk
    cases k with
    | zero => omega
    | succ k => simp [pow_succ, Polynomial.mul_coeff_zero, hp0]
  have hterm1 : term 1 = 0 := by
    have hcoef : ((Polynomial.monomial n c) * p ^ (m - 1)).coeff n = 0 := by
      have h := Polynomial.coeff_monomial_mul (p ^ (m - 1)) n 0 c
      simpa [hconst (m - 1) (by omega)] using h
    simpa [term] using congrArg (fun z : R => z * (m : R)) hcoef
  have htermk : ∀ k ∈ Finset.range (m + 1), k ≠ 0 → k ≠ 1 → term k = 0 := by
    intro k hk hk0 hk1
    have hk2 : 2 ≤ k := by omega
    have hnle : ¬n * k ≤ n := by nlinarith
    simp only [term, Polynomial.monomial_pow]
    rw [Polynomial.coeff_mul_C, ← Polynomial.C_mul_X_pow_eq_monomial,
      mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    simp [hnle]
  change (∑ k ∈ Finset.range (m + 1), term k) = _
  let s := Finset.range (m + 1)
  have hzero : 0 ∈ s := by simp [s]
  calc
    (∑ k ∈ s, term k) = term 0 + ∑ k ∈ s.erase 0, term k :=
      (Finset.add_sum_erase s term hzero).symm
    _ = term 0 + 0 := by
      congr 1
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hk1 : k = 1
      · subst k
        exact hterm1
      · exact htermk k (Finset.mem_of_mem_erase hk)
          (Finset.ne_of_mem_erase hk) hk1
    _ = (p ^ m).coeff n := by rw [hterm0, add_zero]

private theorem coeff_pow_eq_coeff_trunc_pow
    {R : Type*} [CommRing R] (f : R⟦X⟧) (n m : ℕ) :
    PowerSeries.coeff n (f ^ m) =
      ((PowerSeries.trunc (n + 1) f) ^ m).coeff n := by
  have h := congrArg (fun p : R[X] => p.coeff n)
    (PowerSeries.trunc_trunc_pow f (n + 1) m)
  calc
    PowerSeries.coeff n (f ^ m) =
        PowerSeries.coeff n ((PowerSeries.trunc (n + 1) f : R⟦X⟧) ^ m) := by
      simpa only [PowerSeries.coeff_trunc, Nat.lt_succ_iff, le_rfl, if_true,
        Polynomial.coeff_coe] using h.symm
    _ = PowerSeries.coeff n
        ((↑((PowerSeries.trunc (n + 1) f) ^ m)) : R⟦X⟧) := by
      rw [Polynomial.coe_pow]
    _ = ((PowerSeries.trunc (n + 1) f) ^ m).coeff n :=
      Polynomial.coeff_coe _ _

private theorem coeff_pow_eq_strict_trunc_of_constantCoeff_zero
    {R : Type*} [CommRing R] (f : R⟦X⟧) (n m : ℕ)
    (hn : 0 < n) (hm : 1 < m) (hf0 : PowerSeries.coeff 0 f = 0) :
    PowerSeries.coeff n (f ^ m) =
      ((PowerSeries.trunc n f) ^ m).coeff n := by
  rw [coeff_pow_eq_coeff_trunc_pow, PowerSeries.trunc_succ]
  apply coeff_pow_add_monomial_of_constantCoeff_zero
  · exact hn
  · exact hm
  · simpa [PowerSeries.coeff_trunc, hn] using hf0

private theorem coeff_linear_term (f : ℤ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n ((1 + PowerSeries.C 6 * PowerSeries.X) * f) =
      PowerSeries.coeff n f +
        6 * if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  rw [show (1 + PowerSeries.C 6 * PowerSeries.X) * f =
      f + PowerSeries.C 6 * (PowerSeries.X ^ 1 * f) by ring]
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']

private theorem normalizedColumnSeries_constantCoeff :
    PowerSeries.constantCoeff normalizedColumnSeries = 0 := by
  simp [normalizedColumnSeries]

private theorem normalizedColumnSeries_equation :
    PowerSeries.C 36 * normalizedColumnSeries ^ 3 +
        PowerSeries.C 3 * normalizedColumnSeries ^ 2 +
        (1 + PowerSeries.C 6 * PowerSeries.X) * normalizedColumnSeries =
      PowerSeries.X ^ 2 := by
  ext n
  rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    coeff_linear_term, PowerSeries.coeff_X_pow]
  by_cases hn0 : n = 0
  · subst n
    simp [normalizedColumnSeries]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hcube := coeff_pow_eq_strict_trunc_of_constantCoeff_zero
      normalizedColumnSeries n 3 hn (by omega) (by simp [normalizedColumnSeries])
    have hsquare := coeff_pow_eq_strict_trunc_of_constantCoeff_zero
      normalizedColumnSeries n 2 hn (by omega) (by simp [normalizedColumnSeries])
    rw [← prefixPolynomial_eq_trunc] at hcube hsquare
    rw [hcube, hsquare]
    have hprev : (prefixPolynomial n).coeff (n - 1) =
        normalizedCoeff (n - 1) := by
      rw [coeff_prefixPolynomial, if_pos (by omega)]
    rw [if_pos (by omega : 1 ≤ n), normalizedColumnSeries,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rw [normalizedCoeff, nextCoeff, if_neg hn0, hprev]
    ring

private theorem normalizedColumnSeries_unique (z : ℤ⟦X⟧)
    (hz0 : PowerSeries.constantCoeff z = 0)
    (hz : PowerSeries.C 36 * z ^ 3 + PowerSeries.C 3 * z ^ 2 +
        (1 + PowerSeries.C 6 * PowerSeries.X) * z = PowerSeries.X ^ 2) :
    z = normalizedColumnSeries := by
  let u := PowerSeries.C 36 *
      (z ^ 2 + z * normalizedColumnSeries + normalizedColumnSeries ^ 2) +
    PowerSeries.C 3 * (z + normalizedColumnSeries) +
    (1 + PowerSeries.C 6 * PowerSeries.X)
  have hu : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    convert isUnit_one
    simp [u, hz0, normalizedColumnSeries_constantCoeff]
  have hprod : (z - normalizedColumnSeries) * u = 0 := by
    calc
      (z - normalizedColumnSeries) * u =
          (PowerSeries.C 36 * z ^ 3 + PowerSeries.C 3 * z ^ 2 +
              (1 + PowerSeries.C 6 * PowerSeries.X) * z) -
            (PowerSeries.C 36 * normalizedColumnSeries ^ 3 +
              PowerSeries.C 3 * normalizedColumnSeries ^ 2 +
              (1 + PowerSeries.C 6 * PowerSeries.X) * normalizedColumnSeries) := by
        simp only [u]
        ring
      _ = 0 := by rw [hz, normalizedColumnSeries_equation, sub_self]
  apply sub_eq_zero.mp
  apply hu.mul_right_cancel
  simpa using hprod

private abbrev F2 := ZMod 2
private abbrev reduce := PowerSeries.map (Int.castRingHom F2)

private theorem reduced_equation :
    (reduce normalizedColumnSeries) ^ 2 + reduce normalizedColumnSeries =
      PowerSeries.X ^ 2 := by
  have h := congrArg reduce normalizedColumnSeries_equation
  simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    map_one] at h
  have h36 : (Int.castRingHom F2) 36 = 0 := by
    apply ZMod.intCast_eq_zero_iff_even.mpr
    exact ⟨18, by norm_num⟩
  have h3 : (Int.castRingHom F2) 3 = 1 := by
    apply ZMod.intCast_eq_one_iff_odd.mpr
    exact ⟨1, by norm_num⟩
  have h6 : (Int.castRingHom F2) 6 = 0 := by
    apply ZMod.intCast_eq_zero_iff_even.mpr
    exact ⟨3, by norm_num⟩
  rw [h36, h3, h6] at h
  simpa using h

private theorem reduced_constantCoeff :
    PowerSeries.constantCoeff (reduce normalizedColumnSeries) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff,
    normalizedColumnSeries_constantCoeff]
  rfl

private def quadraticSeries : F2⟦X⟧ :=
  D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinSeries + 1 + PowerSeries.X

private theorem coeff_quadraticSeries_zero :
    PowerSeries.coeff 0 quadraticSeries = 0 := by
  simp only [quadraticSeries, map_add,
    D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinSeries,
    PowerSeries.coeff_mk,
    D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinCoeff,
    Nat.evenOddRec_zero, PowerSeries.coeff_zero_one,
    PowerSeries.coeff_zero_X, add_zero]
  exact CharTwo.add_self_eq_zero 1

private theorem coeff_quadraticSeries_one :
    PowerSeries.coeff 1 quadraticSeries = 0 := by
  have hartin :
      D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinCoeff 1 = 1 := by
    have h := Nat.evenOddRec_odd (P := fun _ => F2)
      (1 : F2) (fun _ c => c) (fun n _ => if n = 0 then 1 else 0) rfl 0
    simpa [D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinCoeff] using h
  simp only [quadraticSeries, map_add,
    D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinSeries,
    PowerSeries.coeff_mk, hartin, PowerSeries.coeff_one,
    PowerSeries.coeff_X, if_true]
  exact CharTwo.add_self_eq_zero 1

private theorem series_two_eq_zero : (2 : F2⟦X⟧) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (PowerSeries.C (R := F2)) (CharTwo.two_eq_zero (R := F2))

private theorem series_add_self_eq_zero (f : F2⟦X⟧) : f + f = 0 := by
  ext n
  simpa only [map_add, map_zero] using
    CharTwo.add_self_eq_zero (PowerSeries.coeff n f)

private theorem quadraticSeries_equation :
    quadraticSeries ^ 2 + quadraticSeries = PowerSeries.X ^ 2 := by
  let S := D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinSeries
  have hS : S ^ 2 + S = PowerSeries.X :=
    D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinSeries_square_add
  have hsq : (S + 1 + PowerSeries.X) ^ 2 =
      S ^ 2 + 1 + PowerSeries.X ^ 2 := by
    calc
      (S + 1 + PowerSeries.X) ^ 2 =
          S ^ 2 + 1 + PowerSeries.X ^ 2 +
            (2 : F2⟦X⟧) * (S + S * PowerSeries.X + PowerSeries.X) := by ring
      _ = S ^ 2 + 1 + PowerSeries.X ^ 2 := by
        rw [series_two_eq_zero, zero_mul, add_zero]
  change (S + 1 + PowerSeries.X) ^ 2 + (S + 1 + PowerSeries.X) = _
  rw [hsq]
  calc
    S ^ 2 + 1 + PowerSeries.X ^ 2 + (S + 1 + PowerSeries.X) =
        (S ^ 2 + S) + (1 + 1) + PowerSeries.X ^ 2 + PowerSeries.X := by ring
    _ = (PowerSeries.X + PowerSeries.X) + PowerSeries.X ^ 2 := by
      rw [hS, series_add_self_eq_zero]
      ring
    _ = PowerSeries.X ^ 2 := by rw [series_add_self_eq_zero, zero_add]

private theorem reduced_eq_quadraticSeries :
    reduce normalizedColumnSeries = quadraticSeries := by
  apply D5.S3.Arith.ArtinSchreierQuadraticRootUniqueness.eq_of_square_add_eq_square_add
    (reduce normalizedColumnSeries) quadraticSeries (PowerSeries.X ^ 2)
  · exact reduced_equation
  · exact quadraticSeries_equation
  · rw [reduced_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_quadraticSeries_zero]

private theorem coeff_quadraticSeries_eq_one_iff (n : ℕ) :
    PowerSeries.coeff n quadraticSeries = 1 ↔
      ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k := by
  by_cases hn0 : n = 0
  · subst n
    rw [coeff_quadraticSeries_zero]
    constructor
    · norm_num
    · rintro ⟨k, _hk, hk⟩
      have hpos : 0 < 2 ^ k := pow_pos (by omega) k
      omega
  by_cases hn1 : n = 1
  · subst n
    rw [coeff_quadraticSeries_one]
    constructor
    · norm_num
    · rintro ⟨k, hk, hpow⟩
      cases k with
      | zero => omega
      | succ k =>
          simp only [pow_succ] at hpow
          omega
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hcoeff : PowerSeries.coeff n quadraticSeries =
      PowerSeries.coeff n
        D5.S3.Arith.ArtinSchreierTracePowersOfTwo.artinSeries := by
    simp [quadraticSeries, hn0, hn1, PowerSeries.coeff_X]
  rw [hcoeff]
  have hi := congrArg (PowerSeries.coeff n)
    D5.S3.Arith.ArtinSchreierTracePowersOfTwo.reducedSeries_eq_artinSeries
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk] at hi
  rw [← hi]
  change ((D5.S3.Arith.ArtinSchreierTracePowersOfTwo.a n : ℤ) : F2) = 1 ↔ _
  rw [ZMod.intCast_eq_one_iff_odd]
  rw [D5.S3.Arith.ArtinSchreierTracePowersOfTwo.a396808_first_conjecture n hn]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    cases k with
    | zero =>
        exfalso
        apply hn1
        simpa using hk
    | succ k => omega
  · rintro ⟨k, _hk, hk⟩
    exact ⟨k, hk⟩

/-- OEIS A144637: the coefficients of its normalized integral series are odd
exactly at powers of two with positive exponent. -/
theorem a144637_normalized_column_parity :
    PowerSeries.constantCoeff normalizedColumnSeries = 0 ∧
    (PowerSeries.C 36 * normalizedColumnSeries ^ 3 +
        PowerSeries.C 3 * normalizedColumnSeries ^ 2 +
        (1 + PowerSeries.C 6 * PowerSeries.X) * normalizedColumnSeries =
      PowerSeries.X ^ 2) ∧
    (∀ z : ℤ⟦X⟧, PowerSeries.constantCoeff z = 0 →
      PowerSeries.C 36 * z ^ 3 + PowerSeries.C 3 * z ^ 2 +
          (1 + PowerSeries.C 6 * PowerSeries.X) * z = PowerSeries.X ^ 2 →
        z = normalizedColumnSeries) ∧
    ∀ n : ℕ, Odd (PowerSeries.coeff n normalizedColumnSeries) ↔
      ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k := by
  refine ⟨normalizedColumnSeries_constantCoeff,
    normalizedColumnSeries_equation, normalizedColumnSeries_unique, ?_⟩
  intro n
  rw [← ZMod.intCast_eq_one_iff_odd]
  have h := congrArg (PowerSeries.coeff n) reduced_eq_quadraticSeries
  rw [PowerSeries.coeff_map] at h
  change ((PowerSeries.coeff n normalizedColumnSeries : ℤ) : F2) = 1 ↔ _
  have h' : ((PowerSeries.coeff n normalizedColumnSeries : ℤ) : F2) =
      PowerSeries.coeff n quadraticSeries := h
  rw [h']
  exact coeff_quadraticSeries_eq_one_iff n

#print axioms normalizedColumnSeries
#print axioms a144637_normalized_column_parity

end


end D5.S3.Arith.NormalizedColumnParityPowersOfTwo
