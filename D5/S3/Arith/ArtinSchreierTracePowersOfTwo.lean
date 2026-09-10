/- GID: D5/S3/Arith/ArtinSchreierTracePowersOfTwo
   generality: I
   mirror-B: D5/B/S3/Arith/ArtinSchreierTracePowersOfTwo
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The A396808 coefficients are odd exactly at positive powers of two. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped PowerSeries
open Finset Polynomial

namespace D5.S3.Arith.ArtinSchreierTracePowersOfTwo

noncomputable section

private def nextCoeff (n : ℕ) (p : ℤ[X]) : ℤ :=
  if n < 2 then 1
  else
    (n : ℤ) * (p ^ (n + 2)).coeff n -
      (n + 1 : ℤ) * (p ^ (n + 1)).coeff n

def prefixPolynomial : ℕ → ℤ[X]
  | 0 => 0
  | n + 1 => prefixPolynomial n +
      Polynomial.monomial n (nextCoeff n (prefixPolynomial n))

/-- The normalized integer sequence defined by the finite-prefix recursion of OEIS A396808. -/
def a (n : ℕ) : ℤ := nextCoeff n (prefixPolynomial n)

private def series : ℤ⟦X⟧ := PowerSeries.mk a

@[simp] private theorem prefixPolynomial_zero : prefixPolynomial 0 = 0 := rfl

@[simp] private theorem prefixPolynomial_succ (n : ℕ) :
    prefixPolynomial (n + 1) =
      prefixPolynomial n + Polynomial.monomial n (a n) := rfl

/-- The nth prefix polynomial contains exactly the coefficients with indices below n. -/
theorem prefixPolynomial_eq_sum (n : ℕ) :
    prefixPolynomial n =
      ∑ j ∈ Finset.range n, Polynomial.C (a j) * Polynomial.X ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prefixPolynomial_succ, ih, Finset.sum_range_succ]
      rw [Polynomial.C_mul_X_pow_eq_monomial]

@[simp] private theorem a_zero : a 0 = 1 := by norm_num [a, nextCoeff]

@[simp] private theorem a_one : a 1 = 1 := by
  norm_num [a, nextCoeff, prefixPolynomial]

private theorem coeff_prefixPolynomial (n j : ℕ) :
    (prefixPolynomial n).coeff j = if j < n then a j else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prefixPolynomial_succ, Polynomial.coeff_add, Polynomial.coeff_monomial, ih]
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
    prefixPolynomial n = PowerSeries.trunc n series := by
  ext j
  rw [coeff_prefixPolynomial, PowerSeries.coeff_trunc]
  simp [series]

private theorem coeff_pow_add_monomial
    {R : Type*} [CommRing R] (p : R[X]) (n m : ℕ) (c : R)
    (hn : 0 < n) (hm : 0 < m) (hp0 : p.coeff 0 = 1) :
    ((p + Polynomial.monomial n c) ^ m).coeff n =
      (p ^ m).coeff n + (m : R) * c := by
  classical
  rw [add_comm, (Commute.all (Polynomial.monomial n c) p).add_pow,
    Polynomial.finsetSum_coeff]
  let f : ℕ → R := fun k =>
    ((Polynomial.monomial n c) ^ k * p ^ (m - k) *
      Polynomial.C (m.choose k : R)).coeff n
  have hf0 : f 0 = (p ^ m).coeff n := by
    simp [f]
  have hf1 : f 1 = (m : R) * c := by
    have hconst : ∀ k : ℕ, (p ^ k).coeff 0 = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => simp [pow_succ, Polynomial.mul_coeff_zero, ih, hp0]
    have hcoef : ((Polynomial.monomial n c) * p ^ (m - 1)).coeff n = c := by
      simpa [hconst] using
        (Polynomial.coeff_monomial_mul (p ^ (m - 1)) n 0 c)
    have hcoef' : (p ^ (m - 1) * Polynomial.monomial n c).coeff n = c := by
      rw [mul_comm]
      exact hcoef
    simp [f, hcoef', mul_comm]
  have hfk : ∀ k ∈ Finset.range (m + 1), k ≠ 0 → k ≠ 1 → f k = 0 := by
    intro k hk hk0 hk1
    have hk2 : 2 ≤ k := by omega
    have hlarge : n < k * n := by nlinarith
    have hnle : ¬n * k ≤ n := by nlinarith
    simp only [f, Polynomial.monomial_pow]
    rw [Polynomial.coeff_mul_C, ← Polynomial.C_mul_X_pow_eq_monomial,
      mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    simp [hnle]
  change (∑ k ∈ Finset.range (m + 1), f k) = _
  let s := Finset.range (m + 1)
  have h0 : 0 ∈ s := by simp [s]
  have h1 : 1 ∈ s.erase 0 := by simp [s, hm]
  calc
    (∑ k ∈ s, f k) = f 0 + ∑ k ∈ s.erase 0, f k :=
      (Finset.add_sum_erase s f h0).symm
    _ = f 0 + f 1 := by
      rw [Finset.sum_eq_single 1]
      · intro k hk hk1'
        exact hfk k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk) hk1'
      · exact fun hnot => False.elim (hnot h1)
    _ = (p ^ m).coeff n + (m : R) * c := by rw [hf0, hf1]

private theorem coeff_pow_eq_coeff_trunc_pow
    {R : Type*} [CommRing R] (f : R⟦X⟧) (n m : ℕ) :
    PowerSeries.coeff n (f ^ m) = ((PowerSeries.trunc (n + 1) f) ^ m).coeff n := by
  have h := congrArg (fun p : R[X] => p.coeff n)
    (PowerSeries.trunc_trunc_pow f (n + 1) m)
  calc
    PowerSeries.coeff n (f ^ m) =
        PowerSeries.coeff n ((PowerSeries.trunc (n + 1) f : R⟦X⟧) ^ m) := by
      simpa only [PowerSeries.coeff_trunc, Nat.lt_succ_iff, le_rfl, if_true,
        Polynomial.coeff_coe] using h.symm
    _ = PowerSeries.coeff n ((↑((PowerSeries.trunc (n + 1) f) ^ m)) : R⟦X⟧) := by
      rw [Polynomial.coe_pow]
    _ = ((PowerSeries.trunc (n + 1) f) ^ m).coeff n :=
      Polynomial.coeff_coe _ _

private theorem coeff_pow_eq_strict_trunc_add
    {R : Type*} [CommRing R] (f : R⟦X⟧) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hf0 : PowerSeries.coeff 0 f = 1) :
    PowerSeries.coeff n (f ^ m) =
      ((PowerSeries.trunc n f) ^ m).coeff n + (m : R) * PowerSeries.coeff n f := by
  rw [coeff_pow_eq_coeff_trunc_pow, PowerSeries.trunc_succ]
  exact coeff_pow_add_monomial (PowerSeries.trunc n f) n m
    (PowerSeries.coeff n f) hn hm (by simpa [PowerSeries.coeff_trunc, hn] using hf0)

/-- The generating series of `a` satisfies the coefficient equation stated by OEIS A396808. -/
theorem source_equation (n : ℕ) (hn : 1 < n) :
    (n + 1 : ℤ) * PowerSeries.coeff n ((PowerSeries.mk a) ^ (n + 1)) =
      (n : ℤ) * PowerSeries.coeff n ((PowerSeries.mk a) ^ (n + 2)) := by
  change
    (n + 1 : ℤ) * PowerSeries.coeff n (series ^ (n + 1)) =
      (n : ℤ) * PowerSeries.coeff n (series ^ (n + 2))
  have h1 := coeff_pow_eq_strict_trunc_add series n (n + 1)
    (by omega) (by omega) (by simp [series])
  have h2 := coeff_pow_eq_strict_trunc_add series n (n + 2)
    (by omega) (by omega) (by simp [series])
  rw [← prefixPolynomial_eq_trunc] at h1 h2
  have ha : a n =
      (n : ℤ) * ((prefixPolynomial n) ^ (n + 2)).coeff n -
        (n + 1 : ℤ) * ((prefixPolynomial n) ^ (n + 1)).coeff n := by
    simp [a, nextCoeff, Nat.not_lt.mpr (by omega : 2 ≤ n)]
  generalize ((prefixPolynomial n) ^ (n + 1)).coeff n = c1 at h1 ha
  generalize ((prefixPolynomial n) ^ (n + 2)).coeff n = c2 at h2 ha
  rw [h1, h2]
  simp only [series, PowerSeries.coeff_mk]
  rw [ha]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private theorem recursion_of_source (b : ℕ → ℤ) (hb0 : b 0 = 1)
    (hsource : ∀ n : ℕ, 1 < n →
      (n + 1 : ℤ) * PowerSeries.coeff n ((PowerSeries.mk b) ^ (n + 1)) =
        (n : ℤ) * PowerSeries.coeff n ((PowerSeries.mk b) ^ (n + 2)))
    (n : ℕ) (hn : 1 < n) :
    b n = (n : ℤ) * ((PowerSeries.trunc n (PowerSeries.mk b)) ^ (n + 2)).coeff n -
      (n + 1 : ℤ) * ((PowerSeries.trunc n (PowerSeries.mk b)) ^ (n + 1)).coeff n := by
  have h1 := coeff_pow_eq_strict_trunc_add (PowerSeries.mk b) n (n + 1)
    (by omega) (by omega) (by simpa using hb0)
  have h2 := coeff_pow_eq_strict_trunc_add (PowerSeries.mk b) n (n + 2)
    (by omega) (by omega) (by simpa using hb0)
  simp only [PowerSeries.coeff_mk] at h1 h2
  have hs := hsource n hn
  generalize ((PowerSeries.trunc n (PowerSeries.mk b)) ^ (n + 1)).coeff n = c1 at h1 hs ⊢
  generalize ((PowerSeries.trunc n (PowerSeries.mk b)) ^ (n + 2)).coeff n = c2 at h2 hs ⊢
  rw [h1, h2] at hs
  norm_num [Nat.cast_add, Nat.cast_one] at hs ⊢
  nlinarith

/-- The finite-prefix recursion is the unique normalized integer solution of the source equation. -/
theorem normalized_solution_unique (b : ℕ → ℤ)
    (hb : b 0 = 1 ∧ b 1 = 1 ∧ ∀ n : ℕ, 1 < n →
      (n + 1 : ℤ) * PowerSeries.coeff n ((PowerSeries.mk b) ^ (n + 1)) =
        (n : ℤ) * PowerSeries.coeff n ((PowerSeries.mk b) ^ (n + 2))) :
    b = a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases hb with ⟨hb0, hb1, hsource⟩
      by_cases hn0 : n = 0
      · subst n
        simpa using hb0
      by_cases hn1 : n = 1
      · subst n
        simpa using hb1
      have hn : 1 < n := by omega
      have hr := recursion_of_source b hb0 hsource n hn
      have ht : PowerSeries.trunc n (PowerSeries.mk b) = prefixPolynomial n := by
        ext j
        rw [PowerSeries.coeff_trunc, coeff_prefixPolynomial]
        split_ifs with hj
        · simp only [PowerSeries.coeff_mk]
          exact ih j hj
        · rfl
      rw [ht] at hr
      rw [hr]
      simp [a, nextCoeff, Nat.not_lt.mpr (by omega : 2 ≤ n)]

private abbrev F2 := ZMod 2

def artinCoeff : ℕ → F2 :=
  Nat.evenOddRec 1 (fun _ c => c) (fun n _ => if n = 0 then 1 else 0)

@[simp] private theorem artinCoeff_zero : artinCoeff 0 = 1 := by
  simp [artinCoeff]

@[simp] private theorem artinCoeff_even (n : ℕ) : artinCoeff (2 * n) = artinCoeff n := by
  simp [artinCoeff, Nat.evenOddRec_even]

@[simp] private theorem artinCoeff_odd (n : ℕ) :
    artinCoeff (2 * n + 1) = if n = 0 then 1 else 0 := by
  simp [artinCoeff, Nat.evenOddRec_odd]

private theorem two_mul_zero_or_power_iff (n : ℕ) :
    (2 * n = 0 ∨ ∃ r, 2 * n = 2 ^ r) ↔ (n = 0 ∨ ∃ r, n = 2 ^ r) := by
  constructor
  · rintro (hzero | ⟨r, hr⟩)
    · exact Or.inl (by omega)
    · cases r with
      | zero => simp at hr
      | succ r =>
          right
          refine ⟨r, ?_⟩
          simp only [pow_succ] at hr
          omega
  · rintro (rfl | ⟨r, rfl⟩)
    · exact Or.inl rfl
    · right
      refine ⟨r + 1, ?_⟩
      simp [pow_succ, Nat.mul_comm]

private theorem two_mul_add_one_zero_or_power_iff (n : ℕ) :
    (2 * n + 1 = 0 ∨ ∃ r, 2 * n + 1 = 2 ^ r) ↔ n = 0 := by
  constructor
  · rintro (hzero | ⟨r, hr⟩)
    · omega
    · cases r with
      | zero => simpa using hr
      | succ r =>
          simp only [pow_succ] at hr
          omega
  · rintro rfl
    right
    exact ⟨0, rfl⟩

private theorem artinCoeff_eq_one_iff (n : ℕ) :
    artinCoeff n = 1 ↔ n = 0 ∨ ∃ r, n = 2 ^ r := by
  induction n using Nat.evenOddRec with
  | h0 => simp
  | h_even n ih =>
      rw [artinCoeff_even, ih, ← two_mul_zero_or_power_iff]
  | h_odd n ih =>
      rw [artinCoeff_odd, two_mul_add_one_zero_or_power_iff]
      by_cases hn : n = 0 <;> simp [hn]

/-- The constant-one Artin--Schreier series `1 + x + x^2 + x^4 + x^8 + ...`. -/
def artinSeries : (ZMod 2)⟦X⟧ := PowerSeries.mk artinCoeff

@[simp] private theorem coeff_artinSeries (n : ℕ) :
    PowerSeries.coeff n artinSeries = artinCoeff n := by
  simp [artinSeries]

private theorem expand_artinSeries :
    PowerSeries.expand 2 (by omega) artinSeries = artinSeries + PowerSeries.X := by
  ext n
  induction n using Nat.evenOddRec with
  | h0 =>
      rw [PowerSeries.coeff_expand, if_pos (by simp), Nat.zero_div]
      rw [coeff_artinSeries, map_add, coeff_artinSeries, PowerSeries.coeff_zero_X]
      simp
  | h_even n ih =>
      rw [PowerSeries.coeff_expand, if_pos (by simp)]
      have hdiv : 2 * n / 2 = n := by omega
      rw [hdiv]
      rw [coeff_artinSeries, map_add, coeff_artinSeries, artinCoeff_even,
        PowerSeries.coeff_X, if_neg (by omega)]
      simp
  | h_odd n ih =>
      have hnot : ¬2 ∣ 2 * n + 1 := by omega
      rw [PowerSeries.coeff_expand, if_neg hnot]
      rw [map_add, coeff_artinSeries, artinCoeff_odd, PowerSeries.coeff_X]
      by_cases hn : n = 0
      · subst n
        norm_num
        exact (ZMod.natCast_self 2).symm
      · rw [if_neg hn, if_neg (by omega)]
        simp

/-- The corrected constant-one series is a root of `S^2 + S = X` over `ZMod 2`. -/
theorem artinSeries_square_add :
    artinSeries ^ 2 + artinSeries = PowerSeries.X := by
  have hf := MvPowerSeries.map_frobenius_expand (σ := Unit) 2 (by omega)
    (f := artinSeries)
  rw [ZMod.frobenius_zmod] at hf
  rw [MvPowerSeries.map_id] at hf
  simp only [RingHom.id_apply] at hf
  have hf' : artinSeries ^ 2 = PowerSeries.expand 2 (by omega) artinSeries := hf.symm
  have hself : artinSeries + artinSeries = 0 := by
    ext n
    simp only [map_add, map_zero]
    exact CharTwo.add_self_eq_zero _
  rw [hf', expand_artinSeries]
  rw [add_assoc, add_comm PowerSeries.X artinSeries, ← add_assoc,
    hself, zero_add]

private theorem ps_add_self (f : F2⟦X⟧) : f + f = 0 := by
  ext n
  simp only [map_add, map_zero]
  exact CharTwo.add_self_eq_zero _

private theorem root_square_eq_add {z : F2⟦X⟧}
    (hz : z ^ 2 + z = PowerSeries.X) : z ^ 2 = z + PowerSeries.X := by
  calc
    z ^ 2 = (z ^ 2 + z) + z := by rw [add_assoc, ps_add_self, add_zero]
    _ = PowerSeries.X + z := by rw [hz]
    _ = z + PowerSeries.X := add_comm _ _

private theorem root_pow_recurrence {z : F2⟦X⟧}
    (hz : z ^ 2 + z = PowerSeries.X) (m : ℕ) :
    z ^ (m + 2) = z ^ (m + 1) + PowerSeries.X * z ^ m := by
  rw [pow_add, root_square_eq_add hz, mul_add, pow_add, pow_one]
  ring

private theorem shifted_artinSeries_square_add :
    (artinSeries + 1) ^ 2 + (artinSeries + 1) = PowerSeries.X := by
  have hS := ps_add_self artinSeries
  have h1 := ps_add_self (1 : F2⟦X⟧)
  calc
    (artinSeries + 1) ^ 2 + (artinSeries + 1) =
        (artinSeries ^ 2 + artinSeries) +
          (artinSeries + artinSeries) + (1 + 1) := by ring
    _ = PowerSeries.X := by rw [artinSeries_square_add, hS, h1, add_zero, add_zero]

/-- Trace polynomials for the two roots of `Y^2 + Y = X` over `ZMod 2`. -/
def tracePoly : ℕ → (ZMod 2)[X]
  | 0 => 0
  | 1 => 1
  | m + 2 => tracePoly (m + 1) + Polynomial.X * tracePoly m

@[simp] private theorem tracePoly_zero : tracePoly 0 = 0 := rfl

@[simp] private theorem tracePoly_one : tracePoly 1 = 1 := rfl

@[simp] private theorem tracePoly_add_two (m : ℕ) :
    tracePoly (m + 2) = tracePoly (m + 1) + Polynomial.X * tracePoly m := rfl

/-- The trace recurrence represents the sum of the same power at both roots. -/
theorem tracePoly_identity (m : ℕ) :
    (tracePoly m : (ZMod 2)⟦X⟧) = artinSeries ^ m + (artinSeries + 1) ^ m := by
  induction m using Nat.twoStepInduction with
  | zero =>
      simp only [tracePoly_zero, Polynomial.coe_zero, pow_zero]
      exact (ps_add_self 1).symm
  | one =>
      simp only [tracePoly_one, Polynomial.coe_one, pow_one]
      have hS := ps_add_self artinSeries
      symm
      rw [← add_assoc, hS, zero_add]
  | more m ih0 ih1 =>
      rw [tracePoly_add_two, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X,
        ih1, ih0, root_pow_recurrence artinSeries_square_add,
        root_pow_recurrence shifted_artinSeries_square_add]
      ring

/-- The trace polynomial has natural degree at most the natural quotient `m / 2`. -/
theorem tracePoly_natDegree_le (m : ℕ) : (tracePoly m).natDegree ≤ m / 2 := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m ih0 ih1 =>
      rw [tracePoly_add_two]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · omega
      · apply Polynomial.natDegree_mul_le.trans
        simp only [Polynomial.natDegree_X]
        omega

private theorem shifted_artinSeries_constantCoeff :
    PowerSeries.constantCoeff (artinSeries + 1) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add,
    coeff_artinSeries, artinCoeff_zero]
  simpa using (CharTwo.add_self_eq_zero (1 : F2))

private theorem coeff_shifted_artinSeries_pow_eq_zero (m n : ℕ) (hn : n < m) :
    PowerSeries.coeff n ((artinSeries + 1) ^ m) = 0 := by
  apply PowerSeries.coeff_of_lt_order n
  apply lt_of_lt_of_le _
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero m shifted_artinSeries_constantCoeff)
  exact_mod_cast hn

/-- Between half the exponent and the exponent, the constant-one root power has zero coefficient. -/
theorem coeff_artinSeries_pow_eq_zero (m n : ℕ)
    (hdegree : m / 2 < n) (hexponent : n < m) :
    PowerSeries.coeff n (artinSeries ^ m) = 0 := by
  have hp : (tracePoly m).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (tracePoly_natDegree_le m) hdegree)
  have hshift := coeff_shifted_artinSeries_pow_eq_zero m n hexponent
  have ht := congrArg (PowerSeries.coeff n) (tracePoly_identity m)
  simp only [Polynomial.coeff_coe, map_add] at ht
  rw [hp, hshift] at ht
  simpa using ht.symm

private theorem artinSeries_source_equation (n : ℕ) (hn : 1 < n) :
    (n + 1 : F2) * PowerSeries.coeff n (artinSeries ^ (n + 1)) =
      (n : F2) * PowerSeries.coeff n (artinSeries ^ (n + 2)) := by
  rcases n.even_or_odd with heven | hodd
  · have hv : PowerSeries.coeff n (artinSeries ^ (n + 1)) = 0 := by
      apply coeff_artinSeries_pow_eq_zero
      · rcases heven with ⟨k, hk⟩
        omega
      · omega
    rw [heven.natCast_zmod_two, hv]
    simp
  · have hv : PowerSeries.coeff n (artinSeries ^ (n + 2)) = 0 := by
      apply coeff_artinSeries_pow_eq_zero
      · rcases hodd with ⟨k, hk⟩
        omega
      · omega
    rw [hodd.natCast_zmod_two, hv, CharTwo.add_self_eq_zero]
    simp

private def reducedSeries : F2⟦X⟧ :=
  PowerSeries.map (Int.castRingHom F2) series

@[simp] private theorem coeff_reducedSeries (n : ℕ) :
    PowerSeries.coeff n reducedSeries = (a n : F2) := by
  simp [reducedSeries, series]

private theorem coeff_reducedSeries_pow (n m : ℕ) :
    PowerSeries.coeff n (reducedSeries ^ m) =
      (Int.castRingHom F2) (PowerSeries.coeff n (series ^ m)) := by
  change PowerSeries.coeff n ((PowerSeries.map (Int.castRingHom F2) series) ^ m) = _
  calc
    _ = PowerSeries.coeff n (PowerSeries.map (Int.castRingHom F2) (series ^ m)) := by
      exact congrArg (PowerSeries.coeff n)
        ((PowerSeries.map (Int.castRingHom F2)).map_pow series m).symm
    _ = _ := by rw [PowerSeries.coeff_map]

private theorem reducedSeries_source_equation (n : ℕ) (hn : 1 < n) :
    (n + 1 : F2) * PowerSeries.coeff n (reducedSeries ^ (n + 1)) =
      (n : F2) * PowerSeries.coeff n (reducedSeries ^ (n + 2)) := by
  rw [coeff_reducedSeries_pow, coeff_reducedSeries_pow]
  simpa [series] using congrArg (Int.castRingHom F2) (source_equation n hn)

private theorem modTwo_source_unique (f g : F2⟦X⟧)
    (hf0 : PowerSeries.coeff 0 f = 1) (hg0 : PowerSeries.coeff 0 g = 1)
    (hf1 : PowerSeries.coeff 1 f = 1) (hg1 : PowerSeries.coeff 1 g = 1)
    (hsf : ∀ n : ℕ, 1 < n →
      (n + 1 : F2) * PowerSeries.coeff n (f ^ (n + 1)) =
        (n : F2) * PowerSeries.coeff n (f ^ (n + 2)))
    (hsg : ∀ n : ℕ, 1 < n →
      (n + 1 : F2) * PowerSeries.coeff n (g ^ (n + 1)) =
        (n : F2) * PowerSeries.coeff n (g ^ (n + 2))) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact hf0.trans hg0.symm
      by_cases hn1 : n = 1
      · subst n
        exact hf1.trans hg1.symm
      have hn : 1 < n := by omega
      have ht : PowerSeries.trunc n f = PowerSeries.trunc n g := by
        ext j
        rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
        split_ifs with hj
        · exact ih j hj
        · rfl
      rcases n.even_or_odd with heven | hodd
      · have hvf : PowerSeries.coeff n (f ^ (n + 1)) = 0 := by
          have hs := hsf n hn
          rw [heven.natCast_zmod_two] at hs
          simpa using hs
        have hvg : PowerSeries.coeff n (g ^ (n + 1)) = 0 := by
          have hs := hsg n hn
          rw [heven.natCast_zmod_two] at hs
          simpa using hs
        have hef := coeff_pow_eq_strict_trunc_add f n (n + 1)
          (by omega) (by omega) hf0
        have heg := coeff_pow_eq_strict_trunc_add g n (n + 1)
          (by omega) (by omega) hg0
        rw [hvf] at hef
        rw [hvg, ← ht] at heg
        simp only [Nat.cast_add, Nat.cast_one, heven.natCast_zmod_two, zero_add,
          one_mul] at hef heg
        exact (CharTwo.add_eq_zero.mp hef.symm).symm.trans
          (CharTwo.add_eq_zero.mp heg.symm)
      · have hvf : PowerSeries.coeff n (f ^ (n + 2)) = 0 := by
          have hs := hsf n hn
          rw [hodd.natCast_zmod_two, CharTwo.add_self_eq_zero] at hs
          simpa using hs.symm
        have hvg : PowerSeries.coeff n (g ^ (n + 2)) = 0 := by
          have hs := hsg n hn
          rw [hodd.natCast_zmod_two, CharTwo.add_self_eq_zero] at hs
          simpa using hs.symm
        have hef := coeff_pow_eq_strict_trunc_add f n (n + 2)
          (by omega) (by omega) hf0
        have heg := coeff_pow_eq_strict_trunc_add g n (n + 2)
          (by omega) (by omega) hg0
        rw [hvf] at hef
        rw [hvg, ← ht] at heg
        simp only [Nat.cast_add, hodd.natCast_zmod_two] at hef heg
        have hone : (1 : F2) + ((2 : ℕ) : F2) = 1 := by
          rw [ZMod.natCast_self, add_zero]
        rw [hone, one_mul] at hef heg
        exact (CharTwo.add_eq_zero.mp hef.symm).symm.trans
          (CharTwo.add_eq_zero.mp heg.symm)

/-- The coefficientwise mod-two reduction of the integer series is the constant-one root. -/
theorem reducedSeries_eq_artinSeries :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (PowerSeries.mk a) = artinSeries := by
  change reducedSeries = artinSeries
  apply modTwo_source_unique reducedSeries artinSeries
  · simp [reducedSeries, series]
  · simp
  · simp [reducedSeries, series]
  · rw [coeff_artinSeries]
    simpa using artinCoeff_odd 0
  · exact reducedSeries_source_equation
  · exact artinSeries_source_equation

private theorem parity_iff_power_of_two (n : ℕ) (hn : 0 < n) :
    Odd (a n) ↔ ∃ r, n = 2 ^ r := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hc : (a n : F2) = artinCoeff n := by
    calc
      (a n : F2) = PowerSeries.coeff n reducedSeries := (coeff_reducedSeries n).symm
      _ = PowerSeries.coeff n artinSeries := by
        have h := congrArg (PowerSeries.coeff n) reducedSeries_eq_artinSeries
        simpa [reducedSeries, series] using h
      _ = artinCoeff n := coeff_artinSeries n
  rw [hc, artinCoeff_eq_one_iff]
  simp [Nat.ne_of_gt hn]

/-- OEIS A396808 first conjecture: positive-index coefficients are odd exactly at powers of two. -/
theorem a396808_first_conjecture :
    ∀ n > 0, Odd (a n) ↔ ∃ r, n = 2 ^ r := by
  exact fun n hn => parity_iff_power_of_two n hn

-- Fidelity witnesses: the normalization hypotheses co-occur and the positive domain is inhabited.
example :
    a 0 = 1 ∧ a 1 = 1 ∧ ∀ n : ℕ, 1 < n →
      (n + 1 : ℤ) * PowerSeries.coeff n ((PowerSeries.mk a) ^ (n + 1)) =
        (n : ℤ) * PowerSeries.coeff n ((PowerSeries.mk a) ^ (n + 2)) := by
  exact ⟨a_zero, a_one, source_equation⟩

example : ∃ n : ℕ, 0 < n := ⟨1, by omega⟩

#print axioms source_equation
#print axioms prefixPolynomial_eq_sum
#print axioms normalized_solution_unique
#print axioms artinSeries_square_add
#print axioms tracePoly_identity
#print axioms tracePoly_natDegree_le
#print axioms coeff_artinSeries_pow_eq_zero
#print axioms reducedSeries_eq_artinSeries
#print axioms a396808_first_conjecture

end

end D5.S3.Arith.ArtinSchreierTracePowersOfTwo
