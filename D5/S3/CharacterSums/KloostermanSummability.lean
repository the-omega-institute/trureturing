import D5.S3.CharacterSums.KloostermanCRT
import D5.S3.CharacterSums.PrimeKloostermanFourthMoment
import D5.S3.CharacterSums.PrimePowerKloostermanRootCount
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Summability of normalized Kloosterman weights

The prime fourth moment and the prime-power stationary-phase root counts
bound the same standard-character sum. Coprime CRT glues these bounds, and
splitting the prime divisors at `4 ^ 8` gives a summable power of the modulus
after division by its square.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.CharacterSums.KloostermanSummability

open scoped BigOperators
open PrimePowerKloostermanStationaryPhase
open KloostermanCRT (kloosterman_crt)

/-- At modulus one the unit sum has one term and the phase is trivial. -/
theorem kloosterman_modulus_one (a : ZMod 1) (b : (ZMod 1)ˣ) :
    kloosterman a b = 1 := by
  unfold kloosterman
  rw [Fintype.sum_subsingleton _ (1 : (ZMod 1)ˣ)]
  unfold phase
  have hzero : a * ((1 : (ZMod 1)ˣ) : ZMod 1) +
      (b : ZMod 1) * ((1 : (ZMod 1)ˣ) : ZMod 1)⁻¹ = 0 :=
    Subsingleton.elim _ _
  rw [hzero, AddChar.map_zero_eq_one]

private theorem norm_kloosterman_prime_le {p : ℕ} [Fact p.Prime] [NeZero p]
    (a : ZMod p) (b : (ZMod p)ˣ) :
    ‖kloosterman a b‖ ≤ 4 * (p : ℝ) ^ (3 / 4 : ℝ) := by
  have hmoment : ‖kloosterman a b‖ ^ 4 ≤ 3 * (p : ℝ) ^ 3 := by
    simpa only [kloosterman, phase, PrimeKloostermanFourthMoment.primeKloosterman] using
      PrimeKloostermanFourthMoment.norm_primeKloosterman_pow_four_le
        (p := p) a (b : ZMod p) b.ne_zero
  have hpow : ((p : ℝ) ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = (p : ℝ) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (Nat.cast_nonneg p),
      show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hnonneg : 0 ≤ 4 * (p : ℝ) ^ (3 / 4 : ℝ) := by positivity
  apply (pow_le_pow_iff_left₀ (norm_nonneg (kloosterman a b)) hnonneg
    (by decide : (4 : ℕ) ≠ 0)).mp
  calc
    _ ≤ 3 * (p : ℝ) ^ 3 := hmoment
    _ ≤ (4 : ℝ) ^ (4 : ℕ) * (p : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by rw [mul_pow, hpow]

/-- Fourth moment at exponent one and stationary phase at higher exponents. -/
theorem norm_kloosterman_prime_pow_le {p e : ℕ} [Fact p.Prime]
    (he : 0 < e) (a : ZMod (p ^ e)) (b : (ZMod (p ^ e))ˣ) :
    ‖kloosterman a b‖ ≤ 4 * ((p ^ e : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
  by_cases h1 : e = 1
  · let bound (q : ℕ) : Prop :=
      ∀ [NeZero q] (x : ZMod q) (y : (ZMod q)ˣ),
        ‖kloosterman x y‖ ≤ 4 * (q : ℝ) ^ (3 / 4 : ℝ)
    have hpBound : bound p := by
      intro _ x y
      exact norm_kloosterman_prime_le x y
    have hpeBound : bound (p ^ e) := by
      simpa only [h1, pow_one] using hpBound
    exact @hpeBound inferInstance a b
  · have he₂ : 2 ≤ e := by omega
    have hstationary : ‖kloosterman a b‖ ≤ 4 * ((p ^ (e - e / 2) : ℕ) : ℝ) := by
      by_cases hp₂ : p = 2
      · subst p
        exact norm_kloosterman_le_four_mul_two he₂ a b
      · exact (norm_kloosterman_le_two_mul (p := p) (e := e) he₂ hp₂ a b).trans
          (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))
    have hceil : 4 * (e - e / 2) ≤ 3 * e := by omega
    have hceil' : (4 : ℝ) * ((e - e / 2 : ℕ) : ℝ) ≤ 3 * (e : ℝ) := by
      exact_mod_cast hceil
    have hexp : ((e - e / 2 : ℕ) : ℝ) ≤ (e : ℝ) * (3 / 4 : ℝ) := by linarith
    have hp : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Fact.out : p.Prime).one_lt.le
    calc
      _ ≤ 4 * ((p ^ (e - e / 2) : ℕ) : ℝ) := hstationary
      _ = 4 * (p : ℝ) ^ ((e - e / 2 : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.rpow_natCast]
      _ ≤ 4 * (p : ℝ) ^ ((e : ℝ) * (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp hexp) (by positivity)
      _ = _ := by
        rw [Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast, Nat.cast_pow]

/-- The CRT estimate for every positive modulus, with arbitrary first coefficient. -/
theorem norm_kloosterman_le {c : ℕ} [NeZero c] (a : ZMod c) (b : (ZMod c)ˣ) :
    ‖kloosterman a b‖ ≤ (4 : ℝ) ^ c.primeFactors.card * (c : ℝ) ^ (3 / 4 : ℝ) := by
  have bound : ∀ q : ℕ, ∀ [NeZero q] (x : ZMod q) (y : (ZMod q)ˣ),
      ‖kloosterman x y‖ ≤ (4 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ (3 / 4 : ℝ) := by
    refine Nat.recOnPosPrimePosCoprime
      (motive := fun q => ∀ [NeZero q] (x : ZMod q) (y : (ZMod q)ˣ),
        ‖kloosterman x y‖ ≤ (4 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ (3 / 4 : ℝ))
      ?_ ?_ ?_ ?_
    · intro p e hp he _ x y
      let : Fact p.Prime := ⟨hp⟩
      simpa only [Nat.primeFactors_prime_pow he.ne' hp, Finset.card_singleton, pow_one] using
        (norm_kloosterman_prime_pow_le (p := p) (e := e) he x y)
    · intro hzero
      exact (hzero.out rfl).elim
    · intro _ x y
      simp [kloosterman_modulus_one]
    · intro m n hm hn hmn hmBound hnBound _ x y
      let : NeZero m := ⟨(Nat.zero_lt_one.trans hm).ne'⟩
      let : NeZero n := ⟨(Nat.zero_lt_one.trans hn).ne'⟩
      rw [kloosterman_crt hmn, norm_mul]
      calc
        _ ≤ ((4 : ℝ) ^ m.primeFactors.card * (m : ℝ) ^ (3 / 4 : ℝ)) *
            ((4 : ℝ) ^ n.primeFactors.card * (n : ℝ) ^ (3 / 4 : ℝ)) :=
          mul_le_mul (hmBound _ _) (hnBound _ _) (norm_nonneg _) (by positivity)
        _ = _ := by
          rw [hmn.primeFactors_mul, Finset.card_union_of_disjoint hmn.disjoint_primeFactors,
            pow_add, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
          ac_rfl
  exact @bound c ‹NeZero c› a b

/-- Primes at least `4 ^ 8` each pay for a factor of four through the modulus. -/
theorem four_pow_primeFactors_card_le (c : ℕ) [NeZero c] :
    (4 : ℝ) ^ c.primeFactors.card ≤ (4 : ℝ) ^ (4 ^ 8 : ℕ) * (c : ℝ) ^ (1 / 8 : ℝ) := by
  let cutoff : ℕ := 4 ^ 8
  let small := c.primeFactors.filter fun p => p < cutoff
  let large := c.primeFactors.filter fun p => ¬ p < cutoff
  have hcard : small.card + large.card = c.primeFactors.card :=
    Finset.card_filter_add_card_filter_not (s := c.primeFactors) (fun p => p < cutoff)
  have hsmall : small.card ≤ cutoff := by
    have hsub : small ⊆ Finset.range cutoff := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hlargeDvd : (∏ p ∈ large, p) ∣ c :=
    (Finset.prod_dvd_prod_of_subset large c.primeFactors id
      (Finset.filter_subset (fun p => ¬ p < cutoff) c.primeFactors)).trans
        (Nat.prod_primeFactors_dvd c)
  have hpow : ((4 : ℕ) ^ large.card) ^ 8 ≤ c := by
    calc
      _ = cutoff ^ large.card := pow_right_comm (4 : ℕ) large.card 8
      _ = ∏ _p ∈ large, cutoff := (Finset.prod_const cutoff).symm
      _ ≤ ∏ p ∈ large, p :=
        Finset.prod_le_prod (fun p hp => le_of_not_gt (Finset.mem_filter.mp hp).2)
      _ ≤ c := Nat.le_of_dvd (NeZero.pos c) hlargeDvd
  have hlarge : (4 : ℝ) ^ large.card ≤ (c : ℝ) ^ (1 / 8 : ℝ) := by
    have hpow' : ((4 : ℝ) ^ large.card) ^ (8 : ℕ) ≤ (c : ℝ) := by exact_mod_cast hpow
    calc
      _ = (((4 : ℝ) ^ large.card) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_natCast ((4 : ℝ) ^ large.card) 8,
          ← Real.rpow_mul (by positivity : 0 ≤ (4 : ℝ) ^ large.card),
          show ((8 : ℕ) : ℝ) * (1 / 8 : ℝ) = 1 by norm_num, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow' (by norm_num)
  rw [← hcard, pow_add]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hsmall) hlarge
    (by positivity) (by positivity)

/-- The normalized norm is dominated by an explicit constant times `c ^ (-9 / 8)`. -/
theorem norm_kloosterman_div_sq_le {c : ℕ} [NeZero c]
    (a : ZMod c) (b : (ZMod c)ˣ) :
    ‖kloosterman a b‖ / (c : ℝ) ^ 2 ≤
      (4 : ℝ) ^ (4 ^ 8 : ℕ) * (c : ℝ) ^ (-(9 / 8) : ℝ) := by
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  calc
    _ ≤ ((4 : ℝ) ^ c.primeFactors.card * (c : ℝ) ^ (3 / 4 : ℝ)) / (c : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_kloosterman_le a b) (sq_nonneg _)
    _ ≤ (((4 : ℝ) ^ (4 ^ 8 : ℕ) * (c : ℝ) ^ (1 / 8 : ℝ)) *
        (c : ℝ) ^ (3 / 4 : ℝ)) / (c : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (four_pow_primeFactors_card_le c) (by positivity))
        (sq_nonneg _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hc, mul_div_assoc, ← Real.rpow_natCast (c : ℝ) 2,
        ← Real.rpow_sub hc,
        show (1 / 8 : ℝ) + 3 / 4 - ((2 : ℕ) : ℝ) = -(9 / 8) by norm_num]

/-- Absolute summability of the actual normalized weights on positive moduli `n + 1`. -/
theorem summable_norm_kloosterman_div_sq
    (a : ∀ n : ℕ, ZMod (n + 1)) (b : ∀ n : ℕ, (ZMod (n + 1))ˣ) :
    Summable (fun n : ℕ => ‖kloosterman (a n) (b n)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hp : Summable (fun c : ℕ => (c : ℝ) ^ (-(9 / 8) : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hpShift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8) : ℝ)) :=
    (summable_nat_add_iff (f := fun c : ℕ => (c : ℝ) ^ (-(9 / 8) : ℝ)) 1).2 hp
  exact Summable.of_nonneg_of_le
    (fun _ => div_nonneg (norm_nonneg _) (sq_nonneg _))
    (fun n => norm_kloosterman_div_sq_le (a n) (b n))
    (hpShift.mul_left ((4 : ℝ) ^ (4 ^ 8 : ℕ)))

end D5.S3.CharacterSums.KloostermanSummability
