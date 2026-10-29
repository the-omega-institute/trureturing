/- GID: D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's Thue/Roth weighted formal exponential has integer coefficients. -/

/-
proof_shape: bind-only (b, c, IsSourceSeries, claim, b_mul_prime,
c_dold_three, c_dold_away_three, c_dold, result).
escape_witness: none.
admission_basis: open-problem-resolution (#23128; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23176
Direct frozen dependencies (same-module helpers expanded):
b, c, b_mul_prime, c_dold_three, c_dold_away_three, c_dold: none.
IsSourceSeries, claim: D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.logInput.
result: D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.logInput,
D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.integral_exp_of_dold.
The condition c_dold uses Dold from that module in its statement.
Declaration consumers:
b -> c, b_mul_prime, c_dold_three, c_dold_away_three;
c -> IsSourceSeries, c_dold_three, c_dold_away_three, c_dold, result;
IsSourceSeries -> claim, result; claim -> result;
b_mul_prime -> c_dold_away_three;
c_dold_three -> c_dold; c_dold_away_three -> c_dold; c_dold -> result.
The source is OEIS A174470, with the A014578 valuation formula for its bits.
The logarithmic input reuses logInput; no second input or integrality predicate is defined.
The prime-three case uses the valuation bound; the other cases use Euler's theorem.
The result has no hypotheses and includes the constant coefficient.
-/

import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.HannaThueRothExponentialIntegrality

open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

/-- A014578 has value zero at zero and records even three-adic valuation elsewhere. -/
def b (n : ℕ) : ℤ :=
  if n = 0 then 0 else if padicValNat 3 n % 2 = 0 then 1 else 0

/-- The integer logarithmic weights in A174470. -/
def c (n : ℕ) : ℤ := b n * (3 : ℤ) ^ n

/-- The rational formal exponential specified by A174470. -/
noncomputable def IsSourceSeries (A : PowerSeries ℚ) : Prop :=
  A = PowerSeries.subst
    (D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.logInput c)
    (PowerSeries.exp ℚ)

/-- The specified series exists and every ordinary coefficient is an integer. -/
def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsSourceSeries A) ∧
    ∀ A : PowerSeries ℚ, IsSourceSeries A →
      ∀ N : ℕ, ∃ z : ℤ, PowerSeries.coeff N A = (z : ℚ)

private theorem b_mul_prime (p m : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (hm : m ≠ 0) : b (p * m) = b m := by
  have h3p : ¬ 3 ∣ p := by
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  have hv : padicValNat 3 (p * m) = padicValNat 3 m := by
    rw [padicValNat.mul hp.ne_zero hm, padicValNat.eq_zero_of_not_dvd h3p, zero_add]
  simp only [b, ite_eq_right (mul_ne_zero hp.ne_zero hm), ite_eq_right hm, hv]

private theorem c_dold_three (m : ℕ) (hm : m ≠ 0) :
    (3 : ℤ) ^ (padicValNat 3 m + 1) ∣ c (3 * m) - c m := by
  have hbound : padicValNat 3 m + 1 ≤ m := Nat.succ_le_of_lt (Nat.padicValNat_lt_self hm)
  have hbig : padicValNat 3 m + 1 ≤ 3 * m := hbound.trans (by omega)
  apply dvd_sub
  · exact dvd_mul_of_dvd_right (pow_dvd_pow (3 : ℤ) hbig) (b (3 * m))
  · exact dvd_mul_of_dvd_right (pow_dvd_pow (3 : ℤ) hbound) (b m)

private theorem c_dold_away_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (m : ℕ) (hm : m ≠ 0) :
    (p : ℤ) ^ (padicValNat p m + 1) ∣ c (p * m) - c m := by
  have hcop : Nat.Coprime 3 p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    exact hp3 (((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hp.ne_one)
  obtain ⟨u, hu⟩ := (pow_padicValNat_dvd : p ^ padicValNat p m ∣ m)
  have heuler := (Nat.ModEq.pow_totient (hcop.pow_right (padicValNat p m + 1))).pow u
  rw [Nat.totient_prime_pow_succ hp, ← pow_mul, one_pow] at heuler
  have hexp : p ^ padicValNat p m * (p - 1) * u = (p - 1) * m := by
    calc
      p ^ padicValNat p m * (p - 1) * u = (p - 1) * (p ^ padicValNat p m * u) := by ring
      _ = (p - 1) * m := congrArg (fun t => (p - 1) * t) hu.symm
  rw [hexp] at heuler
  have hd : (p : ℤ) ^ (padicValNat p m + 1) ∣ (3 : ℤ) ^ ((p - 1) * m) - 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using heuler.symm.dvd
  have he : c (p * m) - c m = b m * (3 : ℤ) ^ m * ((3 : ℤ) ^ ((p - 1) * m) - 1) := by
    have hpm : p * m = m + (p - 1) * m := by
      calc
        p * m = ((p - 1) + 1) * m := by rw [Nat.sub_add_cancel hp.one_le]
        _ = m + (p - 1) * m := by ring
    rw [c, c, b_mul_prime p m hp hp3 hm, hpm, pow_add]
    ring
  rw [he]
  exact dvd_mul_of_dvd_right hd _

private theorem c_dold : Dold c := by
  intro p hp m hm
  by_cases hp3 : p = 3
  · subst p
    exact c_dold_three m hm
  · exact c_dold_away_three p hp hp3 m hm

theorem result : claim := by
  constructor
  · exact ⟨_, rfl⟩
  · intro A hA N
    change A = _ at hA
    rw [hA]
    exact integral_exp_of_dold c c_dold N

end D5.S1.Recurrence.Algebraic.HannaThueRothExponentialIntegrality
