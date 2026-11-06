/- GID: D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's quadratic-exponent series has exact dyadic reduced denominators. -/

/-
result:
  proof_shape: content (strong induction computes the exact two-adic coefficient valuation).
  escape_witness: none; admission uses the external open-problem settlement.
  admission_basis: open-problem-resolution (#23621; Proved)
Direct frozen dependencies:
  D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_constant,
  D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_derivative,
  D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.localRat_iff_val_nonneg,
  D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_exp_of_log_difference,
  and its IsRIntegralRat, IsRIntegralPS and IsRIntegralRat.zero interface.
No module pin is used as a declaration identity.
The literal source definitions are retained; proofs use the original private Dwork interface
through Batteries.Tactic.OpenPrivate. The exponential is used directly without a new alias.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25189
Declaration | proof_shape | consumer(s)
logarithmInput | bind-only | IsSourceSeries, logarithmInput_zero, derivative_input_coeff, source_recurrence, source_coeff_pos, term_zero_val, term_pos_val, sum_term_val, source_coeff_val, local_coeff_nondiv, local_coeff_div, local_difference, source_local_integral, denominator_two_valuation, source_coeff_den, exists_source, coeff_zero_source, result
IsSourceSeries | bind-only | claim, exists_source, coeff_zero_source, coeff_zero_den_source
claim | bind-only | result
logarithmInput_zero | bind-only | source_recurrence, source_coeff_pos, term_zero_val, source_coeff_val, source_local_integral, coeff_zero_source
derivative_input_coeff | bind-only | source_recurrence
source_recurrence | bind-only | source_coeff_pos, source_coeff_val
source_coeff_pos | content | term_pos_val, sum_term_val, source_coeff_val
term_zero_val | bind-only | sum_term_val, source_coeff_val
term_pos_val | bind-only | sum_term_val
term_val_strict | bind-only | sum_term_val
sum_term_val | bind-only | source_coeff_val
source_coeff_val | content | denominator_two_valuation
odd_prime_not_dvd_two | bind-only | pow_diff_dvd, local_coeff_nondiv, local_coeff_div, source_coeff_den
exponent_congruence | bind-only | pow_diff_dvd
pow_diff_dvd | bind-only | local_coeff_div
local_coeff_nondiv | bind-only | local_difference
local_coeff_div | bind-only | local_difference
local_difference | bind-only | source_local_integral
source_local_integral | bind-only | source_coeff_den
denominator_two_valuation | content | source_coeff_den
source_coeff_den | content | result
exists_source | bind-only | result
coeff_zero_source | bind-only | coeff_zero_den_source, result
coeff_zero_den_source | bind-only | result
result | content | settling result
Every row has escape_witness: none. The coefficient-positivity and valuation inductions
are the content steps; the denominator conclusions include the valuation induction.
The valuation-of-a-sum step applies Valuation.map_sum_eq_of_lt. Arithmetic, LTE and
Dwork adapters are bind-only and are retained only with the displayed consumers.

-/

import Mathlib.NumberTheory.Padics.PadicNumbers
import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import Mathlib.NumberTheory.Multiplicity

namespace D5.S1.Recurrence.Algebraic.HannaQuadraticExponentialDyadicDenominator

open PowerSeries

open private expSeries_constant expSeries_derivative from
  D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

/-- The sum over m ≥ 1 in OEIS A174491, with zero constant coefficient. -/
noncomputable def logarithmInput : PowerSeries ℚ :=
  PowerSeries.mk fun m : ℕ =>
    if m = 0 then 0 else 1 / ((m : ℚ) * (2 : ℚ) ^ (m ^ 2))

/-- The ((PowerSeries.exp ℚ).subst logarithmInput) equation F(x) = exp(Sum_{m≥1} x^m/(m*2^(m^2))). -/
def IsSourceSeries (F : PowerSeries ℚ) : Prop :=
  F = (PowerSeries.exp ℚ).subst logarithmInput

/-- OEIS A174491, %F conjecture, with its n = 0 term stated separately. -/
def claim : Prop :=
  (∃ F : PowerSeries ℚ, IsSourceSeries F) ∧
    ∀ F : PowerSeries ℚ, IsSourceSeries F →
      PowerSeries.coeff 0 F = 1 ∧
      (PowerSeries.coeff 0 F).den = 1 ∧
      ∀ n : ℕ, 1 ≤ n →
        (PowerSeries.coeff n F).den = 2 ^ (n ^ 2 + padicValNat 2 n)



private lemma logarithmInput_zero : constantCoeff logarithmInput = 0 := by
  exact Eq.symm (Rat.ext rfl rfl)
private lemma derivative_input_coeff (m : ℕ) : coeff m (PowerSeries.derivative logarithmInput) =
    ((2 : ℚ) ^ ((m + 1) ^ 2))⁻¹ := by
  rw [coeff_derivative, logarithmInput, coeff_mk]
  simp
  field_simp
private lemma source_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) * coeff n ((PowerSeries.exp ℚ).subst logarithmInput) =
      ∑ j ∈ Finset.range n, coeff j ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ ((n - j) ^ 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := congrArg (coeff k) (expSeries_derivative logarithmInput_zero)
  rw [coeff_derivative, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i ((PowerSeries.exp ℚ).subst logarithmInput) * coeff j (PowerSeries.derivative logarithmInput)) (k)] at h
  simp_rw [derivative_input_coeff] at h
  calc
    (k.succ : ℚ) * coeff k.succ ((PowerSeries.exp ℚ).subst logarithmInput) =
        ∑ j ∈ Finset.range k.succ, coeff j ((PowerSeries.exp ℚ).subst logarithmInput) * ((2 : ℚ) ^ ((k - j + 1) ^ 2))⁻¹ := by
          simpa [Nat.cast_add, Nat.cast_one, add_comm, mul_comm] using h
    _ = ∑ j ∈ Finset.range k.succ, coeff j ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ ((k.succ - j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hkj : j ≤ k := by exact Finset.mem_range_succ_iff.mp hj
      rw [show k.succ - j = k - j + 1 by omega]
      simp [div_eq_mul_inv]

private lemma source_coeff_pos : ∀ n : ℕ, 0 < coeff n ((PowerSeries.exp ℚ).subst logarithmInput) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff, expSeries_constant logarithmInput_zero]
    | succ n =>
      have hr := source_recurrence (n + 1) (by omega)
      have hterm : ∀ j ∈ Finset.range (n + 1),
          0 < coeff j ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ ((n + 1 - j) ^ 2) := by
        intro j hj
        have hjlt : j < n + 1 := Finset.mem_range.mp hj
        have hc : 0 < coeff j ((PowerSeries.exp ℚ).subst logarithmInput) := by
          exact Submonoid.mem_pos.mp (ih j hjlt)
        apply div_pos hc
        exact pow_pos (by norm_num) _
      have hs : 0 < ∑ j ∈ Finset.range (n + 1),
          coeff j ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ ((n + 1 - j) ^ 2) := by
        apply Finset.sum_pos hterm
        simp
      nlinarith [hr]

private lemma term_zero_val (N : ℕ) :
    padicValRat 2 (coeff 0 ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ (N ^ 2)) = -(N : ℤ) ^ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [coeff_zero_eq_constantCoeff, expSeries_constant logarithmInput_zero,
    padicValRat.div (by norm_num) (by positivity), padicValRat.one, padicValRat.pow]
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [htwo]
  push_cast
  ring

private lemma term_pos_val (N j : ℕ) (hjn : j < N)
    (hval : padicValRat 2 (coeff j ((PowerSeries.exp ℚ).subst logarithmInput)) = -(j : ℤ) ^ 2 - padicValNat 2 j) :
    padicValRat 2 (coeff j ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ ((N - j) ^ 2)) =
      -(j : ℤ) ^ 2 - padicValNat 2 j - (N - j : ℤ) ^ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : coeff j ((PowerSeries.exp ℚ).subst logarithmInput) ≠ 0 := ne_of_gt (source_coeff_pos j)
  rw [padicValRat.div hc (by positivity), hval, padicValRat.pow]
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [htwo]
  have hsub : ((N - j : ℕ) : ℤ) = (N : ℤ) - (j : ℤ) := by
    exact_mod_cast Nat.cast_sub (Nat.le_of_lt hjn)
  rw [Nat.cast_pow, hsub]
  push_cast
  ring

private lemma term_val_strict (N j : ℕ) (hj : 0 < j) (hjn : j < N) :
    -(N : ℤ) ^ 2 < -(j : ℤ) ^ 2 - (padicValNat 2 j : ℤ) - (N - j : ℤ) ^ 2 := by
  have hvj : padicValNat 2 j ≤ j := Nat.padicValNat_le_self j
  have hnm : 1 ≤ N - j := Nat.le_sub_of_add_le' hjn
  have hmul : 2 * j ≤ 2 * j * (N - j) := by
    exact Nat.le_mul_of_pos_right (2 * j) hnm
  have hvlt : padicValNat 2 j < 2 * j * (N - j) := by omega
  have hsub : ((N - j : ℕ) : ℤ) = (N : ℤ) - (j : ℤ) := by
    exact_mod_cast Nat.cast_sub (Nat.le_of_lt hjn)
  have hvltZ : (padicValNat 2 j : ℤ) <
      2 * (j : ℤ) * ((N - j : ℕ) : ℤ) := by
    exact Int.lt_toNat.mp hvlt
  rw [hsub] at hvltZ
  nlinarith

private lemma sum_term_val (N : ℕ) (hN : 2 ≤ N)
    (hval : ∀ j : ℕ, j < N →
      padicValRat 2 (coeff j ((PowerSeries.exp ℚ).subst logarithmInput)) = -(j : ℤ) ^ 2 - padicValNat 2 j) :
    padicValRat 2
      (∑ j ∈ Finset.range N, coeff j ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ ((N - j) ^ 2)) =
      -(N : ℤ) ^ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : ℕ → ℚ := fun j => coeff j ((PowerSeries.exp ℚ).subst logarithmInput) /
    (2 : ℚ) ^ ((N - j) ^ 2)
  have hTpos (j : ℕ) : 0 < T j := by
    exact div_pos (source_coeff_pos j) (pow_pos (by norm_num) _)
  have hsumpos : 0 < ∑ j ∈ Finset.range N, T j := by
    exact Finset.sum_pos (fun j _ => hTpos j) (by simp; omega)
  have hzero : padicValRat 2 (T 0) = -(N : ℤ) ^ 2 := by
    simpa [T] using term_zero_val N
  have hv := (Rat.padicValuation 2).map_sum_eq_of_lt
    (s := Finset.range N) (f := T) (j := 0) (by simp; omega) (by
      intro j hj
      have hjn : j < N := (Finset.mem_sdiff.mp hj).1 |> Finset.mem_range.mp
      have hj0 : 0 < j := Nat.pos_of_ne_zero (by simpa using (Finset.mem_sdiff.mp hj).2)
      have hterm := term_pos_val N j hjn (hval j hjn)
      have hstrict : padicValRat 2 (T 0) < padicValRat 2 (T j) := by
        rw [hzero]
        change -(N : ℤ) ^ 2 < padicValRat 2
          (coeff j ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ ((N - j) ^ 2))
        rw [hterm]
        exact term_val_strict N j hj0 hjn
      simpa [Rat.padicValuation, ne_of_gt (hTpos j), ne_of_gt (hTpos 0)]
        using hstrict)
  have heq : padicValRat 2 (∑ j ∈ Finset.range N, T j) = padicValRat 2 (T 0) := by
    simpa [Rat.padicValuation, ne_of_gt hsumpos, ne_of_gt (hTpos 0)] using hv
  exact heq.trans hzero

private lemma source_coeff_val : ∀ n : ℕ,
    padicValRat 2 (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)) = -(n : ℤ) ^ 2 - padicValNat 2 n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [coeff_zero_eq_constantCoeff, expSeries_constant logarithmInput_zero]
          norm_num
      | succ n =>
          by_cases hn0 : n = 0
          · subst n
            have hr := source_recurrence 1 (by omega)
            have hr' : coeff 1 ((PowerSeries.exp ℚ).subst logarithmInput) = coeff 0 ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ (1 ^ 2) := by
              simpa using hr
            calc
              padicValRat 2 (coeff 1 ((PowerSeries.exp ℚ).subst logarithmInput)) =
                  padicValRat 2 (coeff 0 ((PowerSeries.exp ℚ).subst logarithmInput) / (2 : ℚ) ^ (1 ^ 2)) := by rw [hr']
              _ = -(1 : ℤ) ^ 2 := term_zero_val 1
              _ = -(1 : ℤ) ^ 2 - (padicValNat 2 1 : ℤ) := by norm_num
          · let N := n + 1
            have hN : 2 ≤ N := by dsimp [N]; omega
            have hsum := sum_term_val N hN (fun j hj => ih j hj)
            have hrec := source_recurrence N (by omega)
            have hcoeff_ne : coeff N ((PowerSeries.exp ℚ).subst logarithmInput) ≠ 0 := ne_of_gt (source_coeff_pos N)
            have hN_ne : (N : ℚ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
            have hmul := padicValRat.mul (p := 2) hN_ne hcoeff_ne
            have hleft : padicValRat 2 ((N : ℚ) * coeff N ((PowerSeries.exp ℚ).subst logarithmInput)) =
                padicValNat 2 N + padicValRat 2 (coeff N ((PowerSeries.exp ℚ).subst logarithmInput)) := by
              rw [hmul, padicValRat.of_nat]
            have hright : padicValRat 2 ((N : ℚ) * coeff N ((PowerSeries.exp ℚ).subst logarithmInput)) = -(N : ℤ) ^ 2 := by
              rw [hrec]
              exact hsum
            rw [hleft] at hright
            linarith

open private IsRIntegralRat IsRIntegralRat.zero IsRIntegralPS localRat_iff_val_nonneg
  local_exp_of_log_difference from D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

private lemma odd_prime_not_dvd_two (p : ℕ) (hp : p.Prime) (hodd : Odd p) : ¬ p ∣ 2 := by
  exact hp.coprime_iff_not_dvd.mp hodd.coprime_two_right

private lemma exponent_congruence (p : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ (2 : ℤ) ^ (p ^ 2) - 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  rw [show p ^ 2 = p * p by ring, pow_mul, ZMod.pow_card, ZMod.pow_card, sub_self]

private lemma pow_diff_dvd (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (hk : k ≠ 0) :
    p ^ padicValNat p (p * k) ∣ 2 ^ ((p * k) ^ 2) - 2 ^ (k ^ 2) := by
  let : Fact p.Prime := ⟨hp⟩
  have hyx : 2 < 2 ^ (p ^ 2) := by
    have he : 1 < p ^ 2 := by nlinarith [hp.two_le]
    exact Nat.pow_lt_pow_right (by omega : 1 < 2) he
  have hxy : p ∣ 2 ^ (p ^ 2) - 2 := by
    have he := exponent_congruence p hp
    have hcast : ((2 ^ (p ^ 2) - 2 : ℕ) : ℤ) = (2 : ℤ) ^ (p ^ 2) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ (p ^ 2))]
      norm_cast
    rw [← hcast] at he
    exact_mod_cast he
  have hx : ¬ p ∣ 2 ^ (p ^ 2) := fun h =>
    odd_prime_not_dvd_two p hp hodd (hp.dvd_of_dvd_pow h)
  have hv := padicValNat.pow_sub_pow (p := p) (x := 2 ^ (p ^ 2)) (y := 2)
    hodd hyx hxy hx (show k ^ 2 ≠ 0 by positivity)
  have hbase : 1 ≤ padicValNat p (2 ^ (p ^ 2) - 2) := by
    apply (padicValNat_dvd_iff_le (by omega : 2 ^ (p ^ 2) - 2 ≠ 0)).mp
    simpa using hxy
  have hpow : 2 ^ ((p * k) ^ 2) - 2 ^ (k ^ 2) =
      (2 ^ (p ^ 2)) ^ (k ^ 2) - 2 ^ (k ^ 2) := by
    rw [show (p * k) ^ 2 = p ^ 2 * k ^ 2 by ring, pow_mul]
  have hvaln : padicValNat p (p * k) = 1 + padicValNat p k := by
    rw [padicValNat.mul hp.ne_zero hk, padicValNat.self hp.one_lt]
  have hdiffne : (2 ^ (p ^ 2)) ^ (k ^ 2) - 2 ^ (k ^ 2) ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hyx (by positivity : k ^ 2 ≠ 0))
  rw [hpow]
  apply (padicValNat_dvd_iff_le hdiffne).mpr
  rw [hv, hvaln, padicValNat.pow]
  omega

private lemma local_coeff_nondiv (p n : ℕ) (hp : p.Prime) (hodd : Odd p) (hpn : ¬ p ∣ n) :
    IsRIntegralRat p (coeff n logarithmInput) := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : n ≠ 0 := by intro h; subst n; simp at hpn
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    change padicValRat p ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (odd_prime_not_dvd_two p hp hodd)]
    rfl
  apply (localRat_iff_val_nonneg p hp _).mpr
  simp only [logarithmInput, coeff_mk, ite_eq_right hn]
  rw [padicValRat.div (by norm_num) (mul_ne_zero hnQ (by positivity)), padicValRat.one,
    padicValRat.mul hnQ (by positivity), padicValRat.of_nat, padicValRat.pow,
    padicValNat.eq_zero_of_not_dvd hpn, htwo]
  norm_num

private lemma local_coeff_div (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (hk : k ≠ 0) :
    IsRIntegralRat p
      (coeff (p * k) logarithmInput - (p : ℚ)⁻¹ * coeff k logarithmInput) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hpk : p * k ≠ 0 := mul_ne_zero hp.ne_zero hk
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    change padicValRat p ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (odd_prime_not_dvd_two p hp hodd)]
    rfl
  have hq : coeff (p * k) logarithmInput - (p : ℚ)⁻¹ * coeff k logarithmInput =
      (((2 : ℤ) ^ (k ^ 2) - (2 : ℤ) ^ ((p * k) ^ 2) : ℤ) : ℚ) /
        (((p * k : ℕ) : ℚ) * (2 : ℚ) ^ ((p * k) ^ 2 + k ^ 2)) := by
    simp only [logarithmInput, coeff_mk, ite_eq_right hpk, ite_eq_right hk, Int.cast_sub,
      Int.cast_pow, Int.cast_ofNat, Nat.cast_mul, pow_add]
    field_simp
  rw [hq]
  apply (localRat_iff_val_nonneg p hp _).mpr
  have hklt : k < p * k := by nlinarith [hp.two_le, Nat.pos_of_ne_zero hk]
  have hexp : k ^ 2 < (p * k) ^ 2 := by nlinarith
  have hpow_lt : (2 : ℕ) ^ (k ^ 2) < 2 ^ ((p * k) ^ 2) :=
    Nat.pow_lt_pow_right (by omega : 1 < 2) hexp
  have hcast : ((2 ^ ((p * k) ^ 2) - 2 ^ (k ^ 2) : ℕ) : ℤ) =
      (2 : ℤ) ^ ((p * k) ^ 2) - (2 : ℤ) ^ (k ^ 2) := by
    rw [Nat.cast_sub (Nat.le_of_lt hpow_lt)]
    norm_cast
  have hdvdZ : (p : ℤ) ^ padicValNat p (p * k) ∣
      (2 : ℤ) ^ ((p * k) ^ 2) - (2 : ℤ) ^ (k ^ 2) := by
    rw [← hcast]
    exact_mod_cast pow_diff_dvd p k hp hodd hk
  have hnum : (2 : ℤ) ^ (k ^ 2) - (2 : ℤ) ^ ((p * k) ^ 2) ≠ 0 := by
    have hpos : 0 < (2 : ℤ) ^ ((p * k) ^ 2) - (2 : ℤ) ^ (k ^ 2) := by
      rw [← hcast]
      exact_mod_cast Nat.sub_pos_of_lt hpow_lt
    omega
  have hdiv : (p : ℤ) ^ padicValNat p (p * k) ∣
      (2 : ℤ) ^ (k ^ 2) - (2 : ℤ) ^ ((p * k) ^ 2) := by
    simpa only [neg_sub] using dvd_neg.mpr hdvdZ
  have hvN := ((padicValInt_dvd_iff _ _).mp hdiv).resolve_left hnum
  rw [padicValRat.div (by exact_mod_cast hnum) (by positivity), padicValRat.of_int,
    padicValRat.mul (by exact_mod_cast hpk) (by positivity), padicValRat.of_nat,
    padicValRat.pow, htwo]
  simp only [mul_zero, add_zero]
  omega

private lemma local_difference (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    IsRIntegralPS p
      (logarithmInput - C ((p : ℚ)⁻¹) * logarithmInput.subst ((X : PowerSeries ℚ) ^ p)) := by
  intro n
  rw [map_sub, coeff_C_mul, coeff_subst_X_pow hp.ne_zero]
  simp only [Algebra.algebraMap_self_apply]
  by_cases hn : n = 0
  · subst n
    simpa [logarithmInput] using IsRIntegralRat.zero p
  by_cases hpn : p ∣ n
  · rw [ite_eq_left hpn]
    have hk : n / p ≠ 0 := Nat.ne_of_gt
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos)
    have h := local_coeff_div p (n / p) hp hodd hk
    simpa only [Nat.mul_div_cancel' hpn] using h
  · rw [ite_eq_right hpn, mul_zero, sub_zero]
    exact local_coeff_nondiv p n hp hodd hpn

private lemma source_local_integral (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ∀ n : ℕ, (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).den.Coprime p := by
  exact local_exp_of_log_difference p hp logarithmInput logarithmInput_zero
    (local_difference p hp hodd)

private lemma denominator_two_valuation (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).den = n ^ 2 + padicValNat 2 n := by
  have hv := source_coeff_val n
  have hsplit := (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).num_or_den_zero_padicVal Nat.prime_two
  rw [padicValRat_def] at hv
  have hnZ : (1 : ℤ) ≤ n := Int.toNat_le.mp hn
  rcases hsplit with hnum | hden
  · rw [hnum] at hv
    have he : (padicValNat 2 (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).den : ℤ) =
        ((n ^ 2 + padicValNat 2 n : ℕ) : ℤ) := by
      calc
        _ = -(0 - (padicValNat 2 (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).den : ℤ)) := by ring
        _ = - (-(n : ℤ) ^ 2 - (padicValNat 2 n : ℤ)) := by
          simpa only [Nat.cast_zero] using congrArg Neg.neg hv
        _ = _ := by simp only [Nat.cast_add, Nat.cast_pow]; ring
    exact Int.ofNat.inj he
  · rw [hden] at hv
    have hv' : (padicValInt 2 (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).num : ℤ) =
        -(n : ℤ) ^ 2 - (padicValNat 2 n : ℤ) := by
      exact Int.neg_inj.mp (congrArg Neg.neg hv)
    have hnonneg : (0 : ℤ) ≤ padicValInt 2 (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).num :=
      Int.natCast_nonneg (padicValInt 2 (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).num)
    have hvn : (0 : ℤ) ≤ padicValNat 2 n := Int.natCast_nonneg (padicValNat 2 n)
    have hsq : (0 : ℤ) < (n : ℤ) ^ 2 := pow_pos (by omega) 2
    have hright : -(n : ℤ) ^ 2 - (padicValNat 2 n : ℤ) < 0 :=
      sub_neg.mpr (lt_of_lt_of_le (neg_lt_zero.mpr hsq) hvn)
    exact False.elim ((not_lt_of_ge hnonneg) (hv'.trans_lt hright))

private lemma source_coeff_den (n : ℕ) (hn : 1 ≤ n) :
    (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).den = 2 ^ (n ^ 2 + padicValNat 2 n) := by
  apply (Nat.eq_iff_prime_padicValNat_eq _ _ (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).den_nz (by positivity)).mpr
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    rw [denominator_two_valuation n hn, padicValNat.prime_pow]
  · have hodd : Odd p := hp.odd_of_ne_two hp2
    have hcop := source_local_integral p hp hodd n
    have hnot : ¬ p ∣ (coeff n ((PowerSeries.exp ℚ).subst logarithmInput)).den :=
      hp.coprime_iff_not_dvd.mp hcop.symm
    have hnot2 : ¬ p ∣ 2 := odd_prime_not_dvd_two p hp hodd
    rw [padicValNat.eq_zero_of_not_dvd hnot, padicValNat.pow,
      padicValNat.eq_zero_of_not_dvd hnot2, mul_zero]

private lemma exists_source : ∃ F : PowerSeries ℚ, IsSourceSeries F := by
  exact ⟨(PowerSeries.exp ℚ).subst logarithmInput, rfl⟩

private lemma coeff_zero_source (F : PowerSeries ℚ) (hF : IsSourceSeries F) : coeff 0 F = 1 := by
  change F = ((PowerSeries.exp ℚ).subst logarithmInput) at hF
  rw [hF, coeff_zero_eq_constantCoeff, expSeries_constant logarithmInput_zero]

private lemma coeff_zero_den_source (F : PowerSeries ℚ) (hF : IsSourceSeries F) :
    (coeff 0 F).den = 1 := by
  rw [coeff_zero_source F hF]
  norm_num

theorem result : D5.S1.Recurrence.Algebraic.HannaQuadraticExponentialDyadicDenominator.claim := by
  refine ⟨exists_source, ?_⟩
  intro F hF
  refine ⟨coeff_zero_source F hF, coeff_zero_den_source F hF, ?_⟩
  intro n hn
  change F = ((PowerSeries.exp ℚ).subst logarithmInput) at hF
  rw [hF]
  exact source_coeff_den n hn


end D5.S1.Recurrence.Algebraic.HannaQuadraticExponentialDyadicDenominator
