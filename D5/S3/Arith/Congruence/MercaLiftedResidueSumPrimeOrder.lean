/- GID: D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic]
   utility: none
   digest: Merca's prime-modulus lifted residue sum follows from half-order pairing. -/

/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #9204)
   Direct frozen dependencies: none (pinned Mathlib only) -/

import Mathlib.FieldTheory.Finite.Basic

namespace D5.S3.Arith.Congruence.MercaLiftedResidueSumPrimeOrder

open scoped BigOperators

/-- `Σ_{i=1}^{ord_m(a)} ((2a^i + m) mod 2m)` with `mod` the least non-negative
remainder (page 2), the bracketing of (39), and `ord_m(a)` the paper's
multiplicative order (page 17), encoded by Mathlib's `orderOf (a : ZMod m)`. -/
noncomputable def liftedSum (m a : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 (orderOf (a : ZMod m)), (2 * a ^ i + m) % (2 * m)

/-- Conjecture 2 as printed. -/
def claim : Prop := ∀ a m : ℕ, 0 < a → m.Prime → Nat.Coprime a m →
  Even (orderOf (a : ZMod m)) → liftedSum m a = m * orderOf (a : ZMod m)

example : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by decide)]
  refine ⟨by decide, ?_⟩
  intro n hn hpos
  interval_cases n
  all_goals decide

example : liftedSum 7 3 = 42 := by
  have h : orderOf (3 : ZMod 7) = 6 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro n hn hpos
    interval_cases n
    all_goals decide
  unfold liftedSum
  have h3 : ((3 : ℕ) : ZMod 7) = (3 : ZMod 7) := by norm_num
  rw [h3, h]
  decide

example : orderOf (6 : ZMod 7) = 2 := by
  rw [orderOf_eq_iff (by decide)]
  refine ⟨by decide, ?_⟩
  intro n hn hpos
  interval_cases n
  all_goals decide

example : liftedSum 7 6 = 14 := by
  have h : orderOf (6 : ZMod 7) = 2 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro n hn hpos
    interval_cases n
    all_goals decide
  unfold liftedSum
  have h6 : ((6 : ℕ) : ZMod 7) = (6 : ZMod 7) := by norm_num
  rw [h6, h]
  decide

example : 0 < (3 : ℕ) ∧ Nat.Prime 7 ∧ Nat.Coprime 3 7 ∧
    Even (orderOf (3 : ZMod 7)) := by
  have h : orderOf (3 : ZMod 7) = 6 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro n hn hpos
    interval_cases n
    all_goals decide
  rw [h]
  decide

/-- Conjecture 2 holds. -/
theorem result : claim := by
  intro a m ha hp hcop heven
  let _ : Fact m.Prime := ⟨hp⟩
  have hfermat : a ^ (m - 1) % m = 1 % m :=
    Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have haZ : (a : ZMod m) ≠ 0 := by
    intro ha0
    have hma : m ∣ a := (ZMod.natCast_eq_zero_iff a m).1 ha0
    have hmgcd : m ∣ Nat.gcd a m := Nat.dvd_gcd hma (dvd_refl m)
    have hgcd : Nat.gcd a m = 1 := hcop
    have hm1 : m ∣ 1 := by simpa [hgcd] using hmgcd
    exact hp.not_dvd_one hm1
  have hordZ : (a : ZMod m) ^ orderOf (a : ZMod m) = 1 :=
    pow_orderOf_eq_one (a : ZMod m)
  have hord_pos : 0 < orderOf (a : ZMod m) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨m - 1, Nat.sub_pos_of_lt hp.one_lt, ?_⟩
    have hcast := (ZMod.natCast_eq_natCast_iff' (a ^ (m - 1)) 1 m).2 hfermat
    simpa only [Nat.cast_pow, Nat.cast_one] using hcast
  rcases heven with ⟨s, hs⟩
  have hspos : 0 < s := by omega
  have hmne2 : m ≠ 2 := by
    intro hm2
    have hpow_one : (a : ZMod m) ^ 1 = 1 := by
      have hcast := (ZMod.natCast_eq_natCast_iff' (a ^ 1) 1 m).2 (by
        simpa [hm2] using hfermat)
      simpa only [Nat.cast_pow, Nat.cast_one] using hcast
    have hord_le : orderOf (a : ZMod m) ≤ 1 :=
      orderOf_le_of_pow_eq_one (by decide) hpow_one
    have hord_one : orderOf (a : ZMod m) = 1 := by omega
    omega
  have hmodd : Odd m := hp.odd_of_ne_two hmne2
  have hhalf_sq : (a : ZMod m) ^ s * (a : ZMod m) ^ s = 1 := by
    rw [← pow_add, ← hs, hordZ]
  have hhalf_ne_one : (a : ZMod m) ^ s ≠ 1 :=
    pow_ne_one_of_lt_orderOf hspos.ne' (by omega)
  have hhalf_neg : (a : ZMod m) ^ s = -1 := by
    rcases (mul_self_eq_one_iff.mp hhalf_sq) with h | h
    · exact (hhalf_ne_one h).elim
    · exact h
  let term : ℕ → ℕ := fun i ↦ (2 * a ^ i + m) % (2 * m)
  have hterm_reduced : ∀ i : ℕ,
      term i = (2 * (a ^ i % m) + m) % (2 * m) := by
    intro i
    dsimp [term]
    calc
      (2 * a ^ i + m) % (2 * m) =
          ((2 * a ^ i) % (2 * m) + m % (2 * m)) % (2 * m) := Nat.add_mod _ _ _
      _ = (2 * (a ^ i % m) + m) % (2 * m) := by
        have hm_lt : m < 2 * m := by
          have hmpos := hp.pos
          omega
        rw [Nat.mul_mod_mul_left 2 (a ^ i) m, Nat.mod_eq_of_lt hm_lt]
  have hshift_rem : ∀ i : ℕ, a ^ (i + s) % m = m - a ^ i % m := by
    intro i
    let u := a ^ i % m
    have hum : u < m := Nat.mod_lt _ hp.pos
    have hu0 : 0 < u := by
      apply Nat.pos_of_ne_zero
      intro hu
      apply pow_ne_zero i haZ
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      apply Nat.dvd_of_mod_eq_zero
      simpa [u] using hu
    have hu_cast : (u : ZMod m) = (a : ZMod m) ^ i := by
      rw [← Nat.cast_pow]
      exact (ZMod.natCast_eq_natCast_iff' u (a ^ i) m).2 (by simp [u])
    have hcast : ((a ^ (i + s) : ℕ) : ZMod m) = ((m - u : ℕ) : ZMod m) := by
      calc
        ((a ^ (i + s) : ℕ) : ZMod m) = (a : ZMod m) ^ (i + s) := by simp
        _ = (a : ZMod m) ^ i * (a : ZMod m) ^ s := by rw [pow_add]
        _ = -(a : ZMod m) ^ i := by rw [hhalf_neg, mul_neg, mul_one]
        _ = -(u : ZMod m) := by rw [hu_cast]
        _ = ((m - u : ℕ) : ZMod m) := by
          rw [Nat.cast_sub hum.le, ZMod.natCast_self, zero_sub]
    have hrema := (ZMod.natCast_eq_natCast_iff' (a ^ (i + s)) (m - u) m).1 hcast
    have hmu_lt : m - u < m := by omega
    rw [Nat.mod_eq_of_lt hmu_lt] at hrema
    simpa [u] using hrema
  have hpair : ∀ i : ℕ, term i + term (i + s) = 2 * m := by
    intro i
    let u := a ^ i % m
    have hum : u < m := Nat.mod_lt _ hp.pos
    have hu0 : 0 < u := by
      apply Nat.pos_of_ne_zero
      intro hu
      apply pow_ne_zero i haZ
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero (by simpa [u] using hu)
    rw [hterm_reduced i, hterm_reduced (i + s), hshift_rem i]
    change (2 * u + m) % (2 * m) + (2 * (m - u) + m) % (2 * m) = 2 * m
    rcases hmodd with ⟨k, hk⟩
    by_cases hlt : 2 * u < m
    · rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_sub_mod (by omega)]
      have hsub : 2 * (m - u) + m - 2 * m = m - 2 * u := by omega
      rw [hsub, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hgt : m < 2 * u := by omega
      rw [Nat.mod_eq_sub_mod (by omega)]
      have hsub : 2 * u + m - 2 * m = 2 * u - m := by omega
      rw [hsub, Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  have hsum_range : liftedSum m a = ∑ j ∈ Finset.range (s + s), term (j + 1) := by
    rw [liftedSum, hs]
    change (∑ i ∈ Finset.Icc 1 (s + s), term i) = _
    have hset : Finset.Icc 1 (s + s) =
        (Finset.range (s + s)).image (fun j ↦ j + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hi
        refine ⟨i - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        omega
    calc
      (∑ i ∈ Finset.Icc 1 (s + s), term i) =
          ∑ i ∈ (Finset.range (s + s)).image (fun j ↦ j + 1), term i := by rw [hset]
      _ = ∑ j ∈ Finset.range (s + s), term (j + 1) :=
        Finset.sum_image (by
          intro x hx y hy hxy
          exact Nat.add_right_cancel hxy)
  rw [hsum_range, hs, Finset.sum_range_add]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x ∈ Finset.range s, (term (x + 1) + term (s + x + 1))) =
        ∑ x ∈ Finset.range s, 2 * m := by
          apply Finset.sum_congr rfl
          intro x hx
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpair (x + 1)
    _ = m * (s + s) := by
      simp
      ring

#print axioms result

end D5.S3.Arith.Congruence.MercaLiftedResidueSumPrimeOrder
