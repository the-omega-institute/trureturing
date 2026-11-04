/- GID: D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Divisor-factorial tails prove Bala's A258899 and A258903 totient-period conjectures. -/

/-
# Divisor-factorial tails and totient periods

The source formulas use natural-number division and include the value 1 at
index zero. For every positive modulus m, all proper-factor terms vanish
from n >= 2*m+4, leaving u*v^n+v*u^n in ZMod m for arbitrary natural u,v.
The imported power-period theorem then supplies T = Nat.totient m for
both sequences. No least onset or least period is asserted.

admission_basis: open-problem-resolution (#24054; Proved).
escape_witness: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25641.

Declaration classifications (same-delivery helpers expanded):
- a258899, a258903, claim: definitions; no mathematical novelty asserted.
- proper_factorial_quotient_dvd: proof_shape: bind-only;
  consumer: divisor_sum_tail; escape_witness: none.
  Factorial divisibility and arithmetic normalization supply the conclusion.
  Direct frozen dependencies: none.
- divisor_sum_tail: proof_shape: bind-only;
  consumer: divisor_sum_period; escape_witness: none.
  Finset.sum_subset and the proper-factor divisibility remove all other terms.
  Direct frozen dependencies: none.
- divisor_sum_period: proof_shape: bind-only;
  consumer: result; escape_witness: none.
  Two tail rewrites and the imported power-period theorem supply the equality.
- result: proof_shape: bind-only; escape_witness: none.
  Specialize the weights and supply N=2*m+4, T=Nat.totient m.

Direct frozen dependencies of divisor_sum_period and result:
D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.pow_add_totient,
statement_id: sha256:cdbc1443c51a817b144732c799215e2cd246d0c9a631966518d2704c2c783e4d.
-/

import D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod

open Finset

namespace D5.S1.Recurrence.Periodic.BalaDivisorFactorialTotientPeriod

/-- OEIS A258899, offset zero, with the finite formula in its FORMULA field. -/
def a258899 (n : ℕ) : ℕ :=
  if n = 0 then 1 else
    ∑ d ∈ n.divisors, 2 ^ d * (n.factorial / (d.factorial * (n / d).factorial))

/-- OEIS A258903, offset zero, with the finite formula in its FORMULA field. -/
def a258903 (n : ℕ) : ℕ :=
  if n = 0 then 1 else
    ∑ d ∈ n.divisors,
      2 ^ d * 3 ^ (n / d) * (n.factorial / (d.factorial * (n / d).factorial))

/-- The two conjectures of Peter Bala, each with its own onset and positive period. -/
def claim : Prop :=
  (∀ m : ℕ, 0 < m →
    ∃ N : ℕ, ∃ T : ℕ, 0 < T ∧ T ∣ Nat.totient m ∧
      ∀ n : ℕ, N ≤ n → Nat.ModEq m (a258899 (n + T)) (a258899 n)) ∧
  (∀ m : ℕ, 0 < m →
    ∃ N : ℕ, ∃ T : ℕ, 0 < T ∧ T ∣ Nat.totient m ∧
      ∀ n : ℕ, N ≤ n → Nat.ModEq m (a258903 (n + T)) (a258903 n))



private theorem proper_factorial_quotient_dvd (m n d e : ℕ) (hm : 0 < m)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hde : n = d * e) (hn : 2 * m + 4 ≤ n) :
    m ∣ n.factorial / (d.factorial * e.factorial) := by
  have hbound : 2 * (d + e) ≤ n + 4 := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hd
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le he
    nlinarith [Nat.zero_le (a * b)]
  have hspace : d + e + m ≤ n := by omega
  have hsplit : d.factorial * e.factorial * m.factorial ∣ n.factorial := by
    exact ((Nat.mul_dvd_mul_right (Nat.factorial_mul_factorial_dvd_factorial_add d e) m.factorial).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add (d + e) m)).trans
      (Nat.factorial_dvd_factorial hspace)
  exact Nat.dvd_div_of_mul_dvd
    ((Nat.mul_dvd_mul_left (d.factorial * e.factorial) (Nat.dvd_factorial hm le_rfl)).trans hsplit)

private theorem divisor_sum_tail (u v m n : ℕ) (hm : 0 < m) (hn : 2 * m + 4 ≤ n) :
    ((∑ d ∈ n.divisors, u ^ d * v ^ (n / d) *
      (n.factorial / (d.factorial * (n / d).factorial)) : ℕ) : ZMod m) =
      (u : ZMod m) * (v : ZMod m) ^ n + (v : ZMod m) * (u : ZMod m) ^ n := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have hn1 : n ≠ 1 := by omega
  push_cast
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    rcases mem_insert.mp hd with rfl | hd
    · exact Nat.one_mem_divisors.mpr hn0
    · have : d = n := mem_singleton.mp hd
      subst d
      exact Nat.mem_divisors_self n hn0
  have hsum := Finset.sum_subset hsub (f := fun d : ℕ =>
    (u : ZMod m) ^ d * (v : ZMod m) ^ (n / d) *
      ((n.factorial / (d.factorial * (n / d).factorial) : ℕ) : ZMod m))
  have hzero : ∀ d ∈ n.divisors, d ∉ ({1, n} : Finset ℕ) →
      (u : ZMod m) ^ d * (v : ZMod m) ^ (n / d) *
        ((n.factorial / (d.factorial * (n / d).factorial) : ℕ) : ZMod m) = 0 := by
    intro d hd hnot
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hparts : d ≠ 1 ∧ d ≠ n := by simpa only [mem_insert, mem_singleton, not_or] using hnot
    have hd1 := hparts.1
    have hdn := hparts.2
    have hepos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
    have he1 : n / d ≠ 1 := by
      intro he
      have := Nat.mul_div_cancel' hdvd
      rw [he, mul_one] at this
      exact hdn this
    have hq : m ∣ n.factorial / (d.factorial * (n / d).factorial) :=
      proper_factorial_quotient_dvd m n d (n / d) hm (by omega) (by omega)
        (Nat.mul_div_cancel' hdvd).symm hn
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hq, mul_zero]
  rw [← hsum hzero]
  simp [Finset.sum_pair (Ne.symm hn1), Nat.div_self (Nat.pos_of_ne_zero hn0),
    Nat.div_self (Nat.factorial_pos n), mul_comm]

private theorem divisor_sum_period (u v m n : ℕ) (hm : 0 < m)
    (hn : 2 * m + 4 ≤ n) :
    ((∑ d ∈ (n + m.totient).divisors, u ^ d * v ^ ((n + m.totient) / d) *
      ((n + m.totient).factorial / (d.factorial * ((n + m.totient) / d).factorial)) : ℕ) : ZMod m) =
    ((∑ d ∈ n.divisors, u ^ d * v ^ (n / d) *
      (n.factorial / (d.factorial * (n / d).factorial)) : ℕ) : ZMod m) := by
  rw [divisor_sum_tail u v m (n + m.totient) hm (by omega), divisor_sum_tail u v m n hm hn]
  rw [D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod.pow_add_totient v m n hm (by omega),
    D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod.pow_add_totient u m n hm (by omega)]

theorem result : D5.S1.Recurrence.Periodic.BalaDivisorFactorialTotientPeriod.claim := by
  constructor
  · intro m hm
    refine ⟨2 * m + 4, m.totient, Nat.totient_pos.mpr hm, dvd_refl _, ?_⟩
    intro n hn
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [a258899, show n ≠ 0 by omega, show n + m.totient ≠ 0 by omega] using
      divisor_sum_period 2 1 m n hm hn
  · intro m hm
    refine ⟨2 * m + 4, m.totient, Nat.totient_pos.mpr hm, dvd_refl _, ?_⟩
    intro n hn
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [a258903, show n ≠ 0 by omega, show n + m.totient ≠ 0 by omega] using
      divisor_sum_period 2 3 m n hm hn

end D5.S1.Recurrence.Periodic.BalaDivisorFactorialTotientPeriod
