/- GID: D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/WuAdjacentFibonacciResidues
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Adjacent-index Fibonacci divisibility forces final digit zero, two or eight. -/
/-
claim: definition of the source's universal assertion; consumer: result.
result:
  proof_shape: bind-only; instantiate Fibonacci index divisibility at 3, 4 and 5,
    then use divisibility transitivity, residue cases and Presburger arithmetic.
  escape_witness: none
  admission_basis: open-problem-resolution (#21590; Proved)
  Direct frozen dependencies:
    D5/S1/Recurrence/GoldenFibDivisibility.fib_dvd_iff
    declaration statement_id:
    sha256:355076a74b13f4f9113502f4e965b7f78b429f8d2165d24eb8a4062a12392561
    (from the existing Lean report; the module pin is a different identity).
The claim retains the source's three divisibilities and uses the existing
Nat.fib owner; no new Fibonacci sequence or membership predicate is introduced.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21705
-/

import D5.S1.Recurrence.GoldenFibDivisibility

namespace D5.S3.Arith.Congruence.WuAdjacentFibonacciResidues

/-- OEIS A221018, revision 35, first FORMULA: "a(n) % 10 == 0, 2, or 8
(conjectured). - _Chai Wah Wu_, Aug 06 2026". The source's generator starts at
2. For k ≥ 2, natural subtraction k - 1 agrees with integer subtraction. -/
def claim : Prop :=
  ∀ (k : ℕ), 2 ≤ k →
    (k - 1) ∣ Nat.fib k →
    k ∣ Nat.fib k →
    (k + 1) ∣ Nat.fib k →
    k % 10 = 0 ∨ k % 10 = 2 ∨ k % 10 = 8

theorem result : claim := by
  intro k hk hprev hself hnext
  have rank_two :=
    D5.S1.Recurrence.GoldenFibDivisibility.fib_dvd_iff 3 k (by decide)
  have rank_three :=
    D5.S1.Recurrence.GoldenFibDivisibility.fib_dvd_iff 4 k (by decide)
  have rank_five :=
    D5.S1.Recurrence.GoldenFibDivisibility.fib_dvd_iff 5 k (by decide)
  norm_num [Nat.fib_add_two] at rank_two rank_three rank_five
  have htwo : 2 ∣ Nat.fib k := by
    by_cases heven : 2 ∣ k
    · exact heven.trans hself
    · have hnext_even : 2 ∣ k + 1 := by omega
      exact hnext_even.trans hnext
  have hthree_index : 3 ∣ k := rank_two.mp htwo
  have hthree_fib : 3 ∣ Nat.fib k := hthree_index.trans hself
  have hfour_index : 4 ∣ k := rank_three.mp hthree_fib
  have htwelve_index : 12 ∣ k := by omega
  have hnot_one : k % 5 ≠ 1 := by
    intro hres
    have hfive_prev : 5 ∣ k - 1 := by
      exact Nat.ModEq.dvd' (id (Eq.symm hres))
    have hfive_index : 5 ∣ k := rank_five.mp (hfive_prev.trans hprev)
    omega
  have hnot_four : k % 5 ≠ 4 := by
    intro hres
    have hfive_next : 5 ∣ k + 1 := by omega
    have hfive_index : 5 ∣ k := rank_five.mp (hfive_next.trans hnext)
    omega
  have heven_remainder : k % 2 = 0 := by omega
  have hdecimal_bound : k % 10 < 10 := Nat.mod_lt k (by decide)
  interval_cases hdecimal : k % 10 <;> omega

end D5.S3.Arith.Congruence.WuAdjacentFibonacciResidues
