/- GID: D5/S1/Recurrence/Algebraic/HannaA181080Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA181080Integrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer coefficients of Hanna's OEIS A181080 formal exponential. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#22222; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22605
The claim expands IntegralSeries with its literal quantifiers; proofs use the existing predicate.
Utility is none: all coefficient, divisibility and congruence statements are unbounded.
Direct frozen dependencies (declaration identities):
A: D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.integral_exp_of_dold
   GID: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality
   statement_id: ASSUMED-UNVERIFIED (not present in the available Lean report)
B: D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.logInput
   GID: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality
   statement_id: ASSUMED-UNVERIFIED (not present in the available Lean report)
C: D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.IntegralSeries
   GID: D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure
   statement_id: sha256:63e70f464749e368856bfaa91133b0adfeda478327572310319dbf6077b632cb
D: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst
   GID: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
   statement_id: sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795
E: D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff
   GID: D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators
   statement_id: sha256:8c1882146ae6e181a5d76db021c447d3d876e2310da5375697c52f0bb35ef4a1
F: D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform.coeff_one_add_pow
   GID: D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform
   statement_id: ASSUMED-UNVERIFIED (public declaration identity awaits the scoped report)
Declaration inventory: name | proof_shape | consumers | Direct frozen dependencies.
Every theorem below has escape_witness: none.
logarithm | definition | A, result | none
A | definition | claim, result | none
claim | definition (Prop-valued predicate, not a proof) | result | none
F80 | definition | cong80, result | none
cong80 | bind-only | result | E, D, F
result | bind-only | settling result | C, B, A, E, D, F
-/

import D5.S1.Recurrence.Algebraic.HannaA181070Integrality

open Finset PowerSeries
open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
open D5.S1.Recurrence.Algebraic.HannaA181070Integrality
namespace D5.S1.Recurrence.Algebraic.HannaA181080Integrality

open Finset PowerSeries

/-- The literal rational logarithm in the NAME of OEIS A181080.
At degree m, only 1 <= n <= m and 0 <= k <= m can contribute. -/
noncomputable def logarithm : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (n + 1),
        if 0 < n ∧ n + k = m then
          ((n.choose k : ℕ) : ℚ) ^ (n - k + 1) / (n : ℚ)
        else 0

/-- The source exponential, using the same Mathlib substitution and exp
as DoldExponentialIntegrality.integral_exp_of_dold. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.subst logarithm (PowerSeries.exp ℚ)

/-- The source integrality assertion, with IntegralSeries's quantifiers expanded. -/
def claim : Prop :=
  ∀ m : ℕ, ∃ z : ℤ, PowerSeries.coeff m A = (z : ℚ)

private def F80 (n k : ℕ) : ℕ := (n.choose k)^(n-k+1)

private theorem cong80 (p : ℕ) (hp : p.Prime) (n k : ℕ) :
    (p : ℤ)^(padicValNat p n+1) ∣ (F80 (p*n) (p*k) : ℤ)-F80 n k := by
  by_cases hk : k ≤ n
  · have hdiv : n ∣ (n-k)*n.choose k := by
      rw [Nat.sub_mul]
      exact Nat.dvd_sub (dvd_mul_right _ _) (binomDiv n k)
    have hc := (binomCong p n k hp).pow (p*(n-k)+1)
    have he := D5.S1.Recurrence.Algebraic.HannaA181070Integrality.variableExponent p n (n-k) (n.choose k) hp hdiv
    have h := Nat.modEq_iff_dvd.mp (hc.trans he).symm
    simpa only [F80, Nat.mul_sub_left_distrib, Nat.cast_pow] using h
  · have hpk : p*n < p*k := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hk) hp.pos
    simp only [F80, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk), Nat.choose_eq_zero_of_lt hpk,
      zero_pow (by omega : n-k+1 ≠ 0), zero_pow (by omega : p*n-p*k+1 ≠ 0), Nat.cast_zero, sub_self, dvd_zero]

theorem result : claim := by
  have hl : logarithm = D5.S1.Recurrence.Algebraic.HannaA181070Integrality.L F80 := by
    ext m
    simpa only [logarithm, coeff_mk, F80, Nat.cast_pow] using
      D5.S1.Recurrence.Algebraic.HannaA181070Integrality.literalBounded F80
        (fun n k h => by simp [F80, Nat.choose_eq_zero_of_lt h]) m
  unfold claim A
  rw [hl]
  exact D5.S1.Recurrence.Algebraic.HannaA181070Integrality.integralGeneric _
    (D5.S1.Recurrence.Algebraic.HannaA181070Integrality.divPower (fun n k => n.choose k) (fun n k => n-k)
      (fun n k _ => D5.S1.Recurrence.Algebraic.HannaA181070Integrality.binomDiv n k)) (fun p hp n k _ => cong80 p hp n k)

end D5.S1.Recurrence.Algebraic.HannaA181080Integrality
