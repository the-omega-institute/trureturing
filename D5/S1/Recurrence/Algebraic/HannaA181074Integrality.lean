/- GID: D5/S1/Recurrence/Algebraic/HannaA181074Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA181074Integrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer coefficients of Hanna's OEIS A181074 formal exponential. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#22221; Proved)
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
Declaration inventory: name | proof_shape | consumers | Direct frozen dependencies.
Every theorem below has escape_witness: none.
logarithm | definition | A, result | none
A | definition | claim, result | none
claim | definition (Prop-valued predicate, not a proof) | result | none
negbinomCoeff | bind-only | negbinomDiv, negbinomCong | none
negbinomDiv | bind-only | cong74, result | none
negbinomCong | bind-only | cong74 | E, D
F74 | definition | cong74, result | none
cong74 | bind-only | result | E, D
result | bind-only | settling result | C, B, A, E, D
-/

import D5.S1.Recurrence.Algebraic.HannaA181070Integrality

open Finset PowerSeries
open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
namespace D5.S1.Recurrence.Algebraic.HannaA181074Integrality

open Finset PowerSeries

/-- The literal rational logarithm in the NAME of OEIS A181074.
At degree m, only 1 <= n <= m and 0 <= k <= m can contribute. -/
noncomputable def logarithm : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (m + 1),
        if 0 < n ∧ n + k = m then
          (((n + k - 1).choose k : ℕ) : ℚ) ^ (k + 1) / (n : ℚ)
        else 0

/-- The source exponential, using the same Mathlib substitution and exp
as DoldExponentialIntegrality.integral_exp_of_dold. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.subst logarithm (PowerSeries.exp ℚ)

/-- The source integrality assertion, with IntegralSeries's quantifiers expanded. -/
def claim : Prop :=
  ∀ m : ℕ, ∃ z : ℤ, PowerSeries.coeff m A = (z : ℚ)

private theorem negbinomCoeff (n k : ℕ) (hn : n ≠ 0) :
    coeff k ((PowerSeries.mk fun _ => (1 : ℤ))^n) = ((n+k-1).choose k : ℤ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  change coeff k ((PowerSeries.mk (1 : ℕ → ℤ))^(d+1)) = _
  rw [mk_one_pow_eq_mk_choose_add ℤ d, coeff_mk]
  have ht : d+1+k-1 = d+k := Nat.succ_add_sub_one k d
  rw [ht]
  have hc := Nat.choose_symm (Nat.le_add_right d k)
  simpa only [Nat.add_sub_cancel_left] using congrArg (fun z : ℕ => (z : ℤ)) hc.symm

theorem negbinomDiv (n k : ℕ) (hn : n ≠ 0) : n ∣ k*(n+k-1).choose k := by
  have h := D5.S1.Recurrence.Algebraic.HannaA181070Integrality.coefficientDivisibility
    (PowerSeries.mk fun _ => (1 : ℤ)) n k
  rw [negbinomCoeff n k hn] at h
  exact_mod_cast h

theorem negbinomCong (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    Nat.ModEq (p^(padicValNat p n+1))
      ((p*n+p*k-1).choose (p*k)) ((n+k-1).choose k) := by
  have h := D5.S1.Recurrence.Algebraic.HannaA181070Integrality.coeffLift (PowerSeries.mk fun _ => (1 : ℤ)) p n k hp
  rw [negbinomCoeff _ _ (Nat.mul_ne_zero hp.ne_zero hn), negbinomCoeff _ _ hn] at h
  apply Nat.modEq_of_dvd
  simpa only [Nat.cast_pow, neg_sub] using (dvd_neg.mpr h)

private def F74 (n k : ℕ) : ℕ := ((n+k-1).choose k)^(k+1)

private theorem cong74 (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : n ≠ 0) :
    (p : ℤ)^(padicValNat p n+1) ∣ (F74 (p*n) (p*k) : ℤ)-F74 n k := by
  have hc := (negbinomCong p n k hp hn).pow (p*k+1)
  have he := D5.S1.Recurrence.Algebraic.HannaA181070Integrality.variableExponent p n k ((n+k-1).choose k) hp (negbinomDiv n k hn)
  have h := Nat.modEq_iff_dvd.mp (hc.trans he).symm
  simpa only [F74, Nat.cast_pow] using h

theorem result : claim := by
  have hl : logarithm = D5.S1.Recurrence.Algebraic.HannaA181070Integrality.L F74 := by
    ext m
    simpa only [logarithm, coeff_mk, F74, Nat.cast_pow] using
      D5.S1.Recurrence.Algebraic.HannaA181070Integrality.literalUnbounded F74 m
  unfold claim A
  rw [hl]
  exact D5.S1.Recurrence.Algebraic.HannaA181070Integrality.integralGeneric _
    (D5.S1.Recurrence.Algebraic.HannaA181070Integrality.divPower (fun n k => (n+k-1).choose k) (fun _ k => k)
      negbinomDiv) cong74

end D5.S1.Recurrence.Algebraic.HannaA181074Integrality
