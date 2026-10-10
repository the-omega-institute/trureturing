/- GID: D5/S3/Quantum/Dynamics/KayTransferRateRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/KayTransferRateRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/KayTransferRateRefutation.claim; result=D5/S3/Quantum/Dynamics/KayTransferRateRefutation.result; claim=D5/S3/Quantum/Dynamics/KayTransferRateRefutation.claim
   digest: An eight-level perfect state transfer spectrum meets Kay's rate condition with M = 4. -/

/-
proof_shape:
  SpectrumCondition, derivativeAt, InClass, rateSum, RateCondition, claim: definitions
  result: bind-only (one explicit spectrum; the definitions are unfolded and evaluated by exact
    rational arithmetic with `simp` and `norm_num`)
escape_witness: none; the conclusion is an exact finite evaluation of the definitions at the
  spectrum 0, 31, 46, 65, 88, 107, 122, 153 with transfer time pi and M = 4
admission_basis: open-problem-resolution (#14475; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.KayTransferRateRefutation

/-- The perfect state transfer condition of Eqn. (st_cond) of arXiv:0903.4274v3 for the levels
`lam 0, …, lam (N - 1)` and the transfer time `t₀`: every gap between consecutive levels is
`(2 m + 1) π / t₀` for a positive integer `m`, which may vary with the gap. -/
def SpectrumCondition {N : ℕ} (lam : Fin N → ℝ) (t₀ : ℝ) : Prop :=
  0 < t₀ ∧ ∃ m : ℕ → ℕ, ∀ n : ℕ, ∀ h : n + 1 < N,
    0 < m n ∧
      lam ⟨n + 1, h⟩ - lam ⟨n, Nat.lt_of_succ_lt h⟩ = (2 * (m n : ℝ) + 1) * Real.pi / t₀

/-- `B'(λ_n) = ∏_{j ≠ n} (λ_n - λ_j)`, the derivative of `B(λ) = ∏_j (λ - λ_j)` at `λ_n`. -/
def derivativeAt {N : ℕ} (lam : Fin N → ℝ) (n : Fin N) : ℝ :=
  ∏ j : Fin N with j ≠ n, (lam n - lam j)

/-- The level `n` lies in the residue class `k` modulo `M`: the real number
`(t₀ / π) (λ_n - λ_1)` is an integer congruent to `k` modulo `M`. -/
def InClass {N : ℕ} (lam : Fin N → ℝ) (t₀ : ℝ) (M k : ℕ) (n : Fin N) : Prop :=
  ∃ z : ℤ, t₀ / Real.pi * (lam n - lam ⟨0, n.pos⟩) = (z : ℝ) ∧ z % (M : ℤ) = (k : ℤ)

open Classical in
/-- `R_k = ∑ (-1)^n / B'(λ_n)` of Eqn. (rate_cond), summed over the levels of the residue class
`k` modulo `M`; the sign uses the source's index, which starts at one. -/
noncomputable def rateSum {N : ℕ} (lam : Fin N → ℝ) (t₀ : ℝ) (M k : ℕ) : ℝ :=
  ∑ n : Fin N with InClass lam t₀ M k n, (-1 : ℝ) ^ (n.val + 1) / derivativeAt lam n

/-- The condition of the rate lemma: all `R_k` for `k = 0, …, M - 1` are equal. -/
def RateCondition {N : ℕ} (lam : Fin N → ℝ) (t₀ : ℝ) (M : ℕ) : Prop :=
  ∀ k < M, ∀ k' < M, rateSum lam t₀ M k = rateSum lam t₀ M k'

/-- Kay's transfer-rate conjecture: no nonempty spectrum fulfilling the perfect state transfer
condition fulfils the condition of the rate lemma for an integer `M > 2`. -/
def claim : Prop :=
  ∀ N : ℕ, 0 < N → ∀ (lam : Fin N → ℝ) (t₀ : ℝ), SpectrumCondition lam t₀ →
    ∀ M : ℕ, 2 < M → ¬ RateCondition lam t₀ M

/-- The conjecture fails: the spectrum `0, 31, 46, 65, 88, 107, 122, 153` with transfer time `π`
(gap multipliers `m = 15, 7, 9, 11, 9, 7, 15`) has `R_0 = R_1 = R_2 = R_3 = 194/38984495395755`
for `M = 4`. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin 8 → ℝ, lam = ![0, 31, 46, 65, 88, 107, 122, 153] := ⟨_, rfl⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpst : SpectrumCondition lam Real.pi := by
    refine ⟨Real.pi_pos, fun n => [15, 7, 9, 11, 9, 7, 15].getD n 0, ?_⟩
    intro n hn
    have hn' : n < 7 := by omega
    rw [mul_div_assoc, div_self hpi, mul_one]
    interval_cases n <;> norm_num [hlam]
  have hB : ∀ n : Fin 8, derivativeAt lam n =
      ![-16291106900640, 760363989840, -273136152240, 203460697440,
        -203460697440, 273136152240, -760363989840, 16291106900640] n := by
    intro n
    fin_cases n <;>
      simp [derivativeAt, Finset.prod_filter, Fin.prod_univ_eight, hlam] <;> norm_num
  have hclass : ∀ (k : ℕ) (n : Fin 8), InClass lam Real.pi 4 k n ↔
      (![0, 31, 46, 65, 88, 107, 122, 153] n : ℤ) % 4 = (k : ℤ) := by
    intro k n
    have hval : lam n - lam ⟨0, n.pos⟩ =
        ((![0, 31, 46, 65, 88, 107, 122, 153] n : ℤ) : ℝ) := by
      rw [hlam]
      fin_cases n <;> norm_num
    unfold InClass
    rw [div_self hpi, one_mul, hval]
    constructor
    · rintro ⟨z, hz, hk⟩
      have hzn : (![0, 31, 46, 65, 88, 107, 122, 153] n : ℤ) = z := by exact_mod_cast hz
      rw [hzn]
      exact_mod_cast hk
    · intro hk
      exact ⟨_, rfl, by exact_mod_cast hk⟩
  have hR : ∀ k : ℕ, k < 4 → rateSum lam Real.pi 4 k = 194 / 38984495395755 := by
    intro k hk
    unfold rateSum
    rw [Finset.sum_filter, Fin.sum_univ_eight]
    simp only [hclass, hB]
    interval_cases k <;> simp <;> norm_num
  exact h 8 (by norm_num) lam Real.pi hpst 4 (by norm_num)
    (fun k hk k' hk' => (hR k hk).trans (hR k' hk').symm)

end D5.S3.Quantum.Dynamics.KayTransferRateRefutation
