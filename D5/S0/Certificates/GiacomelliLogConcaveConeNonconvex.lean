/- GID: D5/S0/Certificates/GiacomelliLogConcaveConeNonconvex
   generality: I
   mirror-B: D5/B/S0/Certificates/GiacomelliLogConcaveConeNonconvex
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/GiacomelliLogConcaveConeNonconvex.claim; result=D5/S0/Certificates/GiacomelliLogConcaveConeNonconvex.result; claim=D5/S0/Certificates/GiacomelliLogConcaveConeNonconvex.claim
   digest: Two geometric solutions have a midpoint with negative log-concavity determinant. -/

/-
Public definitions: seq, logConcaveOp, coneInf, claim (source expressions).
Public theorem result:
  proof_shape: content (strong induction for recurrence solutions and induction on all iterates).
  escape_witness: result (the conclusion itself, obtained by the recurrence counterexample
    and its all-index recurrence and interior-iterate inductions).
  admission_basis: open-problem-resolution (#18698; Refuted).
  Direct frozen dependencies: none.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).

Source: P. Giacomelli, arXiv:2604.14391v1, equation (3), Definition 2.1,
and Section 7 (1), printed pages 2, 3, and 13.
The recurrence and operator use the source expressions. Iteration is evaluated
only at interior indices i ≤ n; iteration zero also requires nonnegative terms.
The affirmative convexity assertion ranges over every real coefficient pair
and every order d ≥ 3. The counterexample has d = 3, p = (1,-3,2), q = (3,-2,0).
Its two solutions are 1 and 2^n. Their midpoint fails at i = n = 1.
Characterization and simple connectedness are not asserted.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

namespace D5.S0.Certificates.GiacomelliLogConcaveConeNonconvex

/-- The sequence with initial data `(a_0, …, a_{d-1}) = v0` and the recurrence (3),
`a_{n+1} = Σ_{k=0}^{d-1} (p_k n + q_k) a_{n-k}` for `n ≥ d - 1` (here `m = n + 1`). -/
noncomputable def seq {d : ℕ} (p q v0 : Fin d → ℝ) (m : ℕ) : ℝ :=
  if h : m < d then v0 ⟨m, h⟩ else
    ∑ k : Fin d, (p k * ((m - 1 : ℕ) : ℝ) + q k) * seq p q v0 (m - 1 - k)
termination_by m
decreasing_by
  have := k.isLt
  omega

/-- Definition 2.1: the log-concave operator `L(a_k) = b_k = a_k² - a_{k+1} a_{k-1}`; `L^i(a)` is used
at the interior indices `n ≥ i`. -/
def logConcaveOp (a : ℕ → ℝ) (k : ℕ) : ℝ := a k ^ 2 - a (k + 1) * a (k - 1)

/-- The cone `C_∞ = {v0 : L^i(a_n) ≥ 0 ∀ n, i}` of initial data of `∞`-log-concave sequences. -/
def coneInf {d : ℕ} (p q : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {v0 | ∀ i n : ℕ, i ≤ n → 0 ≤ (logConcaveOp^[i] (seq p q v0)) n}

/-- Giacomelli, arXiv:2604.14391v1, Section 7 (1) ("Characterize the geometry of the cone C∞ … for d ≥ 3.
Is it convex?"), as the assertion that the cone is convex for every `d ≥ 3` and all coefficients. -/
def claim : Prop := ∀ d : ℕ, 3 ≤ d → ∀ p q : Fin d → ℝ, Convex ℝ (coneInf p q)


theorem result : ¬ D5.S0.Certificates.GiacomelliLogConcaveConeNonconvex.claim := by
  let p : Fin 3 → ℝ := ![1, -3, 2]
  let q : Fin 3 → ℝ := ![3, -2, 0]
  let U : Fin 3 → ℝ := fun _ => 1
  let V : Fin 3 → ℝ := fun k => (2 : ℝ) ^ (k : ℕ)
  let M : Fin 3 → ℝ := (1 / 2 : ℝ) • U + (1 / 2 : ℝ) • V
  have hclosed (m : ℕ) : seq p q U m = 1 ∧ seq p q V m = (2 : ℝ) ^ m := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm : m < 3
      · constructor
        · rw [seq, dite_eq_left hm]
        · rw [seq, dite_eq_left hm]
      · obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = t + 3 := Nat.exists_eq_add_of_le' (Nat.le_of_not_gt hm)
        have h0 := ih t (by omega)
        have h1 := ih (t + 1) (by omega)
        have h2 := ih (t + 2) (by omega)
        have ht0 : t + 3 - 1 - (0 : Fin 3) = t + 2 := Eq.symm (Nat.add_succ t 1)
        have ht1 : t + 3 - 1 - (1 : Fin 3) = t + 1 := Eq.symm (Nat.add_succ t 0)
        have ht2 : t + 3 - 1 - (2 : Fin 3) = t := Eq.symm (Nat.eq_sub_of_add_eq rfl)
        constructor
        · rw [seq, dite_eq_right (by omega), Fin.sum_univ_three]
          simp only [ht0, ht1, ht2, h0.1, h1.1, h2.1]
          norm_num [p, q]
          ring
        · rw [seq, dite_eq_right (by omega), Fin.sum_univ_three]
          simp only [ht0, ht1, ht2, h0.2, h1.2, h2.2]
          norm_num [p, q, pow_add]
          ring
  have hUzero (i n : ℕ) (hi : 1 ≤ i) (hn : i ≤ n) :
      (logConcaveOp^[i] (seq p q U)) n = 0 := by
    induction i generalizing n with
    | zero => omega
    | succ i ih =>
      rw [Function.iterate_succ_apply', logConcaveOp]
      by_cases hi0 : i = 0
      · subst i
        simp only [Function.iterate_zero_apply, (hclosed n).1,
          (hclosed (n + 1)).1, (hclosed (n - 1)).1]
        norm_num
      · rw [ih n (by omega) (by omega),
            ih (n + 1) (by omega) (by omega),
            ih (n - 1) (by omega) (by omega)]
        norm_num
  have hVzero (i n : ℕ) (hi : 1 ≤ i) (hn : i ≤ n) :
      (logConcaveOp^[i] (seq p q V)) n = 0 := by
    induction i generalizing n with
    | zero => omega
    | succ i ih =>
      rw [Function.iterate_succ_apply', logConcaveOp]
      by_cases hi0 : i = 0
      · subst i
        simp only [Function.iterate_zero_apply, (hclosed n).2,
          (hclosed (n + 1)).2, (hclosed (n - 1)).2]
        obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t + 1 := Nat.exists_eq_add_one.mpr hn
        simp only [Nat.add_sub_cancel, pow_add]
        ring
      · rw [ih n (by omega) (by omega),
            ih (n + 1) (by omega) (by omega),
            ih (n - 1) (by omega) (by omega)]
        norm_num
  have hU : U ∈ coneInf p q := by
    intro i n hn
    by_cases hi : i = 0
    · subst i
      simp only [Function.iterate_zero_apply, (hclosed n).1]
      norm_num
    · rw [hUzero i n (by omega) hn]
  have hV : V ∈ coneInf p q := by
    intro i n hn
    by_cases hi : i = 0
    · subst i
      simp only [Function.iterate_zero_apply, (hclosed n).2]
      positivity
    · rw [hVzero i n (by omega) hn]
  intro hc
  have hM : M ∈ coneInf p q := hc 3 le_rfl p q hU hV
    (show (0 : ℝ) ≤ 1 / 2 from one_div_nonneg.mpr (by norm_num))
    (show (0 : ℝ) ≤ 1 / 2 from one_div_nonneg.mpr (by norm_num))
    (show (1 / 2 : ℝ) + 1 / 2 = 1 from add_halves 1)
  have hbad := hM 1 1 le_rfl
  norm_num [Function.iterate_one, logConcaveOp, seq, M, U, V] at hbad

end D5.S0.Certificates.GiacomelliLogConcaveConeNonconvex
