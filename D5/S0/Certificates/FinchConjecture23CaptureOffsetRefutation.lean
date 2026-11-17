/- GID: D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/FinchConjecture23CaptureOffsetRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Order.Bounds.Defs]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.claim; result=D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.result; claim=D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.claim
   digest: The k = 2 source sequence has least period 4, least preperiod 0 and least capture endpoint 9, refuting Finch Conjecture 23. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! A small-case refutation of Finch, arXiv:2610.34300v1, Conjecture 23.
The source definitions and the positive-index conventions are those of #23615. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Trureturing.OpenProblems.FinchConjecture23CaptureOffset

/-- Recurrence (A) on the source's positive indices. Index zero is unused. -/
def IsSourceSequence (k : ℕ) (x : ℕ → ZMod 3) : Prop :=
  (∀ n : ℕ, 1 ≤ n → n < k → x n = 0) ∧
  x k = 1 ∧
  (∀ n : ℕ, k + 1 ≤ n → x n = x (n - 1) + x (n - k) ^ 2)

/-- A positive eventual period, with the source's strict pre-period inequality. -/
def IsEventualPeriod (x : ℕ → ZMod 3) (p : ℕ) : Prop :=
  0 < p ∧ ∃ μ : ℕ, ∀ n : ℕ, μ < n → x (n + p) = x n

/-- The least positive eventual period N_A(k), expressed without a partial minimum. -/
def HasLeastEventualPeriod (x : ℕ → ZMod 3) (p : ℕ) : Prop :=
  IsLeast {q : ℕ | IsEventualPeriod x q} p

/-- The exact natural-number ceiling of (k - 1) / 4, used only for k ≥ 2. -/
def gaps (k : ℕ) : ℕ := (k - 1 + 3) / 4

/-- Definition 15: g gaps, with no additional zeros between consecutive listed zeros. -/
def IsRun (k : ℕ) (x : ℕ → ZMod 3) (r g : ℕ) : Prop :=
  k + 1 ≤ r ∧ 1 ≤ g ∧
  (∀ i : ℕ, i ≤ g → x (r + 4 * i) = 0) ∧
  (∀ n : ℕ, r < n → n < r + 4 * g → (n - r) % 4 ≠ 0 → x n ≠ 0)

/-- Definition 21: the least endpoint of a run with G gaps. -/
def IsCapturePoint (k : ℕ) (x : ℕ → ZMod 3) (z : ℕ) : Prop :=
  IsLeast {t : ℕ | ∃ r : ℕ, IsRun k x r (gaps k) ∧ t = r + 4 * gaps k} z

/-- Definition 22: the least μ ≥ 0 after which x is four-periodic. -/
def IsPreperiod (x : ℕ → ZMod 3) (μ : ℕ) : Prop :=
  IsLeast {m : ℕ | ∀ n : ℕ, m < n → x (n + 4) = x n} μ

/-- Conjecture 23, including existence of the implicitly specified source sequence
and of the two least indices used in the asserted identity. -/
def claim : Prop :=
  (∀ k : ℕ, 2 ≤ k → ∃ x : ℕ → ZMod 3, IsSourceSequence k x) ∧
  (∀ k : ℕ, ∀ x : ℕ → ZMod 3,
    2 ≤ k → IsSourceSequence k x →
    (k % 4 = 2 ∨ k % 4 = 3) → HasLeastEventualPeriod x 4 →
    ∃ z : ℕ, ∃ μ : ℕ,
      IsCapturePoint k x z ∧ IsPreperiod x μ ∧ (z : ℤ) - (μ : ℤ) = 6)


/-- The positive-index block is (0,1,1,2); index zero is immaterial. -/
private def cycle (n : ℕ) : ZMod 3 :=
  match n % 4 with
  | 0 => 2
  | 1 => 0
  | _ => 1

private theorem cycle_period (n : ℕ) : cycle (n + 4) = cycle n := by
  simp [cycle]

private theorem cycle_source : IsSourceSequence 2 cycle := by
  refine ⟨?_, by decide, ?_⟩
  · intro n hn hk
    have : n = 1 := by omega
    subst n
    rfl
  · intro n hn
    have hlt := Nat.mod_lt n (by decide : 0 < 4)
    interval_cases h : n % 4
    · have h₁ : (n - 1) % 4 = 3 := by omega
      have h₂ : (n - 2) % 4 = 2 := by omega
      norm_num [cycle, h, h₁, h₂] <;> decide
    · have h₁ : (n - 1) % 4 = 0 := by omega
      have h₂ : (n - 2) % 4 = 3 := by omega
      norm_num [cycle, h, h₁, h₂] <;> decide
    · have h₁ : (n - 1) % 4 = 1 := by omega
      have h₂ : (n - 2) % 4 = 0 := by omega
      norm_num [cycle, h, h₁, h₂] <;> decide
    · have h₁ : (n - 1) % 4 = 2 := by omega
      have h₂ : (n - 2) % 4 = 1 := by omega
      norm_num [cycle, h, h₁, h₂] <;> decide

private theorem cycle_least_period : HasLeastEventualPeriod cycle 4 := by
  refine ⟨⟨by decide, 0, fun n _ => cycle_period n⟩, ?_⟩
  intro q hq
  rcases hq with ⟨hq, μ, hp⟩
  by_contra h
  have hq4 : q < 4 := by omega
  have hn : μ < 4 * (μ + 1) + 1 := by omega
  have heq := hp (4 * (μ + 1) + 1) hn
  interval_cases q <;> norm_num [cycle, Nat.add_mod, Nat.mul_mod] at heq
  exact (by decide : (2 : ZMod 3) ≠ 0) heq

private theorem cycle_preperiod : IsPreperiod cycle 0 := by
  exact ⟨fun n _ => cycle_period n, fun _ _ => Nat.zero_le _⟩

private theorem cycle_capture : IsCapturePoint 2 cycle 9 := by
  refine ⟨?_, ?_⟩
  · refine ⟨5, ?_, by decide⟩
    refine ⟨by decide, by decide, ?_, ?_⟩
    · intro i hi
      have hi1 : i ≤ 1 := by simpa [gaps] using hi
      interval_cases i <;> decide
    · intro n hn hn' _
      have hn9 : n < 9 := by simpa [gaps] using hn'
      interval_cases n <;> decide
  · intro t ht
    rcases ht with ⟨r, hr, rfl⟩
    have hz := hr.2.2.1 0 (Nat.zero_le _)
    have hr3 : 3 ≤ r := hr.1
    have hr5 : 5 ≤ r := by
      by_contra h
      have hrlt : r < 5 := by omega
      interval_cases r <;> norm_num [cycle] at hz
      exact (by decide : (2 : ZMod 3) ≠ 0) hz
    norm_num [gaps]
    omega

/-- Finch's original k ≥ 2 capture-offset conjecture is false at k = 2. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨z, μ, hz, hμ, hoffset⟩ :=
    h.2 2 cycle (by decide) cycle_source (by decide) cycle_least_period
  have hz9 : z = 9 := le_antisymm (hz.2 cycle_capture.1) (cycle_capture.2 hz.1)
  have hμ0 : μ = 0 := le_antisymm (hμ.2 cycle_preperiod.1) (cycle_preperiod.2 hμ.1)
  subst z
  subst μ
  norm_num at hoffset

#print axioms result

end Trureturing.OpenProblems.FinchConjecture23CaptureOffset
