/- GID: D5/S3/Arith/OeisA318314
   generality: G
   mirror-B: D5/B/S3/Arith/OeisA318314
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: The rational Dirichlet square root of the odd unitary divisor count. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.Arith.OeisA318314

/-- A068068 counts the positive odd unitary divisors. -/
def oddUnitaryCount (n : ℕ) : ℕ :=
  (n.divisors.filter fun d => Odd d ∧ Nat.Coprime d (n / d)).card

/-- The interior divisors in the published recurrence. -/
def interior (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => 1 < d ∧ d < n

private lemma interior_bounds {n d : ℕ} (hd : d ∈ interior n) :
    1 < d ∧ d < n ∧ n / d < n := by
  have h := (Finset.mem_filter.mp hd).2
  exact ⟨h.1, h.2, Nat.div_lt_self (by omega) h.1⟩

/-- The actual rational recurrence, extended by zero at index zero. -/
def f (n : ℕ) : ℚ :=
  if hn : 1 < n then
    ((oddUnitaryCount n : ℚ) - ∑ d : interior n,
      f d.val * f (n / d.val)) / 2
  else if n = 1 then 1 else 0
termination_by n
decreasing_by
  all_goals
    have hd := interior_bounds d.property
    omega

/-- The source specification imposes no multiplicativity or nonzero premise. -/
def SourceSpec (u : ℕ → ℚ) : Prop :=
  u 1 = 1 ∧ ∀ n, 1 < n →
    u n = ((oddUnitaryCount n : ℚ) -
      ∑ d ∈ interior n, u d * u (n / d)) / 2

private lemma f_spec : SourceSpec f := by
  constructor
  · rw [f]
    norm_num
  · intro n hn
    rw [f, dif_pos hn]
    congr 2
    exact (Finset.sum_attach _ _).symm

private lemma source_unique {u v : ℕ → ℚ} (hu : SourceSpec u)
    (hv : SourceSpec v) : ∀ n, 0 < n → u n = v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      rw [hu.1, hv.1]
    have hn1 : 1 < n := by omega
    rw [hu.2 n hn1, hv.2 n hn1]
    congr 2
    apply Finset.sum_congr rfl
    intro d hd
    have hb := interior_bounds hd
    have hdiv := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    rw [ih d hb.2.1 (by omega), ih (n / d) hb.2.2]
    exact Nat.div_pos (Nat.le_of_dvd hn hdiv) (by omega)

/-- The recurrence is inhabited, and determines every positive-index value uniquely. -/
theorem source_solution_unique : SourceSpec f ∧
    ∀ u : ℕ → ℚ, SourceSpec u → ∀ n, 0 < n → u n = f n := by
  exact ⟨f_spec, fun _ hu => source_unique hu f_spec⟩

end D5.S3.Arith.OeisA318314
