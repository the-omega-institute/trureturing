/- GID: D5/S3/AnalyticClosure/FamilySums/TermBoundDoesNotBoundFamilySum
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/FamilySums/TermBoundDoesNotBoundFamilySum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Growing finite families can keep a nonzero sum despite vanishing term bounds. -/

import Mathlib.Analysis.SpecificLimits.Basic

/- Library-search audit trail (2026-08-24):
   * Type-shape search
     `rg -n '\(m : ℕ\) → Fin|Fin \([^)]*\) → ℝ|Tendsto .*atTop.*𝓝 0' D5 \
       -g '!TermBoundDoesNotBoundFamilySum.lean'`
     found fixed `Fin`-indexed real families and unrelated vanishing limits, but no
     varying finite real family combining a pointwise power bound with its sum.
   * `rg -n -i 'family sum|finite family|indexed family|growing family' D5 \
       -g '!TermBoundDoesNotBoundFamilySum.lean'` found finite-family constructions;
     `rg -n -i '族和|有限族|指标族' D5 -g '!TermBoundDoesNotBoundFamilySum.lean'`
     found none. The analogous English `termwise|pointwise bound|uniform bound|term
     bound` search found local bounds, while the Chinese `逐项|单项|逐点上界` search
     found none; no hit has this counterexample shape. `InnovationCountBound`
     instead bounds large terms from a summability budget.
   * `ls D5/S3/AnalyticClosure` and
     `git grep -n -E '^def |^  def |^theorem ' -- D5/S3/AnalyticClosure | head -60`
     found the neighboring vocabulary of finite-window closure, positive-series
     tails, limits, and normalization impossibility; it contains no reusable
     family-sum declaration. This module introduces no new definitions.
   * `rg -n 'tendsto_one_div_add_atTop_nhds_zero_nat|tendsto_const_nhds_iff|Finset\.sum_const' \
       .lake/packages/mathlib/Mathlib | head -80` found all three
     pinned-Mathlib declarations; they are reused directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.AnalyticClosure.FamilySums.TermBoundDoesNotBoundFamilySum

open Filter Topology
open scoped BigOperators

/-- For every positive natural exponent, there is a shrinking positive scale
and a growing finite family whose members all obey the corresponding power
bound, while every family sum is exactly one and hence does not tend to zero. -/
theorem term_bound_does_not_bound_family_sum :
    ∀ gamma : ℕ, 0 < gamma →
    ∃ (epsilon : ℕ → ℝ) (familySize : ℕ → ℕ)
        (amplitude : (m : ℕ) → Fin (familySize m) → ℝ),
      Tendsto epsilon atTop (𝓝 0) ∧
      (∀ m : ℕ, 0 < epsilon m) ∧
      (∀ (m : ℕ) (i : Fin (familySize m)),
        |amplitude m i| ≤ epsilon m ^ gamma) ∧
      (∀ m : ℕ, (∑ i, |amplitude m i|) = 1) ∧
      ¬ Tendsto (fun m => ∑ i, |amplitude m i|) atTop (𝓝 0) := by
  intro gamma gamma_pos
  let epsilon : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  let familySize : ℕ → ℕ := fun m => (m + 1) ^ gamma
  let amplitude : (m : ℕ) → Fin (familySize m) → ℝ :=
    fun m _ => epsilon m ^ gamma
  have epsilon_tends_to_zero : Tendsto epsilon atTop (𝓝 0) := by
    simpa only [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have epsilon_pos (m : ℕ) : 0 < epsilon m := by
    dsimp only [epsilon]
    positivity
  have pointwise_bound (m : ℕ) (i : Fin (familySize m)) :
      |amplitude m i| ≤ epsilon m ^ gamma := by
    rw [abs_of_pos (pow_pos (epsilon_pos m) gamma)]
  have family_sum_eq_one (m : ℕ) :
      (∑ i, |amplitude m i|) = 1 := by
    change (∑ _i : Fin ((m + 1) ^ gamma), |epsilon m ^ gamma|) = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, abs_of_pos (pow_pos (epsilon_pos m) gamma)]
    dsimp only [epsilon]
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [← mul_pow, mul_one_div_cancel (by positivity), one_pow]
  have family_sum_not_tendsto_zero :
      ¬ Tendsto (fun m => ∑ i, |amplitude m i|) atTop (𝓝 0) := by
    intro familySumTendsToZero
    have constant_one_tends_to_zero :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
      simpa only [family_sum_eq_one] using familySumTendsToZero
    exact one_ne_zero (tendsto_const_nhds_iff.mp constant_one_tends_to_zero)
  exact ⟨epsilon, familySize, amplitude, epsilon_tends_to_zero,
    epsilon_pos, pointwise_bound, family_sum_eq_one,
    family_sum_not_tendsto_zero⟩

/-- For positive `gamma`, `(m + 1) ^ gamma` copies of
`(1 / (m + 1)) ^ gamma` meet the bound with equality and sum to one. -/
example (gamma m : ℕ) (_gamma_pos : 0 < gamma) :
    let epsilon : ℝ := 1 / ((m : ℝ) + 1)
    (∀ _i : Fin ((m + 1) ^ gamma),
        |epsilon ^ gamma| ≤ epsilon ^ gamma) ∧
      (∑ _i : Fin ((m + 1) ^ gamma), |epsilon ^ gamma|) = 1 := by
  dsimp
  have epsilon_pos : 0 < 1 / ((m : ℝ) + 1) := by positivity
  constructor
  · intro i
    rw [abs_of_pos (pow_pos epsilon_pos gamma)]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, abs_of_pos (pow_pos epsilon_pos gamma),
      Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [← mul_pow, mul_one_div_cancel (by positivity), one_pow]

/-- For a fixed one-element family at the same shrinking scale, the family
sum does tend to zero; the obstruction is therefore not universal. -/
example :
    Tendsto
      (fun m : ℕ => ∑ _i : Fin 1, |1 / ((m : ℝ) + 1)|)
      atTop (𝓝 0) := by
  convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
  ext m
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_nsmul]
  rw [abs_of_pos (by positivity)]

#print axioms term_bound_does_not_bound_family_sum

end D5.S3.AnalyticClosure.FamilySums.TermBoundDoesNotBoundFamilySum
