/- GID: D5/S0/Certificates/RationalMomentElimination
   generality: G
   mirror-B: D5/B/S0/Certificates/RationalMomentElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A data-only rational null-direction and ratio-pivot certificate yields an executable support-reducing update preserving total mass and every nominated linear moment. -/

import D5.S0.Certificates.LinearObjectiveDual

/- Reuse the existing exact linear objective. The validator checks only finite
   rational arithmetic on Fin-indexed arrays. It contains no proof-valued
   payload, classical choice, floating arithmetic, or search-oracle premise.
   Finding a null direction is separate from checking a proposed direction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.RationalMomentElimination

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual

/-- Computable support of a raw rational vector, before probability packaging. -/
def activeAtoms {n : Nat} (weight : Fin n → ℚ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => weight i ≠ 0)

/-- Untrusted step payload: a signed rational direction and its ratio pivot. -/
structure EliminationStep (n : Nat) where
  direction : Fin n → ℚ
  pivot : Fin n

/-- Local conditions for a valid direction. The ratio comparison is cross
multiplied, so the validator does not divide by a possibly zero coordinate. -/
def ValidStep {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (weight : Fin n → ℚ) (step : EliminationStep n) : Prop :=
  (∀ i, 0 ≤ weight i) ∧
  0 < weight step.pivot ∧
  0 < step.direction step.pivot ∧
  (∀ i, weight i = 0 → step.direction i = 0) ∧
  (∑ i, step.direction i) = 0 ∧
  (∀ j, linearObjective (fun i => feature i j) step.direction = 0) ∧
  (∀ i, 0 < step.direction i →
    weight step.pivot * step.direction i ≤ weight i * step.direction step.pivot)

/-- An executable exact validator for the data-only step. -/
def checkStep {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (weight : Fin n → ℚ) (step : EliminationStep n) : Bool :=
  @decide (ValidStep feature weight step) (by unfold ValidStep; infer_instance)

/-- Acceptance is equivalent to the stated finite arithmetic conditions. -/
theorem checkStep_eq_true_iff {n d : Nat} (feature : Fin n → Fin d → ℚ)
    (weight : Fin n → ℚ) (step : EliminationStep n) :
    checkStep feature weight step = true ↔ ValidStep feature weight step := by
  simp only [checkStep, decide_eq_true_eq]

/-- The rational boundary update; its denominator is certified positive on acceptance. -/
def eliminate {n : Nat} (weight : Fin n → ℚ) (step : EliminationStep n) : Fin n → ℚ :=
  fun i => weight i - (weight step.pivot / step.direction step.pivot) * step.direction i

/-- A valid ratio pivot keeps every updated weight nonnegative. -/
theorem validStep_nonnegative {n d : Nat} {feature : Fin n → Fin d → ℚ}
    {weight : Fin n → ℚ} {step : EliminationStep n}
    (valid : ValidStep feature weight step) : ∀ i, 0 ≤ eliminate weight step i := by
  rcases valid with ⟨hw, hp, hz, _, _, _, ratio⟩
  have rate_nonnegative : 0 ≤ weight step.pivot / step.direction step.pivot :=
    div_nonneg hp.le hz.le
  intro i
  unfold eliminate
  apply sub_nonneg.mpr
  by_cases positive : 0 < step.direction i
  · calc
      (weight step.pivot / step.direction step.pivot) * step.direction i =
          (weight step.pivot * step.direction i) / step.direction step.pivot := by ring
      _ ≤ weight i := (div_le_iff₀ hz).mpr (ratio i positive)
  · have nonpositive : step.direction i ≤ 0 := le_of_not_gt positive
    exact (mul_nonpos_of_nonneg_of_nonpos rate_nonnegative nonpositive).trans (hw i)

/-- Zero total direction preserves the original total mass exactly. -/
theorem validStep_total {n d : Nat} {feature : Fin n → Fin d → ℚ}
    {weight : Fin n → ℚ} {step : EliminationStep n}
    (valid : ValidStep feature weight step) :
    (∑ i, eliminate weight step i) = ∑ i, weight i := by
  rcases valid with ⟨_, _, _, _, zero_total, _, _⟩
  simp only [eliminate, Finset.sum_sub_distrib, ← Finset.mul_sum,
    zero_total, mul_zero, sub_zero]

/-- Every checked null moment is preserved by the same rational update. -/
theorem validStep_moment {n d : Nat} {feature : Fin n → Fin d → ℚ}
    {weight : Fin n → ℚ} {step : EliminationStep n}
    (valid : ValidStep feature weight step) (j : Fin d) :
    linearObjective (fun i => feature i j) (eliminate weight step) =
      linearObjective (fun i => feature i j) weight := by
  rcases valid with ⟨_, _, _, _, _, zero_moment, _⟩
  calc
    linearObjective (fun i => feature i j) (eliminate weight step) =
        (∑ i, feature i j * weight i) -
          (weight step.pivot / step.direction step.pivot) *
            (∑ i, feature i j * step.direction i) := by
      unfold linearObjective eliminate
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = linearObjective (fun i => feature i j) weight := by
      change linearObjective (fun i => feature i j) weight -
        (weight step.pivot / step.direction step.pivot) *
          linearObjective (fun i => feature i j) step.direction = _
      rw [zero_moment j, mul_zero, sub_zero]

/-- A zero initial atom never reappears. This preserves arbitrary hard support exclusions. -/
theorem validStep_zero_stays_zero {n d : Nat} {feature : Fin n → Fin d → ℚ}
    {weight : Fin n → ℚ} {step : EliminationStep n}
    (valid : ValidStep feature weight step) {i : Fin n} (zero : weight i = 0) :
    eliminate weight step i = 0 := by
  rcases valid with ⟨_, _, _, inactive, _, _, _⟩
  simp [eliminate, zero, inactive i zero]

/-- The selected positive pivot is removed exactly, without tolerance thresholds. -/
theorem validStep_pivot_zero {n d : Nat} {feature : Fin n → Fin d → ℚ}
    {weight : Fin n → ℚ} {step : EliminationStep n}
    (valid : ValidStep feature weight step) : eliminate weight step step.pivot = 0 := by
  rcases valid with ⟨_, _, hz, _, _, _, _⟩
  simp only [eliminate, div_mul_cancel₀ _ (ne_of_gt hz), sub_self]

/-- Each accepted step strictly decreases actual nonzero support and adds no atoms. -/
theorem validStep_support {n d : Nat} {feature : Fin n → Fin d → ℚ}
    {weight : Fin n → ℚ} {step : EliminationStep n}
    (valid : ValidStep feature weight step) :
    activeAtoms (eliminate weight step) ⊆ activeAtoms weight ∧
      (activeAtoms (eliminate weight step)).card < (activeAtoms weight).card := by
  have subset : activeAtoms (eliminate weight step) ⊆ activeAtoms weight := by
    intro i hi
    simp only [activeAtoms, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro zero
    exact hi (validStep_zero_stays_zero valid zero)
  have pivot_mem : step.pivot ∈ activeAtoms weight := by
    simp only [activeAtoms, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_of_gt valid.2.1
  have pivot_out : step.pivot ∉ activeAtoms (eliminate weight step) := by
    simp [activeAtoms, validStep_pivot_zero valid]
  have erase_subset : activeAtoms (eliminate weight step) ⊆ (activeAtoms weight).erase step.pivot := by
    intro i hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, subset hi⟩
    intro same
    subst i
    exact pivot_out hi
  have card_le := Finset.card_le_card erase_subset
  rw [Finset.card_erase_of_mem pivot_mem] at card_le
  have positive : 0 < (activeAtoms weight).card := Finset.card_pos.mpr ⟨step.pivot, pivot_mem⟩
  exact ⟨subset, by omega⟩

/-- No larger step along this oriented direction can preserve nonnegative weights. -/
theorem validStep_maximal_rate {n d : Nat} {feature : Fin n → Fin d → ℚ}
    {weight : Fin n → ℚ} {step : EliminationStep n}
    (valid : ValidStep feature weight step) (rate : ℚ)
    (nonnegative : ∀ i, 0 ≤ weight i - rate * step.direction i) :
    rate ≤ weight step.pivot / step.direction step.pivot := by
  apply (le_div_iff₀ valid.2.2.1).mpr
  linarith [nonnegative step.pivot]

#print axioms validStep_nonnegative
#print axioms validStep_moment
#print axioms validStep_support
#print axioms validStep_maximal_rate

end D5.S0.Certificates.RationalMomentElimination
