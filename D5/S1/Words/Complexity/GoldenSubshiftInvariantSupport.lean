/- GID: D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/GoldenSubshiftInvariantSupport
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: Every shift-invariant Borel probability measure on the golden word subshift has full support. The support is closed and carried into itself by the shift, so minimality of the subshift forces it to be empty or everything; a probability measure is nonzero, so it is everything. Mathlib states that a measure positive on nonempty open sets has full support but not the converse, which is supplied here. -/

import D5.S1.Words.Complexity.GoldenSubshiftInvariantMeasure
import D5.S1.Words.Complexity.GoldenSubshiftMinimalAction

open Set SymbolicDynamics MeasureTheory Filter
open scoped ENNReal Topology Pointwise
open D5.S1.Words.Complexity.GoldenSubshiftInvariantMeasure

namespace D5.S1.Words.Complexity.GoldenSubshiftInvariantSupport

variable {mu : Measure GoldenPoint}

/-- A measure whose support is the whole space is positive on every nonempty open set.
Mathlib records the forward implication as `Measure.support_eq_univ`; this is the
converse, which the minimality argument below needs. -/
theorem isOpenPosMeasure_of_support_eq_univ (h : mu.support = univ) :
    mu.IsOpenPosMeasure := by
  constructor
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  have hmem : x ∈ mu.support := h ▸ Set.mem_univ x
  exact ((Measure.mem_support_iff_forall x).mp hmem U (hU.mem_nhds hx)).ne'

/-- Under an invariant measure the support is carried into itself by one shift step:
a neighbourhood of the image pulls back to a neighbourhood of the point, and the
pushforward identity transports its positive mass forward. -/
theorem support_mem_of_map_eq (hinv : Measure.map forwardShift mu = mu) {x : GoldenPoint}
    (hx : x ∈ mu.support) : forwardShift x ∈ mu.support := by
  rw [Measure.mem_support_iff_forall] at hx ⊢
  intro U hU
  obtain ⟨V, hVsub, hVo, hVx⟩ := mem_nhds_iff.mp hU
  have hpre : forwardShift ⁻¹' V ∈ 𝓝 x :=
    (hVo.preimage forwardShift_continuous).mem_nhds hVx
  have hpos := hx _ hpre
  have hEq : mu V = mu (forwardShift ⁻¹' V) := by
    conv_lhs => rw [← hinv]
    rw [Measure.map_apply forwardShift_continuous.measurable hVo.measurableSet]
  calc (0 : ℝ≥0∞) < mu (forwardShift ⁻¹' V) := hpos
    _ = mu V := hEq.symm
    _ ≤ mu U := measure_mono hVsub

/-- Iterating the previous step pointwise. -/
private theorem support_mem_vadd (hinv : Measure.map forwardShift mu = mu) (k : ℕ)
    {x : GoldenPoint} (hx : x ∈ mu.support) : k +ᵥ x ∈ mu.support := by
  induction k with
  | zero => simpa using hx
  | succ n ih =>
      have hstep : ((n + 1 : ℕ)) +ᵥ x = forwardShift ((n : ℕ) +ᵥ x) := by
        rw [add_comm, add_vadd]
        rfl
      rw [hstep]
      exact support_mem_of_map_eq hinv ih

/-- The support absorbs every translate of the action. -/
theorem support_vadd_subset (hinv : Measure.map forwardShift mu = mu) (k : ℕ) :
    k +ᵥ mu.support ⊆ mu.support := by
  rintro _ ⟨x, hx, rfl⟩
  exact support_mem_vadd hinv k hx

/-- Minimality forces an invariant probability measure to have full support. -/
theorem invariant_support_eq_univ [IsProbabilityMeasure mu]
    (hinv : Measure.map forwardShift mu = mu) : mu.support = univ := by
  rcases eq_empty_or_univ_of_vadd_invariant_closed ℕ Measure.isClosed_support
      (support_vadd_subset hinv) with hempty | huniv
  · exact absurd hempty (Measure.nonempty_support
      (IsProbabilityMeasure.ne_zero mu)).ne_empty
  · exact huniv

/-- Every shift-invariant Borel probability measure on the golden subshift is positive
on every nonempty open set. -/
theorem invariantMeasure_isOpenPosMeasure [IsProbabilityMeasure mu]
    (hinv : Measure.map forwardShift mu = mu) : mu.IsOpenPosMeasure :=
  isOpenPosMeasure_of_support_eq_univ (invariant_support_eq_univ hinv)

/-- The invariant probability measure produced for the golden subshift has full support. -/
theorem golden_invariant_isOpenPosMeasure :
    ∃ nu : ProbabilityMeasure GoldenPoint,
      MeasurePreserving forwardShift (nu : Measure GoldenPoint) (nu : Measure GoldenPoint)
        ∧ (nu : Measure GoldenPoint).IsOpenPosMeasure := by
  obtain ⟨nu, hnu⟩ := exists_invariant_probabilityMeasure
  exact ⟨nu, hnu, invariantMeasure_isOpenPosMeasure hnu.map_eq⟩

#print axioms isOpenPosMeasure_of_support_eq_univ
#print axioms support_mem_of_map_eq
#print axioms support_vadd_subset
#print axioms invariant_support_eq_univ
#print axioms invariantMeasure_isOpenPosMeasure
#print axioms golden_invariant_isOpenPosMeasure

end D5.S1.Words.Complexity.GoldenSubshiftInvariantSupport
