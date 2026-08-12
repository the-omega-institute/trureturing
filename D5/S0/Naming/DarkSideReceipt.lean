/- GID: D5/S0/Naming/DarkSideReceipt
   generality: G
   mirror-B: D5/B/S0/Naming/DarkSideReceipt
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A countable perfect metric space is dense and meagre in its completion; its anonymous complement is comeagre, nonempty, and has full atomless probability measure. -/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.MetricSpace.Completion

namespace D5.S0.Naming.DarkSideReceipt

open Filter MeasureTheory Set Topology
open UniformSpace

/-- The completion of a metric space without isolated points also has no isolated points. -/
private theorem completion_perfect_of_perfect
    (N : Type*) [MetricSpace N] [PerfectSpace N] : PerfectSpace (Completion N) := by
  rw [perfectSpace_iff_forall_not_isolated]
  intro x
  by_contra hx
  rw [not_neBot, ← isOpen_singleton_iff_punctured_nhds] at hx
  obtain ⟨n, hn⟩ :=
    Completion.denseRange_coe.exists_mem_open hx (singleton_nonempty x)
  have hnx : (n : Completion N) = x := by simpa using hn
  have hpreimage : ((↑) : N → Completion N) ⁻¹' {x} = {n} := by
    ext m
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hm
      apply Completion.coe_injective N
      exact hm.trans hnx.symm
    · rintro rfl
      exact hnx
  have hn_open : IsOpen ({n} : Set N) := by
    rw [← hpreimage]
    exact hx.preimage (Completion.continuous_coe N)
  exact (Filter.neBot_iff.mp (PerfectSpace.not_isolated n))
    ((isOpen_singleton_iff_punctured_nhds n).mp hn_open)

/-- A countable subset of a T1 perfect space is meagre. -/
private theorem countable_isMeagre_of_perfect
    {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    {s : Set X} (hs : s.Countable) : IsMeagre s := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  refine ⟨singleton '' s, ?_, hs.image _, ?_⟩
  · rintro t ⟨x, _, rfl⟩
    rw [isClosed_singleton.isNowhereDense_iff]
    exact interior_singleton x
  · simp

/-- Let `N` be a countable, incomplete metric space without isolated points, and let `X` be its
completion. The canonical image of `N` is dense and meagre in `X`; its anonymous complement is
comeagre and nonempty, and every atomless Borel probability measure on `X` gives that complement
measure one. The incompleteness hypothesis records the source's proper-completion setting; the
remaining conclusions follow from the canonical completion, perfectness, and countability. -/
theorem dark_side_receipt
    (N : Type*) [MetricSpace N] [Countable N] [PerfectSpace N]
    (_h_incomplete : ¬ CompleteSpace N)
    [MeasurableSpace (Completion N)] [BorelSpace (Completion N)]
    (μ : Measure (Completion N)) [NoAtoms μ] [IsProbabilityMeasure μ] :
    DenseRange ((↑) : N → Completion N) ∧
      PerfectSpace (Completion N) ∧
      IsMeagre (Set.range ((↑) : N → Completion N)) ∧
      (Set.range ((↑) : N → Completion N))ᶜ ∈ residual (Completion N) ∧
      (Set.range ((↑) : N → Completion N))ᶜ.Nonempty ∧
      μ (Set.range ((↑) : N → Completion N))ᶜ = 1 := by
  letI : Nonempty N := not_isEmpty_iff.mp fun hN => by
    letI : IsEmpty N := hN
    exact _h_incomplete inferInstance
  letI : Nonempty (Completion N) := ⟨((Classical.choice inferInstance : N) : Completion N)⟩
  letI : PerfectSpace (Completion N) := completion_perfect_of_perfect N
  have hcountable : (Set.range ((↑) : N → Completion N)).Countable := Set.countable_range _
  have hmeagre : IsMeagre (Set.range ((↑) : N → Completion N)) :=
    countable_isMeagre_of_perfect hcountable
  refine ⟨Completion.denseRange_coe, inferInstance, hmeagre, hmeagre, ?_, ?_⟩
  · exact (dense_of_mem_residual hmeagre).nonempty
  rw [prob_compl_eq_one_iff]
  · exact hcountable.measure_zero μ
  · exact hcountable.measurableSet

/-- Checked evidence that the theorem's domain is inhabited. -/
example : ℚ := 0

/-- The rational metric space is countable and has no isolated points. -/
example : Countable ℚ ∧ PerfectSpace ℚ := ⟨inferInstance, inferInstance⟩

/-- The rational metric space is incomplete: otherwise its isometric image in the reals would be
closed as well as dense, contradicting the irrationality of `sqrt 2`. -/
private theorem rat_not_complete : ¬ CompleteSpace ℚ := by
  intro hcomplete
  letI : CompleteSpace ℚ := hcomplete
  have hrat : Isometry ((↑) : ℚ → ℝ) := Isometry.of_dist_eq Rat.dist_cast
  have hclosed : IsClosed (Set.range ((↑) : ℚ → ℝ)) :=
    hrat.isClosedEmbedding.isClosed_range
  have hrange : Set.range ((↑) : ℚ → ℝ) = Set.univ := by
    have hclosure : closure (Set.range ((↑) : ℚ → ℝ)) = Set.univ :=
      dense_iff_closure_eq.mp Rat.denseRange_cast
    rwa [hclosed.closure_eq] at hclosure
  have hsqrt : Real.sqrt 2 ∈ Set.range ((↑) : ℚ → ℝ) := by simp [hrange]
  exact irrational_sqrt_two hsqrt

section RationalMeasureWitness

local instance : MeasurableSpace (Completion ℚ) := borel (Completion ℚ)
local instance : BorelSpace (Completion ℚ) := ⟨rfl⟩

/-- Restricted Lebesgue measure, transported to the completion of the rationals, witnesses the
atomless Borel probability-measure hypotheses simultaneously. -/
private theorem exists_completion_rat_atomless_probability :
    ∃ μ : Measure (Completion ℚ), NoAtoms μ ∧ IsProbabilityMeasure μ := by
  let X := Completion ℚ
  have hrat : Isometry ((↑) : ℚ → ℝ) := Isometry.of_dist_eq Rat.dist_cast
  let f : X → ℝ := Completion.extension ((↑) : ℚ → ℝ)
  have hf : Isometry f := hrat.completion_extension
  have hf_dense : Dense (Set.range f) := Rat.denseRange_cast.mono (by
    rintro y ⟨q, rfl⟩
    refine ⟨(q : X), ?_⟩
    exact Completion.extension_coe hrat.uniformContinuous q)
  have hf_surjective : Function.Surjective f := by
    have hf_closed : IsClosed (Set.range f) := hf.isClosedEmbedding.isClosed_range
    have hrange : Set.range f = Set.univ := by
      have hclosure : closure (Set.range f) = Set.univ := dense_iff_closure_eq.mp hf_dense
      rwa [hf_closed.closure_eq] at hclosure
    intro y
    exact Set.mem_range.mp (hrange.symm ▸ Set.mem_univ y)
  let e : X ≃ᵢ ℝ :=
    { toEquiv := Equiv.ofBijective f ⟨hf.injective, hf_surjective⟩
      isometry_toFun := hf }
  let ρ : Measure ℝ := volume.restrict (Ioc 0 1)
  letI : NoAtoms ρ := inferInstance
  letI : IsProbabilityMeasure ρ := ⟨by simp [ρ, Real.volume_Ioc]⟩
  let μ : Measure X := ρ.comap e.toHomeomorph.toMeasurableEquiv
  refine ⟨μ, ?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    change ρ.comap e.toHomeomorph.toMeasurableEquiv {x} = 0
    rw [MeasurableEquiv.comap_apply]
    have hpreimage : e.toHomeomorph.toMeasurableEquiv.symm ⁻¹' {x} = {e x} := by
      ext y
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro hy
        calc
          y = e (e.symm y) := (e.apply_symm_apply y).symm
          _ = e x := congrArg e hy
      · intro hy
        calc
          e.symm y = e.symm (e x) := congrArg e.symm hy
          _ = x := e.symm_apply_apply x
    rw [hpreimage]
    exact measure_singleton _
  · infer_instance

/-- One checked term realizes all of the theorem's typeclass and value hypotheses at once. -/
example :
    Countable ℚ ∧ PerfectSpace ℚ ∧ (¬ CompleteSpace ℚ) ∧
      ∃ μ : Measure (Completion ℚ), NoAtoms μ ∧ IsProbabilityMeasure μ :=
  ⟨inferInstance, inferInstance, rat_not_complete, exists_completion_rat_atomless_probability⟩

end RationalMeasureWitness

end D5.S0.Naming.DarkSideReceipt
