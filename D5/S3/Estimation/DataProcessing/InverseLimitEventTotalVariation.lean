/- GID: D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Level laws determine measurable-event variation on finite-alphabet threads. -/

import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation

open MeasureTheory MeasurableSpace Set
open scoped ENNReal symmDiff
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/-- A compatible thread of a countable tower. The subtype inherits its product
topology and measurable structure; no additional events are introduced. -/
abbrev Thread (B : ℕ → Type*) (q : (l : ℕ) → B (l + 1) → B l) :=
  {x : (l : ℕ) → B l // ∀ l, q l (x (l + 1)) = x l}

/-- The actual level projection of a finite tuple of compatible threads. -/
def levelProjection {B : ℕ → Type*} (q : (l : ℕ) → B (l + 1) → B l)
    (n l : ℕ) (x : Fin n → Thread B q) : Fin n → B l :=
  fun j => (x j).val l

/-- Total variation over all measurable events equals the supremum of the
total variations of the actual level laws. Finite discrete Borel spaces carry
these measurable structures. Neither law is required to satisfy feasibility
constraints, and no bonding map is required to be surjective. -/
theorem total_variation_eq_iSup_level
    {B : ℕ → Type*} [∀ l, Finite (B l)]
    [∀ l, MeasurableSpace (B l)] [∀ l, MeasurableSingletonClass (B l)]
    (q : (l : ℕ) → B (l + 1) → B l) (n : ℕ)
    (P Q : Measure (Fin n → Thread B q)) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    measurableTotalVariation P Q =
      ⨆ l, measurableTotalVariation
        (P.map (levelProjection q n l)) (Q.map (levelProjection q n l)) := by
  classical
  let X := Fin n → Thread B q
  let π := levelProjection q n
  let C : Set (Set X) := {s | ∃ (l : ℕ) (A : Set (Fin n → B l)), π l ⁻¹' A = s}
  have hπ (l : ℕ) : Measurable (π l) := by
    exact measurable_pi_lambda _ fun j =>
      (measurable_pi_apply l).comp (measurable_subtype_coe.comp (measurable_pi_apply j))
  have descend : ∀ {l m : ℕ}, l ≤ m →
      ∃ f : B m → B l, ∀ x : Thread B q, x.val l = f (x.val m) := by
    intro l m h
    induction h with
    | refl => exact ⟨id, fun _ => rfl⟩
    | @step m h ih =>
      obtain ⟨f, hf⟩ := ih
      refine ⟨f ∘ q m, fun x => ?_⟩
      rw [hf x, Function.comp_apply, x.property m]
  have lift : ∀ {l m : ℕ}, l ≤ m → ∀ A : Set (Fin n → B l),
      ∃ A' : Set (Fin n → B m), π l ⁻¹' A = π m ⁻¹' A' := by
    intro l m h A
    obtain ⟨f, hf⟩ := descend h
    refine ⟨(fun y j => f (y j)) ⁻¹' A, ?_⟩
    have heq : π l = (fun y j => f (y j)) ∘ π m := by
      funext x j
      exact hf (x j)
    rw [heq]
    rfl
  have hC : IsSetRing C := by
    refine ⟨⟨0, ∅, rfl⟩, ?_, ?_⟩
    · rintro s t ⟨l, A, rfl⟩ ⟨m, D, rfl⟩
      obtain ⟨A', hA⟩ := lift (Nat.le_max_left l m) A
      obtain ⟨D', hD⟩ := lift (Nat.le_max_right l m) D
      exact ⟨max l m, A' ∪ D', by rw [preimage_union, ← hA, ← hD]⟩
    · rintro s t ⟨l, A, rfl⟩ ⟨m, D, rfl⟩
      obtain ⟨A', hA⟩ := lift (Nat.le_max_left l m) A
      obtain ⟨D', hD⟩ := lift (Nat.le_max_right l m) D
      exact ⟨max l m, A' \ D', by rw [preimage_sdiff, ← hA, ← hD]⟩
  have hgen : (inferInstance : MeasurableSpace X) = generateFrom C := by
    apply le_antisymm
    · change MeasurableSpace.pi ≤ generateFrom C
      simp only [MeasurableSpace.pi, Subtype.instMeasurableSpace,
        MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      refine iSup_le fun j => iSup_le fun l => ?_
      rintro s ⟨A, hA, rfl⟩
      exact measurableSet_generateFrom ⟨l, (fun y => y j) ⁻¹' A, rfl⟩
    · refine generateFrom_le fun s hs => ?_
      obtain ⟨l, A, rfl⟩ := hs
      exact hπ l (Set.toFinite A).measurableSet
  have hcover : ∃ D : Set (Set X), D.Countable ∧ D ⊆ C ∧ (P + Q) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, countable_singleton _, ?_, by simp⟩
    exact singleton_subset_iff.mpr ⟨0, univ, rfl⟩
  let M := ⨆ l, measurableTotalVariation (P.map (π l)) (Q.map (π l))
  have cylinder_bound {c : Set X} (hc : c ∈ C) :
      max (P c - Q c) (Q c - P c) ≤ M := by
    obtain ⟨l, A, rfl⟩ := hc
    have hA := (Set.toFinite A).measurableSet
    rw [← Measure.map_apply (hπ l) hA, ← Measure.map_apply (hπ l) hA]
    exact (le_iSup (fun e : {s : Set (Fin n → B l) // MeasurableSet s} =>
      max ((P.map (π l)) e.val - (Q.map (π l)) e.val)
        ((Q.map (π l)) e.val - (P.map (π l)) e.val)) ⟨A, hA⟩).trans
      (le_iSup (fun l => measurableTotalVariation (P.map (π l)) (Q.map (π l))) l)
  apply le_antisymm
  · refine iSup_le fun s => ?_
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨c, hc, hclose⟩ :=
      exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := P + Q)
        hC hcover hgen s.property (ENNReal.coe_pos.mpr hε)
    have hgap := cylinder_bound hc
    have bound (μ ν : Measure X) (hgap' : μ c - ν c ≤ M) :
        μ s.val - ν s.val ≤ M + (μ + ν) (c ∆ s.val) := by
      have hu : μ s.val - μ c ≤ μ (c ∆ s.val) := by
        exact le_measure_sdiff.trans (measure_mono (fun _ hx => Or.inr hx))
      have hv : ν c - ν s.val ≤ ν (c ∆ s.val) :=
        le_measure_sdiff.trans (measure_mono (fun _ hx => Or.inl hx))
      calc
        μ s.val - ν s.val ≤ (μ s.val - μ c) + (μ c - ν s.val) :=
          tsub_le_tsub_add_tsub
        _ ≤ (μ s.val - μ c) + ((μ c - ν c) + (ν c - ν s.val)) :=
          add_le_add le_rfl tsub_le_tsub_add_tsub
        _ ≤ μ (c ∆ s.val) + (M + ν (c ∆ s.val)) :=
          add_le_add hu (add_le_add hgap' hv)
        _ = M + (μ + ν) (c ∆ s.val) := by
          rw [Measure.add_apply]
          ac_rfl
    apply max_le
    · exact (bound P Q ((le_max_left _ _).trans hgap)).trans
        (add_le_add le_rfl hclose.le)
    · have hb := bound Q P ((le_max_right _ _).trans hgap)
      rw [add_comm Q P] at hb
      exact hb.trans (add_le_add le_rfl hclose.le)
  · refine iSup_le fun l => iSup_le fun A => ?_
    rw [Measure.map_apply (hπ l) A.property, Measure.map_apply (hπ l) A.property]
    exact le_iSup (fun e : {s : Set X // MeasurableSet s} =>
      max (P e.val - Q e.val) (Q e.val - P e.val))
        ⟨π l ⁻¹' A.val, hπ l A.property⟩

#print axioms total_variation_eq_iSup_level

end D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation
