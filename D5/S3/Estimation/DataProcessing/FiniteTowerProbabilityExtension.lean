/- GID: D5/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension
   generality: I
   mirror-B: D5/B/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compatible probability laws on a tower of finite discrete spaces with arbitrary total bonds have a unique Borel extension on the actual inverse-limit threads. -/

import D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
import D5.S3.TotalVariation.Metric
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation

open Set Function TopologicalSpace CategoryTheory
open D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
open scoped ENNReal NNReal
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open private measurable_total_variation_map_le from
  D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
universe u v w
open Filter

namespace D5.S3.Estimation.DataProcessing.FiniteTowerProbabilityExtension

set_option maxHeartbeats 8000000 in
/-- Compatible laws extend to the actual threads without surjective carrier bonds. -/
theorem exists_unique_extension
    {B : ℕ → Type u} [∀ l, Finite (B l)] [∀ l, Nonempty (B l)]
    [∀ l, TopologicalSpace (B l)] [∀ l, DiscreteTopology (B l)]
    [∀ l, MeasurableSpace (B l)] [∀ l, BorelSpace (B l)]
    (q : (l : ℕ) → B (l + 1) → B l)
    (theta : (l : ℕ) → ProbabilityMeasure (B l))
    (h : ∀ l, (theta (l + 1) : Measure (B (l + 1))).map (q l) =
      (theta l : Measure (B l))) :
    ∃! μ : ProbabilityMeasure (Thread B q),
      ∀ l, (μ : Measure (Thread B q)).map (fun x => x.val l) =
        (theta l : Measure (B l)) := by
  classical
  let C : ℕ → Type u := Nat.rec (motive := fun _ => Type u) (B 0) (fun l T => T × B (l + 1))
  haveI : ∀ l, Finite (C l) := by
    intro l
    induction l with
    | zero => exact inferInstanceAs (Finite (B 0))
    | succ l ih =>
        letI : Finite (C l) := ih
        exact inferInstanceAs (Finite (C l × B (l + 1)))
  haveI : ∀ l, Nonempty (C l) := by
    intro l
    induction l with
    | zero => exact inferInstanceAs (Nonempty (B 0))
    | succ l ih =>
        letI : Nonempty (C l) := ih
        exact inferInstanceAs (Nonempty (C l × B (l + 1)))
  letI tC : ∀ l, TopologicalSpace (C l) := fun l =>
    { IsOpen := fun _ => True
      isOpen_univ := trivial
      isOpen_inter := fun _ _ _ _ => trivial
      isOpen_sUnion := fun _ _ => trivial }
  haveI dC : ∀ l, @DiscreteTopology (C l) (tC l) := fun l => @DiscreteTopology.mk (C l) (tC l) rfl
  letI mC : ∀ l, MeasurableSpace (C l) := fun l =>
    { MeasurableSet' := fun _ => True
      measurableSet_empty := trivial
      measurableSet_compl := fun _ _ => trivial
      measurableSet_iUnion := fun _ _ => trivial }
  haveI bC : ∀ l, @BorelSpace (C l) (tC l) (mC l) := fun l =>
    @BorelSpace.mk (C l) (tC l) (mC l)
      (@borel_eq_top_of_discrete (C l) (tC l) (dC l)).symm
  let p : (l : ℕ) → C (l + 1) → C l := fun _ => Prod.fst
  have hpSurj : ∀ l, Surjective (p l) := fun l c =>
    ⟨(c, Classical.choice (inferInstance : Nonempty (B (l + 1)))), rfl⟩
  let e : (l : ℕ) → B l → C l :=
    Nat.rec (motive := fun l => B l → C l) id (fun l e b => (e (q l b), b))
  let last : (l : ℕ) → C l → B l :=
    Nat.rec (motive := fun l => C l → B l) id (fun _ _ => Prod.snd)
  have last_e (l : ℕ) (b : B l) : last l (e l b) = b := by
    cases l <;> rfl
  have pe (l : ℕ) (b : B (l + 1)) : p l (e (l + 1) b) = e l (q l b) := rfl
  clear_value p e last tC mC C
  let k (l : ℕ) : B l → Fin 1 → C l := fun b _ => e l b
  have hk (l : ℕ) : Measurable (k l) := measurable_of_countable (k l)
  let H (l : ℕ) : ProbabilityMeasure (Fin 1 → C l) := (theta l).map (hk l).aemeasurable
  have hH (l : ℕ) : (H (l + 1) : Measure (Fin 1 → C (l + 1))).map
      (fun (y : Fin 1 → C (l + 1)) j => p l (y j)) = (H l : Measure (Fin 1 → C l)) := by
    change ((theta (l + 1) : Measure _).map (k (l + 1))).map
      (fun y j => p l (y j)) = (theta l : Measure _).map (k l)
    rw [Measure.map_map (measurable_of_countable (fun (y : Fin 1 → C (l + 1)) j => p l (y j))) (hk (l + 1)), ← h l,
      Measure.map_map (hk l) (measurable_of_countable (q l))]
    congr 1
    funext b j
    exact pe l b
  obtain ⟨ν, hν, _⟩ := exists_unique_probability_extension p hpSurj 1 H hH
  let X := Fin 1 → Thread C p
  have hcoord (l : ℕ) : Measurable (fun y : X => (y 0).val l) :=
    (measurable_pi_apply l).comp (measurable_subtype_coe.comp (measurable_pi_apply 0))
  have hlev (l : ℕ) : Measurable (levelProjection p 1 l) :=
    measurable_pi_lambda _ fun j =>
      (measurable_pi_apply l).comp (measurable_subtype_coe.comp (measurable_pi_apply j))
  have hcoordLaw (l : ℕ) : (ν : Measure X).map (fun y => (y 0).val l) =
      (theta l : Measure _).map (e l) := by
    have hc : (fun y : X => (y 0).val l) =
        (fun z : Fin 1 → C l => z 0) ∘ levelProjection p 1 l := rfl
    rw [hc, ← Measure.map_map (measurable_pi_apply 0) (hlev l), hν l]
    change ((theta l : Measure _).map (k l)).map (fun z => z 0) = _
    rw [Measure.map_map (measurable_pi_apply 0) (hk l)]
    rfl
  have hcoordSupport (l : ℕ) : ∀ᵐ y ∂(ν : Measure X), (y 0).val l ∈ range (e l) := by
    have hs : MeasurableSet (range (e l)) := (Set.toFinite _).measurableSet
    have hh : ∀ᵐ z ∂((theta l : Measure _).map (e l)), z ∈ range (e l) := by
      exact (ae_map_iff (μ := (theta l : Measure (B l)))
        (measurable_of_countable (e l)).aemeasurable hs).mpr
        (Filter.Eventually.of_forall fun b => ⟨b, rfl⟩)
    have hh' : ∀ᵐ z ∂((ν : Measure X).map (fun y => (y 0).val l)), z ∈ range (e l) := by
      rw [hcoordLaw l]
      exact hh
    exact (ae_map_iff (μ := (ν : Measure X)) (hcoord l).aemeasurable hs).mp hh'
  let D : X → ((l : ℕ) → B l) := fun y l => last l ((y 0).val l)
  have hD : Measurable D := measurable_pi_lambda _ fun l =>
    (measurable_of_countable (last l)).comp (hcoord l)
  let M : Measure ((l : ℕ) → B l) := (ν : Measure X).map D
  haveI : IsProbabilityMeasure M := Measure.isProbabilityMeasure_map hD.aemeasurable
  have hMcoord (l : ℕ) : M.map (fun x => x l) = (theta l : Measure _) := by
    change ((ν : Measure X).map D).map (fun x => x l) = _
    rw [Measure.map_map (measurable_pi_apply l) hD]
    change (ν : Measure X).map ((last l) ∘ (fun y => (y 0).val l)) = _
    rw [← Measure.map_map (measurable_of_countable (last l)) (hcoord l), hcoordLaw l,
      Measure.map_map (measurable_of_countable (last l)) (measurable_of_countable (e l))]
    have he : last l ∘ e l = id := funext (last_e l)
    rw [he, Measure.map_id]
  let T : Set ((l : ℕ) → B l) := {x | ∀ l, q l (x (l + 1)) = x l}
  have hT : MeasurableSet T := by
    simp only [T, Set.ofPred_forall]
    exact MeasurableSet.iInter fun l => measurableSet_eq_fun
      ((measurable_of_countable (q l)).comp (measurable_pi_apply (l + 1)))
      (measurable_pi_apply l)
  have hνT : ∀ᵐ y ∂(ν : Measure X), D y ∈ T := by
    change ∀ᵐ y ∂(ν : Measure X), ∀ l, q l (D y (l + 1)) = D y l
    rw [ae_all_iff]
    intro l
    filter_upwards [hcoordSupport (l + 1)] with y hy
    obtain ⟨b, hb⟩ := hy
    change q l (last (l + 1) ((y 0).val (l + 1))) = last l ((y 0).val l)
    rw [← hb, last_e]
    have hyThread := (y 0).property l
    rw [← hb, pe] at hyThread
    rw [← hyThread, last_e]
  have hMT : ∀ᵐ x ∂M, x ∈ T := by
    exact (ae_map_iff hD.aemeasurable hT).mpr hνT
  have hEmbed : MeasurableEmbedding ((↑) : Thread B q → ((l : ℕ) → B l)) :=
    MeasurableEmbedding.subtype_coe hT
  have hRange : ∀ᵐ x ∂M, x ∈ range ((↑) : Thread B q → ((l : ℕ) → B l)) := by
    filter_upwards [hMT] with x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  let μ : ProbabilityMeasure (Thread B q) :=
    ⟨M.comap ((↑) : Thread B q → ((l : ℕ) → B l)), hEmbed.isProbabilityMeasure_comap hRange⟩
  have hμcoe : (μ : Measure _).map ((↑) : Thread B q → ((l : ℕ) → B l)) = M := by
    change (M.comap ((↑) : Thread B q → ((l : ℕ) → B l))).map (↑) = M
    have hm : (M.comap ((↑) : Thread B q → ((l : ℕ) → B l))).map (↑) = M.restrict T :=
      map_comap_subtype_coe (s := T) hT M
    exact hm.trans (Measure.restrict_eq_self_of_ae_mem hMT)
  have hμ (l : ℕ) : (μ : Measure (Thread B q)).map (fun x : Thread B q => x.val l) = (theta l : Measure (B l)) := by
    have he : (fun x : Thread B q => x.val l) =
        (fun x : (k : ℕ) → B k => x l) ∘ ((↑) : Thread B q → ((k : ℕ) → B k)) := rfl
    rw [he, ← Measure.map_map (measurable_pi_apply l) measurable_subtype_coe, hμcoe]
    exact hMcoord l
  refine ⟨μ, hμ, ?_⟩
  intro η hη
  apply Subtype.ext
  let c : Thread B q → Fin 1 → Thread B q := fun x _ => x
  have hc : Measurable c := measurable_pi_lambda _ fun _ => measurable_id
  have hlevB (l : ℕ) : Measurable (levelProjection q 1 l) :=
    measurable_pi_lambda _ fun j =>
      (measurable_pi_apply l).comp (measurable_subtype_coe.comp (measurable_pi_apply j))
  have hsame (l : ℕ) : ((η : Measure _).map c).map (levelProjection q 1 l) =
      ((μ : Measure _).map c).map (levelProjection q 1 l) := by
    let cl : B l → Fin 1 → B l := fun x _ => x
    have hcl : Measurable cl := measurable_pi_lambda _ fun _ => measurable_id
    have hπ : Measurable (fun x : Thread B q => x.val l) :=
      (measurable_pi_apply l).comp measurable_subtype_coe
    rw [Measure.map_map (hlevB l) hc, Measure.map_map (hlevB l) hc]
    change (η : Measure _).map (cl ∘ (fun x : Thread B q => x.val l)) =
      (μ : Measure _).map (cl ∘ (fun x : Thread B q => x.val l))
    rw [← Measure.map_map hcl hπ, ← Measure.map_map hcl hπ, hη l, hμ l]
  have hz : measurableTotalVariation ((η : Measure _).map c) ((μ : Measure _).map c) = 0 := by
    rw [total_variation_eq_iSup_level q 1]
    simp only [hsame, measurableTotalVariation, tsub_self, max_self, iSup_const]
  apply Measure.ext
  intro A hA
  let E : Set (Fin 1 → Thread B q) := (fun y => y 0) ⁻¹' A
  have hE : MeasurableSet E := (measurable_pi_apply 0) hA
  have hg := le_iSup (fun s : {s : Set (Fin 1 → Thread B q) // MeasurableSet s} =>
    max (((η : Measure _).map c) s.val - ((μ : Measure _).map c) s.val)
      (((μ : Measure _).map c) s.val - ((η : Measure _).map c) s.val)) ⟨E, hE⟩
  change max (((η : Measure _).map c) E - ((μ : Measure _).map c) E)
    (((μ : Measure _).map c) E - ((η : Measure _).map c) E) ≤
    measurableTotalVariation ((η : Measure _).map c) ((μ : Measure _).map c) at hg
  rw [hz, Measure.map_apply hc hE, Measure.map_apply hc hE] at hg
  have hcE : c ⁻¹' E = A := rfl
  rw [hcE] at hg
  exact le_antisymm
    (tsub_eq_zero_iff_le.mp (le_antisymm ((le_max_left _ _).trans hg) bot_le))
    (tsub_eq_zero_iff_le.mp (le_antisymm ((le_max_right _ _).trans hg) bot_le))

end D5.S3.Estimation.DataProcessing.FiniteTowerProbabilityExtension
