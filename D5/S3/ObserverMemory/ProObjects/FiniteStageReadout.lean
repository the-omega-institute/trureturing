/- GID: D5/S3/ObserverMemory/ProObjects/FiniteStageReadout
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ProObjects/FiniteStageReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ordinary readouts from cofiltered systems have single-stage representatives. -/

/- Library-search audit trail (2026-08-20):
   * Pinned-mathlib searches for pro-categories, constant pro-objects, pro-object morphisms, and
     stage representatives found no pro-category API matching the source statement.
   * Exact hit `Functor.ιColimitType_jointly_surjective` in
     `CategoryTheory.Limits.Types.ColimitType` says every element of the standard colimit quotient
     comes from one component. It is applied directly below.
   * `CategoryTheory.IsCofiltered` supplies the source's cofiltered index-category hypothesis.
     Repository searches found no duplicate finite-stage readout theorem.
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Mathlib.Data.Complex.Basic

namespace D5.S3.ObserverMemory.ProObjects.FiniteStageReadout

open CategoryTheory ConcreteCategory

universe u v w z

/-- Stage maps into an ordinary target, transported contravariantly along refinement maps. -/
def stageReadoutFunctor {C : Type u} [Category.{v} C]
    {I : Type w} [Category.{z} I] (stages : I ⥤ C) (target : C) : Iᵒᵖ ⥤ Type v where
  obj i := stages.obj i.unop ⟶ target
  map f := ↾(fun readout => stages.map f.unop ≫ readout)
  map_id i := by
    ext readout
    simp
  map_comp f g := by
    ext readout
    simp

/-- An ordinary readout is the filtered colimit of the maps from individual stages. -/
def OrdinaryReadout {C : Type u} [Category.{v} C]
    {I : Type w} [Category.{z} I] (stages : I ⥤ C) (target : C) : Type (max w v) :=
  (stageReadoutFunctor stages target).ColimitType

/-- The component type of maps from stage `i` into the ordinary target. -/
abbrev StageReadout {C : Type u} [Category.{v} C]
    {I : Type w} [Category.{z} I] (stages : I ⥤ C) (target : C) (i : I) :=
  (stageReadoutFunctor stages target).obj (Opposite.op i)

/-- The ordinary readout represented by one map out of one presentation stage. -/
def representedReadout {C : Type u} [Category.{v} C]
    {I : Type w} [Category.{z} I] (stages : I ⥤ C) (target : C)
    (i : I) (readout : StageReadout stages target i) : OrdinaryReadout stages target :=
  (stageReadoutFunctor stages target).ιColimitType (Opposite.op i) readout

private theorem exists_stage_representative {C : Type u} [Category.{v} C]
    {I : Type w} [Category.{z} I] [IsCofiltered I]
    (stages : I ⥤ C) (target : C) (readout : OrdinaryReadout stages target) :
    ∃ (i : I) (stageReadout : StageReadout stages target i),
      representedReadout stages target i stageReadout = readout := by
  obtain ⟨i, stageReadout, hrepresent⟩ :=
    (stageReadoutFunctor stages target).ιColimitType_jointly_surjective readout
  refine ⟨i.unop, by simpa only [StageReadout, Opposite.op_unop] using stageReadout, ?_⟩
  simpa [representedReadout, OrdinaryReadout] using hrepresent

/-- Every ordinary readout into a constant target is represented at one stage. The same conclusion
is stated explicitly for real- and complex-valued readouts of any type-valued stage system. -/
theorem every_ordinary_readout_has_finite_stage
    {C : Type u} [Category.{v} C] {I : Type w} [Category.{z} I] [IsCofiltered I]
    (stages : I ⥤ C) (target : C) (typeStages : I ⥤ Type) :
    (∀ readout : OrdinaryReadout stages target,
      ∃ (i : I) (stageReadout : StageReadout stages target i),
        representedReadout stages target i stageReadout = readout) ∧
    (∀ readout : OrdinaryReadout typeStages ℝ,
      ∃ (i : I) (stageReadout : StageReadout typeStages ℝ i),
        representedReadout typeStages ℝ i stageReadout = readout) ∧
    (∀ readout : OrdinaryReadout typeStages ℂ,
      ∃ (i : I) (stageReadout : StageReadout typeStages ℂ i),
        representedReadout typeStages ℂ i stageReadout = readout) := by
  exact ⟨exists_stage_representative stages target,
    exists_stage_representative typeStages ℝ,
    exists_stage_representative typeStages ℂ⟩

/-- A one-stage system with a real-valued constant map witnesses inhabitance of the construction. -/
theorem real_readout_single_stage_witness :
    let stages : Discrete PUnit ⥤ Type := (Functor.const (Discrete PUnit)).obj Unit
    ∃ readout : OrdinaryReadout stages ℝ,
      ∃ (i : Discrete PUnit) (stageReadout : StageReadout stages ℝ i),
        representedReadout stages ℝ i stageReadout = readout := by
  dsimp
  let i : Discrete PUnit := ⟨PUnit.unit⟩
  let stageReadout :
      StageReadout ((Functor.const (Discrete PUnit)).obj Unit) ℝ i := ↾(fun _ => 0)
  let readout := representedReadout ((Functor.const (Discrete PUnit)).obj Unit) ℝ i stageReadout
  exact ⟨readout, i, stageReadout, rfl⟩

end D5.S3.ObserverMemory.ProObjects.FiniteStageReadout
