/- GID: D5/S3/ConceptDynamics/RefinementFactorization/SufficiencyEscapeEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/SufficiencyEscapeEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four sufficient target conditions agree on realized readout images. -/

import D5.S3.ConceptDynamics.DefinitionEscapeLaws.DirectlyProvableLaws
import D5.S3.ConceptDynamics.Refinement.InductiveSufficiency
import D5.S3.ConceptDynamics.Transportability.ModelClassTransportabilityCriterion
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-26):
   * Shape search `rg -n 'Set \(X × X\)' D5` found the canonical
     `TargetRisk.RefinementRiskCostTradeoff.defectRelation`. It is imported; this
     module introduces no second residual, escape relation, kernel, or fiber predicate.
   * English synonym search for escape/residual/defect, kernel/inclusion,
     fiber/fibre/constant/constancy, factor/factorization/descent, and image/range
     found the exact local components `directly_provable_laws` (empty defect iff
     `Function.FactorsThrough`), `model_class_transportability_criterion` (empty
     defect iff reverse kernel inclusion), and `inductive_sufficiency_criterion`
     (`Function.FactorsThrough` iff descent through the realized image). All three
     are applied directly.
     `CompleteObservationExpressibilityCriterion` and `InterventionTargetFactorization`
     concern joint families. `ModelClassTransportabilityCriterion.1` instead states
     uniqueness of a computation into `Set.range target`, so it is adjacent rather
     than the exact third-to-fourth-clause equivalence used here.
   * Chinese synonym search `rg -n '逃逸|残差|缺陷|核包含|纤维|常值|因子化|实现像|下降|充分性'
     D5/S3/ConceptDynamics docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md`
     confirmed the source vocabulary and the existing canonical residual/fiber modules.
   * Neighbor inventory `git grep -n '^def \|^  def ' --
     D5/S3/ConceptDynamics/RefinementFactorization | head -60` found no local
     residual or fiber definition to reuse. The directory has ten Lean files before
     this addition; the suggested `Refinement` and `Sufficiency` directories each
     already have twelve, so route placed this module here without crossing SL-003.
   * Pinned Mathlib search found `Function.FactorsThrough` and
     `Function.factorsThrough_iff` in `Mathlib/Logic/Function/Basic.lean`, plus
     `Set.rangeFactorization` in `Mathlib/Data/Set/Operations.lean`. The whole-codomain
     theorem is not used because it requires `[Nonempty Y]`, absent from the source;
     the realized-image theorem imported above has no such restriction. `loogle` and
     `leansearch` were not on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.SufficiencyEscapeEquivalence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.DirectlyProvableLaws
open D5.S3.ConceptDynamics.Refinement.InductiveSufficiency
open D5.S3.ConceptDynamics.Transportability.ModelClassTransportabilityCriterion

universe u v w

/-- Empty target escape, reverse kernel inclusion, target constancy on each
readout fiber, and target descent through the realized readout image are four
equivalent conditions. No carrier is assumed inhabited. -/
theorem sufficiency_escape_equivalence_tfae
    {X : Type u} {Coordinate : Type v} {Target : Type w}
    (q : Concept X Coordinate) (target : Concept X Target) :
    List.TFAE [
      defectRelation q target = ∅,
      Setoid.ker q ≤ Setoid.ker target,
      Function.FactorsThrough target q,
      ∃ descend : Set.range q → Target,
        target = descend ∘ Set.rangeFactorization q] := by
  have emptyIffFibers :
      defectRelation q target = ∅ ↔ Function.FactorsThrough target q :=
    directly_provable_laws.{0, 0, 0, 0, u, v, w,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}.2.1
        q target
  have transportability := model_class_transportability_criterion q target
  have emptyIffKernel :
      defectRelation q target = ∅ ↔ Setoid.ker q ≤ Setoid.ker target :=
    transportability.2
  tfae_have 1 ↔ 2 := emptyIffKernel
  tfae_have 1 ↔ 3 := emptyIffFibers
  tfae_have 3 ↔ 4 := by
    exact (inductive_sufficiency_criterion q target).1
  tfae_finish

/-- Identity readout and target realize all four sufficient conditions, with two
distinct realized coordinates so the factorization is not a singleton collapse. -/
theorem identity_readout_sufficiency_witness :
    let q : Concept Bool Bool := id
    let target : Concept Bool Bool := id
    defectRelation q target = ∅ ∧
      Setoid.ker q ≤ Setoid.ker target ∧
      Function.FactorsThrough target q ∧
      (∃ descend : Set.range q → Bool,
        target = descend ∘ Set.rangeFactorization q) ∧
      ∃ left right : Set.range q, left ≠ right := by
  let q : Concept Bool Bool := id
  let target : Concept Bool Bool := id
  have equivalence := sufficiency_escape_equivalence_tfae q target
  have emptyEscape : defectRelation q target = ∅ := by
    ext pair
    constructor
    · rintro ⟨sameReadout, differentTarget⟩
      exact (differentTarget sameReadout).elim
    · intro impossible
      exact impossible.elim
  have kernelInclusion : Setoid.ker q ≤ Setoid.ker target :=
    (equivalence.out 0 1).mp emptyEscape
  have fiberConstancy : Function.FactorsThrough target q :=
    (equivalence.out 1 2).mp kernelInclusion
  have imageDescent :
      ∃ descend : Set.range q → Bool,
        target = descend ∘ Set.rangeFactorization q :=
    (equivalence.out 2 3).mp fiberConstancy
  have distinctRange :
      ∃ left right : Set.range q, left ≠ right := by
    refine ⟨Set.rangeFactorization q false,
      Set.rangeFactorization q true, ?_⟩
    intro sameRange
    exact Bool.false_ne_true (congrArg Subtype.val sameRange)
  exact ⟨emptyEscape, kernelInclusion, fiberConstancy, imageDescent, distinctRange⟩

/-- A constant readout with the identity target falsifies every one of the four
conditions, while the canonical defect contains the concrete pair `(false, true)`. -/
theorem constant_readout_escape_witness :
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    ¬defectRelation q target = ∅ ∧
      ¬Setoid.ker q ≤ Setoid.ker target ∧
      ¬Function.FactorsThrough target q ∧
      (¬∃ descend : Set.range q → Bool,
        target = descend ∘ Set.rangeFactorization q) ∧
      (false, true) ∈ defectRelation q target := by
  let q : Concept Bool Unit := fun _ => ()
  let target : Concept Bool Bool := id
  have equivalence := sufficiency_escape_equivalence_tfae q target
  have escapedPair : (false, true) ∈ defectRelation q target :=
    ⟨rfl, Bool.false_ne_true⟩
  have nonemptyEscape : ¬defectRelation q target = ∅ := by
    intro emptyEscape
    rw [emptyEscape] at escapedPair
    exact escapedPair
  have noKernelInclusion : ¬Setoid.ker q ≤ Setoid.ker target := by
    intro kernelInclusion
    exact nonemptyEscape ((equivalence.out 0 1).mpr kernelInclusion)
  have noFiberConstancy : ¬Function.FactorsThrough target q := by
    intro fiberConstancy
    exact nonemptyEscape ((equivalence.out 0 2).mpr fiberConstancy)
  have noImageDescent :
      ¬∃ descend : Set.range q → Bool,
        target = descend ∘ Set.rangeFactorization q := by
    intro imageDescent
    exact nonemptyEscape ((equivalence.out 0 3).mpr imageDescent)
  exact ⟨nonemptyEscape, noKernelInclusion, noFiberConstancy,
    noImageDescent, escapedPair⟩

/-- Fail-closed presence consumer for both named nonvacuity witnesses. -/
theorem sufficiency_escape_equivalence_nonvacuous :
    (let q : Concept Bool Bool := id
     let target : Concept Bool Bool := id
     defectRelation q target = ∅ ∧
       Setoid.ker q ≤ Setoid.ker target ∧
       Function.FactorsThrough target q ∧
       (∃ descend : Set.range q → Bool,
         target = descend ∘ Set.rangeFactorization q) ∧
       ∃ left right : Set.range q, left ≠ right) ∧
    (let q : Concept Bool Unit := fun _ => ()
     let target : Concept Bool Bool := id
     ¬defectRelation q target = ∅ ∧
       ¬Setoid.ker q ≤ Setoid.ker target ∧
       ¬Function.FactorsThrough target q ∧
       (¬∃ descend : Set.range q → Bool,
         target = descend ∘ Set.rangeFactorization q) ∧
       (false, true) ∈ defectRelation q target) :=
  ⟨identity_readout_sufficiency_witness,
    constant_readout_escape_witness⟩

#print axioms sufficiency_escape_equivalence_tfae

end D5.S3.ConceptDynamics.RefinementFactorization.SufficiencyEscapeEquivalence
