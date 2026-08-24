/- GID: D5/S3/ConceptDynamics/DefinitionEscape/DefinitionUniverseKernel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/DefinitionUniverseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Definitions form a dependent universe ordered by their equality kernels. -/

import D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
import D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-24):
   * Type-shape searches `rg -n 'Set \(X × X\)|Setoid\.ker|ker_def|kernel'
     D5/S3/ConceptDynamics --glob '*.lean'` and
     `rg -n 'Σ\s*[A-Za-z_][A-Za-z0-9_]*\s*:\s*Type[^,]*,\s*(Concept|[^\n]*→)'
     D5 --glob '*.lean'` found the canonical `Setoid.ker` uses and dependent
     fiber Sigma types, but no Sigma package of all codomain/readout pairs.
   * Synonym searches for definition universe/space/family, meta-definition,
     generator, transformer, and research method found no matching D5
     declaration. Searches for equal kernels, mutual refinement, and equivalent
     readouts found `ConceptEquivalent`, `Refines`, and
     `concept_kernel_order_duality`; they are imported below. `Refines` is
     factorization and agrees with reverse kernel inclusion for effective
     (surjective) readouts, so it cannot replace the source's unrestricted
     kernel-order definition.
   * Image/range/surjectivity searches found the canonical repository use of
     `Set.range` in `RefinementRiskCostTradeoff` and pinned Mathlib theorem
     `Set.range_eq_univ`; both are reused rather than reproved.
   * Neighbor-vocabulary commands `ls D5/S3/ConceptDynamics/DefinitionEscape`
     and `git grep -n -E '^def |^  def ' -- D5/S3/ConceptDynamics | head -60`
     found `blindResidual`, `languageExtension`, `finiteSelectionSufficient`,
     and `blindKernelReductionMeasure`, none of which packages a definition,
     its realized image, or the higher-order type constructors below.
   * Exact atom-id search outside the digestion ledger and source documentation
     missed. Searches for `DState|DefinitionState|ResidualState` found no D5
     type family, so the two state families remain explicit inputs exactly as
     in the source's "given definition state and residual state" clause. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.DefinitionUniverseKernel

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
open D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

universe u v w

/-- The universe of definitions on `X`: a codomain together with a concept
readout into that codomain. -/
def DefinitionUniverse (X : Type u) :=
  Sigma (fun D : Type u => Concept X D)

/-- The equality kernel of a packaged definition. -/
def definitionKernel {X : Type u} (definition : DefinitionUniverse X) : Setoid X :=
  Setoid.ker definition.2

/-- The coordinates actually realized by a packaged definition. -/
def definitionImage {X : Type u} (definition : DefinitionUniverse X) : Set definition.1 :=
  Set.range definition.2

/-- Packaged definitions are conceptually equivalent when they induce the same
equality kernel on the source. -/
def DefinitionEquivalent {X : Type u}
    (left right : DefinitionUniverse X) : Prop :=
  definitionKernel left = definitionKernel right

/-- A packaged definition refines another exactly when its kernel is smaller;
the argument order follows the source's coarse-to-fine convention. -/
def DefinitionRefines {X : Type u}
    (coarse fine : DefinitionUniverse X) : Prop :=
  definitionKernel fine <= definitionKernel coarse

/-- Definitions whose objects are themselves packaged definitions. -/
def MetaDefinitionUniverse (X : Type u) :=
  DefinitionUniverse (DefinitionUniverse X)

/-- A family indexed by `S` that generates packaged definitions on `X`. -/
def DefinitionGenerator (X : Type u) (S : Type v) :=
  S -> DefinitionUniverse X

/-- A transformer maps packaged definitions on one source to packaged
definitions on another source. -/
def DefinitionTransformer (X : Type u) (Y : Type v) :=
  DefinitionUniverse X -> DefinitionUniverse Y

/-- Given definition-state and residual-state families, a research method maps
their joint state to the next packaged definition. -/
def DefinitionMethod
    (DState Residual : Type u -> Type v) (X : Type u) :=
  DState X × Residual X -> DefinitionUniverse X

@[simp]
theorem mem_definition_image_iff
    {X : Type u} (definition : DefinitionUniverse X) (z : definition.1) :
    z ∈ definitionImage definition <-> ∃ x : X, definition.2 x = z := by
  rfl

theorem definition_image_eq_univ_iff_surjective
    {X : Type u} (definition : DefinitionUniverse X) :
    definitionImage definition = Set.univ <->
      Function.Surjective definition.2 := by
  simpa only [definitionImage] using
    (Set.range_eq_univ (f := definition.2))

theorem definition_equivalent_iff_mutual_refinement
    {X : Type u} (left right : DefinitionUniverse X) :
    DefinitionEquivalent left right <->
      DefinitionRefines left right ∧ DefinitionRefines right left := by
  constructor
  · intro equalKernels
    change definitionKernel left = definitionKernel right at equalKernels
    constructor
    · change definitionKernel right <= definitionKernel left
      rw [equalKernels]
    · change definitionKernel left <= definitionKernel right
      rw [equalKernels]
  · rintro ⟨leftToRight, rightToLeft⟩
    change definitionKernel right <= definitionKernel left at leftToRight
    change definitionKernel left <= definitionKernel right at rightToLeft
    exact le_antisymm rightToLeft leftToRight

/-- On effective definitions, the source's kernel order is exactly the
repository's canonical factorization refinement. -/
theorem surjective_definition_refines_iff_refines
    {X : Type u} (coarse fine : DefinitionUniverse X)
    (coarseEffective : Function.Surjective coarse.2)
    (fineEffective : Function.Surjective fine.2) :
    DefinitionRefines coarse fine <-> Refines coarse.2 fine.2 := by
  let coarseConcept : EffectiveConcept X :=
    { Coordinate := coarse.1
      readout := coarse.2
      effective := coarseEffective }
  let fineConcept : EffectiveConcept X :=
    { Coordinate := fine.1
      readout := fine.2
      effective := fineEffective }
  simpa only [DefinitionRefines, definitionKernel, coarseConcept, fineConcept] using
    ((concept_kernel_order_duality X).2.1 coarseConcept fineConcept).symm

/-- With effective coordinate types, kernel equality also agrees with the
repository's mutual-factorization concept equivalence. -/
theorem surjective_definition_equivalent_iff_concept_equivalent
    {X : Type u} (left right : DefinitionUniverse X)
    (leftEffective : Function.Surjective left.2)
    (rightEffective : Function.Surjective right.2) :
    DefinitionEquivalent left right <-> ConceptEquivalent left.2 right.2 := by
  rw [definition_equivalent_iff_mutual_refinement, ConceptEquivalent,
    surjective_definition_refines_iff_refines left right leftEffective rightEffective,
    surjective_definition_refines_iff_refines right left rightEffective leftEffective]

/-- All clauses of the definition-universe specification: Sigma packaging,
kernel, realized image, equivalence, refinement, the meta-universe, generators,
transformers, and higher-order research methods. -/
theorem definition_universe_kernel
    {X : Type u} {Y : Type v} {S : Type w}
    (DState Residual : Type u -> Type w)
    (left right : DefinitionUniverse X) :
    (DefinitionUniverse X = Sigma (fun D : Type u => Concept X D)) ∧
      (definitionKernel left = Setoid.ker left.2) ∧
      (∀ x y : X, definitionKernel left x y <-> left.2 x = left.2 y) ∧
      (definitionImage left = Set.range left.2) ∧
      (∀ z : left.1, z ∈ definitionImage left <->
        ∃ x : X, left.2 x = z) ∧
      (definitionImage left = Set.univ <-> Function.Surjective left.2) ∧
      (DefinitionEquivalent left right <->
        definitionKernel left = definitionKernel right) ∧
      (DefinitionRefines left right <->
        definitionKernel right <= definitionKernel left) ∧
      (DefinitionEquivalent left right <->
        DefinitionRefines left right ∧ DefinitionRefines right left) ∧
      (MetaDefinitionUniverse X = DefinitionUniverse (DefinitionUniverse X)) ∧
      (DefinitionGenerator X S = (S -> DefinitionUniverse X)) ∧
      (DefinitionTransformer X Y =
        (DefinitionUniverse X -> DefinitionUniverse Y)) ∧
      (DefinitionMethod DState Residual X =
        (DState X × Residual X -> DefinitionUniverse X)) := by
  refine ⟨rfl, rfl, ?_, rfl, ?_, ?_, Iff.rfl, Iff.rfl, ?_, rfl, rfl, rfl, rfl⟩
  · intro x y
    rfl
  · exact mem_definition_image_iff left
  · exact definition_image_eq_univ_iff_surjective left
  · exact definition_equivalent_iff_mutual_refinement left right

/-- Downstream probe: kernel equality exposes both directed refinement facts
through the public proposition. -/
example {X : Type u} (left right : DefinitionUniverse X)
    (equivalent : DefinitionEquivalent left right) :
    DefinitionRefines left right ∧ DefinitionRefines right left :=
  (definition_equivalent_iff_mutual_refinement left right).1 equivalent

/-- Constant and identity definitions on `Bool` give a proper effective
coarse-to-fine refinement, so neither the kernel order nor its bridge to
`Refines` is vacuous. -/
example :
    let coarse : DefinitionUniverse Bool := ⟨Unit, fun _ => ()⟩
    let fine : DefinitionUniverse Bool := ⟨Bool, id⟩
    DefinitionRefines coarse fine ∧
      Refines coarse.2 fine.2 ∧
      definitionKernel coarse false true ∧
      ¬DefinitionEquivalent coarse fine := by
  dsimp only
  let coarse : DefinitionUniverse Bool := ⟨Unit, fun _ => ()⟩
  let fine : DefinitionUniverse Bool := ⟨Bool, id⟩
  have coarseEffective : Function.Surjective coarse.2 :=
    fun _ => ⟨false, rfl⟩
  have fineEffective : Function.Surjective fine.2 := Function.surjective_id
  have factorization : Refines coarse.2 fine.2 := ⟨fun _ => (), rfl⟩
  have kernelRefinement : DefinitionRefines coarse fine :=
    (surjective_definition_refines_iff_refines
      coarse fine coarseEffective fineEffective).2 factorization
  refine ⟨kernelRefinement, factorization, rfl, ?_⟩
  intro equalKernels
  have falseEqualsTrue : false = true := by
    have : definitionKernel fine false true := by
      rw [← equalKernels]
      rfl
    exact this
  exact Bool.false_ne_true falseEqualsTrue

/-- A constant Boolean-valued definition misses `true`; its realized image is
not universally full and its readout is not surjective. -/
example :
    let partialDefinition : DefinitionUniverse Bool := ⟨Bool, fun _ => false⟩
    true ∉ definitionImage partialDefinition ∧
      definitionImage partialDefinition ≠ Set.univ ∧
      ¬Function.Surjective partialDefinition.2 := by
  dsimp only
  let partialDefinition : DefinitionUniverse Bool := ⟨Bool, fun _ => false⟩
  have trueMissing : true ∉ definitionImage partialDefinition := by
    change ¬∃ x : Bool, (fun _ : Bool => false) x = true
    rintro ⟨_, falseEqualsTrue⟩
    exact Bool.false_ne_true falseEqualsTrue
  have imageNotUniversal : definitionImage partialDefinition ≠ Set.univ := by
    intro imageUniversal
    apply trueMissing
    rw [imageUniversal]
    exact Set.mem_univ true
  have notSurjective : ¬Function.Surjective partialDefinition.2 := by
    intro surjective
    exact imageNotUniversal
      ((definition_image_eq_univ_iff_surjective partialDefinition).2 surjective)
  exact ⟨trueMissing, imageNotUniversal, notSurjective⟩

#print axioms definition_universe_kernel

end D5.S3.ConceptDynamics.DefinitionEscape.DefinitionUniverseKernel
