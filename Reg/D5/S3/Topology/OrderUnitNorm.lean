import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.OrderUnitNorm

/-!
# Original order-unit norm source binding

The norm-core family retains every original real normed vector space and its
closed salient cone and interior unit. Its state and output are the entire
candidate real-valued norm function, with identity readout. This binds the
actual source norm without changing the cone or assuming a norm axiom.

The generator family retains each original cone, unit, operator, full algebraic
positive-dual cross-positivity hypothesis and entire exponential orbit. Identity
readout and the source-law equivalence bind cone membership at all nonnegative
times, without assuming preservation or unit fixation.

The quantitative and algebraic Archimedean source scopes retain the original
operator and all real times. Source applications and source bridges are
partial evidence. Whole-family variation, sensitivity,
observational dependence, and raw source-coordinate reconstruction and
occurrence ties are required for a four-slot registration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Topology.OrderUnitNorm

open _root_.D5.S3.Topology.OrderUnitNorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev coreSourceScope.{u} := type_of% (@Data.norm_core.{u})

structure Inputs.{u} where
  E : Type u
  normed : NormedAddCommGroup E
  space : @NormedSpace ℝ E _ normed.toSeminormedAddCommGroup
  data : @Data E normed space

abbrev candidate.{u} (P : Inputs.{u}) := P.E → ℝ

abbrev sourceNorm.{u} (P : Inputs.{u}) : candidate P :=
  letI := P.normed
  letI := P.space
  P.data.orderNorm

abbrev signature.{u} : Signature where
  Params := Inputs.{u}
  State := candidate
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => candidate
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u} : Realization signature.{u} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

abbrev coreLaw.{u} (P : Inputs.{u}) (f : candidate P) : Prop :=
  letI := P.normed
  letI := P.space
  @NormedSpace.Core ℝ P.E _ inferInstance inferInstance ⟨f⟩

abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u}, coreLaw P (R.readout () P (sourceNorm P))

theorem core_source_bridge.{u} : coreSourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.normed
    letI := P.space
    exact h P.data
  · intro h E normed space A
    exact h ⟨E, normed, space, A⟩

theorem core_actual_positive.{u} : arena.{u}.Law actual.{u} :=
  core_source_bridge.mp (@Data.norm_core.{u})

#print axioms core_source_bridge
#print axioms core_actual_positive

abbrev generatorSourceScope.{u} := type_of% (@Data.cross_positive_flow.{u})
abbrev quantitativeSourceScope.{u} := type_of% (@Data.quantitative_generator_iff.{u})
abbrev archimedeanSourceScope.{u} := type_of% (@ArchimedeanData.archimedean_quantitative_generator_iff.{u})

structure GeneratorInputs.{u} extends Inputs.{u} where
  finiteDim : letI := normed; letI := space; FiniteDimensional ℝ E
  operator : letI := normed; letI := space; E →ₗ[ℝ] E
  crossPositive :
    letI := normed
    letI := space
    ∀ z ∈ data.cone, ∀ β : E →ₗ[ℝ] ℝ,
      (∀ v ∈ data.cone, 0 ≤ β v) → β z = 0 → 0 ≤ β (operator z)

abbrev generatorCandidate.{u} (P : GeneratorInputs.{u}) := ℝ → P.E → P.E

abbrev generatorSourceFlow.{u} (P : GeneratorInputs.{u}) : generatorCandidate P :=
  letI := P.normed
  letI := P.space
  letI := P.finiteDim
  fun t y => Data.originalFlow P.operator t y

abbrev generatorSignature.{u} : Signature where
  Params := GeneratorInputs.{u}
  State := generatorCandidate
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => generatorCandidate
  Anchor := Empty
  finiteAnchor := inferInstance

def generatorActual.{u} : Realization generatorSignature.{u} :=
  realize generatorSignature (fun _ _ f => f) (fun e => nomatch e)

abbrev generatorLaw.{u} (P : GeneratorInputs.{u}) (f : generatorCandidate P) : Prop :=
  letI := P.normed
  letI := P.space
  ∀ t : ℝ, 0 ≤ t → ∀ y : P.E, y ∈ P.data.cone → f t y ∈ P.data.cone

abbrev generatorArena.{u} : Arena where
  signature := generatorSignature.{u}
  Law R := ∀ P : GeneratorInputs.{u}, generatorLaw P
    (R.readout () P (generatorSourceFlow P))

theorem generator_source_bridge.{u} :
    generatorSourceScope.{u} ↔ generatorArena.{u}.Law generatorActual.{u} := by
  constructor
  · intro h P
    letI := P.normed
    letI := P.space
    letI := P.finiteDim
    exact h P.data P.operator P.crossPositive
  · intro h E normed space A finiteDim L hcp
    exact h ⟨⟨E, normed, space, A⟩, finiteDim, L, hcp⟩

theorem generator_actual_positive.{u} : generatorArena.{u}.Law generatorActual.{u} :=
  generator_source_bridge.mp (@Data.cross_positive_flow.{u})

theorem quantitative_source_application.{u} : quantitativeSourceScope.{u} :=
  @Data.quantitative_generator_iff.{u}

theorem archimedean_source_application.{u} : archimedeanSourceScope.{u} :=
  @ArchimedeanData.archimedean_quantitative_generator_iff.{u}

#print axioms generator_source_bridge
#print axioms generator_actual_positive
#print axioms quantitative_source_application
#print axioms archimedean_source_application


/-- The original arbitrary carrier, cone and unit; no dimension or completeness fields. -/
abbrev rigiditySourceScope.{u} := type_of% (@Data.identity_dominated_scalar.{u})

abbrev rigidityCandidate.{u} (p : Inputs.{u}) :=
  letI := p.normed
  letI := p.space
  p.E →ₗ[ℝ] p.E

abbrev rigiditySignature.{u} : Signature where
  Params := Inputs.{u}
  State := rigidityCandidate
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => rigidityCandidate
  Anchor := Empty
  finiteAnchor := inferInstance

def rigidityActual.{u} : Realization rigiditySignature.{u} :=
  realize rigiditySignature (fun _ _ op => op) (fun e => nomatch e)

abbrev rigidityArena.{u} : Arena where
  signature := rigiditySignature.{u}
  Law R := ∀ p : Inputs.{u},
    letI := p.normed
    letI := p.space
    ∀ (P : p.E →ₗ[ℝ] p.E) (c : ℝ),
      (∀ v ∈ p.data.cone, P v ∈ p.data.cone ∧ v - P v ∈ p.data.cone) →
      P p.data.unit = c • p.data.unit →
      ∀ v : p.E, R.readout () p P v = c • v

theorem rigidity_source_bridge.{u} :
    rigiditySourceScope.{u} ↔ rigidityArena.{u}.Law rigidityActual.{u} := by
  constructor
  · intro h p
    letI := p.normed
    letI := p.space
    exact h p.data
  · intro h E normed space A
    exact h ⟨E, normed, space, A⟩

theorem rigidity_actual_positive.{u} : rigidityArena.{u}.Law rigidityActual.{u} :=
  rigidity_source_bridge.mp (@Data.identity_dominated_scalar.{u})

#print axioms rigidity_source_bridge
#print axioms rigidity_actual_positive


end Reg.D5.S3.Topology.OrderUnitNorm
