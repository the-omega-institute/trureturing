/- GID: D5/S3/ConceptDynamics/DefinitionEscapeLaws/MarginalCaptureLawBridge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeLaws/MarginalCaptureLawBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite additive escape mass discharges the canonical marginal capture law. -/

import D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCaptureWitnesses

/- Library-search audit trail (2026-08-27):
   * Direct-import inventory: this module imports only
     `SubmodularCaptureWitnesses`. The command `grep -nE
     '^(theorem|def|structure|abbrev|noncomputable def) '
     D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCaptureWitnesses.lean`
     enumerated all thirteen exported declarations: the fixed-language,
     subset-premise, constant-zero-weight, and finite-additivity witnesses;
     `clause_one_false_neighbor_witness` through
     `clause_eight_false_neighbor_witness`; and
     `submodular_capture_witnesses_nonvacuous`.
   * Shape comparison within that direct import found exactly one declaration
     with the same finite-additive marginal inequality, inclusion, freshness,
     and finite-right-set premises:
     `clause_six_false_neighbor_witness`. It is reused below. Clauses one--five,
     seven, and eight concern different conclusions; the four premise/model
     witnesses and package consumer have different quantifier shapes and do
     not replace either the bridge or its positive witness.
   * Type-shape search `rg -n 'Set \(X × X\)' D5/S3/ConceptDynamics`
     found the canonical `defectRelation`, `EscapeWeight`, and neighboring
     relation-valued declarations. This module introduces no relation, residual,
     mass, kernel, readout, or coverage definition.
   * English and Chinese synonym search `rg -n '边际捕获|边际增益|收益递减|递减|
     次模|加权覆盖|有限可加|marginal gain|decreasing return|diminishing return|
     submodular|weighted cover|finite additive|additive mass'
     D5/S3/ConceptDynamics docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md`
     found the exact repository proposition `marginalCaptureLaw`, its weak-weight
     countermodel, and the exact additive theorem `submodular_capture`. The sixth
     conjunct of that theorem is the required diminishing-return inequality and
     is reused below instead of reproved.
   * Declaration search `rg -n 'marginalCaptureLaw|marginal.*capture|diminishing|
     submodular|Submodular|weighted cover|finite additivity|mass_additive'
     D5/S3/ConceptDynamics` also found `WeightedResidualCoverage`, whose carrier
     is a finite shared-codomain specialization, and `MeasureCapture`, whose
     captured-set theorem does not itself state the imported two-step CAS
     `marginalCaptureLaw`. Neither replaces the exact hit above.
   * Neighbor vocabulary inspection `ls D5/S3/ConceptDynamics/DefinitionEscape
     D5/S3/ConceptDynamics/DefinitionEscapeLaws` and `git grep -n -E
     '^def |^  def |^noncomputable def ' -- D5/S3/ConceptDynamics | head -60`
     found the existing dependent `jointReadout`, `residualEscapeMass`,
     `capturedEscapeMass`, and `marginalCaptureLaw`; all are reused unchanged.
   * Pinned-Mathlib shape search `rg -n 'ncard_union|ncard.*Disjoint|
     Disjoint.*ncard' .lake/packages/mathlib/Mathlib D5` found
     `Set.ncard_union_eq`, but no stronger generic bridge is needed because the
     repository theorem is an exact match.
   * Source-sketch scan `grep -nE '^(structure|theorem|def|abbrev) '
     docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md` found no Lean
     sketch for this marginal law. Its canonical formal types are therefore the
     frozen `marginalCaptureLaw` and `submodular_capture` declarations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeLaws.MarginalCaptureLawBridge

open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCapture
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCaptureWitnesses

/-- Finite additivity discharges the canonical CAS marginal-capture proposition.
`Delta.Finite` and nonnegative cost retain the source domain. The projection of
`submodular_capture` uses neither condition as a local proof guard. -/
theorem marginal_capture_law_of_finite_additive_mass
    {I X C Target : Type*} {V : I -> Type*}
    (Gamma Delta : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target) (definition : I)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall candidate, 0 <= cost candidate)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    (delta_source_domain_finite : Delta.Finite) :
    marginalCaptureLaw Gamma Delta definitions q target definition nu := by
  intro premises
  exact (submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).2.2.2.2.2.1 definition
      delta_source_domain_finite premises.1 premises.2

/-- A concrete finite additive model has strictly decreasing marginal capture.
The strict inequality also refutes the one-feature mutation that replaces the
bridge conclusion's `>=` by `<=`. -/
theorem marginal_capture_law_bridge_positive_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then Prod.snd else Prod.fst
    let q : Concept (Bool × Bool) Unit := fun _ => ()
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let firstEdge := ((false, false), (true, false))
    let secondEdge := ((false, false), (false, true))
    let overlapEdge := ((false, false), (true, true))
    let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
      { mass := fun set =>
          (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
          (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
          (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
        empty_mass := by simp
        mass_nonnegative := by intro set; split_ifs <;> norm_num }
    let F := fun S : Set Bool =>
      capturedEscapeMass S definitions q target nu
    marginalCaptureLaw (∅ : Set Bool) {false} definitions q target true nu ∧
      F ((∅ : Set Bool) ∪ {true}) - F ∅ >
        F ({false} ∪ {true}) - F {false} := by
  classical
  dsimp only
  let definitions : Bool -> Concept (Bool × Bool) Bool :=
    fun index => if index then
      (Prod.snd : Concept (Bool × Bool) Bool)
    else (Prod.fst : Concept (Bool × Bool) Bool)
  let q : Concept (Bool × Bool) Unit := fun _ => ()
  let target : Concept (Bool × Bool) (Bool × Bool) := id
  let firstEdge := ((false, false), (true, false))
  let secondEdge := ((false, false), (false, true))
  let overlapEdge := ((false, false), (true, true))
  let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
    { mass := fun set =>
        (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
        (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
        (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
      empty_mass := by simp
      mass_nonnegative := by intro set; split_ifs <;> norm_num }
  let cost : Bool -> Real := fun _ => 1
  let F := fun S : Set Bool =>
    capturedEscapeMass S definitions q target nu
  change marginalCaptureLaw (∅ : Set Bool) {false} definitions q target true nu ∧
    F ((∅ : Set Bool) ∪ {true}) - F ∅ >
      F ({false} ∪ {true}) - F {false}
  have additive : forall left right : Set ((Bool × Bool) × (Bool × Bool)),
      Disjoint left right ->
        nu.mass (left ∪ right) = nu.mass left + nu.mass right := by
    intro left right disjoint
    let unionIndicator := fun edge : (Bool × Bool) × (Bool × Bool) =>
      (@ite Real (edge ∈ left ∪ right) (Classical.propDecidable _) 1 0)
    let leftIndicator := fun edge : (Bool × Bool) × (Bool × Bool) =>
      (@ite Real (edge ∈ left) (Classical.propDecidable _) 1 0)
    let rightIndicator := fun edge : (Bool × Bool) × (Bool × Bool) =>
      (@ite Real (edge ∈ right) (Classical.propDecidable _) 1 0)
    have indicator (edge : (Bool × Bool) × (Bool × Bool)) :
        unionIndicator edge = leftIndicator edge + rightIndicator edge := by
      have notBoth : ¬(edge ∈ left ∧ edge ∈ right) := by
        rintro ⟨inLeft, inRight⟩
        exact Set.disjoint_left.1 disjoint inLeft inRight
      by_cases inLeft : edge ∈ left <;> by_cases inRight : edge ∈ right <;>
        simp_all [unionIndicator, leftIndicator, rightIndicator, Set.mem_union]
    dsimp only [nu]
    change
      (unionIndicator firstEdge + unionIndicator secondEdge) +
          unionIndicator overlapEdge =
        ((leftIndicator firstEdge + leftIndicator secondEdge) +
            leftIndicator overlapEdge) +
          ((rightIndicator firstEdge + rightIndicator secondEdge) +
            rightIndicator overlapEdge)
    rw [indicator firstEdge, indicator secondEdge, indicator overlapEdge]
    ring
  have costNonnegative : forall candidate, 0 <= cost candidate := by
    intro candidate
    norm_num [cost]
  have law :
      marginalCaptureLaw (∅ : Set Bool) {false} definitions q target true nu :=
    marginal_capture_law_of_finite_additive_mass
      (∅ : Set Bool) {false} definitions q target true cost nu
      costNonnegative additive (Set.finite_singleton false)
  have strictDecrease :
      F ((∅ : Set Bool) ∪ {true}) - F ∅ >
        F ({false} ∪ {true}) - F {false} := by
    simpa [F, definitions, q, target, firstEdge, secondEdge, overlapEdge, nu,
      cost] using
        (finite_capture_laws_nonvacuous.2.2.2.2.2.1.2)
  exact ⟨law, strictDecrease⟩

/-- Fail-closed consumer for both complete witness statements. Deleting either
named witness leaves a dangling reference; weakening either statement makes
the corresponding projection fail. -/
theorem marginal_capture_law_bridge_nonvacuous :
    (let definitions : Bool -> Concept (Bool × Bool) Bool :=
       fun index => if index then Prod.snd else Prod.fst
     let q : Concept (Bool × Bool) Unit := fun _ => ()
     let target : Concept (Bool × Bool) (Bool × Bool) := id
     let firstEdge := ((false, false), (true, false))
     let secondEdge := ((false, false), (false, true))
     let overlapEdge := ((false, false), (true, true))
     let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
       { mass := fun set =>
           (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
           (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
           (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
         empty_mass := by simp
         mass_nonnegative := by intro set; split_ifs <;> norm_num }
     let F := fun S : Set Bool =>
       capturedEscapeMass S definitions q target nu
     marginalCaptureLaw (∅ : Set Bool) {false} definitions q target true nu ∧
       F ((∅ : Set Bool) ∪ {true}) - F ∅ >
         F ({false} ∪ {true}) - F {false}) ∧
    (forall {I X C Target : Type*} {V : I -> Type*}
      (Gamma Delta : Set I) (definitions : forall i, Concept X (V i))
      (q : Concept X C) (target : Concept X Target) (definition : I)
      (_cost : I -> Real) (nu : EscapeWeight (X × X))
      (_cost_nonnegative : forall candidate, 0 <= _cost candidate)
      (_mass_additive : forall left right : Set (X × X), Disjoint left right ->
        nu.mass (left ∪ right) = nu.mass left + nu.mass right)
      (_delta_source_domain_finite : Delta.Finite)
      (_subset : Gamma ⊆ Delta) (_fresh : definition ∉ Delta),
      ¬capturedEscapeMass (Gamma ∪ {definition}) definitions q target nu -
          capturedEscapeMass Gamma definitions q target nu <
        capturedEscapeMass (Delta ∪ {definition}) definitions q target nu -
          capturedEscapeMass Delta definitions q target nu) := by
  refine ⟨marginal_capture_law_bridge_positive_witness, ?_⟩
  intro I X C Target V Gamma Delta definitions q target definition cost nu
    costNonnegative massAdditive deltaFinite subset fresh
  exact clause_six_false_neighbor_witness definitions q target cost nu
    costNonnegative massAdditive definition deltaFinite subset fresh

#print axioms marginal_capture_law_of_finite_additive_mass
#print axioms marginal_capture_law_bridge_nonvacuous

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.MarginalCaptureLawBridge
