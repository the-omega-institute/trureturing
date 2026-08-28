/- GID: D5/S3/ConceptDynamics/Completion/EscapeZeroCompletionPoint
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/EscapeZeroCompletionPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Faithful escape zero selects the unique audited regularized completion point. -/

import D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
import D5.S3.ConceptDynamics.RefinementFactorization.SufficiencyEscapeEquivalence
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Extr

-- Library-search audit trail (2026-08-28):
-- * Repository searches found the exact four-way theorem
--   `sufficiency_escape_equivalence_tfae`; it supplies the empty-escape iff
--   fiber-constancy/factorization step and is applied directly below.
-- * The canonical repository declarations `Concept`, `conceptJoin`,
--   `defectRelation`, and `EscapeWeight` are reused. `EscapeWeight` alone is not
--   faithful, so the source law `mass set = 0 <-> set = empty` is a premise.
-- * Pinned Mathlib supplies `IsMinOn` and `isMinOn_univ_iff`, the standard
--   proposition that a parameter realizes a global argmin. `Function.argmin`
--   requires a well-founded strict order and cannot select minima of arbitrary
--   real-valued functions. Compact-minimum theorems need source-absent topology.
-- * Loogle returned `isMinOn_univ_iff`. GitHub ecosystem search found only
--   premise-bearing argmin constructions; LeanSearch and Reservoir API probes
--   returned HTTP 404. Full receipt: `/tmp/SEARCH-u1.md`.

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.EscapeZeroCompletionPoint

open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.RefinementFactorization.SufficiencyEscapeEquivalence
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

universe u v w z t

-- The OACTC escape defect of parameter `a`: the faithful weight of the target
-- pairs still identified by the baseline joined with definition `d a`.
def parameterEscapeDefect
    {A : Type u} {X : Type v} {Coordinate : Type w}
    {DefinitionCoordinate : A -> Type z} {Target : Type t}
    (q : Concept X Coordinate)
    (definitions : forall a, Concept X (DefinitionCoordinate a))
    (target : Concept X Target) (weight : EscapeWeight (X × X))
    (a : A) : Real :=
  weight.mass (defectRelation (conceptJoin q (definitions a)) target)

-- The regularized objective `Delta(a) + lambda * Cost(d a)` from OACTC.
def regularizedCompletionObjective
    {A : Type u} {X : Type v} {Coordinate : Type w}
    {DefinitionCoordinate : A -> Type z} {Target : Type t}
    (q : Concept X Coordinate)
    (definitions : forall a, Concept X (DefinitionCoordinate a))
    (target : Concept X Target) (weight : EscapeWeight (X × X))
    (definitionCost : forall a, Concept X (DefinitionCoordinate a) -> Real)
    (lambda : Real) (a : A) : Real :=
  parameterEscapeDefect q definitions target weight a +
    lambda * definitionCost a (definitions a)

-- A low-cost, nonleaking, zero-escape parameter: it globally minimizes the
-- regularized objective, and the target factors through its joint readout with
-- zero faithful escape defect.
def IsAuditedCompletionParameter
    {A : Type u} {X : Type v} {Coordinate : Type w}
    {DefinitionCoordinate : A -> Type z} {Target : Type t}
    (q : Concept X Coordinate)
    (definitions : forall a, Concept X (DefinitionCoordinate a))
    (target : Concept X Target) (weight : EscapeWeight (X × X))
    (definitionCost : forall a, Concept X (DefinitionCoordinate a) -> Real)
    (lambda : Real) (a : A) : Prop :=
  IsMinOn
      (regularizedCompletionObjective q definitions target weight
        definitionCost lambda) Set.univ a ∧
    Function.FactorsThrough target (conceptJoin q (definitions a)) ∧
    parameterEscapeDefect q definitions target weight a = 0

-- Faithful escape zero is equivalent in both directions to target
-- determination by the joined readout. If the source's low-cost, nonleaking,
-- zero-escape parameter exists uniquely, its witness `kappa` realizes the
-- regularized argmin, clears escape, factors the target, and is unique among all
-- parameters with those three auditable properties.
theorem escape_zero_iff_determined_with_audited_minimizer
    {A : Type u} {X : Type v} {Coordinate : Type w}
    {DefinitionCoordinate : A -> Type z} {Target : Type t}
    (q : Concept X Coordinate)
    (definitions : forall a, Concept X (DefinitionCoordinate a))
    (target : Concept X Target) (weight : EscapeWeight (X × X))
    (definitionCost : forall a, Concept X (DefinitionCoordinate a) -> Real)
    (lambda : Real) (a : A)
    (faithfulWeight : forall set, weight.mass set = 0 <-> set = ∅) :
    (parameterEscapeDefect q definitions target weight a = 0 ->
      Function.FactorsThrough target (conceptJoin q (definitions a))) ∧
    (Function.FactorsThrough target (conceptJoin q (definitions a)) ->
      parameterEscapeDefect q definitions target weight a = 0) ∧
    ((uniqueCompletion : ∃! kappa,
      IsAuditedCompletionParameter q definitions target weight
        definitionCost lambda kappa) ->
      let kappa := uniqueCompletion.choose
      IsMinOn
        (regularizedCompletionObjective q definitions target weight
          definitionCost lambda) Set.univ kappa ∧
      parameterEscapeDefect q definitions target weight kappa = 0 ∧
      Function.FactorsThrough target (conceptJoin q (definitions kappa)) ∧
      forall candidate,
        IsAuditedCompletionParameter q definitions target weight
          definitionCost lambda candidate ->
        candidate = kappa) := by
  have equivalence (parameter : A) :=
    sufficiency_escape_equivalence_tfae
      (conceptJoin q (definitions parameter)) target
  have zeroImpliesDetermined :
      parameterEscapeDefect q definitions target weight a = 0 ->
        Function.FactorsThrough target (conceptJoin q (definitions a)) := by
    intro zeroDefect
    have emptyEscape :
        defectRelation (conceptJoin q (definitions a)) target = ∅ := by
      exact (faithfulWeight _).mp zeroDefect
    exact (equivalence a).out 0 2 |>.mp emptyEscape
  have determinedImpliesZero :
      Function.FactorsThrough target (conceptJoin q (definitions a)) ->
        parameterEscapeDefect q definitions target weight a = 0 := by
    intro determined
    have emptyEscape :
        defectRelation (conceptJoin q (definitions a)) target = ∅ :=
      (equivalence a).out 0 2 |>.mpr determined
    exact (faithfulWeight _).mpr emptyEscape
  refine ⟨zeroImpliesDetermined, determinedImpliesZero, ?_⟩
  intro uniqueCompletion
  let kappa := uniqueCompletion.choose
  have selected :
      IsAuditedCompletionParameter q definitions target weight
        definitionCost lambda kappa :=
    uniqueCompletion.choose_spec.1
  exact ⟨selected.1, selected.2.2, selected.2.1, fun candidate candidateAudit =>
      uniqueCompletion.choose_spec.2 candidate candidateAudit⟩

-- Reverse probe for CAS-A2: the public reverse leaf recovers zero escape from
-- target determination, rather than merely restating the forward implication.
example
    {A : Type u} {X : Type v} {Coordinate : Type w}
    {DefinitionCoordinate : A -> Type z} {Target : Type t}
    (q : Concept X Coordinate)
    (definitions : forall a, Concept X (DefinitionCoordinate a))
    (target : Concept X Target) (weight : EscapeWeight (X × X))
    (definitionCost : forall a, Concept X (DefinitionCoordinate a) -> Real)
    (lambda : Real) (a : A)
    (faithfulWeight : forall set, weight.mass set = 0 <-> set = ∅)
    (determined : Function.FactorsThrough target
      (conceptJoin q (definitions a))) :
    parameterEscapeDefect q definitions target weight a = 0 := by
  exact (escape_zero_iff_determined_with_audited_minimizer q definitions
    target weight definitionCost lambda a faithfulWeight).2.1
      determined

-- Uniqueness probe for CAS-A6: every second audited completion parameter is
-- forced to equal the selected regularized completion point.
example
    {A : Type u} {X : Type v} {Coordinate : Type w}
    {DefinitionCoordinate : A -> Type z} {Target : Type t}
    (q : Concept X Coordinate)
    (definitions : forall a, Concept X (DefinitionCoordinate a))
    (target : Concept X Target) (weight : EscapeWeight (X × X))
    (definitionCost : forall a, Concept X (DefinitionCoordinate a) -> Real)
    (lambda : Real) (a candidate : A)
    (faithfulWeight : forall set, weight.mass set = 0 <-> set = ∅)
    (uniqueCompletion : ∃! kappa,
      IsAuditedCompletionParameter q definitions target weight
        definitionCost lambda kappa)
    (candidateAudit : IsAuditedCompletionParameter q definitions target weight
      definitionCost lambda candidate) :
    candidate = uniqueCompletion.choose := by
  exact (escape_zero_iff_determined_with_audited_minimizer q definitions
    target weight definitionCost lambda a faithfulWeight).2.2 uniqueCompletion
      |>.2.2.2 candidate candidateAudit

private noncomputable def boolCountingWeight : EscapeWeight (Bool × Bool) where
  mass := fun set => (set.ncard : Real)
  empty_mass := by simp
  mass_nonnegative := fun set => Nat.cast_nonneg set.ncard

private def boolConstantReadout : Concept Bool Unit := fun _ => ()

private def boolConstantDefinitions : Unit -> Concept Bool Unit :=
  fun _ _ => ()

-- Trivialization probe for CAS-A2/A4: a constant joined readout leaves the
-- concrete Boolean target pair `(false, true)` escaped, with positive mass.
example :
    parameterEscapeDefect
      (A := Unit) (DefinitionCoordinate := fun _ => Unit)
      boolConstantReadout boolConstantDefinitions (id : Bool -> Bool)
      boolCountingWeight () ≠ 0 := by
  change
    (Set.ncard (defectRelation
      (conceptJoin boolConstantReadout (boolConstantDefinitions ()))
      (id : Bool -> Bool)) : Real) ≠ 0
  apply ne_of_gt
  rw [Nat.cast_pos, Set.ncard_pos]
  exact ⟨(false, true), rfl, Bool.false_ne_true⟩

-- Weak-carrier probe for CAS-A5: the same constant joined readout cannot carry
-- the identity target through its single fiber.
example :
    ¬Function.FactorsThrough (id : Bool -> Bool)
      (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => ())) := by
  intro factors
  exact Bool.false_ne_true (factors rfl)

#print axioms escape_zero_iff_determined_with_audited_minimizer

end D5.S3.ConceptDynamics.Completion.EscapeZeroCompletionPoint
