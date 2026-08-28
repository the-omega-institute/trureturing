/- GID: D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite source selections and additive mass yield the DECT submodular capture laws. -/

import D5.S3.ConceptDynamics.DefinitionCapture.MeasureCapture
import D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
import Mathlib.Tactic.Linarith

/- Library-search audit trail (2026-08-26):
   * Type-shape search `rg -n 'Set \(X × X\)|Set \(.*×.*\)'
     D5/S3/ConceptDynamics --glob '*.lean'` found the canonical
     `defectRelation`, `conceptKernel`, `jointKernel`, and several neighboring
     relations. This module uses `defectRelation` directly and introduces no
     residual or kernel definition.
   * English/Chinese synonym search `rg -n -i 'submodular|submodularity|
     diminishing return|marginal capture|weighted cover|coverage function|次模|
     边际捕获|边际收益|加权覆盖|有限可加|finite additiv' D5 Blueprint
     docs/develop/theory` found the exact CAS `residualEscapeMass`,
     `capturedEscapeMass`, and `marginalCaptureLaw` in `FiniteCoverCounting`,
     generic captured-set submodularity in `MeasureCapture`, and a finite-Nat
     specialization in `WeightedResidualCoverage`. The first two definitions
     are reused verbatim; `capture_weight_submodular` is applied below through
     an `ENNReal.ofReal` view. The finite-Nat theorem is too narrow for the
     source's dependent codomains and general real-valued weight.
   * Neighbor inspection `ls D5/S3/ConceptDynamics` and `git grep -n -E
     '^def |^  def |^structure |^  structure ' -- D5/S3/ConceptDynamics |
     head -60` found no other definition-family mass interface. The weak
     `EscapeWeight` is reused with an explicit finite-additivity premise;
     `marginal_capture_law_not_implied_by_escape_weight` proves that premise
     cannot be omitted.
   * Pinned-Mathlib search `rg -n 'submodular|Submodular|diminishing|
     measure_union_add_inter|encard_union_add_encard_inter'
     .lake/packages/mathlib/Mathlib` found measure and cardinal modularity plus
     matroid-specific submodularity, but no generic weighted-coverage package.
     The repository exact hit `capture_weight_submodular` is therefore the
     reusable theorem used here.
   * `command -v loogle`, `command -v leansearch`, and
     `command -v reservoir` each returned no path (exit 1), so no CLI query was
     available. No exact external library theorem was claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCapture

open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionCapture.MeasureCapture
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- DECT section 4.4. A finitely additive escape mass turns the
source definitions `M(S)` and `F(S) = M(empty) - M(S)` into the canonical
weighted coverage function. C1--C7 retain `Set.Finite` because the source
defines `q ∨ S` only for finite selections; these are source-domain
conditions, not proof guards. C8 is the unrestricted pointwise-union boundary
from section 5.2 and therefore has no finiteness premise. -/
theorem submodular_capture
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X),
      Disjoint left right ->
        nu.mass (left ∪ right) = nu.mass left + nu.mass right) :
    let M := fun S : Set I => residualEscapeMass S definitions q target nu
    let F := fun S : Set I => capturedEscapeMass S definitions q target nu
    let captured := fun S : Set I =>
      defectRelation q target ∩
        ⋃ definition ∈ S,
          ({pair : X × X |
            Setoid.ker (definitions definition) pair.1 pair.2} :
            Set (X × X))ᶜ
    (forall S, S.Finite -> M S = nu.mass (defectRelation
      (conceptJoin q
        (jointReadout (fun item : S => definitions item.1))) target)) ∧
    (forall S, S.Finite -> F S = M ∅ - M S) ∧
    (forall S, S.Finite -> F S = nu.mass (captured S)) ∧
    (forall {A B}, A.Finite -> B.Finite -> A ⊆ B -> F A ≤ F B) ∧
    (forall A B, A.Finite -> B.Finite ->
      F (A ∪ B) + F (A ∩ B) ≤ F A + F B) ∧
    (forall {A B} (definition : I), B.Finite -> A ⊆ B -> definition ∉ B ->
      F (A ∪ {definition}) - F A ≥
        F (B ∪ {definition}) - F B) ∧
    (forall S next, S.Finite ->
      ((forall definition,
        (M S - M (S ∪ {definition})) / cost definition ≤
          (M S - M (S ∪ {next})) / cost next) ↔
      (forall definition,
        (F (S ∪ {definition}) - F S) / cost definition ≤
          (F (S ∪ {next}) - F S) / cost next))) ∧
    (forall (S : Set I) (pair : X × X),
      pair ∈ defectRelation q target ->
      (forall definition, definitions definition pair.1 =
        definitions definition pair.2) ->
      pair ∈ defectRelation
        (conceptJoin q
          (jointReadout (fun item : S => definitions item.1))) target) := by
  classical
  dsimp only
  let M := fun S : Set I => residualEscapeMass S definitions q target nu
  let F := fun S : Set I => capturedEscapeMass S definitions q target nu
  let captured := fun S : Set I =>
    defectRelation q target ∩
      ⋃ definition ∈ S,
        ({pair : X × X |
          Setoid.ker (definitions definition) pair.1 pair.2} :
          Set (X × X))ᶜ
  have mass_mono {left right : Set (X × X)} (subset : left ⊆ right) :
      nu.mass left ≤ nu.mass right := by
    have disjointDifference : Disjoint left (right \ left) := by
      exact Set.disjoint_sdiff_right
    have unionDifference : left ∪ (right \ left) = right := by
      exact Set.union_sdiff_cancel subset
    rw [← unionDifference, mass_additive left (right \ left) disjointDifference]
    exact le_add_of_nonneg_right (nu.mass_nonnegative _)
  have mass_modular (left right : Set (X × X)) :
      nu.mass (left ∪ right) + nu.mass (left ∩ right) =
        nu.mass left + nu.mass right := by
    have leftDisjoint : Disjoint left (right \ left) :=
      Set.disjoint_sdiff_right
    have differenceDisjoint : Disjoint (right \ left) (left ∩ right) := by
      apply Set.disjoint_left.2
      intro edge edgeInDifference edgeInIntersection
      exact edgeInDifference.2 edgeInIntersection.1
    have unionEq : left ∪ (right \ left) = left ∪ right := by
      ext edge
      simp only [Set.mem_union, Set.mem_sdiff]
      tauto
    have rightEq : (right \ left) ∪ (left ∩ right) = right := by
      ext edge
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    calc
      nu.mass (left ∪ right) + nu.mass (left ∩ right) =
          (nu.mass left + nu.mass (right \ left)) +
            nu.mass (left ∩ right) := by
        rw [← unionEq, mass_additive left (right \ left) leftDisjoint]
      _ = nu.mass left +
          (nu.mass (right \ left) + nu.mass (left ∩ right)) := by ring
      _ = nu.mass left + nu.mass right := by
        rw [← mass_additive (right \ left) (left ∩ right)
          differenceDisjoint, rightEq]
  have remaining_union_captured (S : Set I) :
      defectRelation
          (conceptJoin q
            (jointReadout (fun item : S => definitions item.1))) target ∪
        captured S = defectRelation q target := by
    ext pair
    simp only [captured, defectRelation, conceptJoin,
      Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion,
      Set.mem_compl_iff, Set.mem_setOf_eq, Setoid.ker_def]
    constructor
    · rintro (joined | cut)
      · exact ⟨congrArg Prod.fst joined.1, joined.2⟩
      · exact cut.1
    · intro baseline
      by_cases allSelectedEqual :
          forall item : S,
            definitions item.1 pair.1 = definitions item.1 pair.2
      · exact Or.inl ⟨Prod.ext baseline.1 (funext allSelectedEqual), baseline.2⟩
      · simp only [not_forall] at allSelectedEqual
        rcases allSelectedEqual with ⟨item, separated⟩
        exact Or.inr ⟨baseline, item.1, item.2, separated⟩
  have remaining_disjoint_captured (S : Set I) :
      Disjoint
        (defectRelation
          (conceptJoin q
            (jointReadout (fun item : S => definitions item.1))) target)
        (captured S) := by
    apply Set.disjoint_left.2
    intro pair joined capturedPair
    obtain ⟨definition : I, definitionMembership⟩ :=
      Set.mem_iUnion.mp capturedPair.2
    obtain ⟨definitionInS : definition ∈ S, separated⟩ :=
      Set.mem_iUnion.mp definitionMembership
    let item : S := ⟨definition, definitionInS⟩
    have sameReadout := congrArg Prod.snd joined.1
    have sameDefinition := congrFun sameReadout item
    exact separated sameDefinition
  have baseline_empty : M ∅ = nu.mass (defectRelation q target) := by
    apply congrArg nu.mass
    ext pair
    constructor
    · intro joined
      exact ⟨congrArg Prod.fst joined.1, joined.2⟩
    · intro baseline
      refine ⟨Prod.ext baseline.1 ?_, baseline.2⟩
      funext item
      exact False.elim item.2
  have expansion (S : Set I) : F S = nu.mass (captured S) := by
    have partition := mass_additive
      (defectRelation
        (conceptJoin q
          (jointReadout (fun item : S => definitions item.1))) target)
      (captured S) (remaining_disjoint_captured S)
    rw [remaining_union_captured S] at partition
    change M ∅ - M S = nu.mass (captured S)
    rw [baseline_empty]
    dsimp only [M, residualEscapeMass] at partition ⊢
    linarith
  have captured_mono {A B : Set I} (subset : A ⊆ B) :
      captured A ⊆ captured B := by
    intro pair pairCaptured
    obtain ⟨definition : I, definitionMembership⟩ :=
      Set.mem_iUnion.mp pairCaptured.2
    obtain ⟨definitionInA : definition ∈ A, separated⟩ :=
      Set.mem_iUnion.mp definitionMembership
    refine ⟨pairCaptured.1, ?_⟩
    apply Set.mem_iUnion.2
    refine ⟨definition, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨subset definitionInA, separated⟩
  let captureWeight : CaptureWeight (X × X) :=
    { mass := fun set => ENNReal.ofReal (nu.mass set)
      mass_union_add_lower_le := by
        intro left right lower lowerSubset
        have lowerMono : nu.mass lower ≤ nu.mass (left ∩ right) :=
          mass_mono lowerSubset
        have modular := mass_modular left right
        have realInequality :
            nu.mass (left ∪ right) + nu.mass lower ≤
              nu.mass left + nu.mass right := by
          linarith
        rw [← ENNReal.ofReal_add (nu.mass_nonnegative _)
            (nu.mass_nonnegative _),
          ← ENNReal.ofReal_add (nu.mass_nonnegative _)
            (nu.mass_nonnegative _)]
        exact ENNReal.ofReal_le_ofReal realInequality }
  have submodular (A B : Set I) :
      F (A ∪ B) + F (A ∩ B) ≤ F A + F B := by
    have submodularENN := capture_weight_submodular captureWeight
      (defectRelation q target)
      (fun definition =>
        ({pair : X × X |
          Setoid.ker (definitions definition) pair.1 pair.2} :
          Set (X × X))ᶜ) A B
    dsimp only at submodularENN
    dsimp only [captureWeight] at submodularENN
    change
      ENNReal.ofReal (nu.mass (captured (A ∪ B))) +
          ENNReal.ofReal (nu.mass (captured (A ∩ B))) ≤
        ENNReal.ofReal (nu.mass (captured A)) +
          ENNReal.ofReal (nu.mass (captured B)) at submodularENN
    rw [← ENNReal.ofReal_add (nu.mass_nonnegative _)
          (nu.mass_nonnegative _),
      ← ENNReal.ofReal_add (nu.mass_nonnegative _)
          (nu.mass_nonnegative _)] at submodularENN
    have realSubmodular :
        nu.mass (captured (A ∪ B)) + nu.mass (captured (A ∩ B)) ≤
          nu.mass (captured A) + nu.mass (captured B) := by
      exact (ENNReal.ofReal_le_ofReal_iff
        (add_nonneg (nu.mass_nonnegative _) (nu.mass_nonnegative _))).1
          submodularENN
    simpa only [expansion] using realSubmodular
  have monotone {A B : Set I} (subset : A ⊆ B) : F A ≤ F B := by
    rw [expansion A, expansion B]
    exact mass_mono (captured_mono subset)
  have marginal {A B : Set I} (definition : I) (subset : A ⊆ B)
      (definitionNotInB : definition ∉ B) :
      F (B ∪ {definition}) - F B ≤
        F (A ∪ {definition}) - F A := by
    have h := submodular (A ∪ {definition}) B
    have unionEq : (A ∪ {definition}) ∪ B = B ∪ {definition} := by
      ext item
      simp only [Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ((inA | isDefinition) | inB)
        · exact Or.inl (subset inA)
        · exact Or.inr isDefinition
        · exact Or.inl inB
      · rintro (inB | isDefinition)
        · exact Or.inr inB
        · exact Or.inl (Or.inr isDefinition)
    have interEq : (A ∪ {definition}) ∩ B = A := by
      ext item
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨inA | isDefinition, inB⟩
        · exact inA
        · subst item
          exact False.elim (definitionNotInB inB)
      · intro inA
        exact ⟨Or.inl inA, subset inA⟩
    rw [unionEq, interEq] at h
    linarith
  have marginal_identity (S : Set I) (definition : I) :
      M S - M (S ∪ {definition}) =
        F (S ∪ {definition}) - F S := by
    dsimp only [F, capturedEscapeMass]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S _sourceDomainFinite
    rfl
  · intro S _sourceDomainFinite
    rfl
  · intro S _sourceDomainFinite
    exact expansion S
  · intro A B _aSourceDomainFinite _bSourceDomainFinite subset
    exact monotone subset
  · intro A B _aSourceDomainFinite _bSourceDomainFinite
    exact submodular A B
  · intro A B definition _bSourceDomainFinite subset definitionNotInB
    exact marginal definition subset definitionNotInB
  · intro S next _sourceDomainFinite
    have _costNextNonnegative : 0 <= cost next := cost_nonnegative next
    constructor <;> intro maximizes definition
    · rw [← marginal_identity S definition, ← marginal_identity S next]
      exact maximizes definition
    · rw [marginal_identity S definition, marginal_identity S next]
      exact maximizes definition
  · intro S pair baseline blind
    exact ⟨Prod.ext baseline.1 (by
      funext item
      exact blind item.1), baseline.2⟩

/-- A three-edge weight on the canonical four-state residual gives mass three
at baseline. Each coordinate captures mass two, while both together capture
all three. These concrete values make the coverage laws genuinely nonconstant. -/
theorem finite_capture_values_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then
        (Prod.snd : Concept (Bool × Bool) Bool)
      else (Prod.fst : Concept (Bool × Bool) Bool)
    let q : Concept (Bool × Bool) Unit := fun _ => ()
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let firstEdge : (Bool × Bool) × (Bool × Bool) :=
      ((false, false), (true, false))
    let secondEdge : (Bool × Bool) × (Bool × Bool) :=
      ((false, false), (false, true))
    let overlapEdge : (Bool × Bool) × (Bool × Bool) :=
      ((false, false), (true, true))
    let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
      { mass := fun set =>
          (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
          (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
          (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
        empty_mass := by simp
        mass_nonnegative := by intro set; split_ifs <;> norm_num }
    residualEscapeMass (∅ : Set Bool) definitions q target nu = 3 ∧
      residualEscapeMass ({false} : Set Bool) definitions q target nu = 1 ∧
      residualEscapeMass ({true} : Set Bool) definitions q target nu = 1 ∧
      residualEscapeMass Set.univ definitions q target nu = 0 ∧
      capturedEscapeMass ({false} : Set Bool) definitions q target nu = 2 ∧
      capturedEscapeMass ({true} : Set Bool) definitions q target nu = 2 ∧
      capturedEscapeMass Set.univ definitions q target nu = 3 := by
  classical
  dsimp only
  let definitions : Bool -> Concept (Bool × Bool) Bool :=
    fun index => if index then
      (Prod.snd : Concept (Bool × Bool) Bool)
    else (Prod.fst : Concept (Bool × Bool) Bool)
  let q : Concept (Bool × Bool) Unit := fun _ => ()
  let target : Concept (Bool × Bool) (Bool × Bool) := id
  let firstEdge : (Bool × Bool) × (Bool × Bool) :=
    ((false, false), (true, false))
  let secondEdge : (Bool × Bool) × (Bool × Bool) :=
    ((false, false), (false, true))
  let overlapEdge : (Bool × Bool) × (Bool × Bool) :=
    ((false, false), (true, true))
  let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
    { mass := fun set =>
        (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
        (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
        (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
      empty_mass := by simp
      mass_nonnegative := by intro set; split_ifs <;> norm_num }
  change residualEscapeMass (∅ : Set Bool) definitions q target nu = 3 ∧
    residualEscapeMass ({false} : Set Bool) definitions q target nu = 1 ∧
    residualEscapeMass ({true} : Set Bool) definitions q target nu = 1 ∧
    residualEscapeMass Set.univ definitions q target nu = 0 ∧
    capturedEscapeMass ({false} : Set Bool) definitions q target nu = 2 ∧
    capturedEscapeMass ({true} : Set Bool) definitions q target nu = 2 ∧
    capturedEscapeMass Set.univ definitions q target nu = 3
  have emptyReadout (left right : Bool × Bool) :
      jointReadout
          (fun item : (∅ : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool)) left =
        jointReadout
          (fun item : (∅ : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool)) right := by
    funext item
    exact False.elim item.2
  have falseReadout (left right : Bool × Bool) :
      jointReadout
          (fun item : ({false} : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool)) left =
        jointReadout
          (fun item : ({false} : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool)) right ↔
        left.1 = right.1 := by
    constructor
    · intro sameReadout
      let item : ({false} : Set Bool) := ⟨false, by simp⟩
      simpa [jointReadout, item] using congrFun sameReadout item
    · intro sameFirst
      funext item
      have itemFalse : item.1 = false := Set.mem_singleton_iff.mp item.2
      simp [jointReadout, itemFalse, sameFirst]
  have trueReadout (left right : Bool × Bool) :
      jointReadout
          (fun item : ({true} : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool)) left =
        jointReadout
          (fun item : ({true} : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool)) right ↔
        left.2 = right.2 := by
    constructor
    · intro sameReadout
      let item : ({true} : Set Bool) := ⟨true, by simp⟩
      simpa [jointReadout, item] using congrFun sameReadout item
    · intro sameSecond
      funext item
      have itemTrue : item.1 = true := Set.mem_singleton_iff.mp item.2
      simp [jointReadout, itemTrue, sameSecond]
  have univReadout (left right : Bool × Bool) :
      jointReadout
          (fun item : (Set.univ : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool)) left =
        jointReadout
          (fun item : (Set.univ : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool)) right ↔
        left = right := by
    constructor
    · intro sameReadout
      let first : (Set.univ : Set Bool) := ⟨false, by simp⟩
      let second : (Set.univ : Set Bool) := ⟨true, by simp⟩
      apply Prod.ext
      · simpa [jointReadout, first] using congrFun sameReadout first
      · simpa [jointReadout, second] using congrFun sameReadout second
    · rintro rfl
      rfl
  have emptyResidual :
      defectRelation
          (conceptJoin (fun _ : Bool × Bool => ())
            (jointReadout
              (fun item : (∅ : Set Bool) =>
                if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
                else (Prod.fst : Concept (Bool × Bool) Bool))))
          (id : Concept (Bool × Bool) (Bool × Bool)) =
        defectRelation (fun _ : Bool × Bool => ())
          (id : Concept (Bool × Bool) (Bool × Bool)) := by
    ext pair
    constructor
    · intro joined
      exact ⟨congrArg Prod.fst joined.1, joined.2⟩
    · intro baseline
      exact ⟨Prod.ext baseline.1 (emptyReadout pair.1 pair.2), baseline.2⟩
  have falseResidual :
      defectRelation
          (conceptJoin (fun _ : Bool × Bool => ())
            (jointReadout
              (fun item : ({false} : Set Bool) =>
                if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
                else (Prod.fst : Concept (Bool × Bool) Bool))))
          (id : Concept (Bool × Bool) (Bool × Bool)) =
        {pair | pair.1.1 = pair.2.1 ∧ pair.1 ≠ pair.2} := by
    ext pair
    simp only [defectRelation, conceptJoin, Set.mem_setOf_eq,
      Prod.mk.injEq, id_eq, true_and]
    exact and_congr (falseReadout pair.1 pair.2) Iff.rfl
  have trueResidual :
      defectRelation
          (conceptJoin (fun _ : Bool × Bool => ())
            (jointReadout
              (fun item : ({true} : Set Bool) =>
                if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
                else (Prod.fst : Concept (Bool × Bool) Bool))))
          (id : Concept (Bool × Bool) (Bool × Bool)) =
        {pair | pair.1.2 = pair.2.2 ∧ pair.1 ≠ pair.2} := by
    ext pair
    simp only [defectRelation, conceptJoin, Set.mem_setOf_eq,
      Prod.mk.injEq, id_eq, true_and]
    exact and_congr (trueReadout pair.1 pair.2) Iff.rfl
  have univResidual :
      defectRelation
          (conceptJoin (fun _ : Bool × Bool => ())
            (jointReadout
              (fun item : (Set.univ : Set Bool) =>
                if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
                else (Prod.fst : Concept (Bool × Bool) Bool))))
          (id : Concept (Bool × Bool) (Bool × Bool)) = ∅ := by
    ext pair
    simp only [defectRelation, conceptJoin, Set.mem_empty_iff_false,
      Set.mem_setOf_eq, Prod.mk.injEq, id_eq, true_and]
    rw [univReadout pair.1 pair.2]
    simp
  have emptyMass :
      residualEscapeMass (∅ : Set Bool) definitions q target nu = 3 := by
    change nu.mass (defectRelation
      (conceptJoin (fun _ : Bool × Bool => ())
        (jointReadout
          (fun item : (∅ : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool))))
      (id : Concept (Bool × Bool) (Bool × Bool))) = 3
    rw [emptyResidual]
    norm_num [nu, firstEdge, secondEdge, overlapEdge, defectRelation]
  have falseMass :
      residualEscapeMass ({false} : Set Bool) definitions q target nu = 1 := by
    change nu.mass (defectRelation
      (conceptJoin (fun _ : Bool × Bool => ())
        (jointReadout
          (fun item : ({false} : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool))))
      (id : Concept (Bool × Bool) (Bool × Bool))) = 1
    rw [falseResidual]
    norm_num [nu, firstEdge, secondEdge, overlapEdge]
  have trueMass :
      residualEscapeMass ({true} : Set Bool) definitions q target nu = 1 := by
    change nu.mass (defectRelation
      (conceptJoin (fun _ : Bool × Bool => ())
        (jointReadout
          (fun item : ({true} : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool))))
      (id : Concept (Bool × Bool) (Bool × Bool))) = 1
    rw [trueResidual]
    norm_num [nu, firstEdge, secondEdge, overlapEdge]
  have univMass :
      residualEscapeMass Set.univ definitions q target nu = 0 := by
    change nu.mass (defectRelation
      (conceptJoin (fun _ : Bool × Bool => ())
        (jointReadout
          (fun item : (Set.univ : Set Bool) =>
            if item.1 then (Prod.snd : Concept (Bool × Bool) Bool)
            else (Prod.fst : Concept (Bool × Bool) Bool))))
      (id : Concept (Bool × Bool) (Bool × Bool))) = 0
    rw [univResidual]
    norm_num [nu]
  have falseCapture :
      capturedEscapeMass ({false} : Set Bool) definitions q target nu = 2 := by
    rw [capturedEscapeMass, emptyMass, falseMass]
    norm_num
  have trueCapture :
      capturedEscapeMass ({true} : Set Bool) definitions q target nu = 2 := by
    rw [capturedEscapeMass, emptyMass, trueMass]
    norm_num
  have univCapture :
      capturedEscapeMass Set.univ definitions q target nu = 3 := by
    rw [capturedEscapeMass, emptyMass, univMass]
    norm_num
  exact ⟨emptyMass, falseMass, trueMass, univMass,
    falseCapture, trueCapture, univCapture⟩

/-- All seven quantitative clauses are exercised by the three-edge model.
Monotonicity, submodularity, and diminishing returns are strict on the chosen
sets, while the greedy equivalence compares the source and capture scores. -/
theorem finite_capture_laws_nonvacuous :
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
    let cost : Bool -> Real := fun _ => 1
    let M := fun S : Set Bool => residualEscapeMass S definitions q target nu
    let F := fun S : Set Bool => capturedEscapeMass S definitions q target nu
    let captured := fun S : Set Bool =>
      defectRelation q target ∩
        ⋃ definition ∈ S,
          ({pair : (Bool × Bool) × (Bool × Bool) |
            Setoid.ker (definitions definition) pair.1 pair.2} :
            Set ((Bool × Bool) × (Bool × Bool)))ᶜ
    (M ∅ = nu.mass (defectRelation
      (conceptJoin q
        (jointReadout (fun item : (∅ : Set Bool) => definitions item.1))) target) ∧
      0 < M ∅ ∧
      M ∅ = 3) ∧
    (F {false} = M ∅ - M {false} ∧ F {false} = 2) ∧
    (F {false} = nu.mass (captured {false}) ∧
      nu.mass (captured {false}) = 2) ∧
    (F ∅ ≤ F {false} ∧ F ∅ < F {false}) ∧
    (F ({false} ∪ {true}) + F ({false} ∩ {true}) ≤
        F {false} + F {true} ∧
      F ({false} ∪ {true}) + F ({false} ∩ {true}) <
        F {false} + F {true}) ∧
    (F ((∅ : Set Bool) ∪ {true}) - F ∅ ≥
        F ({false} ∪ {true}) - F {false} ∧
      F ((∅ : Set Bool) ∪ {true}) - F ∅ >
        F ({false} ∪ {true}) - F {false}) ∧
    ((forall definition,
        (M ∅ - M (∅ ∪ {definition})) / cost definition ≤
          (M ∅ - M (∅ ∪ {false})) / cost false) ↔
      (forall definition,
        (F (∅ ∪ {definition}) - F ∅) / cost definition ≤
          (F (∅ ∪ {false}) - F ∅) / cost false)) := by
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
  let M := fun S : Set Bool => residualEscapeMass S definitions q target nu
  let F := fun S : Set Bool => capturedEscapeMass S definitions q target nu
  let captured := fun S : Set Bool =>
    defectRelation q target ∩
      ⋃ definition ∈ S,
        ({pair : (Bool × Bool) × (Bool × Bool) |
          Setoid.ker (definitions definition) pair.1 pair.2} :
          Set ((Bool × Bool) × (Bool × Bool)))ᶜ
  change
    (M ∅ = nu.mass (defectRelation
      (conceptJoin q
        (jointReadout (fun item : (∅ : Set Bool) => definitions item.1))) target) ∧
      0 < M ∅ ∧
      M ∅ = 3) ∧
    (F {false} = M ∅ - M {false} ∧ F {false} = 2) ∧
    (F {false} = nu.mass (captured {false}) ∧
      nu.mass (captured {false}) = 2) ∧
    (F ∅ ≤ F {false} ∧ F ∅ < F {false}) ∧
    (F ({false} ∪ {true}) + F ({false} ∩ {true}) ≤
        F {false} + F {true} ∧
      F ({false} ∪ {true}) + F ({false} ∩ {true}) <
        F {false} + F {true}) ∧
    (F ((∅ : Set Bool) ∪ {true}) - F ∅ ≥
        F ({false} ∪ {true}) - F {false} ∧
      F ((∅ : Set Bool) ∪ {true}) - F ∅ >
        F ({false} ∪ {true}) - F {false}) ∧
    ((forall definition,
        (M ∅ - M (∅ ∪ {definition})) / cost definition ≤
          (M ∅ - M (∅ ∪ {false})) / cost false) ↔
      (forall definition,
        (F (∅ ∪ {definition}) - F ∅) / cost definition ≤
          (F (∅ ∪ {false}) - F ∅) / cost false))
  have values :
      M ∅ = 3 ∧ M {false} = 1 ∧ M {true} = 1 ∧ M Set.univ = 0 ∧
        F {false} = 2 ∧ F {true} = 2 ∧ F Set.univ = 3 := by
    simpa [M, F, definitions, q, target, nu, firstEdge, secondEdge,
      overlapEdge] using finite_capture_values_witness
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
  have costNonnegative : forall definition, 0 <= cost definition := by
    intro definition
    norm_num [cost]
  have laws := submodular_capture definitions q target cost nu
    costNonnegative additive
  have unionEq : ({false} : Set Bool) ∪ {true} = Set.univ := by
    ext item
    cases item <;> simp
  have interEq : ({false} : Set Bool) ∩ {true} = ∅ := by simp
  have emptyCapture : F ∅ = 0 := by simp [F, capturedEscapeMass]
  refine ⟨⟨laws.1 ∅ Set.finite_empty, ?_, values.1⟩,
    ⟨laws.2.1 {false} (Set.finite_singleton false), values.2.2.2.2.1⟩,
    ⟨laws.2.2.1 {false} (Set.finite_singleton false), ?_⟩,
    ⟨laws.2.2.2.1 Set.finite_empty (Set.finite_singleton false)
      (Set.empty_subset {false}), ?_⟩,
    ⟨laws.2.2.2.2.1 {false} {true} (Set.finite_singleton false)
      (Set.finite_singleton true), ?_⟩,
    ⟨laws.2.2.2.2.2.1 true (Set.finite_singleton false)
      (Set.empty_subset {false}) (by simp), ?_⟩,
    laws.2.2.2.2.2.2.1 ∅ false Set.finite_empty⟩
  · rw [values.1]
    norm_num
  · rw [← laws.2.2.1 {false} (Set.finite_singleton false)]
    exact values.2.2.2.2.1
  · rw [emptyCapture, values.2.2.2.2.1]
    norm_num
  · rw [unionEq, interEq, emptyCapture, values.2.2.2.2.1,
      values.2.2.2.2.2.1, values.2.2.2.2.2.2]
    norm_num
  · rw [Set.empty_union, unionEq, emptyCapture, values.2.2.2.2.1,
      values.2.2.2.2.2.1, values.2.2.2.2.2.2]
    norm_num

#print axioms submodular_capture

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCapture
