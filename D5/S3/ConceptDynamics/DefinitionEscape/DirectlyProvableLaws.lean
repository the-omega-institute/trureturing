/- GID: D5/S3/ConceptDynamics/DefinitionEscape/DirectlyProvableLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/DirectlyProvableLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nine direct DECT laws share one theorem without duplicating canonical primitives. -/

import D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
import D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.Lipschitz

/- Library-search audit trail (2026-08-24):
   * Shape searches `rg -n 'Set \\(X × X\\)' D5`, `rg -n '⋂ ' D5/S3/ConceptDynamics`,
     and `git grep -n -E '^(theorem|def|structure|abbrev) ' --
     D5/S3/ConceptDynamics/DefinitionEscape` found the canonical `defectRelation`,
     `jointKernel`, `blindResidual`, `languageExtension`, and all declarations in
     the owning directory. No second target-defect, joint-readout, or kernel
     definition is introduced here.
   * Synonym searches covered residual/escape/defect/intersection, sufficient/
     factor/recover, redundant/zero-gain, blind/common/shared/joint kernel,
     finite/compact/selection/cover, capture/submodular/diminishing return,
     prepared/retract/idempotent/defect, semigroup/composition defect, and
     approximate/cascade/triangle/Lipschitz. Exact repository hits are
     `ResidualJoinLaw.residual_join_law`,
     `TargetRecoveryCriterion.target_recovery_criterion`, and
     `BlindKernelObstruction.blind_kernel_obstruction`. The first and third are
     applied directly. The recovery criterion supplies the inhabited branch of
     sufficiency-factorization; only its uncovered empty-state edge is local.
     `RedundantAppealDefectPersistence` proves persistence of nonemptiness, not
     the source's equality of residual sets. The other searched modules are
     adjacent specializations rather than the five missing general laws.
   * Loogle queries for finite ranges, union/intersection cardinality, and
     Lipschitz distance bounds found `Set.finite_range`,
     `Finset.card_union_add_card_inter`, and `LipschitzWith.dist_le_mul`.
   * LeanSearch natural-language queries for finite point separation, coverage
     submodularity, and Lipschitz error transport found `Set.SeparatesPoints`,
     finite-union cardinality lemmas, `measure_union_add_inter`, and
     `LipschitzWith.dist_le_mul`; none packages this DECT conjunction.
   * Pinned-mathlib searches additionally found `Fintype.equivFin`,
     `Finset.measurableSet_biUnion`, `MeasureTheory.measure_union_add_inter`,
     and `Function.iterate_add_apply`. These are reused rather than reproved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.DirectlyProvableLaws

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
open MeasureTheory

/-- The nine claims classified by DECT as already direct or one-line: residual
intersection, sufficiency-factorization, redundant zero gain, blind-kernel
obstruction, finite compactness, submodular capture, prepared one-step defect,
semigroup defect, and approximate cascade. -/
theorem directly_provable_laws :
    (forall {X C D Target : Type*} (q : Concept X C) (definition : Concept X D)
      (target : Concept X Target),
      defectRelation (conceptJoin q definition) target =
        defectRelation q target ∩
          {pair : X × X | Setoid.ker definition pair.1 pair.2}) ∧
    (forall {X C Target : Type*} (q : Concept X C) (target : Concept X Target),
      defectRelation q target = ∅ ↔ Function.FactorsThrough target q) ∧
    (forall {X C D Target : Type*} (q : Concept X C) (definition : Concept X D)
      (target : Concept X Target),
      Refines definition q →
        defectRelation (conceptJoin q definition) target = defectRelation q target) ∧
    (forall {X C B Target : Type*} (Gamma : Set (Concept X B))
      (q : Concept X C) (target : Concept X Target),
      (blindResidual Gamma q target).Nonempty →
        ¬finiteSelectionSufficient Gamma q target) ∧
    (forall {X C B Target : Type*} [Finite X] (Gamma : Set (Concept X B))
      (q : Concept X C) (target : Concept X Target),
      blindResidual Gamma q target = ∅ →
        ∃ (n : Nat) (definitions : Fin n → Gamma),
          defectRelation
            (languageExtension q (fun i => (definitions i).1)) target = ∅) ∧
    (forall {Edge Definition : Type*} [MeasurableSpace Edge]
      [DecidableEq Definition] (measure : Measure Edge) (residual : Set Edge)
      (cut : Definition → Set Edge), MeasurableSet residual →
      (forall definition, MeasurableSet (cut definition)) →
      forall A B : Finset Definition,
        let captured := fun S : Finset Definition =>
          residual ∩ ⋃ definition ∈ S, cut definition
        measure (captured (A ∪ B)) + measure (captured (A ∩ B)) ≤
          measure (captured A) + measure (captured B)) ∧
    (forall {X Z : Type*} [PseudoMetricSpace Z] (projection : X → Z)
      (update : X → X) (prepare : Z → X), Function.RightInverse prepare projection →
      forall x : X,
        dist (projection (update x))
            ((projection ∘ update ∘ prepare) (projection x)) =
          dist (projection (update x))
            (projection (update ((prepare ∘ projection) x)))) ∧
    (forall {X Z : Type*} [PseudoMetricSpace Z] (projection : X → Z)
      (evolution : Nat → X → X) (prepare : Z → X),
      Function.RightInverse prepare projection →
      (forall t s x, evolution (t + s) x = evolution t (evolution s x)) →
      forall (t s : Nat) (m : Z),
        dist (projection (evolution (t + s) (prepare m)))
            (projection (evolution t
              (prepare (projection (evolution s (prepare m)))))) =
          dist (projection (evolution t (evolution s (prepare m))))
            (projection (evolution t
              ((prepare ∘ projection) (evolution s (prepare m)))))) ∧
    (forall {X Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
      (first : X → Y) (second : Y → Z) (direct : X → Z)
      (K : NNReal) (delta eta : Real), LipschitzWith K second →
      forall x y, dist (first x) y ≤ delta → dist (second y) (direct x) ≤ eta →
        dist (second (first x)) (direct x) ≤ K * delta + eta) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X C D Target q definition target
    exact residual_join_law q definition target
  · intro X C Target q target
    by_cases inhabited : Nonempty X
    · letI : Nonempty X := inhabited
      exact (target_recovery_criterion q target).2.1.symm
    · constructor
      · intro emptyDefect x y sameReadout
        exact (inhabited ⟨x⟩).elim
      · intro factorsThrough
        ext pair
        exact (inhabited ⟨pair.1⟩).elim
  · intro X C D Target q definition target definitionRefines
    rw [residual_join_law]
    apply Set.inter_eq_left.mpr
    rintro pair ⟨sameReadout, _⟩
    rcases definitionRefines with ⟨factor, factorization⟩
    change definition pair.1 = definition pair.2
    rw [factorization]
    exact congrArg factor sameReadout
  · intro X C B Target Gamma q target nonemptyResidual
    rcases nonemptyResidual with ⟨pair, pairInResidual⟩
    letI : Nonempty X := ⟨pair.1⟩
    exact
      ((blind_kernel_obstruction Gamma q target).2
        ⟨pair, pairInResidual⟩).2.2
  · intro X C B Target finiteX Gamma q target emptyBlindResidual
    letI : Fintype X := Fintype.ofFinite X
    let DefectPair :=
      {pair : X × X // pair ∈ defectRelation q target}
    letI : Fintype DefectPair := Fintype.ofFinite DefectPair
    classical
    have separated : ∀ pair : DefectPair,
        ∃ definition : Gamma,
          definition.1 pair.1.1 ≠ definition.1 pair.1.2 := by
      intro pair
      by_contra noSeparator
      have pairInKernel :
          pair.1 ∈ jointKernel (fun definition : Gamma => definition.1) := by
        simp only [jointKernel, conceptKernel, Set.mem_iInter,
          Set.mem_setOf_eq]
        intro definition
        by_contra differentValues
        exact noSeparator ⟨definition, differentValues⟩
      have pairInBlind : pair.1 ∈ blindResidual Gamma q target :=
        ⟨pair.2, pairInKernel⟩
      rw [emptyBlindResidual] at pairInBlind
      exact pairInBlind
    let selected : ∀ pair : DefectPair, Gamma :=
      fun pair => Classical.choose (separated pair)
    let enumerate : DefectPair ≃ Fin (Fintype.card DefectPair) :=
      Fintype.equivFin DefectPair
    refine ⟨Fintype.card DefectPair,
      fun i => selected (enumerate.symm i), ?_⟩
    ext pair
    constructor
    · intro extensionDefect
      have baselineDefect : pair ∈ defectRelation q target :=
        ⟨congrArg Prod.fst extensionDefect.1, extensionDefect.2⟩
      let indexedPair : DefectPair := ⟨pair, baselineDefect⟩
      have sameSelectedValues :=
        congrFun (congrArg Prod.snd extensionDefect.1)
          (enumerate indexedPair)
      have selectedSeparates := Classical.choose_spec (separated indexedPair)
      exact selectedSeparates (by
        simpa [languageExtension, conceptJoin, jointReadout, selected,
          indexedPair] using sameSelectedValues)
    · exact False.elim
  · intro Edge Definition measurableEdge decidableDefinition measure residual cut
      measurableResidual measurableCut A B
    let captured := fun S : Finset Definition =>
      residual ∩ ⋃ definition ∈ S, cut definition
    have measurableCaptured (S : Finset Definition) :
        MeasurableSet (captured S) := by
      exact measurableResidual.inter
        (S.measurableSet_biUnion fun definition _ => measurableCut definition)
    have capturedUnion : captured (A ∪ B) = captured A ∪ captured B := by
      ext edge
      simp only [captured, Set.mem_inter_iff, Set.mem_iUnion,
        Finset.mem_union]
      aesop
    have capturedIntersectionSubset :
        captured (A ∩ B) ⊆ captured A ∩ captured B := by
      intro edge edgeCaptured
      simp only [captured, Set.mem_inter_iff, Set.mem_iUnion,
        Finset.mem_inter] at edgeCaptured ⊢
      aesop
    calc
      measure (captured (A ∪ B)) + measure (captured (A ∩ B)) =
          measure (captured A ∪ captured B) +
            measure (captured (A ∩ B)) := by rw [capturedUnion]
      _ ≤ measure (captured A ∪ captured B) +
            measure (captured A ∩ captured B) :=
        add_le_add (le_refl _) (measure_mono capturedIntersectionSubset)
      _ = measure (captured A) + measure (captured B) :=
        measure_union_add_inter (captured A) (measurableCaptured B)
  · intro X Z pseudoMetric projection update prepare rightInverse x
    rfl
  · intro X Z pseudoMetric projection evolution prepare rightInverse semigroup t s m
    rw [semigroup t s (prepare m)]
    rfl
  · intro X Y Z pseudoMetricY pseudoMetricZ first second direct K delta eta
      lipschitz x y firstError secondError
    calc
      dist (second (first x)) (direct x) ≤
          dist (second (first x)) (second y) +
            dist (second y) (direct x) := dist_triangle _ _ _
      _ ≤ K * dist (first x) y + eta :=
        add_le_add (lipschitz.dist_le_mul (first x) y) secondError
      _ ≤ K * delta + eta :=
        add_le_add
          (mul_le_mul_of_nonneg_left firstError (NNReal.coe_nonneg K))
          (le_refl eta)

/-- Clause 1 is exercised on a genuinely nonempty joined residual. -/
example :
    (defectRelation
        (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
        (id : Concept Bool Bool) =
      defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
        {pair : Bool × Bool |
          Setoid.ker (fun _ : Bool => false) pair.1 pair.2}) ∧
    (false, true) ∈ defectRelation
      (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
      (id : Concept Bool Bool) := by
  constructor
  · exact residual_join_law
      (fun _ : Bool => ()) (fun _ : Bool => false) (id : Concept Bool Bool)
  · exact ⟨rfl, Bool.false_ne_true⟩

/-- Clause 2 recovers a nonconstant target through the identity readout. -/
example :
    defectRelation (id : Concept Bool Bool) (id : Concept Bool Bool) = ∅ ∧
      Function.FactorsThrough (id : Concept Bool Bool)
        (id : Concept Bool Bool) := by
  have factors : Function.FactorsThrough (id : Concept Bool Bool)
      (id : Concept Bool Bool) := by
    intro a b sameValue
    exact sameValue
  constructor
  · ext pair
    simp [defectRelation]
  · exact factors

/-- Clause 3 leaves a nonempty defect unchanged by a redundant readout. -/
example :
    Refines (fun _ : Bool => false) (fun _ : Bool => ()) ∧
    defectRelation
        (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
        (id : Concept Bool Bool) =
      defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
    (false, true) ∈ defectRelation
      (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
      (id : Concept Bool Bool) := by
  have redundant : Refines (fun _ : Bool => false) (fun _ : Bool => ()) :=
    ⟨fun _ => false, rfl⟩
  refine ⟨redundant, ?_, ?_⟩
  · rw [residual_join_law]
    apply Set.inter_eq_left.mpr
    intro pair pairInDefect
    rfl
  · exact ⟨rfl, Bool.false_ne_true⟩

/-- Clause 4 obstructs finite selection on a concrete blind Boolean pair. -/
example :
    (blindResidual
        {definition : Concept Bool Bool | definition = fun _ => false}
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty ∧
      ¬finiteSelectionSufficient
        {definition : Concept Bool Bool | definition = fun _ => false}
        (fun _ : Bool => ()) (id : Concept Bool Bool) := by
  have residual :
      (blindResidual
        {definition : Concept Bool Bool | definition = fun _ => false}
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty := by
    refine ⟨(false, true), ⟨rfl, Bool.false_ne_true⟩, ?_⟩
    simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
    rintro ⟨definition, definitionInPackage⟩
    subst definition
    rfl
  exact ⟨residual,
    ((blind_kernel_obstruction
      {definition : Concept Bool Bool | definition = fun _ => false}
      (fun _ : Bool => ()) (id : Concept Bool Bool)).2 residual).2.2⟩

/-- Clause 5 finitely closes a nonempty baseline defect with the identity
definition from a singleton package. -/
example :
    (defectRelation (fun _ : Bool => ())
      (id : Concept Bool Bool)).Nonempty ∧
    blindResidual
        {definition : Concept Bool Bool |
          definition = (id : Concept Bool Bool)}
        (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ ∧
    ∃ (n : Nat)
        (definitions : Fin n →
          {definition : Concept Bool Bool |
            definition = (id : Concept Bool Bool)}),
      defectRelation
        (languageExtension (fun _ : Bool => ())
          (fun i => (definitions i).1))
        (id : Concept Bool Bool) = ∅ := by
  have baselineDefect :
      (defectRelation (fun _ : Bool => ())
        (id : Concept Bool Bool)).Nonempty :=
    ⟨(false, true), rfl, Bool.false_ne_true⟩
  have noBlindPair :
      blindResidual
        {definition : Concept Bool Bool |
          definition = (id : Concept Bool Bool)}
        (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro pair pairInBlind
    rcases pairInBlind with ⟨baseline, pairInKernel⟩
    have allDefinitionsEqual :
        ∀ definition :
            {definition : Concept Bool Bool |
              definition = (id : Concept Bool Bool)},
          definition.1 pair.1 = definition.1 pair.2 := by
      simpa only [jointKernel, conceptKernel, Set.mem_iInter,
        Set.mem_setOf_eq] using pairInKernel
    have identityEqual := allDefinitionsEqual
      ⟨id, rfl⟩
    exact baseline.2 identityEqual
  refine ⟨baselineDefect, noBlindPair, 1,
    fun _ => ⟨id, rfl⟩, ?_⟩
  ext pair
  constructor
  · rintro ⟨sameExtension, differentTarget⟩
    have sameIdentity :=
      congrFun (congrArg Prod.snd sameExtension) (0 : Fin 1)
    exact differentTarget (by
      simpa [languageExtension, conceptJoin, jointReadout] using sameIdentity)
  · exact False.elim

/-- Clause 6 is strict for two different definitions whose cuts both cover the
entire two-point residual. -/
example :
    let residual : Set Bool := Set.univ
    let cut : Bool → Set Bool := fun _ => Set.univ
    let captured := fun S : Finset Bool =>
      residual ∩ ⋃ definition ∈ S, cut definition
    Measure.count (captured ({false} ∪ {true})) +
        Measure.count (captured ({false} ∩ {true})) <
      Measure.count (captured {false}) +
        Measure.count (captured {true}) := by
  dsimp only
  have capturedUnion :
      Set.univ ∩
          ⋃ definition ∈ (({false} : Finset Bool) ∪ {true}), Set.univ =
        (Set.univ : Set Bool) := by
    ext edge
    simp
  have capturedIntersection :
      Set.univ ∩
          ⋃ definition ∈ (({false} : Finset Bool) ∩ {true}), Set.univ =
        (∅ : Set Bool) := by
    ext edge
    simp
  have capturedFalse :
      Set.univ ∩ ⋃ definition ∈ ({false} : Finset Bool), Set.univ =
        (Set.univ : Set Bool) := by
    ext edge
    simp
  have capturedTrue :
      Set.univ ∩ ⋃ definition ∈ ({true} : Finset Bool), Set.univ =
        (Set.univ : Set Bool) := by
    ext edge
    simp
  rw [capturedUnion, capturedIntersection, capturedFalse, capturedTrue]
  have boolUniv :
      (Set.univ : Set Bool) = (↑({false, true} : Finset Bool) : Set Bool) := by
    ext edge
    cases edge <;> simp
  rw [boolUniv]
  have countBool :
      Measure.count (↑({false, true} : Finset Bool) : Set Bool) = 2 := by
    rw [Measure.count_apply_finset]
    norm_num
  rw [countBool]
  norm_num

/-- Clause 7 has a nonzero one-step defect for coordinate preparation followed
by a coordinate swap. -/
example :
    let projection : Real × Real → Real := Prod.fst
    let update : Real × Real → Real × Real := fun pair => (pair.2, pair.1)
    let prepare : Real → Real × Real := fun value => (value, 0)
    Function.RightInverse prepare projection ∧
      dist (projection (update (0, 1)))
          ((projection ∘ update ∘ prepare) (projection (0, 1))) =
        dist (projection (update (0, 1)))
          (projection (update ((prepare ∘ projection) (0, 1)))) ∧
      dist (projection (update (0, 1)))
          ((projection ∘ update ∘ prepare) (projection (0, 1))) = 1 := by
  dsimp
  refine ⟨fun _ => rfl, rfl, ?_⟩
  norm_num [Real.dist_eq]

/-- Clause 8 has a nonzero semigroup defect after two coordinate swaps. -/
example :
    let swap : Real × Real → Real × Real := fun pair => (pair.2, pair.1)
    let projection : Real × Real → Real := Prod.fst
    let evolution : Nat → Real × Real → Real × Real :=
      fun n => swap^[n]
    let prepare : Real → Real × Real := fun value => (value, 0)
    Function.RightInverse prepare projection ∧
      (∀ t s x, evolution (t + s) x = evolution t (evolution s x)) ∧
      dist (projection (evolution (1 + 1) (prepare 1)))
          (projection (evolution 1
            (prepare (projection (evolution 1 (prepare 1)))))) =
        dist (projection (evolution 1 (evolution 1 (prepare 1))))
          (projection (evolution 1
            ((prepare ∘ projection) (evolution 1 (prepare 1))))) ∧
      dist (projection (evolution (1 + 1) (prepare 1)))
          (projection (evolution 1
            (prepare (projection (evolution 1 (prepare 1)))))) = 1 := by
  dsimp only
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro t s x
    exact Function.iterate_add_apply
      (fun pair : Real × Real => (pair.2, pair.1)) t s x
  · rfl
  · norm_num [Function.iterate_succ_apply, Real.dist_eq]

/-- Clause 9 is tight for the identity Lipschitz map and two unit errors. -/
example :
    let first : Real → Real := id
    let second : Real → Real := id
    let direct : Real → Real := fun _ => 2
    LipschitzWith (1 : NNReal) second ∧
      dist (first 0) 1 ≤ 1 ∧
      dist (second 1) (direct 0) ≤ 1 ∧
      dist (second (first 0)) (direct 0) =
        (1 : NNReal) * (1 : Real) + 1 := by
  dsimp
  refine ⟨LipschitzWith.id, ?_, ?_, ?_⟩ <;>
    norm_num [Real.dist_eq]

#print axioms directly_provable_laws

end D5.S3.ConceptDynamics.DefinitionEscape.DirectlyProvableLaws
