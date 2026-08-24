/- GID: D5/S3/ConceptDynamics/DefinitionEscape/DirectlyProvableLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/DirectlyProvableLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nine direct DECT laws share one theorem without duplicating canonical primitives. -/

import D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
import D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
import D5.S0.Diagonal.Naturality.NaturalityDefectComposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
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
     `BlindKernelObstruction.blind_kernel_obstruction`, and
     `NaturalityDefectComposition.naturality_defect_comp_le`. The frozen blind
     theorem has a shared codomain, so this module proves a dependent-family
     analogue and definitionally identifies its constant-codomain specialization
     with the frozen `blindResidual` and `languageExtension`. The recovery
     criterion supplies the inhabited branch of sufficiency-factorization; only
     its uncovered empty-state edge is local.
     `RedundantAppealDefectPersistence` proves persistence of nonemptiness, not
     the source's equality of residual sets. The remaining searched modules are
     adjacent specializations rather than exact packages for clauses 3, 5--8.
   * Loogle queries for finite ranges, weighted sums, and Lipschitz distance
     bounds found `Set.finite_range`, `ENNReal.tsum_add`, and
     `LipschitzWith.dist_le_mul`.
   * LeanSearch natural-language queries for finite point separation, coverage
     submodularity, and Lipschitz error transport found `Set.SeparatesPoints`,
     finite-union cardinality lemmas, `measure_union_add_inter`, and
     `LipschitzWith.dist_le_mul`; none packages this DECT conjunction.
   * Pinned-mathlib searches additionally found `Fintype.equivFin`,
     `ENNReal.tsum_le_tsum`, and `Function.iterate_add_apply`. These are reused
     rather than reproved. -/

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
open D5.S0.Diagonal.Naturality.NaturalityDefectComposition

/-- The dependent-family extension used by clauses 4 and 5.  The frozen
`languageExtension` is its constant-codomain specialization. -/
def dependentLanguageExtension {X C I : Type*} {D : I → Type*}
    (q : Concept X C) (definitions : ∀ i, Concept X (D i)) :
    Concept X (C × (∀ i, D i)) :=
  conceptJoin q (jointReadout definitions)
/-- The dependent-family blind residual uses the canonical target residual and
the existing dependent `jointKernel`; it does not alter the frozen residual. -/
def dependentBlindResidual {X C Target Gamma : Type*} {D : Gamma → Type*}
    (definitions : ∀ gamma, Concept X (D gamma)) (q : Concept X C)
    (target : Concept X Target) : Set (X × X) :=
  defectRelation q target ∩ jointKernel definitions
/-- A finite dependent selection succeeds when the target factors through the
baseline and the selected, potentially heterogeneous, readouts. -/
def dependentFiniteSelectionSufficient
    {X C Target Gamma : Type*} {D : Gamma → Type*}
    (definitions : ∀ gamma, Concept X (D gamma)) (q : Concept X C)
    (target : Concept X Target) : Prop :=
  ∃ (n : Nat) (codes : Fin n → Gamma)
      (recover : (C × (∀ i, D (codes i))) → Target),
    target = recover ∘ dependentLanguageExtension q
      (fun i => definitions (codes i))
/-- On a shared codomain, the dependent extension is definitionally the frozen
`languageExtension`. -/
theorem dependent_language_extension_const_eq {X C B I : Type*}
    (q : Concept X C) (definitions : I → Concept X B) :
    dependentLanguageExtension q definitions = languageExtension q definitions :=
  rfl

/-- On the subtype of a shared-codomain package, the dependent residual is
definitionally the frozen `blindResidual`. -/
theorem dependent_blind_residual_const_eq {X C B Target : Type*}
    (Gamma : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) :
    dependentBlindResidual (fun definition : Gamma => definition.1) q target =
      blindResidual Gamma q target :=
  rfl

/-- The dependent finite-selection predicate also conservatively specializes
to the frozen shared-codomain predicate. -/
theorem dependent_finite_selection_const_iff {X C B Target : Type*}
    (Gamma : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) :
    dependentFiniteSelectionSufficient
        (fun definition : Gamma => definition.1) q target ↔
      finiteSelectionSufficient Gamma q target :=
  Iff.rfl

/-- A dependent blind pair obstructs every finite selection and every arbitrary
subfamily.  This is the append-only dependent-family analogue of the nonempty
branch of the frozen `blind_kernel_obstruction`. -/
theorem dependent_blind_kernel_obstruction
    {X C Target Gamma : Type*} {D : Gamma → Type*}
    (definitions : ∀ gamma, Concept X (D gamma))
    (q : Concept X C) (target : Concept X Target) :
    (dependentBlindResidual definitions q target).Nonempty →
      (∀ (n : Nat) (codes : Fin n → Gamma),
        ¬∃ recover : (C × (∀ i, D (codes i))) → Target,
          target = recover ∘ dependentLanguageExtension q
            (fun i => definitions (codes i))) ∧
      (∀ Delta : Set Gamma,
        ¬∃ recover : (C × (∀ code : Delta, D code.1)) → Target,
          target = recover ∘ dependentLanguageExtension q
            (fun code : Delta => definitions code.1)) ∧
      ¬dependentFiniteSelectionSufficient definitions q target := by
  rintro ⟨pair, pairInResidual⟩
  letI : Nonempty X := ⟨pair.1⟩
  rcases pairInResidual with ⟨baselineDefect, pairInKernel⟩
  have allDefinitionsBlind :
      ∀ gamma : Gamma,
        definitions gamma pair.1 = definitions gamma pair.2 := by
    simpa only [jointKernel, conceptKernel, Set.mem_iInter,
      Set.mem_setOf_eq] using pairInKernel
  have finiteObstruction :
      ∀ (n : Nat) (codes : Fin n → Gamma),
        ¬∃ recover : (C × (∀ i, D (codes i))) → Target,
          target = recover ∘ dependentLanguageExtension q
            (fun i => definitions (codes i)) := by
    intro n codes
    have extensionDefect :
        (defectRelation
          (dependentLanguageExtension q
            (fun i => definitions (codes i))) target).Nonempty := by
      refine ⟨pair, ?_, baselineDefect.2⟩
      change
        (q pair.1, fun i => definitions (codes i) pair.1) =
          (q pair.2, fun i => definitions (codes i) pair.2)
      apply Prod.ext baselineDefect.1
      funext i
      exact allDefinitionsBlind (codes i)
    exact
      (target_recovery_criterion
        (dependentLanguageExtension q
          (fun i => definitions (codes i))) target).2.2.2.mpr
          extensionDefect
  have arbitraryObstruction :
      ∀ Delta : Set Gamma,
        ¬∃ recover : (C × (∀ code : Delta, D code.1)) → Target,
          target = recover ∘ dependentLanguageExtension q
            (fun code : Delta => definitions code.1) := by
    intro Delta
    have extensionDefect :
        (defectRelation
          (dependentLanguageExtension q
            (fun code : Delta => definitions code.1)) target).Nonempty := by
      refine ⟨pair, ?_, baselineDefect.2⟩
      change
        (q pair.1, fun code : Delta => definitions code.1 pair.1) =
          (q pair.2, fun code : Delta => definitions code.1 pair.2)
      apply Prod.ext baselineDefect.1
      funext code
      exact allDefinitionsBlind code.1
    exact
      (target_recovery_criterion
        (dependentLanguageExtension q
          (fun code : Delta => definitions code.1)) target).2.2.2.mpr
          extensionDefect
  refine ⟨finiteObstruction, arbitraryObstruction, ?_⟩
  rintro ⟨n, codes, recover, recovery⟩
  exact finiteObstruction n codes ⟨recover, recovery⟩

/-- The nine claims classified by DECT as already direct or one-line: residual
intersection, sufficiency-factorization, redundant zero gain, blind-kernel
obstruction, finite compactness, submodular capture, prepared one-step defect,
semigroup defect, and approximate cascade. Clause 6 realizes the source's
weight/count reading through arbitrary nonnegative point weights; an unrestricted
non-atomic measure reading would need measurable-domain conditions absent from
the source statement. -/
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
    (forall {X C Target Gamma : Type*} {D : Gamma → Type*}
      (definitions : ∀ gamma, Concept X (D gamma))
      (q : Concept X C) (target : Concept X Target),
      (dependentBlindResidual definitions q target).Nonempty →
        (∀ (n : Nat) (codes : Fin n → Gamma),
          ¬∃ recover : (C × (∀ i, D (codes i))) → Target,
            target = recover ∘
              dependentLanguageExtension q (fun i => definitions (codes i))) ∧
        (∀ Delta : Set Gamma,
          ¬∃ recover : (C × (∀ code : Delta, D code.1)) → Target,
            target = recover ∘
              dependentLanguageExtension q
                (fun code : Delta => definitions code.1)) ∧
        ¬dependentFiniteSelectionSufficient definitions q target) ∧
    (forall {X C Target Gamma : Type*} {D : Gamma → Type*} [Finite X]
      (definitions : ∀ gamma, Concept X (D gamma))
      (q : Concept X C) (target : Concept X Target),
      dependentBlindResidual definitions q target = ∅ →
        ∃ (n : Nat) (codes : Fin n → Gamma),
          defectRelation
            (dependentLanguageExtension q
              (fun i => definitions (codes i))) target = ∅) ∧
    (forall {Edge Definition : Type*} (weight : Edge → ENNReal)
      (residual : Set Edge) (cut : Definition → Set Edge)
      (A B : Set Definition),
      let captured := fun S : Set Definition =>
        residual ∩ ⋃ definition ∈ S, cut definition
      let mass := fun edges : Set Edge =>
        ∑' edge, edges.indicator weight edge
      mass (captured (A ∪ B)) + mass (captured (A ∩ B)) ≤
        mass (captured A) + mass (captured B)) ∧
    (forall {X Z : Type*} [PseudoMetricSpace Z] (projection : X → Z)
      (update : X → X) (prepare : Z → X), Function.RightInverse prepare projection →
      forall x : X,
        dist (projection (update x))
            ((projection ∘ update ∘ prepare) (projection x)) =
          dist (projection (update x))
            (projection (update ((prepare ∘ projection) x)))) ∧
    (forall {X Z Time : Type*} [PseudoMetricSpace Z] [Add Time]
      (projection : X → Z) (evolution : Time → X → X) (prepare : Z → X),
      Function.RightInverse prepare projection →
      (forall t s x, evolution (t + s) x = evolution t (evolution s x)) →
      forall (t s : Time) (m : Z),
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
  · intro X C Target Gamma D definitions q target nonemptyResidual
    rcases nonemptyResidual with ⟨pair, pairInResidual⟩
    letI : Nonempty X := ⟨pair.1⟩
    exact dependent_blind_kernel_obstruction definitions q target
      ⟨pair, pairInResidual⟩
  · intro X C Target Gamma D finiteX definitions q target emptyBlindResidual
    letI : Fintype X := Fintype.ofFinite X
    let DefectPair :=
      {pair : X × X // pair ∈ defectRelation q target}
    letI : Fintype DefectPair := Fintype.ofFinite DefectPair
    classical
    have separated : ∀ pair : DefectPair,
        ∃ gamma : Gamma,
          definitions gamma pair.1.1 ≠ definitions gamma pair.1.2 := by
      intro pair
      by_contra noSeparator
      have pairInKernel :
          pair.1 ∈ jointKernel definitions := by
        simp only [jointKernel, conceptKernel, Set.mem_iInter,
          Set.mem_setOf_eq]
        intro gamma
        by_contra differentValues
        exact noSeparator ⟨gamma, differentValues⟩
      have pairInBlind : pair.1 ∈ dependentBlindResidual definitions q target :=
        ⟨pair.2, pairInKernel⟩
      rw [emptyBlindResidual] at pairInBlind
      exact pairInBlind
    let selected : DefectPair → Gamma :=
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
      change
        definitions (selected (enumerate.symm (enumerate indexedPair))) pair.1 =
          definitions (selected (enumerate.symm (enumerate indexedPair))) pair.2
        at sameSelectedValues
      rw [enumerate.symm_apply_apply] at sameSelectedValues
      exact selectedSeparates sameSelectedValues
    · exact False.elim
  · intro Edge Definition weight residual cut A B
    classical
    dsimp only
    let captured := fun S : Set Definition =>
      residual ∩ ⋃ definition ∈ S, cut definition
    let mass := fun edges : Set Edge =>
      ∑' edge, edges.indicator weight edge
    change mass (captured (A ∪ B)) + mass (captured (A ∩ B)) ≤
      mass (captured A) + mass (captured B)
    have capturedUnion : captured (A ∪ B) = captured A ∪ captured B := by
      ext edge
      simp only [captured, Set.mem_inter_iff, Set.mem_iUnion,
        Set.mem_union]
      aesop
    have capturedIntersectionSubset :
        captured (A ∩ B) ⊆ captured A ∩ captured B := by
      intro edge edgeCaptured
      simp only [captured, Set.mem_inter_iff, Set.mem_iUnion] at edgeCaptured ⊢
      aesop
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro edge
    have unionMembership :
        edge ∈ captured (A ∪ B) ↔ edge ∈ captured A ∨ edge ∈ captured B := by
      rw [capturedUnion]
      exact Set.mem_union edge (captured A) (captured B)
    by_cases inA : edge ∈ captured A
    · by_cases inB : edge ∈ captured B
      · by_cases inIntersection : edge ∈ captured (A ∩ B)
        · simp [inA, inB, inIntersection, unionMembership]
        · simp [inA, inB, inIntersection, unionMembership]
      · have notInIntersection : edge ∉ captured (A ∩ B) := by
          intro inIntersection
          exact inB (capturedIntersectionSubset inIntersection).2
        simp [inA, inB, notInIntersection, unionMembership]
    · have notInIntersection : edge ∉ captured (A ∩ B) := by
        intro inIntersection
        exact inA (capturedIntersectionSubset inIntersection).1
      by_cases inB : edge ∈ captured B <;>
        simp [inA, inB, notInIntersection, unionMembership]
  · intro X Z pseudoMetric projection update prepare rightInverse x
    rfl
  · intro X Z Time pseudoMetric addTime projection evolution prepare rightInverse
      semigroup t s m
    rw [semigroup t s (prepare m)]
    rfl
  · intro X Y Z pseudoMetricY pseudoMetricZ first second direct K delta eta
      lipschitz x y firstError secondError
    have compositionBound := naturality_defect_comp_le
      (projectA := first) (projectB := fun _ : X => y) (projectC := id)
      (globalF := direct) (localF := second) (globalG := id) (localG := id)
      K lipschitz x
    unfold naturalityDefect at compositionBound
    simp only [Function.comp_apply, id_eq] at compositionBound
    calc
      dist (second (first x)) (direct x) =
          dist (direct x) (second (first x)) := dist_comm _ _
      _ ≤ dist (direct x) (second y) + K * dist y (first x) :=
        compositionBound
      _ ≤ eta + K * delta := add_le_add
        (by simpa only [dist_comm] using secondError)
        (mul_le_mul_of_nonneg_left
          (by simpa only [dist_comm] using firstError) (NNReal.coe_nonneg K))
      _ = K * delta + eta := add_comm _ _

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

/-- Clause 4 obstructs finite and arbitrary subfamilies on a blind pair. -/
example :
    (dependentBlindResidual
        (fun _ : Unit => fun _ : Bool => false)
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty ∧
      (∀ (n : Nat) (codes : Fin n → Unit),
        ¬∃ recover : (Unit × (Fin n → Bool)) → Bool,
          (id : Concept Bool Bool) = recover ∘
            dependentLanguageExtension (fun _ : Bool => ())
              (fun i => (fun _ : Unit => fun _ : Bool => false) (codes i))) ∧
      (∀ Delta : Set Unit,
        ¬∃ recover : (Unit × (Delta → Bool)) → Bool,
          (id : Concept Bool Bool) = recover ∘
            dependentLanguageExtension (fun _ : Bool => ())
              (fun code : Delta =>
                (fun _ : Unit => fun _ : Bool => false) code.1)) ∧
      ¬dependentFiniteSelectionSufficient
        (fun _ : Unit => fun _ : Bool => false)
        (fun _ : Bool => ()) (id : Concept Bool Bool) := by
  have residual :
      (dependentBlindResidual
        (fun _ : Unit => fun _ : Bool => false)
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty := by
    refine ⟨(false, true), ⟨rfl, Bool.false_ne_true⟩, ?_⟩
    simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
    intro gamma
    cases gamma
    trivial
  exact ⟨residual, dependent_blind_kernel_obstruction
    (fun _ : Unit => fun _ : Bool => false)
    (fun _ : Bool => ()) (id : Concept Bool Bool) residual⟩

/-- Clause 5 finitely closes a nonempty baseline defect with the identity
definition from a singleton package. -/
example :
    (defectRelation (fun _ : Bool => ())
      (id : Concept Bool Bool)).Nonempty ∧
    dependentBlindResidual (fun _ : Unit => (id : Concept Bool Bool))
        (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ ∧
    ∃ (n : Nat)
        (codes : Fin n → Unit),
      defectRelation
        (dependentLanguageExtension (fun _ : Bool => ())
          (fun i => (fun _ : Unit => (id : Concept Bool Bool)) (codes i)))
        (id : Concept Bool Bool) = ∅ := by
  have baselineDefect :
      (defectRelation (fun _ : Bool => ())
        (id : Concept Bool Bool)).Nonempty :=
    ⟨(false, true), rfl, Bool.false_ne_true⟩
  have noBlindPair :
      dependentBlindResidual (fun _ : Unit => (id : Concept Bool Bool))
        (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro pair pairInBlind
    rcases pairInBlind with ⟨baseline, pairInKernel⟩
    have allDefinitionsEqual :
        ∀ gamma : Unit,
          (id : Concept Bool Bool) pair.1 = id pair.2 := by
      simpa only [jointKernel, conceptKernel, Set.mem_iInter,
        Set.mem_setOf_eq] using pairInKernel
    have identityEqual := allDefinitionsEqual ()
    exact baseline.2 identityEqual
  refine ⟨baselineDefect, noBlindPair, 1,
    fun _ => (), ?_⟩
  ext pair
  constructor
  · rintro ⟨sameExtension, differentTarget⟩
    have sameIdentity :=
      congrFun (congrArg Prod.snd sameExtension) (0 : Fin 1)
    exact differentTarget (by
      simpa [dependentLanguageExtension, conceptJoin, jointReadout]
        using sameIdentity)
  · exact False.elim

/-- Clause 6 is strict for two cuts that both cover a positive-weight residual. -/
example :
    let weight : Bool → ENNReal := fun _ => 1
    let residual : Set Bool := Set.univ
    let cut : Bool → Set Bool := fun _ => Set.univ
    let captured := fun S : Set Bool =>
      residual ∩ ⋃ definition ∈ S, cut definition
    let mass := fun edges : Set Bool =>
      ∑' edge, edges.indicator weight edge
    mass (captured ({false} ∪ {true})) +
      mass (captured ({false} ∩ {true})) <
      mass (captured {false}) + mass (captured {true}) := by
  classical
  norm_num [tsum_fintype, Set.indicator, Set.mem_inter_iff, Set.mem_iUnion]

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

/- The following nine declarations are elaborating falsification witnesses, one
for each conjunct.  Each negates a nearby statement on values that remain in
the law's intended domain; none relies on an ill-typed term or an out-of-package
definition. -/

/-- Replacing the residual intersection in clause 1 by a union is false. -/
theorem false_neighbor_clause1 :
    ¬defectRelation
          (conceptJoin (id : Concept Bool Bool) (fun _ : Bool => ()))
          (id : Concept Bool Bool) =
        defectRelation (id : Concept Bool Bool) (id : Concept Bool Bool) ∪
          {pair : Bool × Bool |
            Setoid.ker (fun _ : Bool => ()) pair.1 pair.2} := by
  intro falseEquality
  have pairInUnion :
      (false, true) ∈
        defectRelation (id : Concept Bool Bool) (id : Concept Bool Bool) ∪
          {pair : Bool × Bool |
            Setoid.ker (fun _ : Bool => ()) pair.1 pair.2} := by
    exact Or.inr rfl
  rw [← falseEquality] at pairInUnion
  exact Bool.false_ne_true (congrArg Prod.fst pairInUnion.1)

/-- Reversing the factorization direction in clause 2 is false. -/
theorem false_neighbor_clause2 :
    ¬(defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ ↔
      Function.FactorsThrough (fun _ : Bool => ()) (id : Concept Bool Bool)) := by
  intro falseEquivalence
  have reverseFactorization :
      Function.FactorsThrough (fun _ : Bool => ())
        (id : Concept Bool Bool) := by
    intro left right sameTarget
    rfl
  have emptyDefect := falseEquivalence.mpr reverseFactorization
  have pairInDefect :
      (false, true) ∈
        defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) :=
    ⟨rfl, Bool.false_ne_true⟩
  rw [emptyDefect] at pairInDefect
  exact pairInDefect

/-- Dropping the refinement premise from clause 3 is false. -/
theorem false_neighbor_clause3 :
    ¬defectRelation
          (conceptJoin (fun _ : Bool => ()) (id : Concept Bool Bool))
          (id : Concept Bool Bool) =
        defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) := by
  intro falseEquality
  have pairInBaseline :
      (false, true) ∈
        defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) :=
    ⟨rfl, Bool.false_ne_true⟩
  rw [← falseEquality] at pairInBaseline
  exact pairInBaseline.2 (congrArg Prod.snd pairInBaseline.1)

/-- Replacing clause 4's nonempty blind residual by an empty one is false. -/
theorem false_neighbor_clause4 :
    ¬(dependentBlindResidual (fun _ : Unit => (id : Concept Bool Bool))
          (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ →
        ¬dependentFiniteSelectionSufficient
          (fun _ : Unit => (id : Concept Bool Bool))
          (fun _ : Bool => ()) (id : Concept Bool Bool)) := by
  intro falseImplication
  have emptyBlindResidual :
      dependentBlindResidual (fun _ : Unit => (id : Concept Bool Bool))
          (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro pair ⟨baselineDefect, pairInKernel⟩
    have identityEqual :
        (id : Concept Bool Bool) pair.1 = id pair.2 := by
      have allDefinitionsEqual :
          ∀ gamma : Unit,
            (id : Concept Bool Bool) pair.1 = id pair.2 := by
        simpa only [jointKernel, conceptKernel, Set.mem_iInter,
          Set.mem_setOf_eq] using pairInKernel
      exact allDefinitionsEqual ()
    exact baselineDefect.2 identityEqual
  have finiteSelection :
      dependentFiniteSelectionSufficient
        (fun _ : Unit => (id : Concept Bool Bool))
        (fun _ : Bool => ()) (id : Concept Bool Bool) := by
    refine ⟨1, fun _ => (), fun readout => readout.2 0, ?_⟩
    funext state
    rfl
  exact falseImplication emptyBlindResidual finiteSelection

private def natPointDefinition (code : Nat) : Concept Nat Bool :=
  fun state => decide (state = code)

/-- Removing the finite-state premise from clause 5 is false: all singleton
tests separate `Nat`, while every finite selection misses two later states. -/
theorem false_neighbor_clause5 :
    ¬(dependentBlindResidual natPointDefinition (fun _ : Nat => ())
          (id : Concept Nat Nat) = ∅ →
        ∃ (n : Nat) (codes : Fin n → Nat),
          defectRelation
            (dependentLanguageExtension (fun _ : Nat => ())
              (fun i => natPointDefinition (codes i)))
            (id : Concept Nat Nat) = ∅) := by
  intro falseImplication
  have emptyBlindResidual :
      dependentBlindResidual natPointDefinition (fun _ : Nat => ())
          (id : Concept Nat Nat) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro pair ⟨baselineDefect, pairInKernel⟩
    have allDefinitionsEqual :
        ∀ code : Nat,
          natPointDefinition code pair.1 = natPointDefinition code pair.2 := by
      simpa only [jointKernel, conceptKernel, Set.mem_iInter,
        Set.mem_setOf_eq] using pairInKernel
    have sameState : pair.2 = pair.1 := by
      by_contra differentState
      have pointEquality := allDefinitionsEqual pair.1
      simp [natPointDefinition, differentState] at pointEquality
    exact baselineDefect.2 sameState.symm
  rcases falseImplication emptyBlindResidual with
    ⟨n, codes, emptyFiniteDefect⟩
  let bound : Nat := ∑ i, codes i
  let left := bound + 1
  let right := bound + 2
  have code_le_bound (i : Fin n) : codes i ≤ bound := by
    dsimp only [bound]
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le (codes j)) (Finset.mem_univ i)
  have left_ne_code (i : Fin n) : left ≠ codes i := by
    have bounded := code_le_bound i
    dsimp only [left] at *
    omega
  have right_ne_code (i : Fin n) : right ≠ codes i := by
    have bounded := code_le_bound i
    dsimp only [right] at *
    omega
  have finiteDefect :
      (left, right) ∈
        defectRelation
          (dependentLanguageExtension (fun _ : Nat => ())
            (fun i => natPointDefinition (codes i)))
          (id : Concept Nat Nat) := by
    constructor
    · change
        ((), fun i => natPointDefinition (codes i) left) =
          ((), fun i => natPointDefinition (codes i) right)
      apply Prod.ext
      · rfl
      · funext i
        simp [natPointDefinition, left_ne_code i, right_ne_code i]
    · change left ≠ right
      dsimp only [left, right]
      omega
  rw [emptyFiniteDefect] at finiteDefect
  exact finiteDefect

/-- Strengthening clause 6's submodular inequality to modular equality is
false when two different definitions capture the same positive-weight edge. -/
theorem false_neighbor_clause6 :
    let weight : Bool → ENNReal := fun _ => 1
    let residual : Set Bool := Set.univ
    let cut : Bool → Set Bool := fun _ => Set.univ
    let captured := fun S : Set Bool =>
      residual ∩ ⋃ definition ∈ S, cut definition
    let mass := fun edges : Set Bool =>
      ∑' edge, edges.indicator weight edge
    ¬mass (captured ({false} ∪ {true})) +
        mass (captured ({false} ∩ {true})) =
      mass (captured {false}) + mass (captured {true}) := by
  classical
  norm_num [tsum_fintype, Set.indicator, Set.mem_inter_iff, Set.mem_iUnion]

/-- Strengthening clause 7's identity to say the displayed defect vanishes is
false for coordinate preparation followed by a swap. -/
theorem false_neighbor_clause7 :
    let projection : Real × Real → Real := Prod.fst
    let update : Real × Real → Real × Real := fun pair => (pair.2, pair.1)
    let prepare : Real → Real × Real := fun value => (value, 0)
    ¬dist (projection (update (0, 1)))
        ((projection ∘ update ∘ prepare) (projection (0, 1))) = 0 := by
  norm_num [Real.dist_eq]

/-- Dropping clause 8's semigroup law is false, here for an `Int`-indexed
evolution whose time-two map is deliberately inconsistent with two time-one
steps. -/
theorem false_neighbor_clause8 :
    let projection : Real → Real := id
    let evolution : Int → Real → Real :=
      fun time state => if time = 2 then state + 1 else state
    let prepare : Real → Real := id
    ¬dist (projection (evolution ((1 : Int) + 1) (prepare 0)))
          (projection (evolution 1
            (prepare (projection (evolution 1 (prepare 0)))))) =
        dist (projection (evolution 1 (evolution 1 (prepare 0))))
          (projection (evolution 1
            ((prepare ∘ projection) (evolution 1 (prepare 0))))) := by
  norm_num [Real.dist_eq]

/-- Deleting the transported second-stage error from clause 9's conclusion is
false even for the identity Lipschitz map. -/
theorem false_neighbor_clause9 :
    ¬(LipschitzWith (1 : NNReal) (id : Real → Real) →
      dist ((id : Real → Real) 0) 1 ≤ 1 →
      dist ((id : Real → Real) 1) ((fun _ : Real => 2) 0) ≤ 1 →
      dist ((id : Real → Real) ((id : Real → Real) 0))
          ((fun _ : Real => 2) 0) ≤
        (1 : NNReal) * (1 : Real)) := by
  intro falseBound
  have impossible := falseBound LipschitzWith.id
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
  norm_num [Real.dist_eq] at impossible

#print axioms directly_provable_laws

end D5.S3.ConceptDynamics.DefinitionEscape.DirectlyProvableLaws
