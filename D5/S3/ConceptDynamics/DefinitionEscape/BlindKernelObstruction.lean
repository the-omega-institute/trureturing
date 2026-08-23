/- GID: D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonempty blind residual obstructs every finite or pointwise language extension. -/

import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-23):
   * `rg -n -F 'blind_kernel_obstruction' D5 Golden/Frozen/accepted` exited 1
     with no output, so the theorem name has no repository or accepted-ledger hit.
   * Searches for `blindKernel`, `blindResidual`, `pointwiseUnion`,
     `finiteSelectionSufficient`, and `compactificationRequired` in the same
     roots also exited 1 with no output.
   * Repository searches found the canonical `Concept`, `conceptJoin`,
     `defectRelation`, and `target_recovery_criterion`; all are imported and
     used directly, and no second target-defect relation is introduced.
   * Pinned Mathlib provides `Setoid.ker`, `Setoid.ker_def`,
     `Function.FactorsThrough`, and `Function.factorsThrough_iff`. The first two
     define the blind-kernel intersection; whole-codomain nonfactorization is
     obtained through the imported recovery criterion rather than reproved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

/-- The blind kernel is the intersection of the kernels of all definitions in
the language package. -/
def blindKernel {X B : Type*} (Gamma : Set (Concept X B)) : Set (X × X) :=
  ⋂ definition : Gamma,
    {pair | Setoid.ker definition.1 pair.1 pair.2}

/-- The blind residual is the canonical target defect restricted to the blind
kernel of the available language. -/
def blindResidual {X C B Target : Type*}
    (Gamma : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) : Set (X × X) :=
  defectRelation q target ∩ blindKernel Gamma

/-- The pointwise union of an indexed family records every definition value. -/
def pointwiseUnion {X B I : Type*}
    (definitions : I → Concept X B) : Concept X (I → B) :=
  fun x i => definitions i x

/-- A language extension retains the baseline readout and joins it with every
value in a pointwise family. -/
def languageExtension {X C B I : Type*} (q : Concept X C)
    (definitions : I → Concept X B) : Concept X (C × (I → B)) :=
  conceptJoin q (pointwiseUnion definitions)

/-- A finite selection succeeds when some finite indexed subfamily of the
package eliminates the canonical target defect. -/
def finiteSelectionSufficient {X C B Target : Type*}
    (Gamma : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) : Prop :=
  ∃ (n : ℕ) (definitions : Fin n → Gamma),
    defectRelation
      (languageExtension q (fun i => (definitions i).1)) target = ∅

/-- Compactification is required exactly when the full pointwise language is
sufficient but no finite selection is sufficient. -/
def compactificationRequired {X C B Target : Type*}
    (Gamma : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) : Prop :=
  defectRelation
      (languageExtension q (fun definition : Gamma => definition.1)) target = ∅ ∧
    ¬finiteSelectionSufficient Gamma q target

/-- Empty blind residual means the full pointwise language is sufficient and
leaves exactly the finite-selection/compactification alternative. A nonempty
blind residual prevents factorization through every finite or arbitrary
pointwise family from the package, so finite package search cannot succeed. -/
theorem blind_kernel_obstruction
    {X C B Target : Type*} (Gamma : Set (Concept X B))
    (q : Concept X C) (target : Concept X Target) :
    (blindResidual Gamma q target = ∅ →
      defectRelation
          (languageExtension q (fun definition : Gamma => definition.1)) target = ∅ ∧
        (finiteSelectionSufficient Gamma q target ∨
          compactificationRequired Gamma q target)) ∧
    ((blindResidual Gamma q target).Nonempty →
      (∀ (n : ℕ) (definitions : Fin n → Gamma),
        ¬∃ recover : (C × (Fin n → B)) → Target,
          target = recover ∘
            languageExtension q (fun i => (definitions i).1)) ∧
      (∀ Delta : Set Gamma,
        ¬∃ recover : (C × (Delta → B)) → Target,
          target = recover ∘
            languageExtension q (fun definition : Delta => definition.1.1)) ∧
      ¬finiteSelectionSufficient Gamma q target) := by
  have fullDefect :
      defectRelation
          (languageExtension q (fun definition : Gamma => definition.1)) target =
        blindResidual Gamma q target := by
    ext pair
    change
      ((q pair.1,
          pointwiseUnion (fun definition : Gamma => definition.1) pair.1) =
          (q pair.2,
            pointwiseUnion (fun definition : Gamma => definition.1) pair.2) ∧
        target pair.1 ≠ target pair.2) ↔
      ((q pair.1 = q pair.2 ∧ target pair.1 ≠ target pair.2) ∧
        pair ∈ blindKernel Gamma)
    constructor
    · rintro ⟨extensionEqual, targetDifferent⟩
      have baselineEqual : q pair.1 = q pair.2 :=
        congrArg Prod.fst extensionEqual
      have languageEqual :
          pointwiseUnion (fun definition : Gamma => definition.1) pair.1 =
            pointwiseUnion (fun definition : Gamma => definition.1) pair.2 :=
        congrArg Prod.snd extensionEqual
      refine ⟨⟨baselineEqual, targetDifferent⟩, ?_⟩
      simp only [blindKernel, Set.mem_iInter, Set.mem_setOf_eq, Setoid.ker_def]
      intro definition
      exact congrFun languageEqual definition
    · rintro ⟨⟨baselineEqual, targetDifferent⟩, pairInKernel⟩
      have allDefinitionsEqual :
          ∀ definition : Gamma,
            definition.1 pair.1 = definition.1 pair.2 := by
        simpa only [blindKernel, Set.mem_iInter, Set.mem_setOf_eq,
          Setoid.ker_def] using pairInKernel
      have languageEqual :
          pointwiseUnion (fun definition : Gamma => definition.1) pair.1 =
            pointwiseUnion (fun definition : Gamma => definition.1) pair.2 := by
        funext definition
        exact allDefinitionsEqual definition
      exact ⟨Prod.ext baselineEqual languageEqual, targetDifferent⟩
  constructor
  · intro emptyResidual
    have languageSufficient :
        defectRelation
            (languageExtension q (fun definition : Gamma => definition.1)) target = ∅ := by
      rw [fullDefect]
      exact emptyResidual
    refine ⟨languageSufficient, ?_⟩
    by_cases finiteSelection : finiteSelectionSufficient Gamma q target
    · exact Or.inl finiteSelection
    · exact Or.inr ⟨languageSufficient, finiteSelection⟩
  · rintro ⟨pair, pairInResidual⟩
    rcases pairInResidual with ⟨baselineDefect, pairInKernel⟩
    letI : Nonempty X := ⟨pair.1⟩
    have allDefinitionsBlind :
        ∀ definition : Gamma,
          definition.1 pair.1 = definition.1 pair.2 := by
      simpa only [blindKernel, Set.mem_iInter, Set.mem_setOf_eq,
        Setoid.ker_def] using pairInKernel
    have finiteObstruction :
        ∀ (n : ℕ) (definitions : Fin n → Gamma),
          ¬∃ recover : (C × (Fin n → B)) → Target,
            target = recover ∘
              languageExtension q (fun i => (definitions i).1) := by
      intro n definitions
      have extensionDefect :
          (defectRelation
            (languageExtension q (fun i => (definitions i).1)) target).Nonempty := by
        refine ⟨pair, ?_, baselineDefect.2⟩
        change
          (q pair.1, fun i => (definitions i).1 pair.1) =
            (q pair.2, fun i => (definitions i).1 pair.2)
        apply Prod.ext baselineDefect.1
        funext i
        exact allDefinitionsBlind (definitions i)
      exact
        (target_recovery_criterion
          (languageExtension q (fun i => (definitions i).1)) target).2.2.2.mpr
            extensionDefect
    have arbitraryObstruction :
        ∀ Delta : Set Gamma,
          ¬∃ recover : (C × (Delta → B)) → Target,
            target = recover ∘
              languageExtension q (fun definition : Delta => definition.1.1) := by
      intro Delta
      have extensionDefect :
          (defectRelation
            (languageExtension q
              (fun definition : Delta => definition.1.1)) target).Nonempty := by
        refine ⟨pair, ?_, baselineDefect.2⟩
        change
          (q pair.1, fun definition : Delta => definition.1.1 pair.1) =
            (q pair.2, fun definition : Delta => definition.1.1 pair.2)
        apply Prod.ext baselineDefect.1
        funext definition
        exact allDefinitionsBlind definition.1
      exact
        (target_recovery_criterion
          (languageExtension q
            (fun definition : Delta => definition.1.1)) target).2.2.2.mpr
              extensionDefect
    refine ⟨finiteObstruction, arbitraryObstruction, ?_⟩
    · rintro ⟨n, definitions, emptyDefect⟩
      have noRecovery := finiteObstruction n definitions
      have recovery :=
        (target_recovery_criterion
          (languageExtension q (fun i => (definitions i).1)) target).2.2.1.mp
            emptyDefect
      exact noRecovery recovery

/-- A constant baseline and constant one-definition package are blind to the
Boolean pair that the identity target distinguishes. -/
example :
    (blindResidual
        {definition : Concept Bool Bool | definition = fun _ => false}
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty ∧
    ¬∃ recover : (Unit × (Fin 1 → Bool)) → Bool,
      (id : Concept Bool Bool) = recover ∘
        languageExtension (fun _ : Bool => ())
          (fun _ : Fin 1 => fun _ : Bool => false) := by
  have residual :
      (blindResidual
        {definition : Concept Bool Bool | definition = fun _ => false}
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty := by
    refine ⟨(false, true), ⟨rfl, Bool.false_ne_true⟩, ?_⟩
    simp only [blindKernel, Set.mem_iInter, Set.mem_setOf_eq, Setoid.ker_def]
    rintro ⟨definition, definitionInPackage⟩
    subst definition
    rfl
  refine ⟨residual, ?_⟩
  exact
    ((blind_kernel_obstruction
      {definition : Concept Bool Bool | definition = fun _ => false}
      (fun _ : Bool => ()) (id : Concept Bool Bool)).2 residual).1
      1 (fun _ : Fin 1 => ⟨fun _ : Bool => false, rfl⟩)

/-- Without a nonempty blind residual, a finite extension may factor the target;
here the baseline identity alone already recovers it. -/
example :
    blindResidual (∅ : Set (Concept Bool Bool))
        (id : Concept Bool Bool) (id : Concept Bool Bool) = ∅ ∧
      ∃ recover : (Bool × (Fin 0 → Bool)) → Bool,
        (id : Concept Bool Bool) = recover ∘
          languageExtension (id : Concept Bool Bool)
            (fun i : Fin 0 => Fin.elim0 i) := by
  constructor
  · ext pair
    simp [blindResidual, defectRelation]
  · exact ⟨Prod.fst, by funext x; rfl⟩

#print axioms blind_kernel_obstruction

end D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
