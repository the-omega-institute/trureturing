/- GID: D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonempty blind residual obstructs every finite or pointwise language extension. -/

import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-24):
   * Shape searches `rg -n 'Set \(X × X\)' D5` and
     `rg -n '⋂ ' D5/S3/ConceptDynamics` found the exact family-kernel definitions
     `conceptKernel` and `jointKernel` in
     `Faithfulness/JointFaithfulnessLeibnizCriterion`; they are imported and
     reused below, so the former local `blindKernel` definition was deleted.
   * `rg -n -i 'joint|common|shared|indexed|family|union|intersection|kernel|readout'
     D5/S3/ConceptDynamics/Faithfulness D5/S3/ConceptDynamics/Experiment
     D5/S3/ConceptDynamics/DefinitionEscape` found the same module's
     `jointReadout` and its existing consumer `ExperimentIdentifiability`;
     `jointReadout` now replaces the former local `pointwiseUnion` definition.
     The public bridge retains its dependent codomain family, so each definition
     code may denote a function into its own type.
   * `rg -n -i 'blind|residual|escape|defect|obstruction|factor|recover|selection|compact'
     D5/S3/ConceptDynamics/DefinitionEscape D5/S3/ConceptDynamics/Restoration
     D5/S3/ConceptDynamics/TargetRisk` found the canonical `defectRelation` and
     `target_recovery_criterion`. `blindResidual` remains only as their new
     named combination with `jointKernel`; factorization is not reproved.
   * The Chinese synonym search `rg -n '盲核|盲残差|逃逸残差|缺陷关系|语言扩展|联合读数|
     点态联合|有限选择|有限子族|有限充分|紧致化|紧致|完备化'
     D5/S3/ConceptDynamics` exited 1 with no hits; the English shape searches
     above supplied the exact canonical declarations.
   * `ls D5/S3/ConceptDynamics/` and
     `git grep -n -E '^def |^  def ' -- D5/S3/ConceptDynamics | head -60`
     surveyed neighboring vocabulary and confirmed the canonical `Concept`,
     `conceptJoin`, family readout/kernel, target defect, and recovery locations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- The blind residual is exactly the canonical `defectRelation` intersected
with the imported `jointKernel` of a possibly dependently typed language. -/
def blindResidual {X C Target Gamma : Type*} {D : Gamma → Type*}
    (definitions : ∀ gamma, Concept X (D gamma)) (q : Concept X C)
    (target : Concept X Target) : Set (X × X) :=
  defectRelation q target ∩
    jointKernel definitions

/-- A language extension retains the baseline readout and joins it with every
value in the imported joint readout of a pointwise family. -/
def languageExtension {X C I : Type*} {D : I → Type*} (q : Concept X C)
    (definitions : ∀ i, Concept X (D i)) : Concept X (C × (∀ i, D i)) :=
  conceptJoin q (jointReadout definitions)

/-- A finite selection succeeds when the target factors through the baseline
extended by some finite indexed subfamily of the package. -/
def finiteSelectionSufficient {X C Target Gamma : Type*} {D : Gamma → Type*}
    (definitions : ∀ gamma, Concept X (D gamma)) (q : Concept X C)
    (target : Concept X Target) : Prop :=
  ∃ (n : ℕ) (codes : Fin n → Gamma)
      (recover : (C × (∀ i, D (codes i))) → Target),
    target = recover ∘ languageExtension q (fun i => definitions (codes i))

/-- Compactification is required exactly when the full pointwise language is
sufficient by factorization but no finite selection is sufficient. -/
def compactificationRequired {X C Target Gamma : Type*} {D : Gamma → Type*}
    (definitions : ∀ gamma, Concept X (D gamma)) (q : Concept X C)
    (target : Concept X Target) : Prop :=
  (∃ recover : (C × (∀ gamma, D gamma)) → Target,
      target = recover ∘
        languageExtension q definitions) ∧
    ¬finiteSelectionSufficient definitions q target

/-- Empty blind residual means the full pointwise language is sufficient and
leaves exactly the finite-selection/compactification alternative. A nonempty
blind residual prevents factorization through every finite or arbitrary
pointwise family from the package, so finite package search cannot succeed. -/
theorem blind_kernel_obstruction
    {X C Target Gamma : Type*} {D : Gamma → Type*} [Nonempty X]
    (definitions : ∀ gamma, Concept X (D gamma))
    (q : Concept X C) (target : Concept X Target) :
    (blindResidual definitions q target = ∅ →
      (∃ recover : (C × (∀ gamma, D gamma)) → Target,
          target = recover ∘
            languageExtension q definitions) ∧
        (finiteSelectionSufficient definitions q target ∨
          compactificationRequired definitions q target)) ∧
    ((blindResidual definitions q target).Nonempty →
      (∀ (n : ℕ) (codes : Fin n → Gamma),
        ¬∃ recover : (C × (∀ i, D (codes i))) → Target,
          target = recover ∘
            languageExtension q (fun i => definitions (codes i))) ∧
      (∀ Delta : Set Gamma,
        ¬∃ recover : (C × (∀ code : Delta, D code.1)) → Target,
          target = recover ∘
            languageExtension q (fun code : Delta => definitions code.1)) ∧
      ¬finiteSelectionSufficient definitions q target) := by
  have fullDefect :
      defectRelation
          (languageExtension q definitions) target =
        blindResidual definitions q target := by
    ext pair
    change
      ((q pair.1,
          jointReadout definitions pair.1) =
          (q pair.2,
            jointReadout definitions pair.2) ∧
        target pair.1 ≠ target pair.2) ↔
      ((q pair.1 = q pair.2 ∧ target pair.1 ≠ target pair.2) ∧
        pair ∈ jointKernel definitions)
    constructor
    · rintro ⟨extensionEqual, targetDifferent⟩
      have baselineEqual : q pair.1 = q pair.2 :=
        congrArg Prod.fst extensionEqual
      have languageEqual :
          jointReadout definitions pair.1 =
            jointReadout definitions pair.2 :=
        congrArg Prod.snd extensionEqual
      refine ⟨⟨baselineEqual, targetDifferent⟩, ?_⟩
      simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
      intro definition
      exact congrFun languageEqual definition
    · rintro ⟨⟨baselineEqual, targetDifferent⟩, pairInKernel⟩
      have allDefinitionsEqual :
          ∀ gamma : Gamma,
            definitions gamma pair.1 = definitions gamma pair.2 := by
        simpa only [jointKernel, conceptKernel, Set.mem_iInter,
          Set.mem_setOf_eq] using pairInKernel
      have languageEqual :
          jointReadout definitions pair.1 =
            jointReadout definitions pair.2 := by
        funext gamma
        exact allDefinitionsEqual gamma
      exact ⟨Prod.ext baselineEqual languageEqual, targetDifferent⟩
  constructor
  · intro emptyResidual
    have languageSufficient :
        defectRelation
            (languageExtension q definitions) target = ∅ := by
      rw [fullDefect]
      exact emptyResidual
    have languageFactorization :
        ∃ recover : (C × (∀ gamma, D gamma)) → Target,
          target = recover ∘
            languageExtension q definitions :=
      (target_recovery_criterion
        (languageExtension q definitions) target).2.2.1.mp
          languageSufficient
    refine ⟨languageFactorization, ?_⟩
    by_cases finiteSelection : finiteSelectionSufficient definitions q target
    · exact Or.inl finiteSelection
    · exact Or.inr ⟨languageFactorization, finiteSelection⟩
  · rintro ⟨pair, pairInResidual⟩
    rcases pairInResidual with ⟨baselineDefect, pairInKernel⟩
    have allDefinitionsBlind :
        ∀ gamma : Gamma,
          definitions gamma pair.1 = definitions gamma pair.2 := by
      simpa only [jointKernel, conceptKernel, Set.mem_iInter,
        Set.mem_setOf_eq] using pairInKernel
    have finiteObstruction :
        ∀ (n : ℕ) (codes : Fin n → Gamma),
          ¬∃ recover : (C × (∀ i, D (codes i))) → Target,
            target = recover ∘
              languageExtension q (fun i => definitions (codes i)) := by
      intro n codes
      have extensionDefect :
          (defectRelation
            (languageExtension q (fun i => definitions (codes i))) target).Nonempty := by
        refine ⟨pair, ?_, baselineDefect.2⟩
        change
          (q pair.1, fun i => definitions (codes i) pair.1) =
            (q pair.2, fun i => definitions (codes i) pair.2)
        apply Prod.ext baselineDefect.1
        funext i
        exact allDefinitionsBlind (codes i)
      exact
        (target_recovery_criterion
          (languageExtension q (fun i => definitions (codes i))) target).2.2.2.mpr
            extensionDefect
    have arbitraryObstruction :
        ∀ Delta : Set Gamma,
          ¬∃ recover : (C × (∀ code : Delta, D code.1)) → Target,
            target = recover ∘
              languageExtension q (fun code : Delta => definitions code.1) := by
      intro Delta
      have extensionDefect :
          (defectRelation
            (languageExtension q
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
          (languageExtension q
            (fun code : Delta => definitions code.1)) target).2.2.2.mpr
              extensionDefect
    refine ⟨finiteObstruction, arbitraryObstruction, ?_⟩
    · rintro ⟨n, codes, recover, recovery⟩
      exact finiteObstruction n codes ⟨recover, recovery⟩

/-- A constant baseline and constant one-definition package are blind to the
Boolean pair that the identity target distinguishes. -/
example :
    (blindResidual
        (fun _ : Unit => fun _ : Bool => false)
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty ∧
    ¬∃ recover : (Unit × (Fin 1 → Bool)) → Bool,
      (id : Concept Bool Bool) = recover ∘
        languageExtension (fun _ : Bool => ())
          (fun _ : Fin 1 => fun _ : Bool => false) := by
  have residual :
      (blindResidual
        (fun _ : Unit => fun _ : Bool => false)
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty := by
    refine ⟨(false, true), ⟨rfl, Bool.false_ne_true⟩, ?_⟩
    simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
    intro gamma
    cases gamma
    trivial
  refine ⟨residual, ?_⟩
  exact
    ((blind_kernel_obstruction
      (fun _ : Unit => fun _ : Bool => false)
      (fun _ : Bool => ()) (id : Concept Bool Bool)).2 residual).1
      1 (fun _ : Fin 1 => ())

/-- Without a nonempty blind residual, a finite extension may factor the target;
here the baseline identity alone already recovers it. -/
example :
    blindResidual (fun code : Empty => (code.elim : Concept Bool Bool))
        (id : Concept Bool Bool) (id : Concept Bool Bool) = ∅ ∧
      ∃ recover : (Bool × (∀ _ : Fin 0, Empty)) → Bool,
        (id : Concept Bool Bool) = recover ∘
          languageExtension (id : Concept Bool Bool)
            (fun i : Fin 0 => Fin.elim0 i) := by
  constructor
  · ext pair
    simp [blindResidual, defectRelation]
  · exact ⟨Prod.fst, by funext x; rfl⟩

/-- The arbitrary-subpackage conjunct is independently exercised: deleting it
from the packaged theorem makes this projection fail to elaborate. -/
example {X C Target Gamma : Type*} {D : Gamma → Type*} [Nonempty X]
    (definitions : ∀ gamma, Concept X (D gamma))
    (q : Concept X C) (target : Concept X Target)
    (residual : (blindResidual definitions q target).Nonempty) (Delta : Set Gamma) :
    ¬∃ recover : (C × (∀ code : Delta, D code.1)) → Target,
      target = recover ∘
        languageExtension q (fun code : Delta => definitions code.1) :=
  ((blind_kernel_obstruction definitions q target).2 residual).2.1 Delta

/-- The rejected empty-state countermodel: its blind residual is empty, but its
extended readout codomain is inhabited and therefore admits no recovery into
`Empty`. The public theorem cannot be instantiated because `Nonempty Empty` is
false. -/
example :
    blindResidual (fun code : Empty => (code.elim : Concept Empty Unit))
        (fun _ : Empty => ()) (id : Concept Empty Empty) = ∅ ∧
      (¬∃ recover : (Unit × (Empty → Unit)) → Empty,
        (id : Concept Empty Empty) = recover ∘
          languageExtension (fun _ : Empty => ())
            (fun code : Empty => (code.elim : Concept Empty Unit))) ∧
      ¬Nonempty Empty := by
  refine ⟨?_, ?_, ?_⟩
  · ext pair
    exact Empty.elim pair.1
  · rintro ⟨recover, _⟩
    exact Empty.elim (recover ((), fun _ => ()))
  · rintro ⟨state⟩
    exact Empty.elim state

#print axioms blind_kernel_obstruction

end D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
