/- GID: D5/S0/Automata/FinitePartialSignatureCompletion
   generality: G
   mirror-B: D5/B/S0/Automata/FinitePartialSignatureCompletion
   mirror-E: none(waiver:finite-signature-completion)
   anchors: [mathlib/module/Mathlib]
   digest: Deduplicated full signatures together with fresh output-only and return-only requirements admit a completion with exactly the number of full pairs plus the maximum of the two residual projection counts, and every injective completion has at least that many states. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.FinitePartialSignatureCompletion

universe u

/-- Normalized finite partial-signature data. `Full` indexes already fixed
output-return pairs. `OutputOnly` and `ReturnOnly` index residual requirements
whose corresponding projections do not occur in a full pair. -/
structure Requirements
    (Output Class Full OutputOnly ReturnOnly : Type u) where
  fullSignature : Full ↪ Output × Class
  outputRequirement : OutputOnly ↪ Output
  returnRequirement : ReturnOnly ↪ Class
  output_fresh :
    ∀ output full,
      outputRequirement output ≠ (fullSignature full).1
  return_fresh :
    ∀ target full,
      returnRequirement target ≠ (fullSignature full).2

/-- The predicted minimum number of distinct completed signatures. -/
def requiredSignatureCount
    {Output Class Full OutputOnly ReturnOnly : Type u}
    [Fintype Full] [Fintype OutputOnly] [Fintype ReturnOnly]
    (_requirements :
      Requirements Output Class Full OutputOnly ReturnOnly) : Nat :=
  Fintype.card Full +
    max (Fintype.card OutputOnly) (Fintype.card ReturnOnly)

/-- A finite injective completion of normalized partial-signature data. The
three witness maps need not be declared injective: injectivity follows from the
signature embedding and freshness of the normalized requirements. -/
structure Completion
    {Output Class Full OutputOnly ReturnOnly : Type u}
    (requirements :
      Requirements Output Class Full OutputOnly ReturnOnly) where
  State : Type u
  stateFintype : Fintype State
  signature : State ↪ Output × Class
  fullState : Full → State
  full_spec :
    ∀ full,
      signature (fullState full) = requirements.fullSignature full
  outputState : OutputOnly → State
  output_spec :
    ∀ output,
      (signature (outputState output)).1 =
        requirements.outputRequirement output
  returnState : ReturnOnly → State
  return_spec :
    ∀ target,
      (signature (returnState target)).2 =
        requirements.returnRequirement target

namespace Completion

variable {Output Class Full OutputOnly ReturnOnly : Type u}
variable [Fintype Full] [Fintype OutputOnly] [Fintype ReturnOnly]
variable (requirements :
  Requirements Output Class Full OutputOnly ReturnOnly)

/-- Full-pair witnesses and residual-output witnesses occupy pairwise distinct
completion states. -/
def fullOutputMap (completion : Completion requirements) :
    Full ⊕ OutputOnly → completion.State
  | Sum.inl full => completion.fullState full
  | Sum.inr output => completion.outputState output

/-- The full-pair plus residual-output witness map is injective. -/
theorem fullOutputMap_injective (completion : Completion requirements) :
    Function.Injective (fullOutputMap requirements completion) := by
  intro left right equal
  cases left with
  | inl leftFull =>
      cases right with
      | inl rightFull =>
          have signatureEqual :
              requirements.fullSignature leftFull =
                requirements.fullSignature rightFull := by
            calc
              requirements.fullSignature leftFull =
                  completion.signature (completion.fullState leftFull) :=
                (completion.full_spec leftFull).symm
              _ = completion.signature (completion.fullState rightFull) := by
                rw [equal]
              _ = requirements.fullSignature rightFull :=
                completion.full_spec rightFull
          exact congrArg Sum.inl
            (requirements.fullSignature.injective signatureEqual)
      | inr output =>
          exfalso
          have firstEqual :
              (requirements.fullSignature leftFull).1 =
                requirements.outputRequirement output := by
            calc
              (requirements.fullSignature leftFull).1 =
                  (completion.signature
                    (completion.fullState leftFull)).1 := by
                rw [completion.full_spec]
              _ = (completion.signature
                    (completion.outputState output)).1 := by
                rw [equal]
              _ = requirements.outputRequirement output :=
                completion.output_spec output
          exact requirements.output_fresh output leftFull firstEqual.symm
  | inr leftOutput =>
      cases right with
      | inl full =>
          exfalso
          have firstEqual :
              requirements.outputRequirement leftOutput =
                (requirements.fullSignature full).1 := by
            calc
              requirements.outputRequirement leftOutput =
                  (completion.signature
                    (completion.outputState leftOutput)).1 :=
                (completion.output_spec leftOutput).symm
              _ = (completion.signature
                    (completion.fullState full)).1 := by
                rw [equal]
              _ = (requirements.fullSignature full).1 := by
                rw [completion.full_spec]
          exact requirements.output_fresh leftOutput full firstEqual
      | inr rightOutput =>
          have outputEqual :
              requirements.outputRequirement leftOutput =
                requirements.outputRequirement rightOutput := by
            calc
              requirements.outputRequirement leftOutput =
                  (completion.signature
                    (completion.outputState leftOutput)).1 :=
                (completion.output_spec leftOutput).symm
              _ = (completion.signature
                    (completion.outputState rightOutput)).1 := by
                rw [equal]
              _ = requirements.outputRequirement rightOutput :=
                completion.output_spec rightOutput
          exact congrArg Sum.inr
            (requirements.outputRequirement.injective outputEqual)

/-- Full-pair witnesses and residual-return witnesses occupy pairwise distinct
completion states. -/
def fullReturnMap (completion : Completion requirements) :
    Full ⊕ ReturnOnly → completion.State
  | Sum.inl full => completion.fullState full
  | Sum.inr target => completion.returnState target

/-- The full-pair plus residual-return witness map is injective. -/
theorem fullReturnMap_injective (completion : Completion requirements) :
    Function.Injective (fullReturnMap requirements completion) := by
  intro left right equal
  cases left with
  | inl leftFull =>
      cases right with
      | inl rightFull =>
          have signatureEqual :
              requirements.fullSignature leftFull =
                requirements.fullSignature rightFull := by
            calc
              requirements.fullSignature leftFull =
                  completion.signature (completion.fullState leftFull) :=
                (completion.full_spec leftFull).symm
              _ = completion.signature (completion.fullState rightFull) := by
                rw [equal]
              _ = requirements.fullSignature rightFull :=
                completion.full_spec rightFull
          exact congrArg Sum.inl
            (requirements.fullSignature.injective signatureEqual)
      | inr target =>
          exfalso
          have secondEqual :
              (requirements.fullSignature leftFull).2 =
                requirements.returnRequirement target := by
            calc
              (requirements.fullSignature leftFull).2 =
                  (completion.signature
                    (completion.fullState leftFull)).2 := by
                rw [completion.full_spec]
              _ = (completion.signature
                    (completion.returnState target)).2 := by
                rw [equal]
              _ = requirements.returnRequirement target :=
                completion.return_spec target
          exact requirements.return_fresh target leftFull secondEqual.symm
  | inr leftTarget =>
      cases right with
      | inl full =>
          exfalso
          have secondEqual :
              requirements.returnRequirement leftTarget =
                (requirements.fullSignature full).2 := by
            calc
              requirements.returnRequirement leftTarget =
                  (completion.signature
                    (completion.returnState leftTarget)).2 :=
                (completion.return_spec leftTarget).symm
              _ = (completion.signature
                    (completion.fullState full)).2 := by
                rw [equal]
              _ = (requirements.fullSignature full).2 := by
                rw [completion.full_spec]
          exact requirements.return_fresh leftTarget full secondEqual
      | inr rightTarget =>
          have targetEqual :
              requirements.returnRequirement leftTarget =
                requirements.returnRequirement rightTarget := by
            calc
              requirements.returnRequirement leftTarget =
                  (completion.signature
                    (completion.returnState leftTarget)).2 :=
                (completion.return_spec leftTarget).symm
              _ = (completion.signature
                    (completion.returnState rightTarget)).2 := by
                rw [equal]
              _ = requirements.returnRequirement rightTarget :=
                completion.return_spec rightTarget
          exact congrArg Sum.inr
            (requirements.returnRequirement.injective targetEqual)

/-- Every completion has enough states for all full pairs and all residual
output projections. -/
theorem full_add_output_card_le
    (completion : Completion requirements) :
    Fintype.card Full + Fintype.card OutputOnly ≤
      Fintype.card completion.State := by
  letI := completion.stateFintype
  simpa using
    Fintype.card_le_of_injective
      (fullOutputMap requirements completion)
      (fullOutputMap_injective requirements completion)

/-- Every completion has enough states for all full pairs and all residual
return projections. -/
theorem full_add_return_card_le
    (completion : Completion requirements) :
    Fintype.card Full + Fintype.card ReturnOnly ≤
      Fintype.card completion.State := by
  letI := completion.stateFintype
  simpa using
    Fintype.card_le_of_injective
      (fullReturnMap requirements completion)
      (fullReturnMap_injective requirements completion)

/-- Universal lower bound: no injective completion can use fewer than the full
pair count plus the larger residual projection count. -/
theorem requiredSignatureCount_le_card
    (completion : Completion requirements) :
    requiredSignatureCount requirements ≤
      Fintype.card completion.State := by
  unfold requiredSignatureCount
  rcases le_total (Fintype.card OutputOnly)
      (Fintype.card ReturnOnly) with outputLeReturn | returnLeOutput
  · rw [Nat.max_eq_right outputLeReturn]
    exact full_add_return_card_le requirements completion
  · rw [Nat.max_eq_left returnLeOutput]
    exact full_add_output_card_le requirements completion

end Completion

section OptimalConstruction

variable {Output Class Full OutputOnly ReturnOnly : Type u}
variable [Fintype Full] [Fintype OutputOnly] [Fintype ReturnOnly]
variable [Nonempty Output] [Nonempty Class]
variable (requirements :
  Requirements Output Class Full OutputOnly ReturnOnly)

private noncomputable def defaultOutput : Output :=
  Classical.choice (inferInstance : Nonempty Output)

private noncomputable def defaultClass : Class :=
  Classical.choice (inferInstance : Nonempty Class)

private noncomputable def outputAtReturnIndex
    (bound : Fintype.card OutputOnly ≤ Fintype.card ReturnOnly)
    (index : Fin (Fintype.card ReturnOnly)) : Output :=
  if inside : index.val < Fintype.card OutputOnly then
    requirements.outputRequirement
      ((Fintype.equivFin OutputOnly).symm ⟨index.val, inside⟩)
  else
    defaultOutput

private noncomputable def returnAtIndex
    (index : Fin (Fintype.card ReturnOnly)) : Class :=
  requirements.returnRequirement
    ((Fintype.equivFin ReturnOnly).symm index)

private theorem outputAtReturnIndex_castLE
    (bound : Fintype.card OutputOnly ≤ Fintype.card ReturnOnly)
    (output : OutputOnly) :
    outputAtReturnIndex requirements bound
        (Fin.castLE bound ((Fintype.equivFin OutputOnly) output)) =
      requirements.outputRequirement output := by
  unfold outputAtReturnIndex
  let smallIndex := (Fintype.equivFin OutputOnly) output
  have inside :
      (Fin.castLE bound smallIndex).val < Fintype.card OutputOnly :=
    smallIndex.isLt
  rw [dif_pos inside]
  have sameIndex :
      (⟨(Fin.castLE bound smallIndex).val, inside⟩ :
        Fin (Fintype.card OutputOnly)) = smallIndex := by
    apply Fin.ext
    rfl
  rw [sameIndex]
  simp [smallIndex]

private theorem returnAtIndex_equiv
    (target : ReturnOnly) :
    returnAtIndex requirements ((Fintype.equivFin ReturnOnly) target) =
      requirements.returnRequirement target := by
  simp [returnAtIndex]

private noncomputable def signatureWhenOutputLeReturn
    (bound : Fintype.card OutputOnly ≤ Fintype.card ReturnOnly) :
    Full ⊕ Fin (Fintype.card ReturnOnly) → Output × Class
  | Sum.inl full => requirements.fullSignature full
  | Sum.inr index =>
      (outputAtReturnIndex requirements bound index,
        returnAtIndex requirements index)

private theorem signatureWhenOutputLeReturn_injective
    (bound : Fintype.card OutputOnly ≤ Fintype.card ReturnOnly) :
    Function.Injective (signatureWhenOutputLeReturn requirements bound) := by
  intro left right equal
  cases left with
  | inl leftFull =>
      cases right with
      | inl rightFull =>
          exact congrArg Sum.inl
            (requirements.fullSignature.injective equal)
      | inr index =>
          exfalso
          have secondEqual :
              (requirements.fullSignature leftFull).2 =
                returnAtIndex requirements index :=
            congrArg Prod.snd equal
          exact requirements.return_fresh
            ((Fintype.equivFin ReturnOnly).symm index) leftFull
            (by simpa [returnAtIndex] using secondEqual.symm)
  | inr leftIndex =>
      cases right with
      | inl full =>
          exfalso
          have secondEqual :
              returnAtIndex requirements leftIndex =
                (requirements.fullSignature full).2 :=
            congrArg Prod.snd equal
          exact requirements.return_fresh
            ((Fintype.equivFin ReturnOnly).symm leftIndex) full
            (by simpa [returnAtIndex] using secondEqual)
      | inr rightIndex =>
          have returnEqual :
              requirements.returnRequirement
                  ((Fintype.equivFin ReturnOnly).symm leftIndex) =
                requirements.returnRequirement
                  ((Fintype.equivFin ReturnOnly).symm rightIndex) := by
            simpa [returnAtIndex] using congrArg Prod.snd equal
          have indexPreimageEqual :
              (Fintype.equivFin ReturnOnly).symm leftIndex =
                (Fintype.equivFin ReturnOnly).symm rightIndex :=
            requirements.returnRequirement.injective returnEqual
          exact congrArg Sum.inr
            ((Fintype.equivFin ReturnOnly).symm.injective
              indexPreimageEqual)

private noncomputable def completionWhenOutputLeReturn
    (bound : Fintype.card OutputOnly ≤ Fintype.card ReturnOnly) :
    Completion requirements where
  State := Full ⊕ Fin (Fintype.card ReturnOnly)
  stateFintype := inferInstance
  signature :=
    ⟨signatureWhenOutputLeReturn requirements bound,
      signatureWhenOutputLeReturn_injective requirements bound⟩
  fullState := Sum.inl
  full_spec := by
    intro full
    rfl
  outputState := fun output =>
    Sum.inr (Fin.castLE bound ((Fintype.equivFin OutputOnly) output))
  output_spec := by
    intro output
    exact outputAtReturnIndex_castLE requirements bound output
  returnState := fun target =>
    Sum.inr ((Fintype.equivFin ReturnOnly) target)
  return_spec := by
    intro target
    exact returnAtIndex_equiv requirements target

private theorem completionWhenOutputLeReturn_card
    (bound : Fintype.card OutputOnly ≤ Fintype.card ReturnOnly) :
    Fintype.card (completionWhenOutputLeReturn requirements bound).State =
      requiredSignatureCount requirements := by
  simp [completionWhenOutputLeReturn, requiredSignatureCount,
    Nat.max_eq_right bound]

private noncomputable def returnAtOutputIndex
    (bound : Fintype.card ReturnOnly ≤ Fintype.card OutputOnly)
    (index : Fin (Fintype.card OutputOnly)) : Class :=
  if inside : index.val < Fintype.card ReturnOnly then
    requirements.returnRequirement
      ((Fintype.equivFin ReturnOnly).symm ⟨index.val, inside⟩)
  else
    defaultClass

private noncomputable def outputAtIndex
    (index : Fin (Fintype.card OutputOnly)) : Output :=
  requirements.outputRequirement
    ((Fintype.equivFin OutputOnly).symm index)

private theorem returnAtOutputIndex_castLE
    (bound : Fintype.card ReturnOnly ≤ Fintype.card OutputOnly)
    (target : ReturnOnly) :
    returnAtOutputIndex requirements bound
        (Fin.castLE bound ((Fintype.equivFin ReturnOnly) target)) =
      requirements.returnRequirement target := by
  unfold returnAtOutputIndex
  let smallIndex := (Fintype.equivFin ReturnOnly) target
  have inside :
      (Fin.castLE bound smallIndex).val < Fintype.card ReturnOnly :=
    smallIndex.isLt
  rw [dif_pos inside]
  have sameIndex :
      (⟨(Fin.castLE bound smallIndex).val, inside⟩ :
        Fin (Fintype.card ReturnOnly)) = smallIndex := by
    apply Fin.ext
    rfl
  rw [sameIndex]
  simp [smallIndex]

private theorem outputAtIndex_equiv
    (output : OutputOnly) :
    outputAtIndex requirements ((Fintype.equivFin OutputOnly) output) =
      requirements.outputRequirement output := by
  simp [outputAtIndex]

private noncomputable def signatureWhenReturnLeOutput
    (bound : Fintype.card ReturnOnly ≤ Fintype.card OutputOnly) :
    Full ⊕ Fin (Fintype.card OutputOnly) → Output × Class
  | Sum.inl full => requirements.fullSignature full
  | Sum.inr index =>
      (outputAtIndex requirements index,
        returnAtOutputIndex requirements bound index)

private theorem signatureWhenReturnLeOutput_injective
    (bound : Fintype.card ReturnOnly ≤ Fintype.card OutputOnly) :
    Function.Injective (signatureWhenReturnLeOutput requirements bound) := by
  intro left right equal
  cases left with
  | inl leftFull =>
      cases right with
      | inl rightFull =>
          exact congrArg Sum.inl
            (requirements.fullSignature.injective equal)
      | inr index =>
          exfalso
          have firstEqual :
              (requirements.fullSignature leftFull).1 =
                outputAtIndex requirements index :=
            congrArg Prod.fst equal
          exact requirements.output_fresh
            ((Fintype.equivFin OutputOnly).symm index) leftFull
            (by simpa [outputAtIndex] using firstEqual.symm)
  | inr leftIndex =>
      cases right with
      | inl full =>
          exfalso
          have firstEqual :
              outputAtIndex requirements leftIndex =
                (requirements.fullSignature full).1 :=
            congrArg Prod.fst equal
          exact requirements.output_fresh
            ((Fintype.equivFin OutputOnly).symm leftIndex) full
            (by simpa [outputAtIndex] using firstEqual)
      | inr rightIndex =>
          have outputEqual :
              requirements.outputRequirement
                  ((Fintype.equivFin OutputOnly).symm leftIndex) =
                requirements.outputRequirement
                  ((Fintype.equivFin OutputOnly).symm rightIndex) := by
            simpa [outputAtIndex] using congrArg Prod.fst equal
          have indexPreimageEqual :
              (Fintype.equivFin OutputOnly).symm leftIndex =
                (Fintype.equivFin OutputOnly).symm rightIndex :=
            requirements.outputRequirement.injective outputEqual
          exact congrArg Sum.inr
            ((Fintype.equivFin OutputOnly).symm.injective
              indexPreimageEqual)

private noncomputable def completionWhenReturnLeOutput
    (bound : Fintype.card ReturnOnly ≤ Fintype.card OutputOnly) :
    Completion requirements where
  State := Full ⊕ Fin (Fintype.card OutputOnly)
  stateFintype := inferInstance
  signature :=
    ⟨signatureWhenReturnLeOutput requirements bound,
      signatureWhenReturnLeOutput_injective requirements bound⟩
  fullState := Sum.inl
  full_spec := by
    intro full
    rfl
  outputState := fun output =>
    Sum.inr ((Fintype.equivFin OutputOnly) output)
  output_spec := by
    intro output
    exact outputAtIndex_equiv requirements output
  returnState := fun target =>
    Sum.inr (Fin.castLE bound ((Fintype.equivFin ReturnOnly) target))
  return_spec := by
    intro target
    exact returnAtOutputIndex_castLE requirements bound target

private theorem completionWhenReturnLeOutput_card
    (bound : Fintype.card ReturnOnly ≤ Fintype.card OutputOnly) :
    Fintype.card (completionWhenReturnLeOutput requirements bound).State =
      requiredSignatureCount requirements := by
  simp [completionWhenReturnLeOutput, requiredSignatureCount,
    Nat.max_eq_left bound]

/-- Sharpness: normalized partial-signature data always has an injective
completion attaining the universal lower bound. -/
noncomputable theorem exists_optimal_completion :
    ∃ completion : Completion requirements,
      Fintype.card completion.State =
        requiredSignatureCount requirements := by
  rcases le_total (Fintype.card OutputOnly)
      (Fintype.card ReturnOnly) with outputLeReturn | returnLeOutput
  · exact ⟨completionWhenOutputLeReturn requirements outputLeReturn,
      completionWhenOutputLeReturn_card requirements outputLeReturn⟩
  · exact ⟨completionWhenReturnLeOutput requirements returnLeOutput,
      completionWhenReturnLeOutput_card requirements returnLeOutput⟩

/-- Exact minimum theorem: the closed formula is a lower bound for every
completion and is attained by a canonical padded pairing construction. -/
theorem finite_partial_signature_completion_exact :
    (∀ completion : Completion requirements,
      requiredSignatureCount requirements ≤
        Fintype.card completion.State) ∧
    ∃ completion : Completion requirements,
      Fintype.card completion.State =
        requiredSignatureCount requirements := by
  constructor
  · intro completion
    exact Completion.requiredSignatureCount_le_card
      requirements completion
  · exact exists_optimal_completion requirements

end OptimalConstruction

section FinsetAdapter

universe w

variable {Output Class : Type w}
variable [DecidableEq Output] [DecidableEq Class]

/-- First projection of a finite set of full signatures. -/
def outputProjection (full : Finset (Output × Class)) : Finset Output :=
  full.image Prod.fst

/-- Second projection of a finite set of full signatures. -/
def returnProjection (full : Finset (Output × Class)) : Finset Class :=
  full.image Prod.snd

/-- Output-only requirements not already covered by a full signature. -/
def residualOutputs
    (full : Finset (Output × Class))
    (outputs : Finset Output) : Finset Output :=
  outputs \ outputProjection full

/-- Return-only requirements not already covered by a full signature. -/
def residualReturns
    (full : Finset (Output × Class))
    (targets : Finset Class) : Finset Class :=
  targets \ returnProjection full

/-- Convert ordinary finite sets of full, output-only, and return-only
requirements into the normalized indexed representation used by the exact
minimum theorem. -/
def requirementsOfFinsets
    (full : Finset (Output × Class))
    (outputs : Finset Output)
    (targets : Finset Class) :
    Requirements Output Class
      (↥full)
      (↥(residualOutputs full outputs))
      (↥(residualReturns full targets)) where
  fullSignature := ⟨Subtype.val, Subtype.val_injective⟩
  outputRequirement := ⟨Subtype.val, Subtype.val_injective⟩
  returnRequirement := ⟨Subtype.val, Subtype.val_injective⟩
  output_fresh := by
    intro output fullPair equal
    have notProjected : output.1 ∉ outputProjection full :=
      (Finset.mem_sdiff.mp output.2).2
    apply notProjected
    exact Finset.mem_image.mpr
      ⟨fullPair.1, fullPair.2, equal.symm⟩
  return_fresh := by
    intro target fullPair equal
    have notProjected : target.1 ∉ returnProjection full :=
      (Finset.mem_sdiff.mp target.2).2
    apply notProjected
    exact Finset.mem_image.mpr
      ⟨fullPair.1, fullPair.2, equal.symm⟩

/-- The abstract count specializes to the expected finite-set formula. -/
@[simp] theorem requiredSignatureCount_requirementsOfFinsets
    (full : Finset (Output × Class))
    (outputs : Finset Output)
    (targets : Finset Class) :
    requiredSignatureCount
      (requirementsOfFinsets full outputs targets) =
      full.card +
        max (residualOutputs full outputs).card
          (residualReturns full targets).card := by
  simp [requiredSignatureCount]

/-- Finset-facing exact completion theorem. -/
theorem finite_partial_signature_completion_finsets
    [Nonempty Output] [Nonempty Class]
    (full : Finset (Output × Class))
    (outputs : Finset Output)
    (targets : Finset Class) :
    let requirements := requirementsOfFinsets full outputs targets
    (∀ completion : Completion requirements,
      full.card +
          max (residualOutputs full outputs).card
            (residualReturns full targets).card ≤
        Fintype.card completion.State) ∧
    ∃ completion : Completion requirements,
      Fintype.card completion.State =
        full.card +
          max (residualOutputs full outputs).card
            (residualReturns full targets).card := by
  intro requirements
  simpa [requirements] using
    finite_partial_signature_completion_exact requirements

#print axioms Completion.requiredSignatureCount_le_card
#print axioms exists_optimal_completion
#print axioms finite_partial_signature_completion_exact
#print axioms finite_partial_signature_completion_finsets

end FinsetAdapter

end D5.S0.Automata.FinitePartialSignatureCompletion
