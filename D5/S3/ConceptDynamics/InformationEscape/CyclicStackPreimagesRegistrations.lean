/- GID: D5/S3/ConceptDynamics/InformationEscape/CyclicStackPreimagesRegistrations
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/CyclicStackPreimages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite cyclic-stack source readouts register the full symbolic proof declarations. -/

import D5.S1.Words.Patterns.CyclicStackPreimages
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import LeanInformationAudit.RegistrationWitnesses
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
open LeanInformationAudit

namespace D5.S1.Words.Patterns.CyclicStackPreimages.Registration

open D5.S1.Words.Patterns.CyclicStackPreimages

abbrev sourceSignature (X : Type) : PrimitiveSignature X where
  Index := Fin 6
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Fin 250
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def sourceWordRealization {X : Type} (readWord : X → Fin 6 → Fin 250) :
    PrimitiveRealization (sourceSignature X) where
  readout index state := readWord state index
  anchor := Fin.elim0

register_information_template sourceWordRealization

def sourceRealization : PrimitiveRealization (sourceSignature CyclicStackSourceWord) :=
  sourceWordRealization fun word index => word index

def bumpCode (code : Fin 250) : Fin 250 :=
  if code = 0 then 1 else 0

private theorem bumpCode_ne (code : Fin 250) : bumpCode code ≠ code := by
  by_cases h : code = 0
  · subst code
    norm_num [bumpCode]
  · simp only [bumpCode, h, ↓reduceIte]
    exact fun hzero => h hzero.symm

def alteredRealization (changed : Fin 6) :
    PrimitiveRealization (sourceSignature CyclicStackSourceWord) :=
  sourceWordRealization fun word index =>
    if index = changed then bumpCode (word index) else word index

def SourceCalibration (word : CyclicStackSourceWord) : Prop :=
  word = cyclicStackSourceWord ∧
    forbidden 1 2 3 = true ∧ forbidden 1 3 2 = false ∧
    forbidden 2 1 3 = false ∧ forbidden 2 3 1 = true ∧
    forbidden 3 1 2 = true ∧ forbidden 3 2 1 = false ∧
    process [3, 1, 2, 4] [] = [4, 2, 1, 3] ∧
    candidate 2 2 2 = [3, 1, 4, 2]

local instance : DecidableEq CyclicStackSourceWord := inferInstance

private theorem actualCalibration : SourceCalibration cyclicStackSourceWord := by
  refine ⟨rfl, ?_⟩
  decide

def sourceArenaFor (statement : Prop) : PrimitiveLawArena where
  toArena := Arena.ofFintype CyclicStackSourceWord
  signature := sourceSignature CyclicStackSourceWord
  Law realization :=
    let readWord : CyclicStackSourceWord := fun index =>
      realization.readout index cyclicStackSourceWord
    statement ↔ SourceCalibration readWord

private theorem altered_not_law (statement : Prop) (hstatement : statement) (changed : Fin 6) :
    ¬(sourceArenaFor statement).Law (alteredRealization changed) := by
  intro law
  have equality := (law.mp hstatement).1
  have atChanged := congrFun equality changed
  apply bumpCode_ne (cyclicStackSourceWord changed)
  simpa [alteredRealization, sourceWordRealization, sourceSignature] using atChanged

private theorem sourceVariation (statement : Prop) (hstatement : statement) :
    FiniteLawVariation (sourceArenaFor statement) := by
  exact ⟨sourceRealization, alteredRealization 0,
    ⟨fun _ => actualCalibration, fun _ => hstatement⟩,
    altered_not_law statement hstatement 0⟩

private theorem sourceSensitivity (statement : Prop) (hstatement : statement) :
    FiniteSlotSensitivity (sourceArenaFor statement) := by
  classical
  constructor
  · intro i
    refine ⟨sourceRealization, alteredRealization i, ?_, ?_, ?_⟩
    · intro j hne
      funext word
      simp only [sourceRealization, alteredRealization, sourceWordRealization, sourceSignature]
      split
      · next h => exact (hne h).elim
      · rfl
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => altered_not_law statement hstatement i,
        fun _ => ⟨fun _ => actualCalibration, fun _ => hstatement⟩⟩
  · intro i
    exact Fin.elim0 i

syntax "register_cyclic_stack_route " ident " for " ident : command

open Lean Meta Elab Command in
elab_rules : command
  | `(register_cyclic_stack_route $_route:ident for $theoremName:ident) =>
    registrationTransaction do
      let theoremName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo theoremName
      let theoremInfo ← getConstInfo theoremName
      let env ← getEnv
      let bridgeName := localCompanionName env theoremName primitiveRealizationSuffix
      let unitName := localCompanionName env theoremName theoremUnitSuffix
      let arenaName := mkPrivateName env (theoremName.str "__source_arena")
      let variationName := mkPrivateName env (theoremName.str "__source_variation")
      let sensitivityName := mkPrivateName env (theoremName.str "__source_sensitivity")
      let descriptor ← liftTermElabM do
        let descriptor ← Term.elabTerm
          (← `(term| (@sourceWordRealization CyclicStackSourceWord
            (fun word index => word index)))) none
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars descriptor
      let escapeInput : EscapeRecordInput := {
        fromObject := some (mkConst ``cyclicStackSourceWord)
        openContinuation := true
      }
      TemplateBinding.withDeclaration {
        theoremName
        arena := arenaName
        descriptor := some descriptor
        escapeInput
      } do
        liftTermElabM do
          let arenaType := mkConst ``PrimitiveLawArena [.zero, .zero, .zero]
          let arenaValue := mkApp (mkConst ``sourceArenaFor) theoremInfo.type
          addAndCompile (.defnDecl {
            name := arenaName
            levelParams := theoremInfo.levelParams
            type := arenaType
            value := arenaValue
            hints := .abbrev
            safety := .safe
          })
          let arena := mkConst arenaName (theoremInfo.levelParams.map Level.param)
          let realization := mkConst ``sourceRealization
          let bridgeType ← mkAppM ``EscapePrimitiveRealization
            #[arena, theoremInfo.type, realization]
          let theoremProof := mkConst theoremName (theoremInfo.levelParams.map Level.param)
          let bridgeValue ← Term.elabTerm
            (← `(term| by
              constructor
              intro h
              exact ⟨fun _ => actualCalibration, fun _ => h⟩)) (some bridgeType)
          Term.synthesizeSyntheticMVarsNoPostponing
          let bridgeType ← instantiateMVars bridgeType
          let bridgeValue ← instantiateMVars bridgeValue
          addDecl (.thmDecl {
            name := bridgeName
            levelParams := theoremInfo.levelParams
            type := bridgeType
            value := bridgeValue
          })
          let objectArena := mkApp
            (mkConst ``PrimitiveLawArena.toArena [.zero, .zero, .zero]) arena
          let compiled ← compilePrimitiveBundle arena realization
          let primitives ← instantiateMVars <| mkAppN
            (mkConst ``PrimitiveRealization.toPrimitiveBundle [.zero, .zero, .zero])
            compiled.getAppArgs
          let unitValue ← instantiateMVars <| mkAppN
            (mkConst ``TheoremUnit.mk [.zero, .zero])
            #[objectArena, primitives, theoremInfo.type, theoremProof]
          let unitType ← instantiateMVars (← inferType unitValue)
          addAndCompile (.defnDecl {
            name := unitName
            levelParams := theoremInfo.levelParams
            type := unitType
            value := unitValue
            hints := .abbrev
            safety := .safe
          })
          let variationType ← mkAppM ``FiniteLawVariation #[arena]
          let variationValue := mkAppN (mkConst ``sourceVariation)
            #[theoremInfo.type, theoremProof]
          addDecl (.thmDecl {
            name := variationName
            levelParams := theoremInfo.levelParams
            type := variationType
            value := variationValue
          })
          let sensitivityType ← mkAppM ``FiniteSlotSensitivity #[arena]
          let sensitivityValue := mkAppN (mkConst ``sourceSensitivity)
            #[theoremInfo.type, theoremProof]
          addDecl (.thmDecl {
            name := sensitivityName
            levelParams := theoremInfo.levelParams
            type := sensitivityType
            value := sensitivityValue
          })
        registerValidatedEntry {
          theoremName
          unitName
          arenaName
          realizationName := bridgeName
          variationWitness := variationName
          sensitivityWitness := sensitivityName
        }

register_cyclic_stack_route ZhanBieConjectures34 for zhan_bie_conjectures_3_4
register_cyclic_stack_route TargetPermRange for target_perm_range
register_cyclic_stack_route OddCandidateLowerBound for oddCandidate_lower_bound
register_cyclic_stack_route EvenCandidateLowerBound for evenCandidate_lower_bound
register_cyclic_stack_route ProcessEqRun for process_eq_run
register_cyclic_stack_route ProcessAppend for process_append
register_cyclic_stack_route ProcessPerm for process_perm
register_cyclic_stack_route TargetLowOrder for target_low_order
register_cyclic_stack_route DrainLowOverHigh for drain_low_over_high
register_cyclic_stack_route NoTwoLowsAfterHigh for no_two_lows_after_high
register_cyclic_stack_route PendingLowForcesHighIncrease for pending_low_forces_high_increase
register_cyclic_stack_route DrainHighWhileLowRemains for drain_high_while_low_remains
register_cyclic_stack_route PendingLowDrainsOnlyLow for
  pending_low_drains_only_low_while_low_remains
register_cyclic_stack_route ProcessPendingLow for process_pending_low_while_low_remains
register_cyclic_stack_route NoLowsBeforeFirstHigh for no_lows_before_first_high
register_cyclic_stack_route SuccessfulHighEntriesFinalLow for successful_high_entries_final_low
register_cyclic_stack_route SuccessfulHighEntries for successful_high_entries
register_cyclic_stack_route AssembleInsertNoneEnds for assemble_insert_none_ends
register_cyclic_stack_route SuccessfulHighLength for successful_high_length
register_cyclic_stack_route GappedFiltersSlots for gapped_filters_slots
register_cyclic_stack_route SuccessPermRange for success_perm_range
register_cyclic_stack_route SuccessfulGapped for successful_gapped
register_cyclic_stack_route SuccessfulLowsPairwise for successful_lows_pairwise
register_cyclic_stack_route HighEntriesRange for highEntries_range
register_cyclic_stack_route SuccessfulLowEntries for successful_low_entries
register_cyclic_stack_route OptionsAllSome for options_all_some
register_cyclic_stack_route OptionsOneNone for options_one_none
register_cyclic_stack_route CandidateSlotsEven for candidateSlots_even
register_cyclic_stack_route CandidateSlotsOdd for candidateSlots_odd
register_cyclic_stack_route CandidateEqAssemble for candidate_eq_assemble
register_cyclic_stack_route FilledUntilLastMapSome for filledUntilLast_map_some
register_cyclic_stack_route FilledUntilLastInsertNoneLast for filledUntilLast_insertNone_last
register_cyclic_stack_route SuccessfulHighsFilledUntilLast for successful_highs_of_filled_until_last

end D5.S1.Words.Patterns.CyclicStackPreimages.Registration
