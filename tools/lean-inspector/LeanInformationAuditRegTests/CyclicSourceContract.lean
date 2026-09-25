import Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
import D5.S1.Words.Patterns.CyclicStackPreimages

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily

namespace LeanInformationAuditRegTests.CyclicSourceContract

private def originalNames : Array (Name × Name) := #[
  (`D5.S1.Words.Patterns.CyclicStackPreimages.zhan_bie_conjectures_3_4, `D5.S1.Words.Patterns.CyclicStackPreimages),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.oddCandidate_lower_bound, `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.evenCandidate_lower_bound, `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.process_append, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.process_perm, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.drain_low_over_high, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.no_two_lows_after_high, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_forces_high_increase, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.drain_high_while_low_remains, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_drains_only_low_while_low_remains, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.process_pending_low_while_low_remains, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.no_lows_before_first_high, `D5.S1.Words.Patterns.CyclicStackPreimagesCore),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.successful_high_entries_final_low, `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.assemble_insert_none_ends, `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.gapped_filters_slots, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.success_perm_range, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.successful_gapped, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.successful_lows_pairwise, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.options_one_none, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_even, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_odd, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.candidate_eq_assemble, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_map_some, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_insertNone_last, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants),
  (`D5.S1.Words.Patterns.CyclicStackPreimages.successful_highs_of_filled_until_last, `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants)]

run_meta do
  unless originalNames.size == 26 do throwError "incorrect live original inventory"
  for (name, owner) in originalNames do
    unless (← getConstInfo name).isTheorem &&
        RegistrationReifier.declaringModuleOf (← getEnv) name == some owner do
      throwError "original theorem owner differs: {name}"
  logInfo "[PASS] all_26_live_original_cyclicstack_compiler_owners"
  let snapshot ← TemplateBinding.exportSnapshot
  let records := snapshot.selected.filter (fun record =>
    record.occurrence.key.registrationModule == `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore)
  unless records.size == 2 do throwError "expected two original unbounded registrations"
  for record in records do
    let .declaredValidated cert := record.result
      | throwError "original unbounded source failed: {(← TemplateBinding.recordJson record).compress}"
    unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
        record.escape.continuation.any (·.kind == "open") do throwError "incomplete unbounded record"
    logInfo m!"[PASS] unbounded_original {record.occurrence.key.theoremName} evidence_ref={cert.evidenceRef}"
  let wires ← TemplateBinding.reportJson #[(
    `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, records.map (·.occurrence.key))]
  let output := (← Repository.root) / ".lake/build/cyclic-family-evidence.json"
  IO.FS.writeFile output ((Json.arr wires).compress ++ "\n")

example : ¬ ObservationalDependence signature rejected := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy rfl

unsafe def unsafeIdentity (x : Nat) : Nat := x
@[implemented_by unsafeIdentity] def redirected (x : Nat) : Nat := x

structure HiddenDecision where
  whole : Decidable (∀ input stack,
    _root_.D5.S1.Words.Patterns.CyclicStackPreimages.process input stack =
      (_root_.D5.S1.Words.Patterns.CyclicStackPreimages.run input stack).1 ++
        (_root_.D5.S1.Words.Patterns.CyclicStackPreimages.run input stack).2)

run_meta do
  for name in #[``unsafeIdentity, ``redirected] do
    let rejected ← try
      discard <| SourceOperands.check
        ``D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run #[mkConst name] 524288
      pure false
    catch _ => pure true
    unless rejected do throwError "unsafe/external identity accepted"
  let discarded := mkApp (.lam `carrier (mkSort (.succ .zero))
    (mkConst ``Unit.unit) .default) (mkConst ``HiddenDecision)
  let rejected ← try
    discard <| SourceOperands.check
      ``D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run #[discarded] 524288
    pure false
  catch _ => pure true
  unless rejected do throwError "target decision hidden in discarded carrier accepted"
  logInfo "[PASS] target_decision_in_discarded_inductive_field"
  let expected ← mkAppM ``Sensitivity #[mkConst ``runArena, mkConst ``actual]
  unless !(← RegistrationGates.checked .anonymous expected) &&
      !(← RegistrationGates.checked ``True.intro expected) do
    throwError "absent or unrelated sensitivity accepted"
  logInfo "[PASS] dead_constant_readout_absent_unrelated_sensitivity_unsafe_external"

end LeanInformationAuditRegTests.CyclicSourceContract
