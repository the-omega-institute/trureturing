import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace GapsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps

theorem dependence : ObservationalDependence Gaps.signature actual := by
  intro i
  refine ⟨(0 : ℕ), [], [(1 : ℕ)], ?_⟩
  dsimp only [Gaps.actual, Gaps.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ Gaps.arena.Law rejected := by
  intro h
  have h := @h 0 [1] (Gapped.last (by decide))
  have h := h.2.1
  change (0 : ℕ) = 1 at h
  cases h

def registration : Registration Gaps.arena (∀ {m : ℕ} {input : List ℕ}
    (hgapped : Gapped m input),
    assembleGaps (highEntries m input) (gapSlots m input) = input ∧
      (gapSlots m input).length = (highEntries m input).length ∧
      (gapSlots m input).filterMap id = lowEntries m input) where
  actual := Gaps.actual
  bridge := Iff.rfl
  variation := ⟨@gapped_filters_slots, Gaps.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.gapped_filters_slots) (type_of% (realize.{0, 0, 0, 0, 0} Gaps.signature (fun _ m input => gapSlots m input) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "gapped_filters_slots") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(Gaps.arena)⟩,
  objectArena := .source ⟨(Gaps.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (Gaps.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} Gaps.signature (fun _ m input => gapSlots m input) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.gapped_filters_slots, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.anchorEnumeration }


end GapsAudit

namespace SuccessPermAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm

theorem dependence : ObservationalDependence SuccessPerm.signature actual := by
  intro i
  refine ⟨(), [], [(0 : ℕ)], ?_⟩
  dsimp only [SuccessPerm.actual, SuccessPerm.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ SuccessPerm.arena.Law rejected := by
  intro h
  have h := @h 0 [0] rfl
  have h := h.length_eq
  change (1 : ℕ) = 0 at h
  cases h

def registration : Registration SuccessPerm.arena (∀ {n : ℕ} {input : List ℕ}
    (houtput : cyclicStackSort input = target n),
    input.Perm (List.range' 1 n)) where
  actual := SuccessPerm.actual
  bridge := Iff.rfl
  variation := ⟨@success_perm_range, SuccessPerm.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.success_perm_range) (type_of% (realize.{0, 0, 0, 0, 0} SuccessPerm.signature (fun _ _ input => cyclicStackSort input) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "success_perm_range") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(SuccessPerm.arena)⟩,
  objectArena := .source ⟨(SuccessPerm.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (SuccessPerm.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} SuccessPerm.signature (fun _ _ input => cyclicStackSort input) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "domain", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.success_perm_range, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.anchorEnumeration }


end SuccessPermAudit

namespace SuccessGappedAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessGapped

theorem dependence : ObservationalDependence SuccessPerm.signature SuccessPerm.actual := by
  intro i
  refine ⟨(), [], [(0 : ℕ)], ?_⟩
  dsimp only [SuccessPerm.actual, SuccessPerm.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ SuccessGapped.arena.Law rejected := by
  intro h
  have h := @h 2 (by decide) [1] rfl
  cases h with
  | last hhigh => exact (Nat.lt_irrefl 1) hhigh

def registration : Registration SuccessGapped.arena (∀ {n : ℕ} (hn : 2 ≤ n) {input : List ℕ}
    (houtput : cyclicStackSort input = target n),
    Gapped (n / 2) input) where
  actual := SuccessPerm.actual
  bridge := Iff.rfl
  variation := ⟨@successful_gapped, SuccessGapped.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.successful_gapped) (type_of% (realize.{0, 0, 0, 0, 0} SuccessPerm.signature (fun _ _ input => cyclicStackSort input) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "successful_gapped") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessGapped.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(SuccessGapped.arena)⟩,
  objectArena := .source ⟨(SuccessGapped.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (SuccessGapped.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} SuccessPerm.signature (fun _ _ input => cyclicStackSort input) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "domain", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_gapped, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.anchorEnumeration }


end SuccessGappedAudit

namespace LowOrderAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder

theorem dependence : ObservationalDependence LowOrder.signature actual := by
  intro i
  refine ⟨(2 : ℕ), [], [(1 : ℕ)], ?_⟩
  dsimp only [LowOrder.actual, LowOrder.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ LowOrder.arena.Law rejected := by
  intro h
  have h := @h 0 [] Gapped.nil rfl
  have h := (List.pairwise_cons.mp h).1 0 (by simp)
  exact (Nat.not_lt_zero 1) h

def registration : Registration LowOrder.arena (∀ {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input)
    (houtput : cyclicStackSort input = target n),
    (lowEntries (n / 2) input).Pairwise (fun x y => x < y)) where
  actual := LowOrder.actual
  bridge := Iff.rfl
  variation := ⟨@successful_lows_pairwise, LowOrder.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.successful_lows_pairwise) (type_of% (realize.{0, 0, 0, 0, 0} LowOrder.signature (fun _ (n : ℕ) input => lowEntries (n / 2) input) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "successful_lows_pairwise") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(LowOrder.arena)⟩,
  objectArena := .source ⟨(LowOrder.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (LowOrder.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} LowOrder.signature (fun _ (n : ℕ) input => lowEntries (n / 2) input) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_lows_pairwise, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.anchorEnumeration }


end LowOrderAudit

namespace OneNoneAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone

theorem dependence : ObservationalDependence OneNone.signature actual := by
  intro i
  refine ⟨(), [], [some (0 : ℕ)], ?_⟩
  dsimp only [OneNone.actual, OneNone.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ OneNone.arena.Law rejected := by
  intro h
  have h := @h [some 0] [] rfl rfl
  obtain ⟨i, hi, heq⟩ := h
  have hi : i = 0 := by simpa using hi
  subst i
  cases heq

def registration : Registration OneNone.arena (∀ {slots : List (Option ℕ)} {lows : List ℕ}
    (hfilter : slots.filterMap id = lows)
    (hlen : slots.length = lows.length + 1),
    ∃ omitted < lows.length + 1, slots = insertNone omitted lows) where
  actual := OneNone.actual
  bridge := Iff.rfl
  variation := ⟨@options_one_none, OneNone.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_5 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.options_one_none) (type_of% (realize.{0, 0, 0, 0, 0} OneNone.signature (fun _ _ slots => slots.filterMap id.{1}) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "options_one_none") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(OneNone.arena)⟩,
  objectArena := .source ⟨(OneNone.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (OneNone.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} OneNone.signature (fun _ _ slots => slots.filterMap id.{1}) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "domain", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.options_one_none, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.anchorEnumeration }


end OneNoneAudit

namespace EvenSlotsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots

theorem dependence : ObservationalDependence EvenSlots.signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [EvenSlots.actual, EvenSlots.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ EvenSlots.arena.Law rejected := by
  intro h
  have h := @h 1
  change ([] : List (Option ℕ)) = [some 1] at h
  cases h

def registration : Registration EvenSlots.arena (∀ (m : ℕ),
    candidateSlots m 0 m = (List.range' 1 m).map some) where
  actual := EvenSlots.actual
  bridge := Iff.rfl
  variation := ⟨@candidateSlots_even, EvenSlots.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_6 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_even) (type_of% (realize.{0, 0, 0, 0, 0} EvenSlots.signature (fun _ _ m => candidateSlots m 0 m) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "candidateSlots_even") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(EvenSlots.arena)⟩,
  objectArena := .source ⟨(EvenSlots.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (EvenSlots.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} EvenSlots.signature (fun _ _ m => candidateSlots m 0 m) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_even, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.anchorEnumeration }


end EvenSlotsAudit

namespace OddSlotsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots

theorem dependence : ObservationalDependence OddSlots.signature actual := by
  intro i
  refine ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [OddSlots.actual, OddSlots.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ OddSlots.arena.Law rejected := by
  intro h
  have h := @h 0 0 (by decide)
  change ([] : List (Option ℕ)) = [none] at h
  cases h

def registration : Registration OddSlots.arena (∀ (m omitted : ℕ) (homitted : omitted < m + 1),
    candidateSlots omitted 0 (m + 1) = insertNone omitted (List.range' 1 m)) where
  actual := OddSlots.actual
  bridge := Iff.rfl
  variation := ⟨@candidateSlots_odd, OddSlots.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_7 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_odd) (type_of% (realize.{0, 0, 0, 0, 0} OddSlots.signature (fun _ (m : ℕ) omitted => candidateSlots omitted 0 (m + 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "candidateSlots_odd") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(OddSlots.arena)⟩,
  objectArena := .source ⟨(OddSlots.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (OddSlots.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} OddSlots.signature (fun _ (m : ℕ) omitted => candidateSlots omitted 0 (m + 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_odd, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.anchorEnumeration }


end OddSlotsAudit

namespace CandidateAssemblyAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly

theorem dependence : ObservationalDependence CandidateAssembly.signature actual := by
  intro i
  refine ⟨⟨(1 : ℕ), (2 : ℕ)⟩, (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [CandidateAssembly.actual, CandidateAssembly.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ CandidateAssembly.arena.Law rejected := by
  intro h
  have h := @h 0 1 0
  change ([] : List ℕ) = [1] at h
  cases h

def registration : Registration CandidateAssembly.arena (∀ (m highCount omitted : ℕ),
    candidate m highCount omitted =
      assembleGaps (List.range' (m + 1) highCount)
        (candidateSlots omitted 0 highCount)) where
  actual := CandidateAssembly.actual
  bridge := Iff.rfl
  variation := ⟨@candidate_eq_assemble, CandidateAssembly.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_8 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.candidate_eq_assemble) (type_of% (realize.{0, 0, 0, 0, 0} CandidateAssembly.signature (fun _ p omitted => candidate p.1 p.2 omitted) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "candidate_eq_assemble") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(CandidateAssembly.arena)⟩,
  objectArena := .source ⟨(CandidateAssembly.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (CandidateAssembly.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} CandidateAssembly.signature (fun _ p omitted => candidate p.1 p.2 omitted) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidate_eq_assemble, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.anchorEnumeration }


end CandidateAssemblyAudit

namespace FilledSomeAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome

theorem dependence : ObservationalDependence FilledSome.signature actual := by
  intro i
  refine ⟨(), [], [(0 : ℕ)], ?_⟩
  dsimp only [FilledSome.actual, FilledSome.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ FilledSome.arena.Law rejected := by
  intro h
  have h := @h []
  cases h

def registration : Registration FilledSome.arena (∀ (lows : List ℕ),
    FilledUntilLast (lows.map some)) where
  actual := FilledSome.actual
  bridge := Iff.rfl
  variation := ⟨@filledUntilLast_map_some, FilledSome.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_9 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_map_some) (type_of% (realize.{0, 0, 0, 0, 0} FilledSome.signature (fun _ _ lows => lows.map some.{0}) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "filledUntilLast_map_some") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(FilledSome.arena)⟩,
  objectArena := .source ⟨(FilledSome.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (FilledSome.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} FilledSome.signature (fun _ _ lows => lows.map some.{0}) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_map_some, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.anchorEnumeration }


end FilledSomeAudit

namespace FilledLastAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast

theorem dependence : ObservationalDependence FilledLast.signature actual := by
  intro i
  refine ⟨(), [], [(0 : ℕ)], ?_⟩
  dsimp only [FilledLast.actual, FilledLast.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ FilledLast.arena.Law rejected := by
  intro h
  have h := @h []
  cases h

def registration : Registration FilledLast.arena (∀ (lows : List ℕ),
    FilledUntilLast (insertNone lows.length lows)) where
  actual := FilledLast.actual
  bridge := Iff.rfl
  variation := ⟨@filledUntilLast_insertNone_last, FilledLast.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_10 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_insertNone_last) (type_of% (realize.{0, 0, 0, 0, 0} FilledLast.signature (fun _ _ lows => insertNone lows.length lows) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "filledUntilLast_insertNone_last") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(FilledLast.arena)⟩,
  objectArena := .source ⟨(FilledLast.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (FilledLast.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} FilledLast.signature (fun _ _ lows => insertNone lows.length lows) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_insertNone_last, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.anchorEnumeration }


end FilledLastAudit

namespace HighOrderAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder

theorem dependence : ObservationalDependence HighOrder.signature actual := by
  intro i
  refine ⟨(0 : ℕ), [], [(1 : ℕ)], ?_⟩
  dsimp only [HighOrder.actual, HighOrder.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ HighOrder.arena.Law rejected := by
  intro h
  have h := @h 0 [] Gapped.nil FilledUntilLast.nil rfl
  have h := (List.pairwise_cons.mp h).1 0 (by simp)
  exact (Nat.not_lt_zero 1) h

def registration : Registration HighOrder.arena (∀ {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input)
    (hfilled : FilledUntilLast (gapSlots (n / 2) input))
    (houtput : cyclicStackSort input = target n),
    (highEntries (n / 2) input).Pairwise (fun x y => x < y)) where
  actual := HighOrder.actual
  bridge := Iff.rfl
  variation := ⟨@successful_highs_of_filled_until_last, HighOrder.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_11 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.successful_highs_of_filled_until_last) (type_of% (realize.{0, 0, 0, 0, 0} HighOrder.signature (fun _ (n : ℕ) input => highEntries (n / 2) input) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "successful_highs_of_filled_until_last") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(HighOrder.arena)⟩,
  objectArena := .source ⟨(HighOrder.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (HighOrder.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} HighOrder.signature (fun _ (n : ℕ) input => highEntries (n / 2) input) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_highs_of_filled_until_last, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.anchorEnumeration }


end HighOrderAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessGapped.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessGapped.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.arena
    (∀ (m highCount omitted : Nat),
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.candidate m highCount omitted)
        (D5.S1.Words.Patterns.CyclicStackPreimages.assembleGaps
          (List.range'
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            highCount (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots omitted
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) highCount)))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidate_eq_assemble\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidate_eq_assemble, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.arena
  (∀ (m highCount omitted : Nat),
    @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.candidate m highCount omitted)
      (D5.S1.Words.Patterns.CyclicStackPreimages.assembleGaps
        (List.range'
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          highCount (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots omitted
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) highCount)))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.observation0 : (m highCount omitted : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.signature PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) m highCount) :=
  fun (m highCount omitted : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) m highCount) omitted

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidate_eq_assemble\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidate_eq_assemble, part := .type, path := [.body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidate_eq_assemble\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidate_eq_assemble, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"CandidateAssemblyAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.CandidateAssemblyAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.arena
    (∀ (lows : List.{0} Nat),
      D5.S1.Words.Patterns.CyclicStackPreimages.FilledUntilLast
        (D5.S1.Words.Patterns.CyclicStackPreimages.insertNone (@List.length.{0} Nat lows) lows))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"filledUntilLast_insertNone_last\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_insertNone_last, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.arena
  (∀ (lows : List.{0} Nat),
    D5.S1.Words.Patterns.CyclicStackPreimages.FilledUntilLast
      (D5.S1.Words.Patterns.CyclicStackPreimages.insertNone (@List.length.{0} Nat lows) lows))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.observation0 : (lows : List.{0} Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (lows : List.{0} Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast.actual PUnit.unit.{1} PUnit.unit.{1} lows

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"filledUntilLast_insertNone_last\"],\"part\":\"type\",\"path\":[\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_insertNone_last, part := .type, path := [.body, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"filledUntilLast_insertNone_last\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_insertNone_last, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledLastAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledLastAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.arena
    (∀ {m : Nat} {input : List.{0} Nat} (hgapped : D5.S1.Words.Patterns.CyclicStackPreimages.Gapped m input),
      And
        (@Eq.{1} (List.{0} Nat)
          (D5.S1.Words.Patterns.CyclicStackPreimages.assembleGaps
            (D5.S1.Words.Patterns.CyclicStackPreimages.highEntries m input)
            (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots m input))
          input)
        (And
          (@Eq.{1} Nat (@List.length.{0} (Option.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots m input))
            (@List.length.{0} Nat (D5.S1.Words.Patterns.CyclicStackPreimages.highEntries m input)))
          (@Eq.{1} (List.{0} Nat)
            (@List.filterMap.{0, 0} (Option.{0} Nat) Nat (@id.{1} (Option.{0} Nat))
              (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots m input))
            (D5.S1.Words.Patterns.CyclicStackPreimages.lowEntries m input))))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"gapped_filters_slots\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.gapped_filters_slots, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.arena
  (∀ {m : Nat} {input : List.{0} Nat} (hgapped : D5.S1.Words.Patterns.CyclicStackPreimages.Gapped m input),
    And
      (@Eq.{1} (List.{0} Nat)
        (D5.S1.Words.Patterns.CyclicStackPreimages.assembleGaps
          (D5.S1.Words.Patterns.CyclicStackPreimages.highEntries m input)
          (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots m input))
        input)
      (And
        (@Eq.{1} Nat (@List.length.{0} (Option.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots m input))
          (@List.length.{0} Nat (D5.S1.Words.Patterns.CyclicStackPreimages.highEntries m input)))
        (@Eq.{1} (List.{0} Nat)
          (@List.filterMap.{0, 0} (Option.{0} Nat) Nat (@id.{1} (Option.{0} Nat))
            (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots m input))
          (D5.S1.Words.Patterns.CyclicStackPreimages.lowEntries m input))))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.observation0 : {m : Nat} →
  {input : List.{0} Nat} →
    (hgapped : D5.S1.Words.Patterns.CyclicStackPreimages.Gapped m input) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.signature PUnit.unit.{1} m :=
  fun {m : Nat} {input : List.{0} Nat} (hgapped : D5.S1.Words.Patterns.CyclicStackPreimages.Gapped m input) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps.actual PUnit.unit.{1} m input

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"gapped_filters_slots\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.gapped_filters_slots, part := .type, path := [.body, .body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"gapped_filters_slots\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.gapped_filters_slots, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"GapsAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.GapsAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.arena
    (∀ (lows : List.{0} Nat),
      D5.S1.Words.Patterns.CyclicStackPreimages.FilledUntilLast
        (@List.map.{0, 0} Nat (Option.{0} Nat) (@Option.some.{0} Nat) lows))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"filledUntilLast_map_some\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_map_some, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.arena
  (∀ (lows : List.{0} Nat),
    D5.S1.Words.Patterns.CyclicStackPreimages.FilledUntilLast
      (@List.map.{0, 0} Nat (Option.{0} Nat) (@Option.some.{0} Nat) lows))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.observation0 : (lows : List.{0} Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (lows : List.{0} Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome.actual PUnit.unit.{1} PUnit.unit.{1} lows

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"filledUntilLast_map_some\"],\"part\":\"type\",\"path\":[\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_map_some, part := .type, path := [.body, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"filledUntilLast_map_some\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.filledUntilLast_map_some, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"FilledSomeAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.FilledSomeAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.arena
    (∀ {n : Nat} {input : List.{0} Nat}
      (houtput :
        @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
          (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
      @List.Perm.{0} Nat input
        (List.range' (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"success_perm_range\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.success_perm_range, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.arena
  (∀ {n : Nat} {input : List.{0} Nat}
    (houtput :
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
    @List.Perm.{0} Nat input
      (List.range' (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.observation0 : {n : Nat} →
  {input : List.{0} Nat} →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {n : Nat} {input : List.{0} Nat} =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.actual PUnit.unit.{1} PUnit.unit.{1} input

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"success_perm_range\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.success_perm_range, part := .type, path := [.body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"success_perm_range\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.success_perm_range, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessPermAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessPermAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.arena
    (∀ (m : Nat),
      @Eq.{1} (List.{0} (Option.{0} Nat))
        (D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots m
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
        (@List.map.{0, 0} Nat (Option.{0} Nat) (@Option.some.{0} Nat)
          (List.range' (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidateSlots_even\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_even, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.arena
  (∀ (m : Nat),
    @Eq.{1} (List.{0} (Option.{0} Nat))
      (D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots m
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
      (@List.map.{0, 0} Nat (Option.{0} Nat) (@Option.some.{0} Nat)
        (List.range' (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.observation0 : (m : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (m : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots.actual PUnit.unit.{1} PUnit.unit.{1} m

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidateSlots_even\"],\"part\":\"type\",\"path\":[\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_even, part := .type, path := [.body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidateSlots_even\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_even, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"EvenSlotsAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.EvenSlotsAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.arena
    (∀ {slots : List.{0} (Option.{0} Nat)} {lows : List.{0} Nat}
      (hfilter :
        @Eq.{1} (List.{0} Nat) (@List.filterMap.{0, 0} (Option.{0} Nat) Nat (@id.{1} (Option.{0} Nat)) slots) lows)
      (hlen :
        @Eq.{1} Nat (@List.length.{0} (Option.{0} Nat) slots)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat lows)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Exists.{1} Nat fun (omitted : Nat) =>
        And
          (@LT.lt.{0} Nat instLTNat omitted
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat lows)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Eq.{1} (List.{0} (Option.{0} Nat)) slots
            (D5.S1.Words.Patterns.CyclicStackPreimages.insertNone omitted lows)))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"options_one_none\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.options_one_none, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.arena
  (∀ {slots : List.{0} (Option.{0} Nat)} {lows : List.{0} Nat}
    (hfilter :
      @Eq.{1} (List.{0} Nat) (@List.filterMap.{0, 0} (Option.{0} Nat) Nat (@id.{1} (Option.{0} Nat)) slots) lows)
    (hlen :
      @Eq.{1} Nat (@List.length.{0} (Option.{0} Nat) slots)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat lows)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
    @Exists.{1} Nat fun (omitted : Nat) =>
      And
        (@LT.lt.{0} Nat instLTNat omitted
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat lows)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Eq.{1} (List.{0} (Option.{0} Nat)) slots (D5.S1.Words.Patterns.CyclicStackPreimages.insertNone omitted lows)))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.observation0 : {slots : List.{0} (Option.{0} Nat)} →
  {lows : List.{0} Nat} →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {slots : List.{0} (Option.{0} Nat)} {lows : List.{0} Nat} =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone.actual PUnit.unit.{1} PUnit.unit.{1} slots

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"options_one_none\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.options_one_none, part := .type, path := [.body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"options_one_none\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.options_one_none, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OneNoneAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OneNoneAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessGapped.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessGapped.arena
    (∀ {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
      {input : List.{0} Nat}
      (houtput :
        @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
          (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
      D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_gapped\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_gapped, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessGapped.arena
  (∀ {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
    {input : List.{0} Nat}
    (houtput :
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
    D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      input)
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.observation0 : {n : Nat} →
  (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n) →
    {input : List.{0} Nat} →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
    {input : List.{0} Nat} =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm.actual PUnit.unit.{1} PUnit.unit.{1} input

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_gapped\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_gapped, part := .type, path := [.body, .body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_gapped\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_gapped, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"SuccessGappedAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.SuccessGappedAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.arena
    (∀ {n : Nat} {input : List.{0} Nat}
      (hgapped :
        D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input)
      (hfilled :
        D5.S1.Words.Patterns.CyclicStackPreimages.FilledUntilLast
          (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            input))
      (houtput :
        @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
          (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
      @List.Pairwise.{0} Nat (fun (x y : Nat) => @LT.lt.{0} Nat instLTNat x y)
        (D5.S1.Words.Patterns.CyclicStackPreimages.highEntries
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_highs_of_filled_until_last\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_highs_of_filled_until_last, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.arena
  (∀ {n : Nat} {input : List.{0} Nat}
    (hgapped :
      D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
    (hfilled :
      D5.S1.Words.Patterns.CyclicStackPreimages.FilledUntilLast
        (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input))
    (houtput :
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
    @List.Pairwise.{0} Nat (fun (x y : Nat) => @LT.lt.{0} Nat instLTNat x y)
      (D5.S1.Words.Patterns.CyclicStackPreimages.highEntries
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.observation0 : {n : Nat} →
  {input : List.{0} Nat} →
    (hgapped :
        D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input) →
      (hfilled :
          D5.S1.Words.Patterns.CyclicStackPreimages.FilledUntilLast
            (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              input)) →
        (houtput :
            @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
              (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.signature PUnit.unit.{1} n :=
  fun {n : Nat} {input : List.{0} Nat}
    (hgapped :
      D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
    (hfilled :
      D5.S1.Words.Patterns.CyclicStackPreimages.FilledUntilLast
        (D5.S1.Words.Patterns.CyclicStackPreimages.gapSlots
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input))
    (houtput :
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.actual PUnit.unit.{1} n input

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_highs_of_filled_until_last\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_highs_of_filled_until_last, part := .type, path := [.body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_highs_of_filled_until_last\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_highs_of_filled_until_last, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration_11\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"HighOrderAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration_11, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.HighOrderAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.arena
    (∀ (m omitted : Nat)
      (homitted :
        @LT.lt.{0} Nat instLTNat omitted
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Eq.{1} (List.{0} (Option.{0} Nat))
        (D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots omitted
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (D5.S1.Words.Patterns.CyclicStackPreimages.insertNone omitted
          (List.range' (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidateSlots_odd\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_odd, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.arena
  (∀ (m omitted : Nat)
    (homitted :
      @LT.lt.{0} Nat instLTNat omitted
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
    @Eq.{1} (List.{0} (Option.{0} Nat))
      (D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots omitted
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (D5.S1.Words.Patterns.CyclicStackPreimages.insertNone omitted
        (List.range' (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.observation0 : (m omitted : Nat) →
  (homitted :
      @LT.lt.{0} Nat instLTNat omitted
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.signature PUnit.unit.{1} m :=
  fun (m omitted : Nat)
    (homitted :
      @LT.lt.{0} Nat instLTNat omitted
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots.actual PUnit.unit.{1} m omitted

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidateSlots_odd\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_odd, part := .type, path := [.body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"candidateSlots_odd\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.candidateSlots_odd, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"OddSlotsAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.OddSlotsAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.arena
    (∀ {n : Nat} {input : List.{0} Nat}
      (hgapped :
        D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input)
      (houtput :
        @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
          (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
      @List.Pairwise.{0} Nat (fun (x y : Nat) => @LT.lt.{0} Nat instLTNat x y)
        (D5.S1.Words.Patterns.CyclicStackPreimages.lowEntries
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_lows_pairwise\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_lows_pairwise, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.arena
  (∀ {n : Nat} {input : List.{0} Nat}
    (hgapped :
      D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
    (houtput :
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
    @List.Pairwise.{0} Nat (fun (x y : Nat) => @LT.lt.{0} Nat instLTNat x y)
      (D5.S1.Words.Patterns.CyclicStackPreimages.lowEntries
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.observation0 : {n : Nat} →
  {input : List.{0} Nat} →
    (hgapped :
        D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input) →
      (houtput :
          @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
            (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.signature PUnit.unit.{1} n :=
  fun {n : Nat} {input : List.{0} Nat}
    (hgapped :
      D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
    (houtput :
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder.actual PUnit.unit.{1} n input

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_lows_pairwise\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_lows_pairwise, part := .type, path := [.body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_lows_pairwise\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_lows_pairwise, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesInvariants\",\"LowOrderAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants.LowOrderAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
