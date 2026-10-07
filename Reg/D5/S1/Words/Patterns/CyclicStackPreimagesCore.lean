import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨[], [], [(0 : ℕ)], ?_⟩
  change ([] : List ℕ) ≠ [0]
  simp

theorem rejected_run : ¬ runArena.Law rejected := by
  intro h
  have h := h [] [0]
  change ([] : List ℕ) = [0] at h
  cases h

theorem rejected_perm : ¬ permArena.Law rejected := by
  intro h
  have h := (h [] [0]).length_eq
  change (0 : ℕ) = 1 at h
  cases h

def runRegistration : Registration runArena (∀ input stack,
    process input stack = (run input stack).1 ++ (run input stack).2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨process_eq_run, rejected, rejected_run⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_run⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := dependence

def permRegistration : Registration permArena (∀ input stack,
    (process input stack).Perm (input ++ stack)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨process_perm, rejected, rejected_perm⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_perm⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ input stack => process input stack) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "process_eq_run") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.runArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.runRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(runArena)⟩,
  objectArena := .source ⟨(runArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (runArena) ⟨(runRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ input stack => process input stack) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.anchorEnumeration }


noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.process_perm) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ input stack => process input stack) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "process_perm") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.permArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.permRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(permArena)⟩,
  objectArena := .source ⟨(permArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (permArena) ⟨(permRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ input stack => process input stack) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_perm, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.anchorEnumeration }


namespace AppendAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append

theorem dependence : ObservationalDependence Append.signature actual := by
  intro i
  refine ⟨⟨[], []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [Append.actual, Append.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ Append.arena.Law rejected := by
  intro h
  have h := @h [] [] [0]
  change ([] : List ℕ) = [0] at h
  cases h

def registration : Registration Append.arena (∀ (pre suffix stack : List ℕ),
    process (pre ++ suffix) stack =
      (run pre stack).1 ++ process suffix (run pre stack).2) where
  actual := Append.actual
  bridge := Iff.rfl
  variation := ⟨@process_append, Append.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.process_append) (type_of% (realize.{0, 0, 0, 0, 0} Append.signature (fun _ p stack => process (p.1 ++ p.2) stack) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "process_append") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(Append.arena)⟩,
  objectArena := .source ⟨(Append.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (Append.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} Append.signature (fun _ p stack => process (p.1 ++ p.2) stack) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_append, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.anchorEnumeration }


end AppendAudit

namespace DrainLowAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow

theorem dependence : ObservationalDependence DrainLow.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ)⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [DrainLow.actual, DrainLow.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ DrainLow.arena.Law rejected := by
  intro h
  have h := @h 2 1 2 (by decide) (by decide) [] [] (by decide)
  change (([], []) : List ℕ × List ℕ) = ([], [2]) at h
  cases h

def registration : Registration DrainLow.arena (∀ {n low high : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) {input stack : List ℕ}
    (houtput : (process (low :: input) (high :: stack)).Sublist (target n)),
    drain low (high :: stack) = ([], high :: stack)) where
  actual := DrainLow.actual
  bridge := Iff.rfl
  variation := ⟨@drain_low_over_high, DrainLow.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.drain_low_over_high) (type_of% (realize.{0, 0, 0, 0, 0} DrainLow.signature (fun _ p stack => drain p.1 (p.2 :: stack)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "drain_low_over_high") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(DrainLow.arena)⟩,
  objectArena := .source ⟨(DrainLow.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (DrainLow.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} DrainLow.signature (fun _ p stack => drain p.1 (p.2 :: stack)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.drain_low_over_high, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.anchorEnumeration }


end DrainLowAudit

namespace TwoLowsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows

theorem dependence : ObservationalDependence TwoLows.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [TwoLows.actual, TwoLows.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ TwoLows.arena.Law rejected := by
  intro h
  have h := @h 2 0 1 2 (by decide) (by decide) (by decide) (by decide) [] [] (List.nil_sublist _)
  exact h

def registration : Registration TwoLows.arena (∀ {n low₁ low₂ high : ℕ}
    (hlow₁ : low₁ ≤ n / 2) (hlow₂ : low₂ ≤ n / 2)
    (hne : low₁ ≠ low₂) (hhigh : n / 2 < high) {input stack : List ℕ}
    (houtput : (process (low₁ :: low₂ :: input) (high :: stack)).Sublist
      (target n)),
    False) where
  actual := TwoLows.actual
  bridge := Iff.rfl
  variation := ⟨@no_two_lows_after_high, TwoLows.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_5 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.no_two_lows_after_high) (type_of% (realize.{0, 0, 0, 0, 0} TwoLows.signature (fun _ p stack => process (p.1 :: p.2.1 :: p.2.2.2) (p.2.2.1 :: stack)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "no_two_lows_after_high") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(TwoLows.arena)⟩,
  objectArena := .source ⟨(TwoLows.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (TwoLows.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} TwoLows.signature (fun _ p stack => process (p.1 :: p.2.1 :: p.2.2.2) (p.2.2.1 :: stack)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[1, 2, 3, 8], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.no_two_lows_after_high, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.anchorEnumeration }


end TwoLowsAudit

namespace HighIncreaseAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease

theorem dependence : ObservationalDependence HighIncrease.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [HighIncrease.actual, HighIncrease.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ HighIncrease.arena.Law rejected := by
  intro h
  have h := @h 0 0 1 1 (by decide) (by decide) [] [] (List.nil_sublist _)
  exact (Nat.lt_irrefl 1) h

def registration : Registration HighIncrease.arena (∀ {n low high next : ℕ}
    (hlow : low ≤ n / 2) (hnext : n / 2 < next)
    {input stack : List ℕ}
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)),
    high < next) where
  actual := HighIncrease.actual
  bridge := Iff.rfl
  variation := ⟨@pending_low_forces_high_increase, HighIncrease.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_6 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_forces_high_increase) (type_of% (realize.{0, 0, 0, 0, 0} HighIncrease.signature (fun _ p stack => process (p.2.2.1 :: p.2.2.2) (p.1 :: p.2.1 :: stack)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "pending_low_forces_high_increase") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(HighIncrease.arena)⟩,
  objectArena := .source ⟨(HighIncrease.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (HighIncrease.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} HighIncrease.signature (fun _ p stack => process (p.2.2.1 :: p.2.2.2) (p.1 :: p.2.1 :: stack)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[1, 2, 3, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_forces_high_increase, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.anchorEnumeration }


end HighIncreaseAudit

namespace DrainHighAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainHigh

theorem dependence : ObservationalDependence DrainLow.signature DrainLow.actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ)⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [DrainLow.actual, DrainLow.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ DrainHigh.arena.Law DrainLow.rejected := by
  intro h
  have h := @h 4 4 3 1 (by decide) (by decide) [1] [] (by simp) (by decide)
  change (([], []) : List ℕ × List ℕ) = ([], [3]) at h
  cases h

def registration : Registration DrainHigh.arena (∀ {n x high futureLow : ℕ}
    (hhigh : n / 2 < high) (hlow : futureLow ≤ n / 2)
    {input stack : List ℕ} (hmem : futureLow ∈ input)
    (houtput : (process (x :: input) (high :: stack)).Sublist (target n)),
    drain x (high :: stack) = ([], high :: stack)) where
  actual := DrainLow.actual
  bridge := Iff.rfl
  variation := ⟨@drain_high_while_low_remains, DrainLow.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_7 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.drain_high_while_low_remains) (type_of% (realize.{0, 0, 0, 0, 0} DrainLow.signature (fun _ p stack => drain p.1 (p.2 :: stack)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "drain_high_while_low_remains") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainHigh.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(DrainHigh.arena)⟩,
  objectArena := .source ⟨(DrainHigh.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (DrainHigh.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} DrainLow.signature (fun _ p stack => drain p.1 (p.2 :: stack)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.drain_high_while_low_remains, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.anchorEnumeration }


end DrainHighAudit

namespace DrainPendingAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending

theorem dependence : ObservationalDependence DrainPending.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ), (0 : ℕ)⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [DrainPending.actual, DrainPending.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ DrainPending.arena.Law rejected := by
  intro h
  have h := @h 4 1 3 4 2 (by decide) (by decide) (by decide) (by decide) [2] [] (by simp) (by decide)
  change (([], []) : List ℕ × List ℕ) = ([1], [3]) at h
  cases h

def registration : Registration DrainPending.arena (∀
    {n low high next futureLow : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hfutureLow : futureLow ≤ n / 2) {input stack : List ℕ}
    (hmem : futureLow ∈ input)
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)),
    drain next (low :: high :: stack) = ([low], high :: stack)) where
  actual := DrainPending.actual
  bridge := Iff.rfl
  variation := ⟨@pending_low_drains_only_low_while_low_remains, DrainPending.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_8 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_drains_only_low_while_low_remains) (type_of% (realize.{0, 0, 0, 0, 0} DrainPending.signature (fun _ p stack => drain p.2.2 (p.1 :: p.2.1 :: stack)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "pending_low_drains_only_low_while_low_remains") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(DrainPending.arena)⟩,
  objectArena := .source ⟨(DrainPending.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (DrainPending.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} DrainPending.signature (fun _ p stack => drain p.2.2 (p.1 :: p.2.1 :: stack)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[1, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_drains_only_low_while_low_remains, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.anchorEnumeration }


end DrainPendingAudit

namespace ProcessPendingAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.ProcessPending

theorem dependence : ObservationalDependence HighIncrease.signature HighIncrease.actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [HighIncrease.actual, HighIncrease.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ ProcessPending.arena.Law HighIncrease.rejected := by
  intro h
  have h := @h 4 1 3 4 2 (by decide) (by decide) (by decide) (by decide) [2] [] (by simp) (by decide)
  change ([] : List ℕ) = [1, 2, 4, 3] at h
  cases h

def registration : Registration ProcessPending.arena (∀
    {n low high next futureLow : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hfutureLow : futureLow ≤ n / 2) {input stack : List ℕ}
    (hmem : futureLow ∈ input)
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)),
    process (next :: input) (low :: high :: stack) =
      low :: process input (next :: high :: stack)) where
  actual := HighIncrease.actual
  bridge := Iff.rfl
  variation := ⟨@process_pending_low_while_low_remains, HighIncrease.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_9 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.process_pending_low_while_low_remains) (type_of% (realize.{0, 0, 0, 0, 0} HighIncrease.signature (fun _ p stack => process (p.2.2.1 :: p.2.2.2) (p.1 :: p.2.1 :: stack)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "process_pending_low_while_low_remains") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.ProcessPending.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(ProcessPending.arena)⟩,
  objectArena := .source ⟨(ProcessPending.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (ProcessPending.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} HighIncrease.signature (fun _ p stack => process (p.2.2.1 :: p.2.2.2) (p.1 :: p.2.1 :: stack)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[1, 2, 3, 9], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_pending_low_while_low_remains, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.anchorEnumeration }


end ProcessPendingAudit

namespace InitialLowsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows

theorem dependence : ObservationalDependence InitialLows.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [InitialLows.actual, InitialLows.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ InitialLows.arena.Law rejected := by
  intro h
  have h := @h 2 2 [1] [] (by simp) (by decide) rfl
  cases h

def registration : Registration InitialLows.arena (∀ {n high : ℕ} {pre rest : List ℕ}
    (hpre : ∀ low ∈ pre, low ≤ n / 2) (hhigh : n / 2 < high)
    (houtput : cyclicStackSort (pre ++ high :: rest) = target n),
    pre = []) where
  actual := InitialLows.actual
  bridge := Iff.rfl
  variation := ⟨@no_lows_before_first_high, InitialLows.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_10 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.no_lows_before_first_high) (type_of% (realize.{0, 0, 0, 0, 0} InitialLows.signature (fun _ p rest => cyclicStackSort (p.2 ++ p.1 :: rest)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "no_lows_before_first_high") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(InitialLows.arena)⟩,
  objectArena := .source ⟨(InitialLows.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (InitialLows.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} InitialLows.signature (fun _ p rest => cyclicStackSort (p.2 ++ p.1 :: rest)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, definition := none, coordinates := #[1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.no_lows_before_first_high, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.anchorEnumeration }


end InitialLowsAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainHigh.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainHigh.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.ProcessPending.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.ProcessPending.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.permArena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.permArena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.runArena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.runArena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"no_lows_before_first_high\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.no_lows_before_first_high, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.observation0 : {n high : Nat} →
  {pre rest : List.{0} Nat} →
    (hpre :
        ∀ (low : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) pre low →
            @LE.le.{0} Nat instLENat low
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      (hhigh :
          @LT.lt.{0} Nat instLTNat
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            high) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows.signature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) high pre) :=
  fun {n high : Nat} {pre rest : List.{0} Nat}
    (hpre :
      ∀ (low : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) pre low →
          @LE.le.{0} Nat instLENat low
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hhigh :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        high) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) high pre) rest

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"no_lows_before_first_high\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.no_lows_before_first_high, part := .type, path := [.body, .body, .body, .body, .body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"no_lows_before_first_high\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.no_lows_before_first_high, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"InitialLowsAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.InitialLowsAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"drain_low_over_high\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.drain_low_over_high, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.observation0 : {n low high : Nat} →
  (hlow :
      @LE.le.{0} Nat instLENat low
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    (hhigh :
        @LT.lt.{0} Nat instLTNat
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          high) →
      {input stack : List.{0} Nat} →
        (houtput :
            @List.Sublist.{0} Nat
              (D5.S1.Words.Patterns.CyclicStackPreimages.process (@List.cons.{0} Nat low input)
                (@List.cons.{0} Nat high stack))
              (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.signature PUnit.unit.{1}
            (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) low high) :=
  fun {n low high : Nat}
    (hlow :
      @LE.le.{0} Nat instLENat low
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hhigh :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        high)
    {input stack : List.{0} Nat}
    (houtput :
      @List.Sublist.{0} Nat
        (D5.S1.Words.Patterns.CyclicStackPreimages.process (@List.cons.{0} Nat low input)
          (@List.cons.{0} Nat high stack))
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) low high) stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"drain_low_over_high\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.drain_low_over_high, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"drain_low_over_high\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.drain_low_over_high, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainLowAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainLowAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"no_two_lows_after_high\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.no_two_lows_after_high, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.observation0 : {n low₁ low₂ high : Nat} →
  (hlow₁ :
      @LE.le.{0} Nat instLENat low₁
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    (hlow₂ :
        @LE.le.{0} Nat instLENat low₂
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      (hne : @Ne.{1} Nat low₁ low₂) →
        (hhigh :
            @LT.lt.{0} Nat instLTNat
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              high) →
          {input stack : List.{0} Nat} →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat
                (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat)
                low₁
                (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) low₂
                  (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) high input))) :=
  fun {n low₁ low₂ high : Nat}
    (hlow₁ :
      @LE.le.{0} Nat instLENat low₁
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hlow₂ :
      @LE.le.{0} Nat instLENat low₂
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hne : @Ne.{1} Nat low₁ low₂)
    (hhigh :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        high)
    {input stack : List.{0} Nat} =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) low₁
      (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) low₂
        (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) high input)))
    stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"no_two_lows_after_high\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.no_two_lows_after_high, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"no_two_lows_after_high\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.no_two_lows_after_high, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"TwoLowsAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.TwoLowsAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainHigh.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"drain_high_while_low_remains\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.drain_high_while_low_remains, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.observation0 : {n x high futureLow : Nat} →
  (hhigh :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        high) →
    (hlow :
        @LE.le.{0} Nat instLENat futureLow
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      {input stack : List.{0} Nat} →
        (hmem : @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) input futureLow) →
          (houtput :
              @List.Sublist.{0} Nat
                (D5.S1.Words.Patterns.CyclicStackPreimages.process (@List.cons.{0} Nat x input)
                  (@List.cons.{0} Nat high stack))
                (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) x high) :=
  fun {n x high futureLow : Nat}
    (hhigh :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        high)
    (hlow :
      @LE.le.{0} Nat instLENat futureLow
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    {input stack : List.{0} Nat}
    (hmem : @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) input futureLow)
    (houtput :
      @List.Sublist.{0} Nat
        (D5.S1.Words.Patterns.CyclicStackPreimages.process (@List.cons.{0} Nat x input) (@List.cons.{0} Nat high stack))
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) x high) stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"drain_high_while_low_remains\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.drain_high_while_low_remains, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"drain_high_while_low_remains\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.drain_high_while_low_remains, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainHighAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainHighAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.ProcessPending.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_pending_low_while_low_remains\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_pending_low_while_low_remains, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.observation0 : {n low high next futureLow : Nat} →
  (hlow :
      @LE.le.{0} Nat instLENat low
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    (hhigh :
        @LT.lt.{0} Nat instLTNat
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          high) →
      (hnext :
          @LT.lt.{0} Nat instLTNat
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            next) →
        (hfutureLow :
            @LE.le.{0} Nat instLENat futureLow
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
          {input stack : List.{0} Nat} →
            (hmem : @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) input futureLow) →
              (houtput :
                  @List.Sublist.{0} Nat
                    (D5.S1.Words.Patterns.CyclicStackPreimages.process (@List.cons.{0} Nat next input)
                      (@List.cons.{0} Nat low (@List.cons.{0} Nat high stack)))
                    (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.signature PUnit.unit.{1}
                  (@Sigma.mk.{0, 0} Nat
                    (fun (x : Nat) =>
                      @Sigma.{0, 0} Nat fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat)
                    low
                    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) high
                      (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) next input))) :=
  fun {n low high next futureLow : Nat}
    (hlow :
      @LE.le.{0} Nat instLENat low
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hhigh :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        high)
    (hnext :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        next)
    (hfutureLow :
      @LE.le.{0} Nat instLENat futureLow
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    {input stack : List.{0} Nat}
    (hmem : @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) input futureLow)
    (houtput :
      @List.Sublist.{0} Nat
        (D5.S1.Words.Patterns.CyclicStackPreimages.process (@List.cons.{0} Nat next input)
          (@List.cons.{0} Nat low (@List.cons.{0} Nat high stack)))
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) low
      (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) high
        (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) next input)))
    stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_pending_low_while_low_remains\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_pending_low_while_low_remains, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_pending_low_while_low_remains\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_pending_low_while_low_remains, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"ProcessPendingAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.ProcessPendingAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"pending_low_drains_only_low_while_low_remains\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_drains_only_low_while_low_remains, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.observation0 : {n low high next futureLow : Nat} →
  (hlow :
      @LE.le.{0} Nat instLENat low
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    (hhigh :
        @LT.lt.{0} Nat instLTNat
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          high) →
      (hnext :
          @LT.lt.{0} Nat instLTNat
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            next) →
        (hfutureLow :
            @LE.le.{0} Nat instLENat futureLow
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
          {input stack : List.{0} Nat} →
            (hmem : @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) input futureLow) →
              (houtput :
                  @List.Sublist.{0} Nat
                    (D5.S1.Words.Patterns.CyclicStackPreimages.process (@List.cons.{0} Nat next input)
                      (@List.cons.{0} Nat low (@List.cons.{0} Nat high stack)))
                    (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending.signature PUnit.unit.{1}
                  (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => Nat) low
                    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) high next)) :=
  fun {n low high next futureLow : Nat}
    (hlow :
      @LE.le.{0} Nat instLENat low
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hhigh :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        high)
    (hnext :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        next)
    (hfutureLow :
      @LE.le.{0} Nat instLENat futureLow
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    {input stack : List.{0} Nat}
    (hmem : @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) input futureLow)
    (houtput :
      @List.Sublist.{0} Nat
        (D5.S1.Words.Patterns.CyclicStackPreimages.process (@List.cons.{0} Nat next input)
          (@List.cons.{0} Nat low (@List.cons.{0} Nat high stack)))
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => Nat) low
      (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) high next))
    stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"pending_low_drains_only_low_while_low_remains\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_drains_only_low_while_low_remains, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"pending_low_drains_only_low_while_low_remains\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_drains_only_low_while_low_remains, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"DrainPendingAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.DrainPendingAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"pending_low_forces_high_increase\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_forces_high_increase, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.observation0 : {n low high next : Nat} →
  (hlow :
      @LE.le.{0} Nat instLENat low
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    (hnext :
        @LT.lt.{0} Nat instLTNat
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          next) →
      {input stack : List.{0} Nat} →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.signature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Nat
            (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) low
            (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) high
              (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) next input))) :=
  fun {n low high next : Nat}
    (hlow :
      @LE.le.{0} Nat instLENat low
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hnext :
      @LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        next)
    {input stack : List.{0} Nat} =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) low
      (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => @Sigma.{0, 0} Nat fun (x : Nat) => List.{0} Nat) high
        (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) next input)))
    stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"pending_low_forces_high_increase\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_forces_high_increase, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"pending_low_forces_high_increase\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.pending_low_forces_high_increase, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"HighIncreaseAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.HighIncreaseAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.permArena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.permRegistration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_perm\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_perm, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.permRegistration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.observation0 : (input stack : List.{0} Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.signature PUnit.unit.{1} input :=
  fun (input stack : List.{0} Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.actual PUnit.unit.{1} input stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_perm\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_perm, part := .type, path := [.body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_perm\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_perm, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.permRegistration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.permRegistration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.permRegistration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.permRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"permRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.permRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.runArena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.runRegistration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_eq_run\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.runRegistration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.observation0 : (input stack : List.{0} Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.signature PUnit.unit.{1} input :=
  fun (input stack : List.{0} Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.actual PUnit.unit.{1} input stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_eq_run\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run, part := .type, path := [.body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_eq_run\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.runRegistration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.runRegistration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.runRegistration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.runRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"runRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.runRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_append\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_append, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.observation0 : (pre suffix stack : List.{0} Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append.signature PUnit.unit.{1}
    (@Sigma.mk.{0, 0} (List.{0} Nat) (fun (x : List.{0} Nat) => List.{0} Nat) pre suffix) :=
  fun (pre suffix stack : List.{0} Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} (List.{0} Nat) (fun (x : List.{0} Nat) => List.{0} Nat) pre suffix) stack

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_append\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_append, part := .type, path := [.body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"process_append\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.process_append, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCore\",\"AppendAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore.AppendAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
