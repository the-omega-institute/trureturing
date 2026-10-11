import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace FinalHighsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FinalHighs

theorem dependence : ObservationalDependence HighOrder.signature HighOrder.actual := by
  intro i
  refine ⟨(0 : ℕ), [], [(1 : ℕ)], ?_⟩
  dsimp only [HighOrder.actual, HighOrder.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ FinalHighs.arena.Law rejected := by
  intro h
  have h := @h 2 [2, 1] (Gapped.filled (by decide) (by decide) Gapped.nil) ⟨[2], 1, rfl, by decide⟩ rfl
  change ([] : List ℕ) = [2] at h
  cases h

def registration : Registration FinalHighs.arena (∀ {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input) (hlast : EndsWithLow (n / 2) input)
    (houtput : cyclicStackSort input = target n),
    highEntries (n / 2) input = List.range' (n / 2 + 1) (n - n / 2)) where
  actual := HighOrder.actual
  bridge := Iff.rfl
  variation := ⟨@successful_high_entries_final_low, FinalHighs.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.successful_high_entries_final_low) (type_of% (realize.{0, 0, 0, 0, 0} HighOrder.signature (fun _ (n : ℕ) input => highEntries (n / 2) input) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "successful_high_entries_final_low") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FinalHighs.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(FinalHighs.arena)⟩,
  objectArena := .source ⟨(FinalHighs.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (FinalHighs.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} HighOrder.signature (fun _ (n : ℕ) input => highEntries (n / 2) input) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end FinalHighsAudit

namespace AssemblyEndsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds

theorem dependence : ObservationalDependence AssemblyEnds.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), [(1 : ℕ), (2 : ℕ)]⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [AssemblyEnds.actual, AssemblyEnds.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ AssemblyEnds.arena.Law rejected := by
  intro h
  have h := @h 0 0 [1, 2] [0] rfl (by decide) (by simp)
  obtain ⟨pre, low, heq, _⟩ := h
  change ([] : List ℕ) = pre ++ [low] at heq
  simpa using heq

def registration : Registration AssemblyEnds.arena (∀ {m omitted : ℕ} {highs lows : List ℕ}
    (hlen : highs.length = lows.length + 1) (homitted : omitted < lows.length)
    (hlow : ∀ low ∈ lows, low ≤ m),
    EndsWithLow m (assembleGaps highs (insertNone omitted lows))) where
  actual := AssemblyEnds.actual
  bridge := Iff.rfl
  variation := ⟨@assemble_insert_none_ends, AssemblyEnds.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.assemble_insert_none_ends) (type_of% (realize.{0, 0, 0, 0, 0} AssemblyEnds.signature (fun _ p lows => assembleGaps p.2 (insertNone p.1 lows)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "assemble_insert_none_ends") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(AssemblyEnds.arena)⟩,
  objectArena := .source ⟨(AssemblyEnds.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (AssemblyEnds.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} AssemblyEnds.signature (fun _ p lows => assembleGaps p.2 (insertNone p.1 lows)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, definition := none, coordinates := #[1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end AssemblyEndsAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow
