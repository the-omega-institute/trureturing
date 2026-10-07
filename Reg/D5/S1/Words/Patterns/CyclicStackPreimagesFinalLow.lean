import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
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
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_high_entries_final_low, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.anchorEnumeration }


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
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.assemble_insert_none_ends, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.anchorEnumeration }


end AssemblyEndsAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FinalHighs.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FinalHighs.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.arena
    (∀ {m omitted : Nat} {highs lows : List.{0} Nat}
      (hlen :
        @Eq.{1} Nat (@List.length.{0} Nat highs)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat lows)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (homitted : @LT.lt.{0} Nat instLTNat omitted (@List.length.{0} Nat lows))
      (hlow :
        ∀ (low : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) lows low →
            @LE.le.{0} Nat instLENat low m),
      D5.S1.Words.Patterns.CyclicStackPreimages.EndsWithLow m
        (D5.S1.Words.Patterns.CyclicStackPreimages.assembleGaps highs
          (D5.S1.Words.Patterns.CyclicStackPreimages.insertNone omitted lows)))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"assemble_insert_none_ends\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.assemble_insert_none_ends, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.arena
  (∀ {m omitted : Nat} {highs lows : List.{0} Nat}
    (hlen :
      @Eq.{1} Nat (@List.length.{0} Nat highs)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat lows)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (homitted : @LT.lt.{0} Nat instLTNat omitted (@List.length.{0} Nat lows))
    (hlow :
      ∀ (low : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) lows low →
          @LE.le.{0} Nat instLENat low m),
    D5.S1.Words.Patterns.CyclicStackPreimages.EndsWithLow m
      (D5.S1.Words.Patterns.CyclicStackPreimages.assembleGaps highs
        (D5.S1.Words.Patterns.CyclicStackPreimages.insertNone omitted lows)))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.observation0 : {m omitted : Nat} →
  {highs lows : List.{0} Nat} →
    (hlen :
        @Eq.{1} Nat (@List.length.{0} Nat highs)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat lows)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      (homitted : @LT.lt.{0} Nat instLTNat omitted (@List.length.{0} Nat lows)) →
        (hlow :
            ∀ (low : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) lows low →
                @LE.le.{0} Nat instLENat low m) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.signature PUnit.unit.{1}
            (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) omitted highs) :=
  fun {m omitted : Nat} {highs lows : List.{0} Nat}
    (hlen :
      @Eq.{1} Nat (@List.length.{0} Nat highs)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Nat lows)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (homitted : @LT.lt.{0} Nat instLTNat omitted (@List.length.{0} Nat lows))
    (hlow :
      ∀ (low : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) lows low →
          @LE.le.{0} Nat instLENat low m) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.AssemblyEnds.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => List.{0} Nat) omitted highs) lows

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"assemble_insert_none_ends\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.assemble_insert_none_ends, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"assemble_insert_none_ends\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.assemble_insert_none_ends, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"AssemblyEndsAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.AssemblyEndsAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FinalHighs.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FinalHighs.arena
    (∀ {n : Nat} {input : List.{0} Nat}
      (hgapped :
        D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input)
      (hlast :
        D5.S1.Words.Patterns.CyclicStackPreimages.EndsWithLow
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input)
      (houtput :
        @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
          (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
      @Eq.{1} (List.{0} Nat)
        (D5.S1.Words.Patterns.CyclicStackPreimages.highEntries
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input)
        (List.range'
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_high_entries_final_low\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_high_entries_final_low, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FinalHighs.arena
  (∀ {n : Nat} {input : List.{0} Nat}
    (hgapped :
      D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
    (hlast :
      D5.S1.Words.Patterns.CyclicStackPreimages.EndsWithLow
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
    (houtput :
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)),
    @Eq.{1} (List.{0} Nat)
      (D5.S1.Words.Patterns.CyclicStackPreimages.highEntries
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
      (List.range'
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.observation0 : {n : Nat} →
  {input : List.{0} Nat} →
    (hgapped :
        D5.S1.Words.Patterns.CyclicStackPreimages.Gapped
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          input) →
      (hlast :
          D5.S1.Words.Patterns.CyclicStackPreimages.EndsWithLow
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            input) →
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
    (hlast :
      D5.S1.Words.Patterns.CyclicStackPreimages.EndsWithLow
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        input)
    (houtput :
      @Eq.{1} (List.{0} Nat) (D5.S1.Words.Patterns.CyclicStackPreimages.cyclicStackSort input)
        (D5.S1.Words.Patterns.CyclicStackPreimages.target n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder.actual PUnit.unit.{1} n input

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_high_entries_final_low\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_high_entries_final_low, part := .type, path := [.body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"successful_high_entries_final_low\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.successful_high_entries_final_low, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesFinalLow\",\"FinalHighsAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow.FinalHighsAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
