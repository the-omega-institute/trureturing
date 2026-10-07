import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace OddFibreAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre

theorem dependence : ObservationalDependence OddFibre.signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [OddFibre.actual, OddFibre.signature, singleObservation, realize]
  exact _root_.Reg.Support.CyclicStackFamily.fibre_distinct_of_member
    (m := 1) (n := 3) (word := [1])
    (List.mem_filter.mpr ⟨List.mem_permutations.mpr (List.Perm.refl [1]), rfl⟩)
    (by decide)

theorem rejected_law : ¬ OddFibre.arena.Law rejected := by
  intro h
  have h := @h 1 (by decide)
  change 2 ≤ 0 at h
  omega

def registration : Registration OddFibre.arena (∀ (m : ℕ) (hm : 0 < m),
    m + 1 ≤ (fibre (2 * m + 1)).length) where
  actual := OddFibre.actual
  bridge := Iff.rfl
  variation := ⟨@oddCandidate_lower_bound, OddFibre.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.oddCandidate_lower_bound) (type_of% (realize.{0, 0, 0, 0, 0} OddFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m + 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "oddCandidate_lower_bound") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(OddFibre.arena)⟩,
  objectArena := .source ⟨(OddFibre.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (OddFibre.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} OddFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m + 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.oddCandidate_lower_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.anchorEnumeration }


end OddFibreAudit

namespace EvenFibreAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre

theorem dependence : ObservationalDependence EvenFibre.signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [EvenFibre.actual, EvenFibre.signature, singleObservation, realize]
  exact _root_.Reg.Support.CyclicStackFamily.fibre_distinct_of_member
    (m := 0) (n := 2) (word := [])
    (List.mem_filter.mpr ⟨List.mem_permutations.mpr (List.Perm.refl []), rfl⟩)
    (by decide)

theorem rejected_law : ¬ EvenFibre.arena.Law rejected := by
  intro h
  have h := @h 1 (by decide)
  change 1 ≤ 0 at h
  omega

def registration : Registration EvenFibre.arena (∀ (m : ℕ) (hm : 0 < m),
    1 ≤ (fibre (2 * m)).length) where
  actual := EvenFibre.actual
  bridge := Iff.rfl
  variation := ⟨@evenCandidate_lower_bound, EvenFibre.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.evenCandidate_lower_bound) (type_of% (realize.{0, 0, 0, 0, 0} EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "evenCandidate_lower_bound") "Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(EvenFibre.arena)⟩,
  objectArena := .source ⟨(EvenFibre.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (EvenFibre.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.evenCandidate_lower_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.anchorEnumeration }


end EvenFibreAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"oddCandidate_lower_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.oddCandidate_lower_bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.observation0 : (m : Nat) →
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (m : Nat) (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddFibre.actual PUnit.unit.{1} PUnit.unit.{1} m

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"oddCandidate_lower_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.oddCandidate_lower_bound, part := .type, path := [.body, .body, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"oddCandidate_lower_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.oddCandidate_lower_bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"OddFibreAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.OddFibreAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.arena) (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration).actual

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"evenCandidate_lower_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.evenCandidate_lower_bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration).bridge

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.observation0 : (m : Nat) →
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (m : Nat) (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.actual PUnit.unit.{1} PUnit.unit.{1} m

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"evenCandidate_lower_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.evenCandidate_lower_bound, part := .type, path := [.body, .body, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"evenCandidate_lower_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.evenCandidate_lower_bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimagesCandidates\",\"EvenFibreAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates.EvenFibreAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
