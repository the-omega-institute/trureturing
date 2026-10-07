import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount
open _root_.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => oeisSequence n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := subsetCount 0 = 0 ∧ subsetCount 1 = 0 ∧ subsetCount 2 = 0 ∧
    ∀ n : ℕ, subsetCount (n + 3) = r.readout () () n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood : subsetCount 3 = 1 := by
    have h0 := result.2.2.2 0
    simpa [oeisSequence] using h0
  have hbad := h.2.2.2 0
  change subsetCount 3 = 0 at hbad
  omega

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 0, 1, ?_⟩
  change oeisSequence 0 ≠ oeisSequence 1
  norm_num [oeisSequence]

noncomputable def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => oeisSequence n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "KimberlingLeastTwoSubsetCount") "result") "Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount/Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => oeisSequence n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, definition := some { owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, name := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.claim, path := #[] }, coordinates := #[], readouts := #[{ path := #["arg", "arg", "arg", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount


noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.arena
noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.arena
noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.arena D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.claim
    Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration)

noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.arena D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.claim
  Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration)

noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.observation0 : (n : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.signature
    Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.actual PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"claim\"],\"part\":\"value\",\"path\":[\"argument\",\"argument\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.claim, part := .value, path := [.argument, .argument, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration).actual (Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration).variation.2.choose (Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration).variation.1 (Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"KimberlingLeastTwoSubsetCount\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount, declaration := `Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
