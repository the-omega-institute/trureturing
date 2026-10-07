import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Separation.BooleanRankThreeProtocol
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol

open _root_.D5.S3.Observer.Separation.BooleanRankThreeProtocol
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => delta a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => false) (fun e => nomatch e)

/-- The complete negated necessity statement, with the decoder row as readout. -/
abbrev arena : Arena where
  signature := signature
  Law R := ¬ (TaskData →
    Protocol Ftheta 3 3 alpha beta (R.readout () ()) →
    ∃ c d, Balanced Ftheta c d)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro _ hp
  have bad := hp.2.2 1 0 true (by decide)
  change false = true at bad
  exact Bool.noConfusion bad

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have bad := congrFun h 0
    change false = true at bad
    exact Bool.noConfusion bad

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Separation.BooleanRankThreeProtocol.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ a => delta a) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Separation") "BooleanRankThreeProtocol") "result") "Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol/Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ a => delta a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, definition := some { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, name := `D5.S3.Observer.Separation.BooleanRankThreeProtocol.claim, path := #["arg"] }, coordinates := #[], readouts := #[{ path := #["arg", "body", "domain", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `D5.S3.Observer.Separation.BooleanRankThreeProtocol.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `D5.S3.Observer.Separation.BooleanRankThreeProtocol.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.observationFact0, `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.anchorEnumeration }


#print axioms result
#print axioms registration

end Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol


noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.arena
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.arena
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.arena) (Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration).actual

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `D5.S3.Observer.Separation.BooleanRankThreeProtocol.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration).bridge

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.observation0 : D5.S3.Observer.Separation.BooleanRankThreeProtocol.TaskData →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.signature PUnit.unit.{1} →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (a : D5.S3.Observer.Separation.BooleanRankThreeProtocol.TaskData) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.signature
    Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.actual PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"domain\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `D5.S3.Observer.Separation.BooleanRankThreeProtocol.claim, part := .value, path := [.body, .domain, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `D5.S3.Observer.Separation.BooleanRankThreeProtocol.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration).actual (Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration).variation.2.choose (Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration).variation.1 (Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeProtocol\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
