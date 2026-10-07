import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => d + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q),
    L.response 0 = ⊥ ∧ ∀ d, L.response d ≤ L.response (r.readout () () d)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A : CountMat 1 1 := fun _ _ => 1
  let L : IncomingLift A Bool := {
    project := fun _ => 0
    onto := by intro i; exact ⟨false, (Fin.eq_zero i).symm⟩
    lift := fun e q => ⟨false, (Fin.eq_zero _).symm⟩ }
  have hstep := (h L).2 1
  have hrel : L.response 1 true false := by
    change L.responseReadout 1 true = L.responseReadout 1 false
    apply Prod.ext
    · rfl
    · funext i j path
      cases path with
      | cons edge tail =>
        simp [IncomingLift.responseReadout, IncomingLift.liftPath, L]
  have hbad := hstep hrel
  change (L.response 0) true false at hbad
  rw [(response_zero_and_step L).1] at hbad
  change (true : Bool) = false at hbad
  cases hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro n A Q L
    simpa [actual, realize] using response_zero_and_step L,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (1 : Nat) ≠ 2
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.response_zero_and_step) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d + 1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "ResponseQuotientKernel") "response_zero_and_step") "Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel/Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.response_zero_and_step, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena
      Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.actual)
    Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"response_zero_and_step\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.response_zero_and_step, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena
    Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.actual)
  Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.observation0 : {n : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {Q : Type} →
      (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift n A Q) →
        (d : Nat) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {n : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} {Q : Type}
    (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift n A Q) (d : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.signature
    Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.actual PUnit.unit.{1} PUnit.unit.{1} d

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"response_zero_and_step\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.response_zero_and_step, part := .type, path := [.body, .body, .body, .body, .argument, .body, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"response_zero_and_step\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.response_zero_and_step, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"ResponseQuotientKernel\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, declaration := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
