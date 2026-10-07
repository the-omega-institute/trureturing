import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
open _root_.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
noncomputable section

abbrev signature : Signature where
  Params := (_ : ℕ) × ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p r => stirlingHat p.1 p.2 r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original claim; only the selected source operand is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ n k : ℕ, k ≤ n → ∀ r : ℤ,
    O.readout () ⟨n, k⟩ r = conjectureSum n k r

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 0 (by omega) 0
  rw [← result 0 0 (by omega) 0] at h0
  norm_num [rejected, realize, stirlingHat] at h0

def registration : Registration arena (claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
    norm_num [actual, realize, stirlingHat]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p r => stirlingHat p.1 p.2 r) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "FockSpace") "BosonOrderingStirlingClosedForm") "result") "Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm/Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p r => stirlingHat p.1 p.2 r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, definition := some { owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, name := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.claim, path := #[] }, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.observationFact0, `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm


noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.arena
noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.arena
noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.arena
    D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.claim
    Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration)

noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.arena
  D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.claim
  Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration)

noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.observation0 : (n k : Nat) →
  @LE.le.{0} Nat instLENat k n →
    (r : Int) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.signature PUnit.unit.{1}
        (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) n k) :=
  fun (n k : Nat) (a : @LE.le.{0} Nat instLENat k n) (r : Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.signature
    Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) n k) r

noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.claim, part := .value, path := [.body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration).actual (Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration).variation.2.choose (Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration).variation.1 (Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"FockSpace\",\"BosonOrderingStirlingClosedForm\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, declaration := `Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
