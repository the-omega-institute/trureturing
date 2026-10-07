import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.TauCubeRootBound
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.TauCubeRootBound

open _root_.D5.S3.Factorization.TauCubeRootBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => j.divisors.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R :=
    (∀ j : ℕ, 0 < j →
      (R.readout () () j : ℝ) ≤ 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) ∧
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) < 4 * (j : ℝ) ^ ((1 : ℝ) / 3)) ∧
    (R.readout () () 2520 : ℝ) =
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (2520 : ℝ) ^ ((1 : ℝ) / 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have heq : (0 : ℝ) = 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
      (2520 : ℝ) ^ ((1 : ℝ) / 3) := by
    simpa [arena, rejected, realize] using h.2
  have hp : 0 < 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
      (2520 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  linarith

def registration : Registration arena
    ((∀ j : ℕ, 0 < j →
      (j.divisors.card : ℝ) ≤ 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) ∧
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) < 4 * (j : ℝ) ^ ((1 : ℝ) / 3)) ∧
    ((2520 : ℕ).divisors.card : ℝ) =
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (2520 : ℝ) ^ ((1 : ℝ) / 3)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℕ) ≠ 2
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.TauCubeRootBound.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => j.divisors.card)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "TauCubeRootBound") "result") "Reg.D5.S3.Factorization.TauCubeRootBound/Reg.D5.S3.Factorization.TauCubeRootBound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.TauCubeRootBound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => j.divisors.card)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.TauCubeRootBound, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.TauCubeRootBound, declaration := `D5.S3.Factorization.TauCubeRootBound.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.observationFact0, `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Factorization.TauCubeRootBound


noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.TauCubeRootBound.arena
noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.TauCubeRootBound.arena
noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.TauCubeRootBound.arena) (Reg.D5.S3.Factorization.TauCubeRootBound.registration).actual

noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.TauCubeRootBound, declaration := `D5.S3.Factorization.TauCubeRootBound.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.TauCubeRootBound.registration).bridge

noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.observation0 : (j : Nat) →
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.TauCubeRootBound.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (j : Nat) (a : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.TauCubeRootBound.signature Reg.D5.S3.Factorization.TauCubeRootBound.actual PUnit.unit.{1}
    PUnit.unit.{1} j

noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"result\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.TauCubeRootBound, declaration := `D5.S3.Factorization.TauCubeRootBound.result, part := .type, path := [.function, .argument, .body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.TauCubeRootBound, declaration := `D5.S3.Factorization.TauCubeRootBound.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.TauCubeRootBound.registration).actual (Reg.D5.S3.Factorization.TauCubeRootBound.registration).variation.2.choose (Reg.D5.S3.Factorization.TauCubeRootBound.registration).variation.1 (Reg.D5.S3.Factorization.TauCubeRootBound.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.TauCubeRootBound.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"TauCubeRootBound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.TauCubeRootBound, declaration := `Reg.D5.S3.Factorization.TauCubeRootBound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
