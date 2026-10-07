import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.HoggarSicSumNegativity
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity
open _root_.D5.S3.Quantum.Measurement.HoggarSicSumNegativity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 8) (Fin 8) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ρ => sumNegativity ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IsGreatest {r : ℝ | ∃ ρ : Matrix (Fin 8) (Fin 8) ℂ,
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ R.readout () () ρ = r} (7/8)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases h.1 with ⟨ρ, _hρ, _ht, he⟩
  change (0 : ℝ) = 7/8 at he
  norm_num at he

def registration : Registration arena claim where
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
    rcases result.1 with ⟨ρ, _hρ, _ht, he⟩
    refine ⟨(), 0, ρ, ?_⟩
    change sumNegativity 0 ≠ sumNegativity ρ
    have hzero : sumNegativity (0 : Matrix (Fin 8) (Fin 8) ℂ) = 0 := by
      simp [sumNegativity, negativePart, quasiprobability]
    rw [hzero, he]
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ρ => sumNegativity ρ) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "HoggarSicSumNegativity") "result") "Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity/Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ρ => sumNegativity ρ) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity, definition := some { owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity, name := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity.claim, path := #[] }, coordinates := #[], readouts := #[{ path := #["fn", "arg", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity


noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.arena D5.S3.Quantum.Measurement.HoggarSicSumNegativity.claim
    Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration)

noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.arena D5.S3.Quantum.Measurement.HoggarSicSumNegativity.claim
  Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration)

noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.observation0 : (r : Real) →
  (ρ :
      Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) Complex) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (r : Real)
    (ρ :
      Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.signature
    Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.actual PUnit.unit.{1} PUnit.unit.{1} ρ

noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"claim\"],\"part\":\"value\",\"path\":[\"function\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity.claim, part := .value, path := [.function, .argument, .argument, .body, .argument, .body, .argument, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration).actual (Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration).variation.2.choose (Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration).variation.1 (Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"HoggarSicSumNegativity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity, declaration := `Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
