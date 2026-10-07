import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
open _root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ L N => ecc 3 L N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Both original diameter readings and all three guards remain in the Law. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ L N : ℕ, 2 ≤ L → L ≤ N → 3 < N →
    r.readout () L N = (L * (N - L) + 1) / 2 ∧
      diam 3 L N = (L * (N - L) + 1) / 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (h 2 4 (by decide) (by decide) (by decide)).1
  change 0 = 2 at hzero
  contradiction

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨2, 4, 5, ?_⟩
  change ecc 3 2 4 ≠ ecc 3 2 5
  rw [(_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result
    2 4 (by decide) (by decide) (by decide)).1,
    (_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result
    2 5 (by decide) (by decide) (by decide)).1]
  decide

noncomputable def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result,
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ L N => ecc 3 L N) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "ShrunkenGrassmannianThreeCycleDiameter") "result") "Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter/Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ L N => ecc 3 L N) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, definition := some { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, name := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.claim, path := #[] }, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter


noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.arena
noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.arena
noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.arena) (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration).actual

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration).bridge

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.observation0 : (L N : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L →
    @LE.le.{0} Nat instLENat L N →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.signature PUnit.unit.{1} L :=
  fun (L N : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
    (a_1 : @LE.le.{0} Nat instLENat L N)
    (a_2 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.signature
    Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.actual PUnit.unit.{1} L N

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.claim, part := .value, path := [.body, .body, .body, .body, .body, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration).actual (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration).variation.2.choose (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration).variation.1 (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianThreeCycleDiameter\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
