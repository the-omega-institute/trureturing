import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
import Reg.Support.DependentFamily
import Mathlib.Tactic.Linarith

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
open _root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => expectedRange n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 / 2 : ℚ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℤ, r.readout () () n * 2 ^ (3 * n - 3) = m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, hm⟩ := h 1 (by norm_num)
  change (1 / 2 : ℚ) * 2 ^ (3 * 1 - 3) = m at hm
  have hi : (m : ℚ) > 0 ∧ (m : ℚ) < 1 := by norm_num at hm; constructor <;> linarith
  have : (0 : ℤ) < m ∧ m < 1 := by exact_mod_cast hi
  omega

theorem dependence_proof : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change expectedRange 0 ≠ expectedRange 1
  decide +kernel

def registration : Registration arena (_root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim) where
  actual := actual
  bridge := by rfl
  variation := ⟨_root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result,
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => expectedRange n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "StatisticalMechanics") "RandomWalks") "KnightWalkRangeIntegrality") "result") "Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality/Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => expectedRange n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, definition := some { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, name := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim, path := #[] }, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalArenaFact, `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.sourceBridgeFact, `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.observationFact0, `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality


noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.arena
noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.arena
noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.arena
    D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim
    Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration)

noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.arena
  D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim
  Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration)

noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.observation0 : (n : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
    (m : Int) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
    (m : Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.signature
    Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.actual PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"argument\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim, part := .value, path := [.body, .body, .argument, .body, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration).actual (Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration).variation.2.choose (Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration).variation.1 (Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"RandomWalks\",\"KnightWalkRangeIntegrality\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality, declaration := `Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
