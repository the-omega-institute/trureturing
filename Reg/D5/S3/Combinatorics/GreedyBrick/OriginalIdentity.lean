import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.GreedyBrick.OriginalIdentity
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity
open _root_.D5.S3.ArithSums.GreedyBrickCapacityTotality

namespace Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity

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
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ m : ℕ, 1 ≤ m →
    r.readout () () (a m) = a m * (a m + 3) / 2 - m

theorem first_birth : a 1 = 1 := by
  have spec := Nat.find_spec (birth_totality 1 (by omega))
  have ha : 0 < a 1 ∧ a 1 ≤ 1 := by
    simpa only [a, dif_pos (by omega : 1 ≤ 1), birth, ↓reduceIte] using
      (show 0 < birth 1 (by omega) ∧ birth 1 (by omega) ≤ 1 from ⟨spec.1, spec.2.2.2⟩)
  omega

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 1 (by omega)
  change 0 = a 1 * (a 1 + 3) / 2 - 1 at hx
  rw [first_birth] at hx
  norm_num at hx

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 1, 2, ?_⟩
  change a 1 ≠ a 2
  intro h
  have spec := Nat.find_spec (birth_totality 2 (by omega))
  have hx : (trajectory (a 2)).length = 2 := by
    simpa only [a, dif_pos (by omega : 1 ≤ 2), birth] using spec.2.1
  rw [← h, first_birth] at hx
  norm_num [trajectory, step, transfer] at hx

noncomputable def registration : Registration arena
    (∀ m : ℕ, 1 ≤ m → a (a m) = a m * (a m + 3) / 2 - m) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.result,
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => a n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "GreedyBrick") "OriginalIdentity") "result") "Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity/Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => a n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity


noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.arena
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.arena
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.arena) (Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration).actual

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration).bridge

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.observation0 : (m : Nat) →
  (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
        Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.signature PUnit.unit.{1} →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.signature
    Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.actual PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.result, part := .type, path := [.body, .body, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration).actual (Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration).variation.2.choose (Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration).variation.1 (Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"OriginalIdentity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.OriginalIdentity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
