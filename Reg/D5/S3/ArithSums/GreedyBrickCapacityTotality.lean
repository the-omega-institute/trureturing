import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.GreedyBrickCapacityTotality
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.GreedyBrickCapacityTotality

namespace Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => List ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role n cs => if role then sourceRowStep n (widths cs) else widths (step n cs))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n cs, 0 < n → R.readout false n cs = R.readout true n cs

def rejected (role : Bool) : Realization signature := realize signature
  (fun r n cs => if r = role then [] else actual.readout r n cs)
  (fun e => nomatch e)

theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have hbad := h (1 : ℕ) ([] : List ℕ) Nat.zero_lt_one
  cases role <;>
    simp [rejected, actual, realize, widths, step, transfer, sourceRowStep] at hbad

def registration : Registration arena RowTransitionCorrespondence where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨row_transition_correspondence, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext n cs
      simp [rejected, realize, hj]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1, [], [2], ?_⟩
    cases i <;> decide

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality
  definition := some {
    owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality
    name := `D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence }
  coordinates := #[0]
  readouts := #[
    { path := #["body", "body", "body", "arg"], stateBinder := 1 },
    { path := #["body", "body", "body", "fn", "arg"], stateBinder := 1 }] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ArithSums.GreedyBrickCapacityTotality.row_transition_correspondence) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun role n cs => if role then sourceRowStep n (widths cs) else widths (step n cs))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ArithSums") "GreedyBrickCapacityTotality") "row_transition_correspondence") "Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality/Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun role n cs => if role then sourceRowStep n (widths cs) else widths (step n cs))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, definition := some { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, name := `D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence, path := #[] }, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.row_transition_correspondence, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalArenaFact, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.sourceBridgeFact, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.observationFact0, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.observationFact1, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.anchorEnumeration }


#print axioms registration

namespace GeometryAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n ws => sourceRowStep n ws) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → ∀ (ws : List ℕ), ws.Pairwise (· ≤ ·) →
    ∃ x y, PlacementSite n ws x y ∧
      (∀ x' y', LegalBrick n ws x' y' → x ≤ x' ∧ y' ≤ y) ∧
      BrickAddition ws (R.readout () n ws) n x y

def rejected : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, y, hs, _, hb⟩ := h (1 : ℕ) Nat.zero_lt_one ([] : List ℕ) (by simp)
  have hxy : x = 0 ∧ y = 0 := by simpa [PlacementSite, AppendSite] using hs
  rcases hxy with ⟨rfl, rfl⟩
  have hbad := hb.1 0 0
  simp [rejected, realize, occupied] at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_row_geometry, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨1, [], [2], by decide⟩

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
      "arg", "arg", "fn", "fn", "fn", "arg"]
    stateBinder := 2 }] }

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ArithSums.GreedyBrickCapacityTotality.source_row_geometry) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ n ws => sourceRowStep n ws) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ArithSums") "GreedyBrickCapacityTotality") "source_row_geometry") "Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality/Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ n ws => sourceRowStep n ws) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.source_row_geometry, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalArenaFact, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.sourceBridgeFact, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.observationFact0, `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.anchorEnumeration }


#print axioms registration

end GeometryAudit

end Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality


noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.arena
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.arena
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.arena
    D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration)

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"row_transition_correspondence\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.row_transition_correspondence, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.arena
  D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration)

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Bool) where
  values := [Bool.true, Bool.false]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.observation0 : (n : Nat) →
  (cs : List.{0} Nat) →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.signature Bool.true n :=
  fun (n : Nat) (cs : List.{0} Nat)
    (a : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.signature Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.actual
    Bool.true n cs

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"RowTransitionCorrespondence\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence, part := .value, path := [.body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.observation1 : (n : Nat) →
  (cs : List.{0} Nat) →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.signature Bool.false n :=
  fun (n : Nat) (cs : List.{0} Nat)
    (a : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.signature Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.actual
    Bool.false n cs

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"RowTransitionCorrespondence\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence, part := .value, path := [.body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"row_transition_correspondence\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.row_transition_correspondence, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration).actual (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration).variation.2.choose (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration).variation.1 (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena
      Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.actual)
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration)

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"source_row_geometry\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.source_row_geometry, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.actual)
  Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration)

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.observation0 : (n : Nat) →
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (ws : List.{0} Nat) →
      (hp : @List.Pairwise.{0} Nat (fun (x1 x2 : Nat) => @LE.le.{0} Nat instLENat x1 x2) ws) →
        (x y : Nat) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.signature PUnit.unit.{1} n :=
  fun (n : Nat) (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
    (ws : List.{0} Nat) (hp : @List.Pairwise.{0} Nat (fun (x1 x2 : Nat) => @LE.le.{0} Nat instLENat x1 x2) ws)
    (x y : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.signature
    Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.actual PUnit.unit.{1} n ws

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"source_row_geometry\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.source_row_geometry, part := .type, path := [.body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .argument, .function, .function, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"source_row_geometry\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `D5.S3.ArithSums.GreedyBrickCapacityTotality.source_row_geometry, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration).actual (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration).variation.2.choose (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration).variation.1 (Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickCapacityTotality\",\"GeometryAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality, declaration := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
