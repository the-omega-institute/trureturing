import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.GreedyBrickLabelledHistory
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.GreedyBrickCapacityTotality
open _root_.D5.S3.ArithSums.GreedyBrickLabelledHistory

namespace Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory

namespace Continuous

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
    ∃ x y : ℕ, PlacementSite n ws x y ∧
      sourceOptimal n ws (x : ℝ) (y : ℝ) ∧
      ∀ t z, wall (R.readout () n ws) t z ↔
        wall ws t z ∨ rectangle n (x : ℝ) (y : ℝ) t z

def rejected : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, y, hs, _, hu⟩ := h 1 (by omega) [] (by simp)
  have hxy : x = 0 ∧ y = 0 := by simpa [PlacementSite, AppendSite] using hs
  rcases hxy with ⟨rfl, rfl⟩
  have hw := (hu 0 0).mpr (Or.inr (by norm_num [rectangle]))
  rcases hw with ⟨k, _, _, ht, hk⟩
  simp [rejected, realize, rowEnd] at hk

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_row_geometry, rejected, rejected_law⟩
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
  owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
      "arg", "arg", "body", "body", "fn", "arg", "fn", "fn", "arg"]
    stateBinder := 2 }] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ArithSums.GreedyBrickLabelledHistory.continuous_row_geometry) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ n ws => sourceRowStep n ws) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ArithSums") "GreedyBrickLabelledHistory") "continuous_row_geometry") "Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory/Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration,
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
  sourceSelection := some { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "fn", "arg", "fn", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `D5.S3.ArithSums.GreedyBrickLabelledHistory.continuous_row_geometry, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalArenaFact, `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.sourceBridgeFact, `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.observationFact0, `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.anchorEnumeration }


#print axioms registration

end Continuous

namespace History

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ N => widths (trajectory N)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ pos : ℕ → ℕ × ℕ,
    (∀ N t z, wall (R.readout () () N) t z ↔ labelledWall pos N t z) ∧
    (∀ n, 0 < n → historyOptimal pos (n - 1) n (pos n).1 (pos n).2) ∧
    (∀ n, 0 < n → closedSupport pos (n - 1) n (pos n).1 (pos n).2) ∧
    (∀ i j, 0 < i → i < j → ∀ t z,
      rectangle i (pos i).1 (pos i).2 t z →
      ¬ rectangle j (pos j).1 (pos j).2 t z)

def rejected : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨pos, hu, _⟩
  have hr : rectangle 1 (pos 1).1 (pos 1).2 (pos 1).1 (pos 1).2 := by
    simp [rectangle]
  have hw := (hu 1 (pos 1).1 (pos 1).2).mpr ⟨1, by omega, le_rfl, hr⟩
  rcases hw with ⟨k, _, _, ht, hk⟩
  simp [rejected, realize, rowEnd] at hk
  have ht0 : (0 : ℝ) ≤ (pos 1).1 := Nat.cast_nonneg _
  linarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_labelled_history, rejected, rejected_law⟩
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
    exact ⟨(), 0, 1, by decide⟩

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory
  coordinates := #[]
  readouts := #[{
    path := #["arg", "body", "fn", "arg", "body", "body", "body",
      "fn", "arg", "fn", "fn", "arg"]
    stateBinder := 1 }] }

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ArithSums.GreedyBrickLabelledHistory.actual_labelled_history) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ N => widths (trajectory N)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ArithSums") "GreedyBrickLabelledHistory") "actual_labelled_history") "Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory/Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration,
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
    (fun _ _ N => widths (trajectory N)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "body", "fn", "arg", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `D5.S3.ArithSums.GreedyBrickLabelledHistory.actual_labelled_history, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalArenaFact, `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.sourceBridgeFact, `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.observationFact0, `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.anchorEnumeration }


#print axioms registration

end History

end Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory


noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.arena
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.arena
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.arena
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.arena
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.arena) (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration).actual

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"actual_labelled_history\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `D5.S3.ArithSums.GreedyBrickLabelledHistory.actual_labelled_history, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration).bridge

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.observation0 : (pos : Nat → Prod.{0, 0} Nat Nat) →
  (N : Nat) →
    (t z : Real) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (pos : Nat → Prod.{0, 0} Nat Nat) (N : Nat) (t z : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.signature
    Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.actual PUnit.unit.{1} PUnit.unit.{1} N

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"actual_labelled_history\"],\"part\":\"type\",\"path\":[\"argument\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `D5.S3.ArithSums.GreedyBrickLabelledHistory.actual_labelled_history, part := .type, path := [.argument, .body, .function, .argument, .body, .body, .body, .function, .argument, .function, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"actual_labelled_history\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `D5.S3.ArithSums.GreedyBrickLabelledHistory.actual_labelled_history, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration).actual (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration).variation.2.choose (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration).variation.1 (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"History\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.History.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.arena) (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration).actual

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"continuous_row_geometry\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `D5.S3.ArithSums.GreedyBrickLabelledHistory.continuous_row_geometry, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration).bridge

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.observation0 : (n : Nat) →
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (ws : List.{0} Nat) →
      (hp : @List.Pairwise.{0} Nat (fun (x1 x2 : Nat) => @LE.le.{0} Nat instLENat x1 x2) ws) →
        (x y : Nat) →
          (t z : Real) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.signature PUnit.unit.{1} n :=
  fun (n : Nat) (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
    (ws : List.{0} Nat) (hp : @List.Pairwise.{0} Nat (fun (x1 x2 : Nat) => @LE.le.{0} Nat instLENat x1 x2) ws)
    (x y : Nat) (t z : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.signature
    Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.actual PUnit.unit.{1} n ws

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"continuous_row_geometry\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `D5.S3.ArithSums.GreedyBrickLabelledHistory.continuous_row_geometry, part := .type, path := [.body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .argument, .body, .body, .function, .argument, .function, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"continuous_row_geometry\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `D5.S3.ArithSums.GreedyBrickLabelledHistory.continuous_row_geometry, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration).actual (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration).variation.2.choose (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration).variation.1 (Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ArithSums\",\"GreedyBrickLabelledHistory\",\"Continuous\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory, declaration := `Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory.Continuous.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
