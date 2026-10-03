import LeanInformationAuditInterface.SourceSelection
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

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality
  definition := some {
    owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality
    name := `D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence }
  coordinates := #[0]
  readouts := #[
    { path := #["body", "body", "body", "arg"], stateBinder := 1 },
    { path := #["body", "body", "body", "fn", "arg"], stateBinder := 1 }] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ArithSums.GreedyBrickCapacityTotality.row_transition_correspondence) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun role n cs => if role then sourceRowStep n (widths cs) else widths (step n cs))
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ArithSums") "GreedyBrickCapacityTotality") "row_transition_correspondence") "Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality/Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun role n cs => if role then sourceRowStep n (widths cs) else widths (step n cs))
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, definition := some { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, name := `D5.S3.ArithSums.GreedyBrickCapacityTotality.RowTransitionCorrespondence, path := #[] }, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


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

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
      "arg", "arg", "fn", "fn", "fn", "arg"]
    stateBinder := 2 }] }

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ArithSums.GreedyBrickCapacityTotality.source_row_geometry) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ n ws => sourceRowStep n ws) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ArithSums") "GreedyBrickCapacityTotality") "source_row_geometry") "Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality/Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality.GeometryAudit.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ n ws => sourceRowStep n ws) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ArithSums.GreedyBrickCapacityTotality, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end GeometryAudit

end Reg.D5.S3.ArithSums.GreedyBrickCapacityTotality
