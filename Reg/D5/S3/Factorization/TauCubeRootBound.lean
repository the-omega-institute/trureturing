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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Factorization.TauCubeRootBound.result) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => j.divisors.card)
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "TauCubeRootBound") "result") "Reg.D5.S3.Factorization.TauCubeRootBound/Reg.D5.S3.Factorization.TauCubeRootBound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.TauCubeRootBound.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => j.divisors.card)
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.TauCubeRootBound, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.Factorization.TauCubeRootBound
