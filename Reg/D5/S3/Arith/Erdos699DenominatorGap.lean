import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Erdos699DenominatorGap
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Erdos699DenominatorGap

open _root_.D5.S3.Arith.Erdos699DenominatorGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The only observed state is the original integer `n`; no parameter is hidden
in a coordinate or replaced by an assumption on a restricted state space. -/
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Substitute only the selected conclusion LHS. All seven integer parameters
and all eight assumptions retain the source order and expressions. -/
def arena : Arena where
  signature := signature
  Law := fun r => ∀ (n L R j m D k : ℤ),
    8 ≤ n → 0 < R → 0 < m → 2 * m < L → 0 < D →
    n - 1 = L * R → j = 1 + m * R →
    D * (n - j) * (n - j - 1) = k * (n - 1) * (n - 2) →
    (r.readout () () n : ℤ) < D * L ^ 2

def actual : Realization signature :=
  realize signature (fun _ _ (n : ℤ) => 4 * (n - 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (256 : ℤ)) (fun e => nomatch e)

/-- This tuple satisfies every original hypothesis; the intervention gives
`256 < 256`. Thus the rejection does not depend on inconsistent assumptions. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h 9 8 1 2 1 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (256 : ℤ) < 4 * 8 ^ 2 at hfalse
  norm_num at hfalse

def registration : Registration arena
    (∀ (n L R j m D k : ℤ),
      8 ≤ n → 0 < R → 0 < m → 2 * m < L → 0 < D →
      n - 1 = L * R → j = 1 + m * R →
      D * (n - j) * (n - j - 1) = k * (n - 1) * (n - 2) →
      4 * (n - 2) < D * L ^ 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨erdos699_denominator_gap, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (2 : ℤ), (3 : ℤ), ?_⟩
    change (4 : ℤ) * (2 - 2) ≠ 4 * (3 - 2)
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Erdos699DenominatorGap.erdos699_denominator_gap) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ (n : ℤ) => 4 * (n - 2)) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Erdos699DenominatorGap") "erdos699_denominator_gap") "Reg.D5.S3.Arith.Erdos699DenominatorGap/Reg.D5.S3.Arith.Erdos699DenominatorGap.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Erdos699DenominatorGap.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ (n : ℤ) => 4 * (n - 2)) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Erdos699DenominatorGap, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms rejected_law
#print axioms registration

end Reg.D5.S3.Arith.Erdos699DenominatorGap
