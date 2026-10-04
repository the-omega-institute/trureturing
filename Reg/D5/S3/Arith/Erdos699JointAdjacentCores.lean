import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Erdos699JointAdjacentCores
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Erdos699JointAdjacentCores
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Erdos699JointAdjacentCores

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law := fun r => ∀ (B s : ℤ),
    5 ≤ B → Odd B → 1 ≤ s → s ≤ B - 1 →
    2 * B + 1 ∣ 4 * s ^ 2 - 1 →
    B ∣ (s - 1) * s * (s + 1) →
    1 < Int.gcd B (s - 1) ∧
    1 < Int.gcd B s ∧
    1 < Int.gcd B (r.readout () () s)

def actual : Realization signature :=
  realize signature (fun _ _ s => s + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := (h 38335 11561
    (by norm_num) (by norm_num [Odd]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2.2
  change (1 : ℕ) < Int.gcd 38335 1 at hfalse
  norm_num at hfalse

def registration : Registration arena
    (∀ (B s : ℤ), 5 ≤ B → Odd B → 1 ≤ s → s ≤ B - 1 →
      2 * B + 1 ∣ 4 * s ^ 2 - 1 →
      B ∣ (s - 1) * s * (s + 1) →
      1 < Int.gcd B (s - 1) ∧
      1 < Int.gcd B s ∧
      1 < Int.gcd B (s + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨erdos699_joint_adjacent_gcds, rejected, rejected_law⟩
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
    refine ⟨(), (0 : ℤ), (1 : ℤ), ?_⟩
    change (0 : ℤ) + 1 ≠ 1 + 1
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ s => s + 1) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Erdos699JointAdjacentCores") "erdos699_joint_adjacent_gcds") "Reg.D5.S3.Arith.Erdos699JointAdjacentCores/Reg.D5.S3.Arith.Erdos699JointAdjacentCores.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Erdos699JointAdjacentCores.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ s => s + 1) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Erdos699JointAdjacentCores, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms rejected_law
#print axioms registration

end Reg.D5.S3.Arith.Erdos699JointAdjacentCores
