import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Erdos699AdjacentCores
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Erdos699AdjacentCores

open _root_.D5.S3.Arith.Erdos699AdjacentCores
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law := fun r => ∀ (n M t R₁ R₂ δ₁ δ₂ : ℕ),
    0 < t → 2 * t < M → R₁.Coprime R₂ →
    R₁ ∣ t * (M - t) → R₂ ∣ t * (M - t) * (M - 2 * t) →
    δ₁ ≤ 3 → δ₂ ≤ 3 →
    n = δ₁ * R₁ + 1 → n = 2 * δ₂ * R₂ + 2 →
    r.readout () () n ≤ 3 * M ^ 6

def actual : Realization signature :=
  realize signature (fun _ _ n => ((n - 1) * (n - 2)) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2188) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h 4 3 1 1 1 3 1
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  change (2188 : ℕ) ≤ 3 * 3 ^ 6 at hfalse
  norm_num at hfalse

def registration : Registration arena
    (∀ (n M t R₁ R₂ δ₁ δ₂ : ℕ),
      0 < t → 2 * t < M → R₁.Coprime R₂ →
      R₁ ∣ t * (M - t) → R₂ ∣ t * (M - t) * (M - 2 * t) →
      δ₁ ≤ 3 → δ₂ ≤ 3 →
      n = δ₁ * R₁ + 1 → n = 2 * δ₂ * R₂ + 2 →
      ((n - 1) * (n - 2)) ^ 2 ≤ 3 * M ^ 6) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨adjacent_core_numerator_bound, rejected, rejected_law⟩
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
    refine ⟨(), (4 : ℕ), (5 : ℕ), ?_⟩
    change (((4 - 1) * (4 - 2)) ^ 2 : ℕ) ≠ ((5 - 1) * (5 - 2)) ^ 2
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Erdos699AdjacentCores.adjacent_core_numerator_bound) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ n => ((n - 1) * (n - 2)) ^ 2) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Erdos699AdjacentCores") "adjacent_core_numerator_bound") "Reg.D5.S3.Arith.Erdos699AdjacentCores/Reg.D5.S3.Arith.Erdos699AdjacentCores.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Erdos699AdjacentCores.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ n => ((n - 1) * (n - 2)) ^ 2) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Erdos699AdjacentCores, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms rejected_law
#print axioms registration

end Reg.D5.S3.Arith.Erdos699AdjacentCores
