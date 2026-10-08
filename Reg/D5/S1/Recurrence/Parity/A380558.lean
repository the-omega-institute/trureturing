import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Parity.A380558
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.Parity.A380558

open PowerSeries
open _root_.D5.S1.Recurrence.Parity.A380558
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => coeff n generatingSeries) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r :=
    constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 0 ∧
    generatingSeries.subst (X - generatingSeries) =
      X ^ 2 * invOfUnit (1 - X ^ 2) 1 ∧
    (∀ F : PowerSeries ℤ, constantCoeff F = 0 → coeff 1 F = 0 →
      F.subst (X - F) = X ^ 2 * invOfUnit (1 - X ^ 2) 1 →
      F = generatingSeries) ∧
    ∀ n : ℕ, Odd (r.readout () () n) ↔ n = 2 ∨
      ∃ m j : ℕ, n = 2 * m ∧ 3 * 2 ^ j ≤ m ∧ m < 4 * 2 ^ j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h2 := (h.2.2.2.2 2).2 (Or.inl rfl)
  change Odd (0 : ℤ) at h2
  norm_num at h2

def registration : Registration arena
    (constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 0 ∧
    generatingSeries.subst (X - generatingSeries) =
      X ^ 2 * invOfUnit (1 - X ^ 2) 1 ∧
    (∀ F : PowerSeries ℤ, constantCoeff F = 0 → coeff 1 F = 0 →
      F.subst (X - F) = X ^ 2 * invOfUnit (1 - X ^ 2) 1 →
      F = generatingSeries) ∧
    ∀ n : ℕ, Odd (coeff n generatingSeries) ↔ n = 2 ∨
      ∃ m j : ℕ, n = 2 * m ∧ 3 * 2 ^ j ≤ m ∧ m < 4 * 2 ^ j) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i
      cases j
      exact False.elim (h rfl)
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (2 : ℕ), ?_⟩
    change coeff 0 generatingSeries ≠ coeff 2 generatingSeries
    intro h
    have h0 : coeff 0 generatingSeries = 0 := by
      simpa only [coeff_zero_eq_constantCoeff] using result.1
    have hodd : Odd (coeff 2 generatingSeries) := (result.2.2.2.2 2).2 (Or.inl rfl)
    rw [h0] at h
    rw [← h] at hodd
    norm_num at hodd

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Recurrence.Parity.A380558.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => coeff.{0} n generatingSeries) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Recurrence") "Parity") "A380558") "result") "Reg.D5.S1.Recurrence.Parity.A380558/Reg.D5.S1.Recurrence.Parity.A380558.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Recurrence.Parity.A380558.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => coeff.{0} n generatingSeries) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Recurrence.Parity.A380558, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "arg", "arg", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S1.Recurrence.Parity.A380558
