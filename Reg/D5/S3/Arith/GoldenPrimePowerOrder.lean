import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenPrimePowerOrder
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenPrimePowerOrder

open _root_.D5.S3.Arith.GoldenApparition
open _root_.D5.S3.Arith.GoldenPrimePowerOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => p ^ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p n => p ^ n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law readout := ∀ {p m n : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hpm : m + 2 ≤ p * m) (a b : ℤ)
    (hab : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b),
    orderOf (1 + (p ^ m : GoldenMod (p ^ (n + m))) *
      (⟨a, b⟩ : GoldenMod (p ^ (n + m)))) = readout.readout () p n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood := golden_prime_power_order (p := 3) (m := 1) (n := 0)
    (by decide) (by omega) (by omega) 1 0
    (Or.inl (by norm_num))
  have hbad := h (p := 3) (m := 1) (n := 0)
    (by decide) (by omega) (by omega) 1 0
    (Or.inl (by norm_num))
  change orderOf (1 + (3 ^ 1 : GoldenMod (3 ^ (0 + 1))) *
    (⟨1, 0⟩ : GoldenMod (3 ^ (0 + 1)))) = 3 ^ (0 : ℕ) at hgood
  change orderOf (1 + (3 ^ 1 : GoldenMod (3 ^ (0 + 1))) *
    (⟨1, 0⟩ : GoldenMod (3 ^ (0 + 1)))) = 3 ^ (0 : ℕ) + 1 at hbad
  rw [hgood] at hbad
  omega

def registration : Registration arena
    (∀ {p m n : ℕ} (hp : p.Prime)
      (hm : 0 < m) (hpm : m + 2 ≤ p * m) (a b : ℤ)
      (hab : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b),
      orderOf (1 + (p ^ m : GoldenMod (p ^ (n + m))) *
        (⟨a, b⟩ : GoldenMod (p ^ (n + m)))) = p ^ n) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_prime_power_order, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨3, (0 : ℕ), (1 : ℕ), ?_⟩
    change (3 : ℕ) ^ 0 ≠ 3 ^ 1
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.GoldenPrimePowerOrder.golden_prime_power_order) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p n => p ^ n) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "GoldenPrimePowerOrder") "golden_prime_power_order") "Reg.D5.S3.Arith.GoldenPrimePowerOrder/Reg.D5.S3.Arith.GoldenPrimePowerOrder.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.GoldenPrimePowerOrder.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p n => p ^ n) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.GoldenPrimePowerOrder, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.GoldenPrimePowerOrder
