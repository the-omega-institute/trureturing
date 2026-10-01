/- L0 原型 -/
import D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
import Reg.ContractPrototype.Templates.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.ContractPrototype.Source

open _root_.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

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
  realize signature (fun _ _ H => 2 ^ (H + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ) (ε : ℝ) (_hε : 0 ≤ ε) (_hε1 : ε < 1),
    IsLeast {s : ℕ | HasFiniteHorizonPredictor
      (fun (_ : Unit) (x : ℕ → Bool) j => x (j + 1)) binaryObservation H ε s}
      (R.readout () () H) ∧
    Nat.clog 2 (2 ^ (H + 1)) = H + 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (binary_shift_exact_bit_law 0 0 le_rfl zero_lt_one).1.2
    (h 0 0 le_rfl zero_lt_one).1.1
  norm_num [rejected, realize, signature] at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨binary_shift_exact_bit_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    exact (by decide : (2 : ℕ) ^ (0 + 1) ≠ 2 ^ (1 + 1))

def declaration : LeanInformationAudit.Contract.Registration binary_shift_exact_bit_law
    Arena Arena
    (Realization signature) Unit Unit Unit Unit Unit where
  targetName := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.binary_shift_exact_bit_law
  arena := ⟨`Reg.ContractPrototype.Source.arena, arena⟩
  objectArena := ⟨`Reg.ContractPrototype.Source.arena, arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨`Reg.ContractPrototype.Source.registration, registration⟩
  readout := some (realize signature (fun _ _ H => 2 ^ (H + 1)) (fun e => nomatch e))
  variation := none
  sensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := {}

end Reg.ContractPrototype.Source
