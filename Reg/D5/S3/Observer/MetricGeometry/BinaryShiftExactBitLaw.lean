import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw

open _root_.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.binary_shift_exact_bit_law) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ H => 2 ^ (H + 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "MetricGeometry") "BinaryShiftExactBitLaw") "binary_shift_exact_bit_law") "Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw/Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ H => 2 ^ (H + 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
