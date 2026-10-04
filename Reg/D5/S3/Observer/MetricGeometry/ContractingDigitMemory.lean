import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.ContractingDigitMemory
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

open _root_.D5.S3.Observer.MetricGeometry.ContractingDigitMemory
open _root_.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
namespace Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory

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
  realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve every original hypothesis and the full least-state assertion. -/
def arena : Arena where
  signature := signature
  Law obs := ∀ {lam eps : ℝ} (hlampos : 0 < lam) (hlamhalf : lam < 1 / 2)
    (L : ℕ) (_hL : 1 ≤ L)
    (_heps_lower : lam ^ L / 2 ≤ eps)
    (_heps_upper : eps < (1 - lam) * lam ^ (L - 1) / 2),
    IsLeast
      {s : ℕ |
        HasFinitePredictor
          (digitStep lam hlampos.le (by linarith))
          (fun x : DigitState lam => x.1) eps s}
      (obs.readout () () L)

theorem positiveLaw : arena.Law actual :=
  @contracting_digit_memory_exact

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (h (lam := 1/4) (eps := 1/8) (by norm_num) (by norm_num)
    1 (by norm_num) (by norm_num) (by norm_num)).1
  obtain ⟨S, finiteS, hne, hcard, _⟩ := hzero
  let : Fintype S := finiteS
  let : Nonempty S := hne
  have hpos := Fintype.card_pos (α := S)
  change Fintype.card S ≤ 0 at hcard
  omega

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (@Subsingleton.elim Unit _ j i)).elim
  · intro e; exact nomatch e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) :=
  Registration.mk actual Iff.rfl ⟨positiveLaw, rejected, rejected_law⟩ sensitivity dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.contracting_digit_memory_exact) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ t => 2 ^ t) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "MetricGeometry") "ContractingDigitMemory") "contracting_digit_memory_exact") "Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory/Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ t => 2 ^ t) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory
