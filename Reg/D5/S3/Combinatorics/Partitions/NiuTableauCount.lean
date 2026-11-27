import D5.S3.Combinatorics.Partitions.NiuTableauCount
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The rational count as a readout of the row shape. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.NiuTableauCount
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.Partitions.NiuTableauCount

abbrev signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun k => Fin k → ℕ) (fun _ => ℚ)

def countReadout : Realization signature :=
  realize signature (fun _ _ rows => shiftedCount rows) (fun e => nomatch e)

def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev recurrenceArena : Arena where
  signature := signature
  Law r := ∀ {k : ℕ}, 2 ≤ k → ∀ (rows : Fin k → ℕ), Antitone rows →
    0 < ∑ j, rows j →
    r.readout () k rows =
      ∑ i ∈ Finset.univ.filter (RemovableRow rows), shiftedCount (deleteRow rows i)

private def oneCell (i : Fin 2) : ℕ := if i = 0 then 1 else 0

private theorem zeroReadout_fails : ¬ recurrenceArena.Law zeroReadout := by
  intro h
  have hcase := h (k := 2) (by decide) oneCell (by decide) (by decide)
  have hrem : Finset.univ.filter (RemovableRow oneCell) = {0} := by decide
  have hdelete : deleteRow oneCell 0 = (fun _ => 0) := by decide
  change (0 : ℚ) = ∑ i ∈ Finset.univ.filter (RemovableRow oneCell),
    shiftedCount (deleteRow oneCell i) at hcase
  rw [hrem, Finset.sum_singleton, hdelete, shiftedCount_empty] at hcase
  exact zero_ne_one hcase

private theorem countReadout_depends : ObservationalDependence signature countReadout := by
  intro i
  refine ⟨2, (fun _ => 0), (fun j => if j = 0 then 2 else 1), ?_⟩
  change shiftedCount (fun _ : Fin 2 => 0) ≠ shiftedCount (fun j : Fin 2 => if j = 0 then 2 else 1)
  decide +kernel

def recurrenceFamily : Registration recurrenceArena (type_of% @shiftedCount_recurrence) where
  actual := countReadout
  bridge := Iff.rfl
  variation := ⟨@shiftedCount_recurrence, zeroReadout, zeroReadout_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    recurrenceArena.Law countReadout zeroReadout zeroReadout_fails
  dependence := countReadout_depends

def recurrenceRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@shiftedCount_recurrence) (type_of% countReadout) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Partitions.NiuTableauCount.shiftedCount_recurrence.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.NiuTableauCount.recurrenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨recurrenceArena⟩
  objectArena := .source ⟨recurrenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source recurrenceArena ⟨recurrenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rows => shiftedCount rows) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.NiuTableauCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev emptyArena : Arena where
  signature := signature
  Law r := ∀ k : ℕ, r.readout () k (fun _ => 0) = 1

private theorem zeroReadout_fails_empty : ¬ emptyArena.Law zeroReadout := by
  intro h
  exact zero_ne_one (show (0 : ℚ) = 1 from h 0)

def emptyFamily : Registration emptyArena (type_of% shiftedCount_empty) where
  actual := countReadout
  bridge := Iff.rfl
  variation := ⟨shiftedCount_empty, zeroReadout, zeroReadout_fails_empty⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    emptyArena.Law countReadout zeroReadout zeroReadout_fails_empty
  dependence := countReadout_depends

def emptyRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      shiftedCount_empty (type_of% countReadout) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.NiuTableauCount.shiftedCount_empty.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.NiuTableauCount.emptyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨emptyArena⟩
  objectArena := .source ⟨emptyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source emptyArena ⟨emptyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rows => shiftedCount rows) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.NiuTableauCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Partitions.NiuTableauCount
