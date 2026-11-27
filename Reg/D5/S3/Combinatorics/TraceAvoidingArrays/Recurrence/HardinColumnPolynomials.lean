import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.Hardin.LagAudit
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials

/-! The per-column readout in the full six-row continuation sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnPolynomials
open HardinActualTransfers
open HardinColumnContinuations (Column columnV)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := Column 5
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ m p => ((C 5) ^ m).mulVec (1 : Column 5 → ℤ) p)
    (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), (HardinA233179PairTransfer.L (m + 1) : ℤ) =
    Finset.univ.sum (R.readout () m)

private theorem erased_law : ¬ arena.Law erased := by
  intro h
  have hz : (HardinA233179PairTransfer.L 1 : ℤ) = 0 := by
    simpa [erased, realize] using h 0
  have hw : (HardinA233179PairTransfer.L 1 : ℤ) = 729 := by
    simpa [Fintype.card_fun] using sixRow_walk 0
  exact (by decide : (729 : ℤ) ≠ 0) (hw.symm.trans hz)

private def constantColumn : Column 5 := fun _ => 0
private def threeColors : Column 5 := ![0, 1, 2, 0, 1, 2]

set_option maxHeartbeats 4000000 in
-- Kernel reduction enumerates the column continuations for the two fixed columns.
set_option maxRecDepth 10000 in
private theorem one_step_counts :
    columnV 1 constantColumn = 64 ∧ columnV 1 threeColors = 0 := by
  decide +kernel

def source : Registration arena (type_of% (@sixRow_walk)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sixRow_walk, erased, erased_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, constantColumn, threeColors, ?_⟩
    change ((C 5) ^ (1 : ℕ)).mulVec (1 : Column 5 → ℤ) constantColumn ≠
      ((C 5) ^ (1 : ℕ)).mulVec (1 : Column 5 → ℤ) threeColors
    rw [column_power, column_power, one_step_counts.1, one_step_counts.2]
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sixRow_walk) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnPolynomials.sixRow_walk.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ m p => ((C 5) ^ m).mulVec (1 : Column 5 → ℤ) p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials

/-! Source registrations for the full-state lag certificates. -/

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials
noncomputable section

open Reg.Support.HardinLagAudit (column_power_one_ne_two)

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnPolynomials
  (rowFour rowSix)

namespace RowFour

abbrev signature : Signature := Reg.Support.HardinLagAudit.signature 7

def actual : Realization signature :=
  realize signature (fun _ _ j => (![4, 13, -19, -22, 27, 2, -4] : Fin 7 → ℤ) j) (fun e => Empty.elim e)

abbrev arena : Arena := Reg.Support.HardinLagAudit.arena 7 (C 3) 1

def registration : Registration arena (type_of% (@rowFour)) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    Reg.Support.HardinLagAudit.variation (T := C 3) (b := 1) (d := 7)
      rowFour 5 6 (fun _ => 0)
      (column_power_one_ne_two 3).symm
  sensitivity :=
    Reg.Support.HardinLagAudit.sensitivity (T := C 3) (b := 1) (d := 7)
      rowFour 5 6 (fun _ => 0)
      (column_power_one_ne_two 3).symm
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change (![4, 13, -19, -22, 27, 2, -4] : Fin 7 → ℤ) 0 ≠ (![4, 13, -19, -22, 27, 2, -4] : Fin 7 → ℤ) 1
    decide +kernel

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rowFour) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials.RowFour.information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials.RowFour.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => (![4, 13, -19, -22, 27, 2, -4] : Fin 7 → ℤ) j) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn", "arg", "arg"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "fn", "arg", "arg", "body"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }
  ]

end RowFour

namespace RowSix

abbrev signature : Signature := Reg.Support.HardinLagAudit.signature 24

def actual : Realization signature :=
  realize signature (fun _ _ j => (![7, 103, -365, -2896, 7168, 32291, -75471, -161805, 426135,
      333692, -1225001, -155206, 1850161, -363389, -1524689, 557502, 690388, -312941,
      -166928, 81406, 19997, -9672, -906, 420] : Fin 24 → ℤ) j) (fun e => Empty.elim e)

abbrev arena : Arena := Reg.Support.HardinLagAudit.arena 24 (C 5) 1

def registration : Registration arena (type_of% (@rowSix)) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    Reg.Support.HardinLagAudit.variation (T := C 5) (b := 1) (d := 24)
      rowSix 22 23 (fun _ => 0)
      (column_power_one_ne_two 5).symm
  sensitivity :=
    Reg.Support.HardinLagAudit.sensitivity (T := C 5) (b := 1) (d := 24)
      rowSix 22 23 (fun _ => 0)
      (column_power_one_ne_two 5).symm
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change (![7, 103, -365, -2896, 7168, 32291, -75471, -161805, 426135,
      333692, -1225001, -155206, 1850161, -363389, -1524689, 557502, 690388, -312941,
      -166928, 81406, 19997, -9672, -906, 420] : Fin 24 → ℤ) 0 ≠ (![7, 103, -365, -2896, 7168, 32291, -75471, -161805, 426135,
      333692, -1225001, -155206, 1850161, -363389, -1524689, 557502, 690388, -312941,
      -166928, 81406, 19997, -9672, -906, 420] : Fin 24 → ℤ) 1
    decide +kernel

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rowSix) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials.RowSix.information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials.RowSix.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => (![7, 103, -365, -2896, 7168, 32291, -75471, -161805, 426135,
      333692, -1225001, -155206, 1850161, -363389, -1524689, 557502, 690388, -312941,
      -166928, 81406, 19997, -9672, -906, 420] : Fin 24 → ℤ) j) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn", "arg", "arg"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "fn", "arg", "arg", "body"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }
  ]

end RowSix

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinColumnPolynomials
