import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Square-Avoider Enumeration and Rational Generating Series -/

namespace Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration

open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareDefs
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareCounting
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
open _root_.D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace IndecomposableCountAndRecurrenceBoundary

attribute [local instance 2000] Classical.propDecidable

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    (∀ n : ℕ, b (O.readout () () n) =
      if n = 0 then 0 else if n ≤ 2 then 1 else if n = 3 then 2 else
      if n ≤ 5 then 3 else if n = 6 then 5 else if n = 7 then 6 else
      if n = 8 then 7 else n / 2 + 4) ∧
    b 1 = 1 ∧ b 2 = 1 ∧ b 3 = 2 ∧ b 4 = 3 ∧ b 5 = 3 ∧ b 6 = 5 ∧ b 7 = 6 ∧ b 8 = 7 ∧
    (∀ n : ℕ, 9 ≤ n → b n = n / 2 + 4) ∧
    c 0 = 1 ∧ (∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.Icc 1 n, b k * c (n - k)) ∧
    (∀ n : ℕ, 6 ≤ n →
      (a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + (n - 1) ↔ n ≤ 10)) ∧
    (∀ n : ℕ, 11 ≤ n →
      a n < a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + (n - 1)) ∧
    (∀ n : ℕ, 5 ≤ n → a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + b n) ∧
    (∀ n : ℕ, 6 ≤ n →
      (a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + (n - 1) ↔ b n = n - 1)) ∧
    (∀ n : ℕ, 6 ≤ n → n ≤ 10 → b n = n - 1) ∧
    (∀ n : ℕ, 11 ≤ n → b n < n - 1)

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hbad := h.1 1
  change b 0 = _ at hbad
  have hbad1 : b 0 = 1 := by simpa using hbad
  have hb0 : b 0 = 0 := indecomposable_shape_and_prefix_iff.1
  omega

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def evidence : Registration arena
    (type_of% (@indecomposable_count_and_recurrence_boundary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨indecomposable_count_and_recurrence_boundary, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@indecomposable_count_and_recurrence_boundary)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration.IndecomposableCountAndRecurrenceBoundary.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration.IndecomposableCountAndRecurrenceBoundary.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IndecomposableCountAndRecurrenceBoundary

namespace GeneratingSeriesAndOrderSevenRecurrence

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    let num : PowerSeries ℤ := PowerSeries.X + PowerSeries.X ^ 4 - PowerSeries.X ^ 5 +
      PowerSeries.X ^ 6 + PowerSeries.X ^ 7 - PowerSeries.X ^ 8 - PowerSeries.X ^ 11
    let denB : PowerSeries ℤ := (1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2)
    let denC : PowerSeries ℤ :=
      1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4
    let denA : PowerSeries ℤ := denB * denC
    PowerSeries.constantCoeff seriesB = 0 ∧ PowerSeries.constantCoeff seriesA = 0 ∧
    IsUnit denB ∧ IsUnit denC ∧ IsUnit denA ∧
    seriesA * denC = seriesB ∧ seriesA = seriesB * Ring.inverse denC ∧
    seriesB * denB = num ∧ seriesB = num * Ring.inverse denB ∧
    seriesA * denA = num ∧ seriesA = num * Ring.inverse denA ∧
    denA = (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 5 - PowerSeries.X ^ 7 : PowerSeries ℤ) ∧
    (∀ n : ℕ, 12 ≤ n →
      (a (O.readout () () n) : ℤ) = 2 * (a (n - 1) : ℤ) + (a (n - 2) : ℤ) -
        2 * (a (n - 3) : ℤ) - (a (n - 5) : ℤ) + (a (n - 7) : ℤ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.2.2.2.2.2.2.2.2.2.2.2.2 12 (by omega)
  have hgood := generating_series_and_order_seven_recurrence.2.2.2.2.2.2.2.2.2.2.2.2 12 (by omega)
  have hbd := indecomposable_count_and_recurrence_boundary
  have ha1 : a 1 = 1 := by
    rw [hbd.2.2.2.2.2.2.2.2.2.2.2.1 1 (by omega)]
    simp [hbd.2.1, hbd.2.2.2.2.2.2.2.2.2.2.1]
  have ha12 : 10 ≤ a 12 := by
    have hrec := count_recurrence 12 (by omega)
    rw [← (indecomposable_shape_and_prefix_iff.2.1 12 (by omega)).2,
      hbd.2.2.2.2.2.2.2.2.2.1 12 (by omega)] at hrec
    omega
  change (a 1 : ℤ) = _ at hbad
  omega

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@generating_series_and_order_seven_recurrence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨generating_series_and_order_seven_recurrence, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@generating_series_and_order_seven_recurrence)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration.GeneratingSeriesAndOrderSevenRecurrence.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration.GeneratingSeriesAndOrderSevenRecurrence.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeneratingSeriesAndOrderSevenRecurrence

end Reg.D5.S3.Combinatorics.PermutationSquare.PermutationSquareEnumeration
