import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance

open _root_.D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open Finset

noncomputable section

abbrev Parameter := Σ q : ℕ, Cover q

def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameter (fun _ => ℤ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (p : Parameter) (j : ℤ) => p.2.spanCount j)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (p : Parameter) (j : ℤ) => p.2.spanCount j + 1)
    (fun e => nomatch e)

/-- The complete original telescope, replacing only the span-incidence readout. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} (C : Cover q),
    (∀ j : ℤ, |j| < (q : ℤ) →
      R.readout () ⟨q, C⟩ j = (q : ℤ) - |j| + C.holeCount j) ∧
    C.holeCount 0 = 0 ∧ C.holeCount (1 - (q : ℤ)) = 0 ∧
    C.holeCount ((q : ℤ) - 1) = 0 ∧
    (∀ j : ℤ, |j| < (q : ℤ) → 0 ≤ C.holeCount j ∧ C.holeCount j ≤ |j|) ∧
    (∀ j : ℤ, j < 1 - (q : ℤ) ∨ (q : ℤ) - 1 < j → C.holeCount j = 0) ∧
    C.totalGap = (∑ j ∈ Icc (1 - (q : ℤ)) ((q : ℤ) - 1), C.holeCount j) ∧
    (∀ j : ℤ, 1 - (q : ℤ) ≤ j ∧ j ≤ 0 →
      C.starts j = 1 + C.holeCount j - C.holeCount (j - 1)) ∧
    (∀ j : ℤ, 0 ≤ j ∧ j ≤ (q : ℤ) - 1 →
      C.ends j = 1 + C.holeCount j - C.holeCount (j + 1)) ∧
    (∀ t : Fin q, C.upper t - C.lower t = 18 - C.defect t + C.gap t) ∧
    (∑ t : Fin q, (C.upper t - C.lower t)) = (q : ℤ) * ((q : ℤ) - 1) + C.totalGap ∧
    (∀ k : ℤ, 0 < k ∧ k < (q : ℤ) →
      ((univ.filter (fun t : Fin q => C.upper t < k)).card : ℤ) = k - C.holeCount k ∧
      ((univ.filter (fun t : Fin q => -C.lower t < k)).card : ℤ) = k - C.holeCount (-k))

def oneCover : Cover 1 where
  label := Prod.fst
  anchor _ := rfl
  separates x y _ _ := Subsingleton.elim x y

def registration : Registration arena
    (type_of% (@Cover.complete_span_endpoint_balance)) := by
  classical
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hb := (h oneCover).1 0 (by norm_num)
    have ha := oneCover.complete_span_endpoint_balance.1 0 (by norm_num)
    change oneCover.spanCount 0 + 1 = (1 : ℤ) - |(0 : ℤ)| + oneCover.holeCount 0 at hb
    omega
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨Cover.complete_span_endpoint_balance, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := ?_ }
  intro i
  refine ⟨⟨1, oneCover⟩, (0 : ℤ), (1 : ℤ), ?_⟩
  have hzero := oneCover.complete_span_endpoint_balance.2.1
  have hspan := oneCover.complete_span_endpoint_balance.1 0 (by norm_num)
  have hpositive : oneCover.spanCount 1 = 0 := by
    simp [Cover.spanCount, Cover.spanning, Cover.lower, Cover.upper,
      Cover.occupied, Cover.cells, difference, oneCover]
  change oneCover.spanCount 0 ≠ oneCover.spanCount 1
  rw [hpositive]
  simp only [hzero, abs_zero, sub_zero, add_zero] at hspan
  omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Cover.complete_span_endpoint_balance)
    (type_of% (realize signature
      (fun (_ : Unit) (p : Parameter) (j : ℤ) => p.2.spanCount j)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance.Cover.complete_span_endpoint_balance.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (p : Parameter) (j : ℤ) => p.2.spanCount j)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Combinatorics.Geometry.AnchoredSquareSpanBalance
