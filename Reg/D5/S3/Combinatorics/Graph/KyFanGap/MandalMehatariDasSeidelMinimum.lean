import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of counting occurrences in a finite function's list. -/

namespace Reg.D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.CountOfFn

open _root_.D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.MMDCounts
  (count_ofFn)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe equality between the occurrence count and its indicator sum. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Retain the carrier, equality dictionary, length, function and counted value. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} [DecidableEq α] {n : ℕ} (f : Fin n → α) (p : α),
    R.readout () () ((List.ofFn f).count p) (∑ i, if f i = p then 1 else 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (α := ULift.{u} Unit) (n := 0) (fun _ => ⟨()⟩) ⟨()⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def source_registration : Registration arena.{u} (type_of% @count_ofFn.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_ofFn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@count_ofFn.{u}) (Realization signature) Unit Unit := {
  unitName := .str
    `D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.MMDCounts.count_ofFn
    "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.CountOfFn
