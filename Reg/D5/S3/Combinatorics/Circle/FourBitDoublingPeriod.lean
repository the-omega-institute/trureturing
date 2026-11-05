import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.FourBitDoublingPeriod
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Four-slot source registration attempt. Source binding is subject to issue #11434;
no declared_validated status is asserted by these typed proof terms. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle
open _root_.D5.S3.Combinatorics.Circle.FourBitDoublingPeriod
namespace Reg.D5.S3.Combinatorics.Circle.FourBitDoublingPeriod
noncomputable section

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p h => NarrowDoublingOrbit.residue p.1 p.2 h)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (_ : 2 ≤ a) (_ : 2 ≤ b) (_ : 2 ≤ c) (_ : 2 ≤ d),
    let r := a + b + c + d
    let M := 2 ^ r - 1
    let Q := 1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)
    let p := if a = b ∧ b = c ∧ c = d then a
      else if a = c ∧ b = d then a + b else r
    NarrowDoublingOrbit.period M Q = p ∧
      ∀ h : ℕ, (R.readout () (M, Q) h = Q ↔ p ∣ h)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hh := (hall 2 2 2 2 (by decide) (by decide) (by decide) (by decide)).2 0
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(255, 85), 0, 1, ?_⟩
  norm_num [actual, realize, NarrowDoublingOrbit.residue]

def family : Registration arena (type_of% (@four_gap_actual_period)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@four_gap_actual_period, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@four_gap_actual_period) (type_of% actual) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.FourBitDoublingPeriod.four_gap_actual_period.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourBitDoublingPeriod.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p h => NarrowDoublingOrbit.residue p.1 p.2 h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.FourBitDoublingPeriod
    definition := none
    coordinates := #[9, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end
end Reg.D5.S3.Combinatorics.Circle.FourBitDoublingPeriod
