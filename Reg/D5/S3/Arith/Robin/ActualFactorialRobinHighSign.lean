import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualFactorialRobinHighSign
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter
open scoped BigOperators Topology
namespace Reg.D5.S3.Arith.Robin.ActualFactorialRobinHighSign
open _root_.D5.S3.Arith.Robin.ActualFactorialRobinHighSign
open _root_.D5.S3.Arith.Robin.ActualFactorialRobinHighWeight (q naturalPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ N => naturalPrefix N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ Q : ℝ, Tendsto (R.readout () ()) atTop (𝓝 Q) ∧
    Q ≤ -q (Real.log 3)/3 ∧ -q (Real.log 3)/3 < 0

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨Q, hQ, hb, hn⟩
  have hz : Q = 0 := tendsto_nhds_unique hQ tendsto_const_nhds
  subst Q
  linarith

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 0, 4, ?_⟩
    change naturalPrefix 0 ≠ naturalPrefix 4
    have hl : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hp := (_root_.D5.S3.Arith.Robin.ActualFactorialRobinHighWeight.result.1
      (Real.log 3) hl).1
    have hm : ArithmeticFunction.moebius 3 = -1 :=
      ArithmeticFunction.moebius_apply_prime (by norm_num)
    norm_num [naturalPrefix, Finset.sum_filter, Finset.sum_range_succ, hm]
    linarith

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    result (type_of% (realize signature actual.readout actual.anchor)) (ℕ → ℝ) Unit where
  unitName := `D5.S3.Arith.Robin.ActualFactorialRobinHighSign.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualFactorialRobinHighSign.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some naturalPrefix
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualFactorialRobinHighSign
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Arith.Robin.ActualFactorialRobinHighSign
