import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualFactorialRobinHighWeight
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter
open scoped BigOperators Topology
namespace Reg.D5.S3.Arith.Robin.ActualFactorialRobinHighWeight
open _root_.D5.S3.Arith.Robin.ActualFactorialRobinHighWeight
open _root_.D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail (weightedOddTail)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => q r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ r : ℝ, 0 < r → 0 < R.readout () () r ∧
      HasDerivAt (R.readout () ()) (qDerivative r) r ∧ qDerivative r < 0) ∧
    StrictAntiOn (R.readout () ()) (Ioi (0 : ℝ)) ∧
    Tendsto (R.readout () ()) atTop (𝓝 0) ∧
    (∀ D M : ℕ, 2 ≤ D → D < M →
      |weightedOddTail D M (fun m => R.readout () () (Real.log m))| ≤
        4 * R.readout () () (Real.log ((D+1 : ℕ) : ℝ))) ∧
    CauchySeq (fun N : ℕ =>
      ∑ m ∈ (Finset.range N).filter (fun m => Odd m ∧ 3 ≤ m),
        (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) * R.readout () () (Real.log m)) ∧
    ∃ Q : ℝ, Tendsto (fun N : ℕ =>
      ∑ m ∈ (Finset.range N).filter (fun m => Odd m ∧ 3 ≤ m),
        (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) * R.readout () () (Real.log m)) atTop (𝓝 Q)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (0 : ℝ) < 0 := (h.1 1 (by norm_num)).1
  exact (lt_irrefl (0 : ℝ)) hz

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change q 1 ≠ q 2
    exact (ne_of_gt (result.2.1 (by norm_num) (by norm_num) (by norm_num)))

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    result (type_of% (realize signature actual.readout actual.anchor)) (ℝ → ℝ) Unit where
  unitName := `D5.S3.Arith.Robin.ActualFactorialRobinHighWeight.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualFactorialRobinHighWeight.family
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
  escapeFrom := some q
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualFactorialRobinHighWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "arg", "fn"]
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
end Reg.D5.S3.Arith.Robin.ActualFactorialRobinHighWeight
