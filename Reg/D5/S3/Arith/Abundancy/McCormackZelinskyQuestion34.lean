import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34
import Reg.Support.SingleDependentReadout

/-! A source family for strict comparison of the two weighted totient means. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.WeightedTotientEulerDensity

namespace Reg.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {S : Finset ℕ}, Odd n → S ⊆ n.divisors →
    1 ∈ S → ∑ d ∈ S, d = 2 * n →
    R.readout () () (weightA S n) (weightC S n)

private def exampleSet : Finset ℕ := (945 : ℕ).divisors \ {3, 27}

private theorem example_subset : exampleSet ⊆ (945 : ℕ).divisors :=
  sdiff_subset

private theorem example_one : 1 ∈ exampleSet := by decide

set_option maxRecDepth 4096 in
private theorem example_sum : ∑ d ∈ exampleSet, d = 2 * 945 := by decide

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := 945) (S := exampleSet) (by decide)
    example_subset example_one example_sum

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
  exact (lt_irrefl 1) hf

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34.odd_weight_reverse)
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34.odd_weight_reverse,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34.odd_weight_reverse)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34.odd_weight_reverse.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34
