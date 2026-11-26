import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointFiniteArithmetic

/-! The real comparison readout for the centered Bernoulli moment gap. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuEndpointFiniteArithmetic

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointFiniteArithmetic

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def weak : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private theorem weak_dependence : ObservationalDependence signature weak := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (Eq.mp (congrFun h 0) (le_refl 0))

namespace CenteredBernoulliGap

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ}, -a ≤ b → b ≤ a →
    R.readout () () ((14 / 3) * (a ^ 2) ^ 4 * (b ^ 2) ^ 2)
      ((a ^ 3 + 3 * a * b ^ 2) ^ 4 -
        (a ^ 4 + 4 * a ^ 2 * b ^ 2 + (4 / 9) * b ^ 4) ^ 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (a := 1) (b := 0) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @centered_bernoulli_moment_gap) where
  actual := weak
  bridge := Iff.rfl
  variation := ⟨@centered_bernoulli_moment_gap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law weak rejected rejected_law
  dependence := weak_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_bernoulli_moment_gap) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointFiniteArithmetic.centered_bernoulli_moment_gap.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointFiniteArithmetic.CenteredBernoulliGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature weak.readout weak.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointFiniteArithmetic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CenteredBernoulliGap

end Reg.D5.S3.Quantum.Semigroups.WuEndpointFiniteArithmetic
