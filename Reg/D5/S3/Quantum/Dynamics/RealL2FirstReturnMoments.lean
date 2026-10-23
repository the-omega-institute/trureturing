import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments
open scoped InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments

@[reducible] def signature : Signature where
  Params := Unit
  State _ := lp (fun _ : Nat => Real) 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Real
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => inner Real endpoint x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (hn : 1 ≤ n),
    (∀ k : Nat, k < 2 * n →
      inner Real (finiteEndpoint n hn) ((finiteOperator n ^ k) (finiteEndpoint n hn)) =
      R.readout () () ((infiniteOperator ^ k) endpoint)) ∧
    inner Real endpoint ((infiniteOperator ^ (2 * n)) endpoint) -
      inner Real (finiteEndpoint n hn)
        ((finiteOperator n ^ (2 * n)) (finiteEndpoint n hn)) = 1

def family : Registration arena (type_of% @endpoint_moments) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hz := (h 1 (Nat.le_refl 1)).1 0 (by norm_num)
    norm_num [rejected, realize, finiteEndpoint, PiLp.inner_apply, PiLp.single_apply] at hz
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨endpoint_moments, rejected, hbad⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hbad⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  · intro i
    refine ⟨(), 0, endpoint, ?_⟩
    simp [actual, realize, endpoint, lp.inner_single_left]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@endpoint_moments)
    (type_of% (realize signature (fun _ _ x => inner Real endpoint x)
      (fun e => nomatch e))) (lp (fun _ : Nat => Real) 2) Unit := {
  unitName := `D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments.endpoint_moments.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => inner Real endpoint x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some endpoint
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments
