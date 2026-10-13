import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments
open _root_.D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates
open _root_.D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

noncomputable section
namespace Reg.D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates

@[reducible] def signature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Real
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k j => ((infiniteOperator ^ k) endpoint) j)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ k j : Nat, R.readout () k j = (-1 : Real) ^ j *
    MvPolynomial.eval₂Hom (Int.castRingHom Real) (fun _ : Fin 2 => (3 : Real))
      (motzkin k j)

def family : Registration arena (type_of% @iterate_coordinates) := by
  have hactual : arena.Law actual := by
    intro k j
    exact iterate_coordinates k j
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hz := h 0 0
    norm_num [rejected, realize, motzkin] at hz
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨hactual, rejected, hbad⟩
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
    refine ⟨0, 0, 1, ?_⟩
    simp [actual, realize, endpoint, lp.single_apply]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@iterate_coordinates)
    (type_of% (realize signature
      (fun _ k j => ((infiniteOperator ^ k) endpoint) j) (fun e => nomatch e)))
    Unit Unit := {
  unitName :=
    `D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates.iterate_coordinates.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates.family
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
    (fun _ k j => ((infiniteOperator ^ k) endpoint) j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates
