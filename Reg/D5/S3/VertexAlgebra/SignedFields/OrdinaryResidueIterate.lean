import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Module.ULift
import D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate

/-! Source-bound equality readouts for ordinary residue iteration and its alternating weight. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators VertexOperator
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)
open _root_.D5.S3.VertexAlgebra.OrdinaryResidueIterate (residue_iterate alternating_iterate_weight)
open _root_.D5.S3.VertexAlgebra.FieldNormalProduct (identityField)
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality (delta)
open _root_.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality (signedComm)
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus (R)
open _root_.D5.S3.VertexAlgebra.BinomialKernelDelta (chooseSign)
open _root_.D5.S3.VertexAlgebra.StateFieldResidueReconstruction (epsilon)

namespace Reg.D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate
universe u

namespace Iterate

abbrev Params := Σ V : Type u, Σ group : AddCommGroup V, @Module ℂ V _ group.toAddCommMonoid

abbrev FieldAt (p : Params.{u}) := @VertexOperator ℂ p.1 _ p.2.1 p.2.2

abbrev observation := signature Params.{u} FieldAt (fun p => FieldAt p → Prop)

def actual : Realization observation.{u} :=
  realize observation (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization observation.{u} :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := observation.{u}
  Law readout := ∀ {V : Type u} [group : AddCommGroup V] [scalars : Module ℂ V]
    (J A B : VertexOperator ℂ V) (K L : ℕ)
    (_localityAB : delta^[K] (signedComm 1 A B) = 0)
    (_localityJB : delta^[L] (signedComm 1 J B) = 0) (m n : ℤ),
    readout.readout () ⟨V, group, scalars⟩ (R (R J A m) B n)
      ((∑ i ∈ Finset.range ((K : ℤ)-n).toNat,
        chooseSign m i • R J (R A B (n+i)) (m-i)) +
      (∑ i ∈ Finset.range L,
        (-epsilon m * chooseSign m i) • R A (R J B i) (m+n-i)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have zeroLocal : delta^[0] (signedComm 1 (0 : VertexOperator ℂ (ULift.{u} ℂ)) 0) = 0 := by
    funext a b
    simp [signedComm]
  exact h 0 0 0 0 0 zeroLocal zeroLocal 0 0

private theorem dependence : ObservationalDependence observation.{u} actual := by
  intro role
  let p : Params.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
  refine ⟨p, 0, identityField, ?_⟩
  intro h
  have same := congrFun h (0 : FieldAt p)
  have zeroField : (identityField : FieldAt p) = 0 := Eq.mp same rfl
  have zeroCoeff := congrArg (fun F : FieldAt p => (F[[-1]]) (ULift.up (1 : ℂ))) zeroField
  change ((identityField : VertexOperator ℂ (ULift.{u} ℂ))[[-1]]) (ULift.up (1 : ℂ)) =
    ((0 : VertexOperator ℂ (ULift.{u} ℂ))[[-1]]) (ULift.up (1 : ℂ)) at zeroCoeff
  erw [identityField, VertexOperator.ncoeff_of_coeff] at zeroCoeff
  have oneIsZero : (ULift.up (1 : ℂ) : ULift.{u} ℂ) = 0 := by simpa using zeroCoeff
  exact one_ne_zero (congrArg ULift.down oneIsZero)

def family : Registration arena (type_of% @residue_iterate.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@residue_iterate.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@residue_iterate.{u}) (Realization observation.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate.Iterate.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate.Iterate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Iterate

namespace AlternatingWeight

abbrev observation := signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization observation :=
  realize observation (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := observation
  Law readout := ∀ (a : ℂ) (k j : ℕ),
    readout.readout () ()
      (∑ p ∈ Finset.range (k+1), ((-1 : ℂ)^p * (k.choose p : ℂ)) * Ring.choose (a+p) j)
      ((-1 : ℂ)^k *
        @ite ℂ (k ≤ j) (Classical.propDecidable _) (Ring.choose a (j-k)) 0)

private theorem rejected_law : ¬ arena.Law rejected := fun h => h 0 0 0

private theorem dependence : ObservationalDependence observation actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def family : Registration arena (type_of% @alternating_iterate_weight) where
  actual := actual
  bridge := by
    dsimp only [arena, actual, realize]
    refine forall_congr' fun a => forall_congr' fun k => forall_congr' fun j => ?_
    rw [show Classical.propDecidable (k ≤ j) = inferInstance from Subsingleton.elim _ _]
  variation := ⟨by
    dsimp only [arena, actual, realize]
    intro a k j
    rw [show Classical.propDecidable (k ≤ j) = inferInstance from Subsingleton.elim _ _]
    exact alternating_iterate_weight a k j, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    alternating_iterate_weight (Realization observation) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate.AlternatingWeight.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate.AlternatingWeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AlternatingWeight

end Reg.D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate
