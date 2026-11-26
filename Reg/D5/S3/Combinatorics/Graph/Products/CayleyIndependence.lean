import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Products.CayleyIndependence
import Mathlib.Algebra.Group.ULift

/-! Vertex differences as a dependent readout on the original abelian Cayley domain. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Products.CayleyIndependence

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph

universe u

noncomputable section

abbrev differenceScope := type_of% (@CayleySquare.cayley_adj_iff.{u})

abbrev differenceSignature : Signature where
  Params := Σ A : Type u, Σ _ : AddCommGroup A, A
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def differenceActual : Realization differenceSignature.{u} :=
  realize differenceSignature (fun _ p y => by
    letI : AddCommGroup p.1 := p.2.1
    exact y - p.2.2)
    (fun e => nomatch e)

abbrev differenceArena : Arena where
  signature := differenceSignature.{u}
  Law r := ∀ {A : Type u} [g : AddCommGroup A] (S : Set A)
    (_ : (0 : A) ∉ S) (_ : ∀ a ∈ S, -a ∈ S) (x y : A),
    (addCayley S).Adj x y ↔ r.readout () ⟨A, g, x⟩ y ∈ S

private theorem difference_bridge :
    differenceScope.{u} ↔ differenceArena.{u}.Law differenceActual.{u} := by
  exact Iff.rfl

def alwaysZero : Realization differenceSignature.{u} :=
  realize differenceSignature (fun _ p _ => by
    letI : AddCommGroup p.1 := p.2.1
    exact 0) (fun e => nomatch e)

private theorem always_zero_fails : ¬ differenceArena.{u}.Law alwaysZero.{u} := by
  intro h
  let S : Set (ULift.{u} ℤ) := {a | a ≠ 0}
  have hzero : (0 : ULift.{u} ℤ) ∉ S := by simp [S]
  have hneg : ∀ a ∈ S, -a ∈ S := by simp [S]
  let one : ULift.{u} ℤ := ULift.up 1
  have hone : one ≠ 0 := fun h => Int.one_ne_zero (congrArg ULift.down h)
  have hadj : (addCayley S).Adj 0 one :=
    (CayleySquare.cayley_adj_iff S hzero hneg 0 one).mpr (by simpa [S] using hone)
  exact hzero ((h S hzero hneg 0 one).mp hadj)

private theorem difference_dependence :
    ObservationalDependence differenceSignature.{u} differenceActual.{u} := by
  intro role
  let one : ULift.{u} ℤ := ULift.up 1
  have hone : one ≠ 0 := fun h => Int.one_ne_zero (congrArg ULift.down h)
  refine ⟨⟨ULift.{u} ℤ, inferInstance, 0⟩, one, 0, ?_⟩
  simpa [differenceActual, realize] using hone

def differenceFamily : Registration differenceArena.{u} differenceScope.{u} where
  actual := differenceActual
  bridge := difference_bridge
  variation := ⟨difference_bridge.mp (@CayleySquare.cayley_adj_iff.{u}),
    alwaysZero, always_zero_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysZero, ?_, rfl, always_zero_fails⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := difference_dependence

def differenceRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, u + 1, u, 0, u, 0, 0}
      (@CayleySquare.cayley_adj_iff.{u}) (Realization differenceSignature.{u}) Type Unit where
  unitName := `CayleySquare.cayley_adj_iff.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Products.CayleyIndependence.differenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨differenceArena⟩
  objectArena := .source ⟨differenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source differenceArena ⟨differenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize differenceSignature (fun _ p y => by
    letI : AddCommGroup p.1 := p.2.1
    exact y - p.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Products.CayleyIndependence
    definition := none
    coordinates := #[0, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Products.CayleyIndependence
