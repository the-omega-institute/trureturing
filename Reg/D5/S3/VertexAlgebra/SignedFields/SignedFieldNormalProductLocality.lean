import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Module.ULift
import D5.S3.VertexAlgebra.SignedFields.SignedFieldNormalProductLocality

/-! Dependent-family source attempts; the original source selectors remain unresolved. -/
open scoped VertexOperator
open _root_.D5.S3.VertexAlgebra.FieldNormalProduct
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality
open _root_.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality
universe u

structure Context where
  V : Type u
  group : AddCommGroup V
  scalars : @Module ℂ V inferInstance group.toAddCommMonoid
attribute [instance] Context.group Context.scalars

abbrev signature : Signature where
  Params := Context.{u}
  State C := ℤ → ℤ → Module.End ℂ C.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ d => d = 0) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let C : Context.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
  refine ⟨C, 0, (fun _ _ => 1), ?_⟩
  intro h
  have h' : (fun _ _ : ℤ => (1 : Module.End ℂ C.V)) = 0 := Eq.mp h rfl
  have h'' := congrFun (congrFun h' 0) 0
  exact one_ne_zero h''

namespace Normal
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Context.{u}) (x y z : ℂ) (A B C : VertexOperator ℂ K.V)
    (Na Nb Nc : ℕ), delta^[Na] (signedComm y A C) = 0 →
      delta^[Nb] (signedComm z B C) = 0 → delta^[Nc] (signedComm x A B) = 0 →
      R.readout () K (delta^[Na + Nb + Nc]
        (signedComm (y * z) (signedNormalMinusOne x A B).1 C))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K : Context.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
  exact h K 0 0 0 0 0 0 0 0 0 (by ext; simp [signedComm])
    (by ext; simp [signedComm]) (by ext; simp [signedComm])
def family : Registration arena (type_of% @signedNormal_locality.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h K
      exact h
    · intro h V hGroup hScalars
      exact h ⟨V, hGroup, hScalars⟩
  variation := ⟨(fun K => signedNormal_locality), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signedNormal_locality.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.Normal.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.Normal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => d = 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Normal

namespace Derivative
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Context.{u}) (s : ℂ) (A B : VertexOperator ℂ K.V) (N d : ℕ),
    delta^[N] (signedComm s A B) = 0 →
      R.readout () K (delta^[N + d] (signedComm s (dividedDerivative d A) B))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K : Context.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
  exact h K 0 0 0 0 0 (by ext; simp [signedComm])
def family : Registration arena (type_of% @signedDerivative_locality.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h K
      exact h
    · intro h V hGroup hScalars
      exact h ⟨V, hGroup, hScalars⟩
  variation := ⟨(fun K => signedDerivative_locality), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signedDerivative_locality.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.Derivative.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => d = 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Derivative

end Reg.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality
