import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Eigenstructure.DiagonalTensorEigenspace
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

set_option autoImplicit false

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Eigenstructure.DiagonalTensorEigenspace
open LeanInformationAudit
open scoped TensorProduct

noncomputable section
universe u v w z

namespace Reg.D5.S1.Eigenstructure.DiagonalTensorEigenspace

namespace CoeffAction

/-- Equality is observed in the original, arbitrary ground type. -/
abbrev signature : Signature where
  Params := Type z
  State T := T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := T → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{z}
  Law R := ∀ {K : Type u} {I : Type v} {M : Type w} {T : Type z}
    [Field K] [AddCommGroup M] [Module K M] [AddCommGroup T] [Module K T]
    (b : Module.Basis I K M) (A : Module.End K M)
    (a : I → K) (hA : ∀ i, A (b i) = a i • b i)
    (x : M ⊗[K] T) (i : I),
    R.readout () T
      (coeffEquiv b (TensorProduct.map A (LinearMap.id : Module.End K T) x) i)
      (a i • coeffEquiv b x i)

theorem source_bridge : (type_of% (@coeff_action.{u,v,w,z})) ↔ arena.{u,v,w,z}.Law actual := Iff.rfl

private theorem actual_law : arena.{u,v,w,z}.Law actual := @coeff_action.{u,v,w,z}

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  let K := ULift.{u} ℚ
  let M := ULift.{w} ℚ
  let φ : K →+* M := ULift.ringEquiv.symm.toRingHom.comp ULift.ringEquiv.toRingHom
  letI : Algebra K M := φ.toAlgebra
  let e : K ≃ₗ[K] M := {
    toFun := fun k => ⟨k.down⟩
    invFun := fun m => ⟨m.down⟩
    left_inv := by intro k; cases k; rfl
    right_inv := by intro m; cases m; rfl
    map_add' := by intro a b; rfl
    map_smul' := by intro a b; rfl }
  let b : Module.Basis PUnit.{v+1} K M := (Module.Basis.singleton PUnit K).map e
  intro h
  exact @h K PUnit.{v+1} M PUnit.{z+1} inferInstance inferInstance inferInstance
    inferInstance inferInstance b LinearMap.id (fun _ => 1) (by intro i; simp)
    0 PUnit.unit

private theorem dependence : ObservationalDependence signature.{z} actual := by
  intro i
  refine ⟨ULift.{z} ℚ, 0, 1, ?_⟩
  intro he
  have h : (1 : ULift.{z} ℚ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

def family : Registration arena.{u,v,w,z} (type_of% (@coeff_action.{u,v,w,z})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coeff_action.{u,v,w,z}) (Realization signature.{z}) Type Unit where
  unitName := `Reg.D5.S1.Eigenstructure.DiagonalTensorEigenspace.CoeffAction.unit
  realizationName := `Reg.D5.S1.Eigenstructure.DiagonalTensorEigenspace.CoeffAction.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.DiagonalTensorEigenspace
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoeffAction

namespace EigenSupported

abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p q => p ↔ q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} {I : Type v} {M : Type w} {T : Type z}
    [Field K] [AddCommGroup M] [Module K M] [AddCommGroup T] [Module K T]
    (b : Module.Basis I K M) (A : Module.End K M)
    (a : I → K) (hA : ∀ i, A (b i) = a i • b i)
    (mu : K) (x : M ⊗[K] T),
    R.readout () ()
      (TensorProduct.map A (LinearMap.id : Module.End K T) x = mu • x)
      (coeffEquiv b x ∈ Finsupp.supported T K {i : I | a i = mu})

theorem source_bridge : (type_of% (@eigen_iff_supported.{u,v,w,z})) ↔ arena.{u,v,w,z}.Law actual := Iff.rfl

private theorem actual_law : arena.{u,v,w,z}.Law actual := @eigen_iff_supported.{u,v,w,z}

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  exact @h (ULift.{u} ℚ) PEmpty.{v+1} PUnit.{w+1} PUnit.{z+1}
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (Module.Basis.empty PUnit) 0 (fun _ => 0) (by intro i; cases i) 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact h.mpr trivial

def family : Registration arena.{u,v,w,z} (type_of% (@eigen_iff_supported.{u,v,w,z})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eigen_iff_supported.{u,v,w,z}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Eigenstructure.DiagonalTensorEigenspace.EigenSupported.unit
  realizationName := `Reg.D5.S1.Eigenstructure.DiagonalTensorEigenspace.EigenSupported.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.DiagonalTensorEigenspace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EigenSupported
end Reg.D5.S1.Eigenstructure.DiagonalTensorEigenspace
