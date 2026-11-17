import D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
import Reg.Support.FactorialFockMetric

set_option autoImplicit false
universe u v
noncomputable section
open scoped Matrix BigOperators
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra
open D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric

namespace AffineTransport
open _root_.D5.S3.VertexAlgebra.TwistedGround
open MvPolynomial OriginalChargedRowSource
open scoped BigOperators

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    {J : Type v} [Fintype J] [DecidableEq J]
    (U : Matrix I J ℂ) (A : Matrix J J ℂ) (mu : J → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N),
    r.readout () ()
      (∑ e ∈ (Finsupp.finite_of_degree_le (σ := J) N).toFinset,
        affineCoefficient A mu e * (linearSubstitution U (monomial e 1)).coeff d)
      (affineCoefficient (transportCovariance U A) (transportMean U mu) d)

theorem sourceBridge : (type_of% (@affineCoefficient_linear_substitution.{u,v})) ↔
    arena.{u,v}.Law complexEqual := Iff.rfl

private theorem actualLaw : arena.{u,v}.Law complexEqual := @affineCoefficient_linear_substitution.{u,v}

private theorem rejectedLaw : ¬ arena.{u,v}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} (Fin 0)) inferInstance inferInstance
    (ULift.{v} (Fin 0)) inferInstance inferInstance 0 0 0 (by intros; rfl) 0 0 (by simp)

def family : Registration arena.{u,v} (type_of% (@affineCoefficient_linear_substitution.{u,v})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affineCoefficient_linear_substitution.{u,v}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.AffineTransport.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.AffineTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AffineTransport

namespace TaylorCut
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
open MvPolynomial

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (mu : I → ℂ) (d : I →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N),
    r.readout () () (taylorCoefficient A mu d) ((expCut (affineExponent A mu) N).coeff d)

theorem sourceBridge : (type_of% (@taylorCoefficient_cut.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl

private theorem actualLaw : arena.{u}.Law complexEqual := @taylorCoefficient_cut.{u}

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} (Fin 0)) inferInstance inferInstance 0 0 0 0 (by simp)

def family : Registration arena.{u} (type_of% (@taylorCoefficient_cut.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@taylorCoefficient_cut.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.TaylorCut.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.TaylorCut.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TaylorCut

namespace NativeTaylor
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
open MvPolynomial

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (mu : I → ℂ) (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ),
    r.readout () () (affineCoefficient A mu d) (taylorCoefficient A mu d)

theorem sourceBridge : (type_of% (@native_affine_eq_taylor.{u})) ↔
    arena.{u}.Law complexEqual := Iff.rfl

private theorem actualLaw : arena.{u}.Law complexEqual := @native_affine_eq_taylor.{u}

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} (Fin 0)) inferInstance inferInstance 0 0 (by intros; rfl) 0

def family : Registration arena.{u} (type_of% (@native_affine_eq_taylor.{u})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_affine_eq_taylor.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.NativeTaylor.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.NativeTaylor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NativeTaylor

namespace ExternalCoefficient
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
open MvPolynomial

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    {J : Type v} [Fintype J] [DecidableEq J]
    (p : MvPolynomial (I ⊕ J) ℂ) (h : J →₀ ℕ) (d : I →₀ ℕ),
    r.readout () () ((externalSection p h).coeff d) (p.coeff (d.sumElim h))

theorem sourceBridge : (type_of% (@externalSection_coeff.{u,v})) ↔
    arena.{u,v}.Law complexEqual := Iff.rfl

private theorem actualLaw : arena.{u,v}.Law complexEqual := @externalSection_coeff.{u,v}

private theorem rejectedLaw : ¬ arena.{u,v}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} (Fin 0)) inferInstance inferInstance
    (ULift.{v} (Fin 0)) inferInstance inferInstance 0 0 0

def family : Registration arena.{u,v} (type_of% (@externalSection_coeff.{u,v})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalSection_coeff.{u,v}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.ExternalCoefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.ExternalCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExternalCoefficient

namespace ExternalNative
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
open MvPolynomial

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    {J : Type v} [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (A : Matrix (I ⊕ J) (I ⊕ J) ℂ) (mu : I ⊕ J → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (h : J →₀ ℕ)
    (N : ℕ) (hN : (d.sumElim h).degree ≤ N),
    r.readout () ()
      ((linearSubstitution U (externalSection (expCut (affineExponent A mu) N) h)).coeff d)
      (affineCoefficient (transportCovariance (sourceBlock U) A)
        (transportMean (sourceBlock U) mu) (d.sumElim h))

theorem sourceBridge : (type_of% (@externalSection_native.{u,v})) ↔
    arena.{u,v}.Law complexEqual := Iff.rfl

private theorem actualLaw : arena.{u,v}.Law complexEqual := @externalSection_native.{u,v}

private theorem rejectedLaw : ¬ arena.{u,v}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} (Fin 0)) inferInstance inferInstance
    (ULift.{v} (Fin 0)) inferInstance inferInstance 0 0 0 (by intros; rfl) 0 0 0 (by simp)

def family : Registration arena.{u,v} (type_of% (@externalSection_native.{u,v})) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalSection_native.{u,v}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.ExternalNative.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport.ExternalNative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExternalNative

end Reg.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
