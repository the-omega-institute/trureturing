import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose

/-! Exact-telescope dependent-family registration of the original scalar
insertion theorem. Equality is the observed complex scalar readout; no finite
parameter catalog replaces the arbitrary lattice, form, fields or label type. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open scoped BigOperators VertexOperator
namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open FieldNormalProduct
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.SourceBPZ
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

private def zeroLattice : LatticeData where
  rank := 1
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact ⟨0, rfl⟩

def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (p : ℕ) (F : VertexOperator ℂ (Carrier D))
    {σ : Type u} (S : Finset σ) (G : σ → VertexOperator ℂ (Carrier D))
    (weight : σ → ℂ) (K : σ → ℤ) (κ : ℂ)
    (htail : ∀ t x y, B ((F[[t]]) x) y =
      ∑ a ∈ S, weight a * B x (((G a)[[K a - t]]) y))
    (hzero : ∀ a ∈ S, ∀ t x, neutralMode D i 0 (((G a)[[t]]) x) =
      ((G a)[[t]]) (neutralMode D i 0 x) + κ • ((G a)[[t]]) x)
    (m : ℤ) (u v : Carrier D),
    R.readout () ()
      (B (((insertion D i p F)[[m]]) u) v)
      ((-1 : ℂ)^(p+1) * ∑ a ∈ S, weight a *
        ((∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℂ) *
          B u (((insertion D i s (G a))[[K a+p+s+2-m]]) v)) +
          κ * B u (((G a)[[K a+p+1-m]]) v)))

private theorem source_bridge :
    (type_of% (@consumed_normal_product_form.{u})) ↔ arena.{u}.Law complexEqual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h zeroLattice 0 ⟨0, by decide⟩ (by intros; simp) 0 0
    (∅ : Finset (ULift.{u} Unit)) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0
    (by intros; simp) (by simp) 0 0 0

def family : Registration arena.{u} (type_of% (@consumed_normal_product_form.{u})) where
  actual := complexEqual
  bridge := source_bridge
  variation := ⟨source_bridge.mp consumed_normal_product_form, complexFalse, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    complexEqual complexFalse rejected_law
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@consumed_normal_product_form.{u})
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.consumed_normal_product_form "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace ExposedSupport
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ p => p) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro h
  exact Eq.mp h True.intro

namespace DerivativeMode
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (i : Fin D.rank) (p : ℕ) (m : ℤ),
    R.readout () () (((dividedDerivative p (neutralField D i))[[m]]) =
      coefficient p (m-p) • neutralMode D i (m-p))

private theorem source_bridge : (type_of% (@derivative_mode)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  exact h zeroLattice ⟨0, by decide⟩ 0 0

def family : Registration arena (type_of% (@derivative_mode)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp derivative_mode, bad, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@derivative_mode)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.derivative_mode "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.ExposedSupport.DerivativeMode.family
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
  escapeFrom := some Prop
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end DerivativeMode

namespace CoefficientZeroBand
def arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) (k : ℤ) (hk : -(p : ℤ) ≤ k) (hn : k < 0),
    R.readout () () (coefficient p k = 0)

private theorem source_bridge : (type_of% (@coefficient_zero_band)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  exact h 1 (-1) (by omega) (by omega)

def family : Registration arena (type_of% (@coefficient_zero_band)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp coefficient_zero_band, bad, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@coefficient_zero_band)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.coefficient_zero_band "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.ExposedSupport.CoefficientZeroBand.family
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
  escapeFrom := some Prop
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end CoefficientZeroBand

namespace ForwardFinite
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (L F : VertexOperator ℂ (Carrier D))
    (m : ℤ) (u : Carrier D),
    R.readout () () (Function.HasFiniteSupport
      (fun t : ℕ => (L[[-(t : ℤ)-1]]) ((F[[m+t]]) u)))

private theorem source_bridge : (type_of% (@forward_finite)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  exact h zeroLattice 0 0 0 0

def family : Registration arena (type_of% (@forward_finite)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp forward_finite, bad, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@forward_finite)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.forward_finite "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.ExposedSupport.ForwardFinite.family
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
  escapeFrom := some Prop
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end ForwardFinite

namespace ReverseFinite
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (L F : VertexOperator ℂ (Carrier D))
    (m : ℤ) (u : Carrier D),
    R.readout () () (Function.HasFiniteSupport
      (fun t : ℕ => (F[[m-t-1]]) ((L[[t]]) u)))

private theorem source_bridge : (type_of% (@reverse_finite)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  exact h zeroLattice 0 0 0 0

def family : Registration arena (type_of% (@reverse_finite)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp reverse_finite, bad, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@reverse_finite)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.reverse_finite "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose.ExposedSupport.ReverseFinite.family
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
  escapeFrom := some Prop
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end ReverseFinite
end ExposedSupport

end Reg.D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose
