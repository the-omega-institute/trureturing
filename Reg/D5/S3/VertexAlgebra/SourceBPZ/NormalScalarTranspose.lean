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
      ∑ a ∈ S, weight a * B x (((G a)[[K a-t]]) y))
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
end Reg.D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose
