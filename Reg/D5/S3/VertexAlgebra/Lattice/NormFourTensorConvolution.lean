import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourTensorConvolution

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourTensorConvolution

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open Lattice.NormFourVacuumIrreducible Lattice.NormFourTensorConvolution
open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators TensorProduct VertexOperator

/- The actual algebra readout and source bridges retain the entire dependent
parameter telescope, all factor states, every integer, finite support and the
global translation operator. Whole-family intervention, sensitivity, actual
observational dependence, lawful enrolled readout and source selection remain
unproved. This source reconstruction is not a Contract.Registration. -/
structure Params where
  D : LatticeData
  a : Charge D
  ha : bilinear D a a = 4
  s : ℂ
  hs : s ^ 2 = 1

abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := StateFieldVertexAlgebra (vacuumDescendants p.D p.a p.s ⊗[ℂ]
    Lattice.NormFourCommutant.space p.D p.a p.s)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => Lattice.NormFourTensorVertexAlgebra.tensorVertexAlgebra p.D p.a p.ha p.s p.hs)
  (fun e => nomatch e)

def convolutionLaw (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u v : vacuumDescendants D a s) (b c : Lattice.NormFourCommutant.space D a s)
    (n : ℤ),
    let V_S := Lattice.NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs
    let V_C := Lattice.NormFourCommutant.restrictedVertexAlgebra D a s
    let V_T := r.readout () (⟨D, a, ha, s, hs⟩ : Params) ()
    let f : ℤ → vacuumDescendants D a s ⊗[ℂ] Lattice.NormFourCommutant.space D a s :=
      fun k => (((V_S.stateField u)[[k]]) v) ⊗ₜ[ℂ]
        (((V_C.stateField b)[[n - 1 - k]]) c)
    Function.HasFiniteSupport f ∧
      (((V_T.stateField (u ⊗ₜ[ℂ] b))[[n]]) (v ⊗ₜ[ℂ] c)) = ∑ᶠ k : ℤ, f k

def translationLaw (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    let S := vacuumDescendants D a s
    let C := Lattice.NormFourCommutant.space D a s
    let V_S := Lattice.NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs
    let V_C := Lattice.NormFourCommutant.restrictedVertexAlgebra D a s
    let V_T := r.readout () (⟨D, a, ha, s, hs⟩ : Params) ()
    V_T.translation = TensorProduct.map V_S.translation (LinearMap.id : C →ₗ[ℂ] C) +
      TensorProduct.map (LinearMap.id : S →ₗ[ℂ] S) V_C.translation ∧
    ∀ (u : S) (b : C), V_T.translation (u ⊗ₜ[ℂ] b) =
      (V_S.translation u) ⊗ₜ[ℂ] b + u ⊗ₜ[ℂ] (V_C.translation b)

theorem source_convolution_bridge :
    (type_of% (@actual_tensor_field_convolution)) ↔ convolutionLaw actual := Iff.rfl

theorem source_convolution_actual : convolutionLaw actual :=
  source_convolution_bridge.mp (@actual_tensor_field_convolution)

theorem source_translation_bridge :
    (type_of% (@actual_tensor_translation_split)) ↔ translationLaw actual := Iff.rfl

theorem source_translation_actual : translationLaw actual :=
  source_translation_bridge.mp (@actual_tensor_translation_split)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourTensorConvolution
