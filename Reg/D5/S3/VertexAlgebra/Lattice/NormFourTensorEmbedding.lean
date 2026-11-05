import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourTensorEmbedding

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourTensorEmbedding

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open Lattice.NormFourVacuumIrreducible Lattice.NormFourVacuumVertexAlgebra
open Lattice.NormFourTensorEmbedding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped TensorProduct VertexOperator

/- The exact source bridge preserves both full carriers, all S-states, all
integer coefficients and the actual vacuum line. Whole-family intervention,
sensitivity, observational dependence, lawful enrolled readout and source
selection remain unproved; this evidence is not a Contract.Registration. -/
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
  Output _ p := (vacuumDescendants p.D p.a p.s ⊗[ℂ]
    Lattice.NormFourCommutant.space p.D p.a p.s) →ₗ[ℂ] Carrier p.D
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => tensorMap p.D p.a p.s) (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    let S := vacuumDescendants D a s
    let C := Lattice.NormFourCommutant.space D a s
    let V := vertexAlgebra D a ha s hs
    let F := r.readout () (⟨D, a, ha, s, hs⟩ : Params) ()
    Function.Injective F ∧
    (∀ (u : S) (c : C), F (u ⊗ₜ[ℂ] c) = mu D c.val (-1) u.val) ∧
    (∀ (u : S) (p : ℤ) (z : S ⊗[ℂ] C),
      F (TensorProduct.map ((V.stateField u)[[p]]) LinearMap.id z) =
        mu D u.val p (F z)) ∧
    ∀ c : C, F (V.vacuum ⊗ₜ[ℂ] c) = c.val

theorem source_bridge :
    (type_of% (@actual_tensor_embedding)) ↔ law actual := Iff.rfl

theorem source_actual : law actual := source_bridge.mp (@actual_tensor_embedding)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourTensorEmbedding
