import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourTensorVertexAlgebra

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourTensorVertexAlgebra

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal Lattice.NormFourVacuumIrreducible
open Lattice.NormFourTensorEmbedding Lattice.NormFourTensorVertexAlgebra
open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped TensorProduct VertexOperator

/- The source bridge retains the full lattice, charge, norm and scalar
parameter telescope, both actual algebra values and every closure and embedding
clause. Whole-family intervention, sensitivity, observational dependence,
lawful enrolled readout and source selection remain unproved. This bridge is
not a Contract.Registration. -/
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
  Output _ p := StateFieldVertexAlgebra (LinearMap.range (tensorMap p.D p.a p.s)) ×
    StateFieldVertexAlgebra (vacuumDescendants p.D p.a p.s ⊗[ℂ]
      Lattice.NormFourCommutant.space p.D p.a p.s)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => (rangeVertexAlgebra p.D p.a p.ha p.s p.hs,
    tensorVertexAlgebra p.D p.a p.ha p.s p.hs)) (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    let S := vacuumDescendants D a s
    let C := Lattice.NormFourCommutant.space D a s
    let TensorState := S ⊗[ℂ] C
    let F := tensorMap D a s
    let R := LinearMap.range F
    let pair := r.readout () (⟨D, a, ha, s, hs⟩ : Params) ()
    let V_R := pair.1
    let V_T := pair.2
    Function.Injective F ∧
    vacuum D ∈ R ∧
    (∀ (u v : Carrier D), u ∈ R → v ∈ R → ∀ n : ℤ, mu D u n v ∈ R) ∧
    (∀ v : Carrier D, v ∈ R → translation D v ∈ R) ∧
    (V_R.vacuum : Carrier D) = vacuum D ∧
    (∀ (u v : R) (n : ℤ), (((V_R.stateField u)[[n]]) v : Carrier D) =
      mu D u.val n v.val) ∧
    (∀ v : R, (V_R.translation v : Carrier D) = translation D v.val) ∧
    V_T.vacuum = (Lattice.NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs).vacuum ⊗ₜ[ℂ]
      (Lattice.NormFourCommutant.restrictedVertexAlgebra D a s).vacuum ∧
    F V_T.vacuum = vacuum D ∧
    (∀ (u v : TensorState) (n : ℤ), F (((V_T.stateField u)[[n]]) v) =
      mu D (F u) n (F v)) ∧
    (∀ v : TensorState, F (V_T.translation v) = translation D (F v))

theorem source_bridge :
    (type_of% (@actual_tensor_vertex_algebra_embedding)) ↔ law actual := Iff.rfl

theorem source_actual : law actual :=
  source_bridge.mp (@actual_tensor_vertex_algebra_embedding)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourTensorVertexAlgebra
