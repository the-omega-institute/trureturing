import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourTensorCommutantModes

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourTensorCommutantModes

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open Lattice.NormFourVacuumIrreducible Lattice.NormFourTensorEmbedding
open Lattice.NormFourTensorCommutantModes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped TensorProduct VertexOperator

/- The source bridge preserves arbitrary D,a,s, the literal tensor factors,
every commutant state and every integer coefficient. Whole-family intervention,
sensitivity, observational dependence, lawful enrolled readout and source
selection remain unproved; this evidence is not a Contract.Registration. -/
structure Params where
  D : LatticeData
  a : Charge D
  s : ℂ

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
  ∀ (D : LatticeData) (a : Charge D) (s : ℂ)
    (b : Lattice.NormFourCommutant.space D a s) (q : ℤ)
    (z : vacuumDescendants D a s ⊗[ℂ] Lattice.NormFourCommutant.space D a s),
    let F := r.readout () (⟨D, a, s⟩ : Params) ()
    F (TensorProduct.map LinearMap.id
      (((Lattice.NormFourCommutant.restrictedVertexAlgebra D a s).stateField b)[[q]]) z) =
      mu D b.val q (F z)

theorem source_bridge :
    (type_of% (@actual_commutant_mode_intertwining)) ↔ law actual := Iff.rfl

theorem source_actual : law actual := source_bridge.mp (@actual_commutant_mode_intertwining)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourTensorCommutantModes
