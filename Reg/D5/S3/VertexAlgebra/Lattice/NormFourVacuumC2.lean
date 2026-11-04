import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open Lattice.NormFourVacuumIrreducible Lattice.NormFourVacuumC2
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- The source bridge retains the literal ambient C2 span and the quotient of
the same actual vacuum space throughout the lattice-parameter family.
Whole-family variation, sensitivity, actual observational dependence,
lawful enrolled readout and source selection remain unproved.
This bridge is not a Contract.Registration.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22367 -/
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
  Output _ p := Submodule ℂ (Carrier p.D)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => C2 p.D p.a p.s)
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D)
    (_ha : bilinear D a a = 4) (s : ℂ) (_hs : s ^ 2 = 1),
    let S := vacuumDescendants D a s
    let W := r.readout () (⟨D, a, _ha, s, _hs⟩ : Params) ()
    let C := W.comap S.subtype
    W ≤ S ∧ FiniteDimensional ℂ (S ⧸ C) ∧ Module.finrank ℂ (S ⧸ C) ≤ 3

theorem source_bridge :
    (type_of% (@actual_vacuum_c2_cofinite)) ↔ law actual := Iff.rfl

theorem source_actual : law actual :=
  source_bridge.mp (@actual_vacuum_c2_cofinite)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2
