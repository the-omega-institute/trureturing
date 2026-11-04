import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourZhuFinite

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourZhuFinite

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open Lattice.NormFourVacuumIrreducible Lattice.NormFourZhuFinite
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- The original lattice family and literal O-space are retained.
Whole-family variation, sensitivity, actual observational dependence,
lawful enrolled readout and source selection remain unproved.
This source bridge is not a Contract.Registration.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22489 -/
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
  (fun _ p _ => zhuO p.D p.a p.s)
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    let S := vacuumDescendants D a s
    let W := r.readout () (⟨D,a,ha,s,hs⟩ : Params) ()
    let O := W.comap S.subtype
    W ≤ S ∧ FiniteDimensional ℂ (S ⧸ O) ∧ Module.finrank ℂ (S ⧸ O) ≤ 3

theorem source_bridge :
    (type_of% (@actual_zhu_quotient_finite)) ↔ law actual := Iff.rfl

theorem source_actual : law actual := source_bridge.mp (@actual_zhu_quotient_finite)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourZhuFinite
