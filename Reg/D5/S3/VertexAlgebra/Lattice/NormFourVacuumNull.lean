import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open Lattice.NormFourVirasoroVector Lattice.NormFourVacuumNull
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- The realization retains the full original dependent domain and actual mode action.
Whole-family variation, role sensitivity, observational dependence, lawful readout
and source selection remain unproved; this is not a Contract.Registration.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22198 -/
structure Params where
  D : LatticeData
  a : Charge D
  ha : bilinear D a a = 4
  s : ℂ
  hs : s ^ 2 = 1

abbrev signature : Signature where
  Params := Params
  State p := ℤ × Carrier p.D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Carrier p.D
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => mode p.D p.a p.s x.1 x.2) (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D) (ha : bilinear D a a = 4)
    (s : ℂ) (hs : s ^ 2 = 1),
    let p : Params := ⟨D, a, ha, s, hs⟩
    let L := fun n v => r.readout () p (n, v)
    (64 : ℂ) • L (-2) (L (-2) (L (-2) (vacuum D))) +
      (93 : ℂ) • L (-3) (L (-3) (vacuum D)) -
      (264 : ℂ) • L (-4) (L (-2) (vacuum D)) -
      (108 : ℂ) • L (-6) (vacuum D) = 0

theorem source_bridge : (type_of% (@level_six_vacuum_null)) ↔ law actual := Iff.rfl

theorem source_actual : law actual := (source_bridge.mp (@level_six_vacuum_null))

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull
