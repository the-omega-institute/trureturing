import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra

set_option autoImplicit false

open private product
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra
open private vacuum_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open Lattice.NormFourVirasoroVector Lattice.NormFourVacuumIrreducible
open Lattice.NormFourVacuumC2 Lattice.NormFourVacuumC2Algebra
open Lattice.NormFourVacuumC2Algebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- The source bridge retains the complete original lattice-parameter family
and the literal vacuum quotient. Whole-family variation, sensitivity,
actual observational dependence, lawful enrolled readout and source selection
remain unproved. This bridge is not a Contract.Registration.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22450 -/
structure Params where
  D : LatticeData
  a : Charge D
  ha : bilinear D a a = 4
  s : ℂ
  hs : s ^ 2 = 1

abbrev Q (p : Params) :=
  vacuumDescendants p.D p.a p.s ⧸
    (C2 p.D p.a p.s).comap (vacuumDescendants p.D p.a p.s).subtype

abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Q p →ₗ[ℂ] Q p →ₗ[ℂ] Q p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => quotientProduct p.D p.a p.ha p.s p.hs)
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    let S := vacuumDescendants D a s
    let C := (C2 D a s).comap S.subtype
    letI := quotientRing D a ha s hs
    letI := quotientAlgebra D a ha s hs
    (∀ u v : S, C.mkQ (product D a ha s hs u v) =
      r.readout () (⟨D,a,ha,s,hs⟩ : Params) () (C.mkQ u) (C.mkQ v)) ∧
      (1 : S ⧸ C) = C.mkQ ⟨vacuum D,vacuum_mem D a s⟩ ∧
      FiniteDimensional ℂ (S ⧸ C) ∧ Module.finrank ℂ (S ⧸ C) = 3

theorem source_bridge :
    (type_of% (@actual_vacuum_c2_algebra)) ↔ law actual := Iff.rfl

theorem source_actual : law actual :=
  source_bridge.mp (@actual_vacuum_c2_algebra)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra
