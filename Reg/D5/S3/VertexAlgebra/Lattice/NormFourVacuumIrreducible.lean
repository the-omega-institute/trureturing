import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open Lattice.NormFourVacuumIrreducible
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- The realization uses the actual restricted action on the entire cyclic
vacuum representation. Whole-family variation, sensitivity, observational
dependence, lawful readout and source selection remain unproved; this is not
a Contract.Registration.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22298 -/
structure Params where
  D : LatticeData
  a : Charge D
  ha : bilinear D a a = 4
  s : ℂ
  hs : s ^ 2 = 1

abbrev signature : Signature where
  Params := Params
  State p := ℤ × vacuumDescendants p.D p.a p.s
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := vacuumDescendants p.D p.a p.s
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => restrictedMode p.D p.a p.ha p.s p.hs x.1 x.2)
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D) (ha : bilinear D a a = 4)
    (s : ℂ) (hs : s ^ 2 = 1)
    (U : Submodule ℂ (vacuumDescendants D a s)),
    let p : Params := ⟨D, a, ha, s, hs⟩
    (∀ (m : ℤ) (v : vacuumDescendants D a s),
      v ∈ U → r.readout () p (m, v) ∈ U) →
    U = ⊥ ∨ U = ⊤

theorem source_bridge :
    (type_of% (@vacuum_descendants_irreducible)) ↔ law actual := Iff.rfl

theorem source_actual : law actual := source_bridge.mp (@vacuum_descendants_irreducible)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
