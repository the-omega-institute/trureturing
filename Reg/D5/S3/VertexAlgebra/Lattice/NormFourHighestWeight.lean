import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourHighestWeight

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourHighestWeight

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open Lattice.NormFourVirasoroVector Lattice.NormFourHighestWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- The realization retains the full lattice domain and actual mode action.
Whole-family variation, sensitivity, observational dependence, lawful readout
and source selection remain unproved; this is not a Contract.Registration.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22237 -/
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
    (s : ℂ) (hs : s ^ 2 = 1) (h : ℂ) (w : Carrier D),
    w ≠ 0 →
    let p : Params := ⟨D, a, ha, s, hs⟩
    r.readout () p (0, w) = h • w →
    (∀ m : ℤ, 0 < m → r.readout () p (m, w) = 0) →
    h = 0 ∨ h = (1 / 16 : ℂ) ∨ h = (1 / 2 : ℂ)

theorem source_bridge : (type_of% (@highest_weight_values)) ↔ law actual := Iff.rfl

theorem source_actual : law actual := source_bridge.mp (@highest_weight_values)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourHighestWeight
