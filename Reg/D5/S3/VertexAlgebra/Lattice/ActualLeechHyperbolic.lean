import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality ActualLeechHyperbolic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- Exact source-family reconstruction on every charge of the same actual Leech
witness. Four-slot registration remains unfinished. No lawful readout enrollment,
whole-family intervention, sensitivity or declared_validated record is asserted. -/
namespace Reg.D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
namespace ActualPairing
abbrev signature : Signature where
  Params := Unit
  State _ := Charge rank26Data × Charge rank26Data
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ v => (bilinear rank26Data v.1 v.2 : ℝ) =
    productPairing (productInclusion (coordinates v.1)) (productInclusion (coordinates v.2)))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (q q' : Charge rank26Data), r.readout () () (q, q')

theorem source_bridge : (type_of% (@actual_pairing)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@actual_pairing)
end ActualPairing
end Reg.D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
