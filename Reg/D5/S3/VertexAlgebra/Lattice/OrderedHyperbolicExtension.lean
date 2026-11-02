import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.OrderedHyperbolicExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeRealNullFrame OrderedHyperbolicExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- Exact original source-family reconstruction, with both charges, all four
integer axes and every finite rank, including rank zero. Four-slot registration
is unfinished: no lawful enrolled readout, whole-family intervention or role
sensitivity evidence is asserted. This is not declared_validated. -/
namespace Reg.D5.S3.VertexAlgebra.Lattice.OrderedHyperbolicExtension
namespace LowerCocycle
structure Params where
  D : LatticeData
abbrev signature : Signature where
  Params := Params
  State t := (Charge t.D × Charge t.D) × (ℤ × ℤ × ℤ × ℤ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ t v =>
    lowerCocycleExponent (extend t.D)
      (splice t.D v.1.1 v.2.1 v.2.2.1) (splice t.D v.1.2 v.2.2.2.1 v.2.2.2.2) =
        lowerCocycleExponent t.D v.1.1 v.1.2 + v.2.2.1 * v.2.2.2.1)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (a b : Charge D) (m n r' s : ℤ),
    r.readout () ⟨D⟩ ((a, b), (m, n, r', s))

theorem source_bridge : (type_of% (@lowerCocycleExponent_splice)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@lowerCocycleExponent_splice)
end LowerCocycle
end Reg.D5.S3.VertexAlgebra.Lattice.OrderedHyperbolicExtension
