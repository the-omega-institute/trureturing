import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeAbsoluteZeroFullCohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeMatterGhostCoupling
open LatticeOriginalAbsoluteZeroCohomology LatticeAbsoluteZeroFullCohomology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- Exact source-family reconstruction attempts. These compiled bridges do not
assert declared_validated. Lawful readout selection, whole-family variation,
sensitivity, observational dependence and sourceSelection remain unfinished;
there is no placeholder Contract.Registration or claimed certificate. -/
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeAbsoluteZeroFullCohomology

structure Params where
  D : LatticeData
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ
  h26 : D.rank = 26
  hHG : H * gramComplex D = 1
  hGH : gramComplex D * H = 1

namespace OriginalChain
abbrev signature : Signature where
  Params := Params
  State p := Unit
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℂ (State p.D)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p z => if role then LatticeBRST.totalCharge p.D p.H * rho p.D
    else rho p.D * LatticeBRST.totalCharge p.D p.H) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1),
    r.readout false ⟨D,H,h26,hHG,hGH⟩ () = r.readout true ⟨D,H,h26,hHG,hGH⟩ ()

theorem source_bridge : (type_of% (@rho_chain)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@rho_chain)
end OriginalChain

namespace AmbientPrimitive
abbrev signature : Signature where
  Params := Params
  State p := E0 p.D p.H × State p.D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := E0 p.D p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p z => if role then z.1 else
    Q0 p.D p.H p.hHG p.hGH (retractState p.D p.H p.hHG p.hGH z.2)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : E0 D H) (y : State D)
    (hy : LatticeBRST.totalCharge D H y = (x : State D)),
    r.readout false ⟨D,H,h26,hHG,hGH⟩ (x,y) =
      r.readout true ⟨D,H,h26,hHG,hGH⟩ (x,y)

theorem source_bridge : (type_of% (@ambient_primitive)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@ambient_primitive)
end AmbientPrimitive

namespace AmbientRange
abbrev signature : Signature where
  Params := Params
  State p := Unit
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule ℂ (E0 p.D p.H)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p z => if role then (LinearMap.range (LatticeBRST.totalCharge p.D p.H)).comap
      (E0 p.D p.H).subtype else LinearMap.range (Q0 p.D p.H p.hHG p.hGH)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1),
    r.readout false ⟨D,H,h26,hHG,hGH⟩ () = r.readout true ⟨D,H,h26,hHG,hGH⟩ ()

theorem source_bridge : (type_of% (@range_Q0_eq_comap)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@range_Q0_eq_comap)
end AmbientRange

namespace QuotientSplit
abbrev signature : Signature where
  Params := Params
  State p := Cohomology p.D p.H p.hHG p.hGH
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Cohomology p.D p.H p.hHG p.hGH
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p z => if role then z else retraction p.D p.H p.h26 p.hHG p.hGH
      (inclusion p.D p.H p.h26 p.hHG p.hGH z)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (c : Cohomology D H hHG hGH),
    r.readout false ⟨D,H,h26,hHG,hGH⟩ c = r.readout true ⟨D,H,h26,hHG,hGH⟩ c

theorem source_bridge : (type_of% (@retraction_inclusion)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@retraction_inclusion)
end QuotientSplit

namespace FullFamily
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ =>
    Function.LeftInverse (fullCoordinates p.D p.H p.h26 p.hHG p.hGH)
      (fullClass p.D p.H p.h26 p.hHG p.hGH) ∧
    LinearIndependent ℂ (fullClasses p.D p.H p.h26 p.hHG p.hGH) ∧
      Fintype.card (ClassIndex p.D) = 2 + 2 * p.D.rank ∧
      Fintype.card (ClassIndex p.D) = 54) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1),
    r.readout () ⟨D,H,h26,hHG,hGH⟩ ()

theorem source_bridge : (type_of% (@fullClasses_independent)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@fullClasses_independent)
end FullFamily

end Reg.D5.S3.VertexAlgebra.Lattice.LatticeAbsoluteZeroFullCohomology
