import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeLightConeCoordinates
open LatticeMatterGhostCoupling LatticeBRST
open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction
open LatticeBRSTModeFiltration LatticeBRSTFullOriginalRaising
open _root_.D5.S3.HomologicalAlgebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression

structure Parameters where
  D : LatticeData
  F : NullFrame D
  t : ℕ
  B : Module.Basis (Fin t) ℂ F.K
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ
  hHG : H * gramComplex D = 1
  hGH : gramComplex D * H = 1

abbrev signature : Signature where
  Params := Parameters
  State x := LatticeQuartetContraction.State x.D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ x := LatticeQuartetContraction.State x.D
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ x v => LatticeBRST.totalCharge x.D x.H v) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (F : NullFrame D) (t : ℕ)
    (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
     (v : LatticeQuartetContraction.State D),
    P0 F B (r.readout () ⟨D, F, t, B, H, hHG, hGH⟩ (P0 F B v)) =
      (P0 F B * ghostC D 0 * (matterMode D H 0 + ghostVirasoro D 0) * P0 F B) v

theorem source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression.original_Q_ground_compression)) ↔ arena.Law actual := by
  constructor
  · intro source D F t B H hHG hGH v
    exact LinearMap.congr_fun (source F B H hHG hGH) v
  · intro law D F t B H hHG hGH
    apply LinearMap.ext
    intro v
    exact law D F t B H hHG hGH v

end Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression
