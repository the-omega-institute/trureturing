import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetTransferTail

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

namespace Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetTransferTail

structure Parameters where
  D : LatticeData
  F : NullFrame D
  t : ℕ
  B : Module.Basis (Fin t) ℂ F.K
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ
  hHG : H * gramComplex D = 1
  hGH : gramComplex D * H = 1
  p : Charge D
  N : ℕ
  hN : 1 ≤ N

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
  (fun _ x v => ((LatticeBRST.totalCharge x.D x.H - d0 x.F x.p) *
      FinitePerturbation.inversePolynomial
        (h x.F x.B x.p * (LatticeBRST.totalCharge x.D x.H - d0 x.F x.p)) x.N) v) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (F : NullFrame D) (t : ℕ)
    (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (N : ℕ) (hN : 1 ≤ N) (v : LatticeQuartetContraction.State D),
    P0 F B (r.readout () ⟨D, F, t, B, H, hHG, hGH, p, N, hN⟩ ((P0 F B * chargeProject p) v)) =
      (P0 F B * (LatticeBRST.totalCharge D H - d0 F p) * P0 F B * chargeProject p) v

theorem source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetTransferTail.full_original_finite_transfer_compression)) ↔ arena.Law actual := by
  constructor
  · intro source D F t B H hHG hGH p N hN v
    exact LinearMap.congr_fun (source F B H hHG hGH p N hN) v
  · intro law D F t B H hHG hGH p N hN
    apply LinearMap.ext
    intro v
    exact law D F t B H hHG hGH p N hN v

end Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetTransferTail
