import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeOriginalAbsoluteZeroCohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeMatterGhostCoupling
open LatticeZeroMomentumBRST LatticeOriginalAbsoluteZeroCohomology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- These exact source-family bridges are unfinished registration attempts.
They do not assert declared_validated. Whole-family variation, sensitivity,
observational dependence, lawful readout binding and sourceSelection remain
required for a four-slot Contract.Registration. No placeholder is a certificate. -/
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeOriginalAbsoluteZeroCohomology

structure Params where
  D : LatticeData
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ
  hHG : H * gramComplex D = 1
  hGH : gramComplex D * H = 1

namespace OriginalAction
abbrev signature : Signature where
  Params := Params
  State p := Coordinates p.D × Coordinates p.D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := State p.D
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p z => if role then
    Psi p.D p.H p.hHG p.hGH (0,(0,2*z.2.1))
    else LatticeBRST.totalCharge p.D p.H
      (Psi p.D p.H p.hHG p.hGH z.1 + ghostC p.D 0 (Psi p.D p.H p.hHG p.hGH z.2)))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (z w : Coordinates D),
    r.readout false ⟨D,H,hHG,hGH⟩ (z,w) = r.readout true ⟨D,H,hHG,hGH⟩ (z,w)

theorem source_bridge : (type_of% (@Q_representative)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@Q_representative)
end OriginalAction

namespace NativeDimension
abbrev signature : Signature where
  Params := Params
  State _ := ℤ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p q => if role then
    if q = 0 then 1 else if q = 1 then p.D.rank else
      if q = 2 then p.D.rank else if q = 3 then 1 else 0
    else Module.finrank ℂ (GradedCohomology p.D p.H p.hHG p.hGH q))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (q : ℤ),
    r.readout false ⟨D,H,hHG,hGH⟩ q = r.readout true ⟨D,H,hHG,hGH⟩ q

theorem source_bridge : (type_of% (@native_finrank)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@native_finrank)
end NativeDimension

end Reg.D5.S3.VertexAlgebra.Lattice.LatticeOriginalAbsoluteZeroCohomology
