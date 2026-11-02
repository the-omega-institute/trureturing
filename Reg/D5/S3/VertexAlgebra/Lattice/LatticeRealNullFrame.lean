import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeLightConeCoordinates LatticeRealNullFrame
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- Exact original source-family bridges only. No enrolled readout, lawful
whole-family intervention, role sensitivity or source-selection evidence is
asserted here. Native compilation of these bridges is not declared_validated.
The 66 public-theorem audits remain unresolved, with no Contract registrations
or declared_validated audits. The delivery links the exact registration issue. -/
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame
namespace SignatureGeometry
structure Params where
  D : LatticeData
  hrank : 2 ≤ D.rank
  hneg : sigNeg (Q_R D) = 1
  hpos : sigPos (Q_R D) = D.rank - 1

def geometry (D : LatticeData) (p : Charge D) : Prop :=
∃ P : PositivePlane D,
      g_R D P.ePlus P.ePlus = 0 ∧
      g_R D P.eMinus P.eMinus = 0 ∧
      g_R D P.ePlus P.eMinus = 1 ∧
      g_R D P.ePlus (realCharge p) ≠ 0 ∧
      P.complexFrame.pPlus p ≠ 0 ∧
      P.projection (realCharge p) = 0 ∧
      P.complexFrame.projK (chargeVector p) = 0 ∧
      Module.finrank ℝ P.K_R = D.rank - 2 ∧
      Module.finrank ℂ P.complexFrame.K = D.rank - 2 ∧
      ((Q_R D).restrict P.K_R).PosDef ∧
      (∀ i j : Fin (D.rank - 2),
        g D (P.complexBasis i : E D) (P.complexBasis j : E D) =
          if i = j then 1 else 0) ∧
      (∀ j : Fin (D.rank - 2),
        conjugateVector (P.complexBasis j : E D) = (P.complexBasis j : E D)) ∧
      (∀ z : P.complexFrame.K, z ≠ 0 →
        0 < (g D (conjugateVector (z : E D)) (z : E D)).re)

abbrev signature : Signature where
  Params := Params
  State t := {p : Charge t.D // p ≠ 0}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ t p => geometry t.D p.val) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hrank : 2 ≤ D.rank)
    (hneg : sigNeg (Q_R D) = 1) (hpos : sigPos (Q_R D) = D.rank - 1)
    (p : Charge D) (hp : p ≠ 0),
    r.readout () ⟨D, hrank, hneg, hpos⟩ ⟨p, hp⟩

theorem source_bridge : (type_of% (@exists_original_real_geometry)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@exists_original_real_geometry)
end SignatureGeometry

namespace ProjectionBridge
structure Params where
  D : LatticeData
  P : PositivePlane D
abbrev signature : Signature where
  Params := Params
  State t := E_R t.D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ t := E t.D
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role t v => if role then complexify t.D (t.P.projection v : E_R t.D)
    else (t.P.complexFrame.projK (complexify t.D v) : E t.D))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (P : PositivePlane D) (v : E_R D),
    r.readout false ⟨D,P⟩ v = r.readout true ⟨D,P⟩ v

theorem source_bridge : (type_of% (@PositivePlane.complex_projection_bridge)) ↔
    arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual :=
  source_bridge.mp (@PositivePlane.complex_projection_bridge)
end ProjectionBridge

namespace PositiveRestriction
structure Params where
  D : LatticeData
  P : PositivePlane D
abbrev signature : Signature where
  Params := Params
  State t := t.P.K_R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ t k => Q_R t.D (k : E_R t.D)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (P : PositivePlane D) (k : P.K_R),
    k ≠ 0 → 0 < r.readout () ⟨D,P⟩ k

theorem source_bridge : (type_of% (@PositivePlane.positive_K_R)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@PositivePlane.positive_K_R)
end PositiveRestriction

namespace HermitianDiagonal
structure Params where
  D : LatticeData
  P : PositivePlane D
abbrev signature : Signature where
  Params := Params
  State t := t.P.complexFrame.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ t z => (g t.D (conjugateVector (z : E t.D)) (z : E t.D)).re)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (P : PositivePlane D) (z : P.complexFrame.K),
    z ≠ 0 → 0 < r.readout () ⟨D,P⟩ z

theorem source_bridge : (type_of% (@PositivePlane.hermitian_positive)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@PositivePlane.hermitian_positive)
end HermitianDiagonal
namespace RealHermitianDiagonal
abbrev signature : Signature where
  Params := LatticeData
  State D := E D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role D z => if role then ((Q_R D (realPart z) + Q_R D (imagPart z) : ℝ) : ℂ)
    else g D (conjugateVector z) z) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (z : E D), r.readout false D z = r.readout true D z

theorem source_bridge : (type_of% (@hermitian_diagonal)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@hermitian_diagonal)
end RealHermitianDiagonal

end Reg.D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame
