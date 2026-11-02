import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeLightConeCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
/- Faithful source-family attempts. The archived conditional assemblies did not supply
whole-family variation, role sensitivity, observational dependence or native
source-selection evidence. Their native report decoding failed with computed_type;
only the actual source bridges are retained. No declared_validated registration is claimed. -/
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
open _root_.D5.S3.VertexAlgebra.LatticeNullFrameExistence
namespace ChargeDetectedFrame
structure Params where
  D : LatticeData
  p : Charge D
abbrev signature : Signature where
  Params := Params
  State p := E p.D × E p.D
  Role := Fin 4
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p v => if role = 0 then g p.D v.1 v.1
    else if role = 1 then g p.D v.2 v.2
    else if role = 2 then g p.D v.1 v.2
    else g p.D v.1 (chargeVector p.p))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (_ : H * gramComplex D = 1) (_ : 2 ≤ D.rank) (p : Charge D) (_ : p ≠ 0),
    ∃ v : E D × E D,
      r.readout 0 ⟨D,p⟩ v = 0 ∧ r.readout 1 ⟨D,p⟩ v = 0 ∧
      r.readout 2 ⟨D,p⟩ v = 1 ∧ r.readout 3 ⟨D,p⟩ v ≠ 0

theorem source_bridge : (type_of% (@exists_nullFrame_pPlus_ne_zero)) ↔
    arena.Law actual := by
  constructor
  · intro h D H hHG hrank p hp
    obtain ⟨F,hF⟩ := h D H hHG hrank p hp
    exact ⟨(F.ePlus,F.eMinus), F.plus_null, F.minus_null, F.plus_minus, hF⟩
  · intro h D H hHG hrank p hp
    obtain ⟨⟨v,w⟩,hvv,hww,hvw,hvp⟩ := h D H hHG hrank p hp
    exact ⟨⟨v,w,hvv,hww,hvw⟩,hvp⟩

theorem source_actual : arena.Law actual :=
  source_bridge.mp (@exists_nullFrame_pPlus_ne_zero)

end ChargeDetectedFrame
end Reg.D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
