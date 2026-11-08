import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeOriginalTypeIINullState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
open SourceBPZ.OriginalMatterHermitian LatticeOriginalTypeIINullState
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- Faithful source-family reconstruction only. This is an unfinished four-slot
registration attempt, not Contract.Registration or declared_validated evidence.
No lawful enrolled readout, family variation, role sensitivity or observational
 dependence is asserted. All original hypotheses and all finite charges remain. -/
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeOriginalTypeIINullState
structure Params where
  D : LatticeData
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ

abbrev signature : Signature where
  Params := Params
  State t := Charge t.D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ t p =>
    sugawaraMode t.D t.H 0 (typeII t.D t.H p) = typeII t.D t.H p ∧
    (∀ n : ℤ, 0 < n → sugawaraMode t.D t.H n (typeII t.D t.H p) = 0) ∧
    (∀ w : Carrier t.D, (∀ n : ℤ, 0 < n → sugawaraMode t.D t.H n w = 0) →
      Hm (typeII t.D t.H p) w = 0) ∧
    typeII t.D t.H p ≠ 0 ∧
    (∀ u : Carrier t.D, sugawaraMode t.D t.H 1 u = 0 →
      translation t.D u ≠ typeII t.D t.H p) ∧
    typeII t.D t.H p ∉ (translation t.D) ''
      {u : Carrier t.D | sugawaraMode t.D t.H 0 u = 0 ∧
        ∀ n : ℤ, 0 < n → sugawaraMode t.D t.H n u = 0})
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    H * gramComplex D = 1 → gramComplex D * H = 1 → D.rank = 26 →
    ∀ p : Charge D, bilinear D p p = -2 → r.readout () ⟨D,H⟩ p

theorem source_bridge : (type_of% (@original_typeII_null_obstruction)) ↔
    arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual :=
  source_bridge.mp (@original_typeII_null_obstruction)
end Reg.D5.S3.VertexAlgebra.Lattice.LatticeOriginalTypeIINullState
