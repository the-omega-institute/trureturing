import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFourCurrentTrace

namespace Reg.D5.S3.VertexAlgebra.LatticeFourCurrentTrace

structure Params where
  D : LatticeData
  positive : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  i : Four → Fin D.rank

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun _ => Four → ℕ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p n => actualFourCurrentCycleTrace p.D p.positive p.i n)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ),
    a.readout () ⟨D, hD, i⟩ n = boundedFourCurrentCoefficient D hD i n

end Reg.D5.S3.VertexAlgebra.LatticeFourCurrentTrace
