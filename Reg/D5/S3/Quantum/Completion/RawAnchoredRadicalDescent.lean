import Reg.Support.DependentFamily
import D5.S3.Quantum.Completion.RawAnchoredRadicalDescent

/-! The original comparison family for the source reconstruction problem. -/

namespace Reg.D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

/-- Every operand of the original source telescope, before any RawBalance premise. -/
structure Parameters where
  Carrier : Type u
  magma : MulOneClass Carrier
  marker : Carrier → Carrier
  comparison : Carrier → Carrier → ℝ

/-- Observations are actual ordered comparisons on the original carrier. -/
def comparisonSignature : Signature where
  Params := Parameters.{u}
  State p := p.Carrier × p.Carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def comparisonReadout : Realization comparisonSignature.{u} :=
  realize comparisonSignature (fun _ p x => p.comparison x.1 x.2)
    (fun e => nomatch e)

end Reg.D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
