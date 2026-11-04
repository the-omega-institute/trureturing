import D5.S3.Arith.FactorialRatio.GridAntidiagonalTrafficBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology
open _root_.D5.S3.Arith.FactorialRatio.GridAntidiagonalTrafficBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FactorialRatio.GridAntidiagonalTrafficBound

/- Source-law component for the exposed logarithmic factorial envelope.
The state domain is the full natural numbers and the law retains the
positive-index hypothesis of the original theorem. No finite catalogue or
Contract.Registration is asserted; the four-slot audit remains unfinished
under the existing linked audit issue. -/

namespace log_factorial_upper_bound

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => fun m : ℕ => Real.log (m.factorial : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ} (hm : 0 < m),
    (V.readout () ()) m ≤ (m : ℝ) * Real.log m - m +
      Real.log m / 2 + Real.log (2 * Real.pi) / 2 + 1 / (12 * m)

private theorem actual_law : arena.Law actual := @log_factorial_upper_bound

private theorem sourceBridge :
    (type_of% (@log_factorial_upper_bound)) ↔ arena.Law actual := Iff.rfl

end log_factorial_upper_bound

end Reg.D5.S3.Arith.FactorialRatio.GridAntidiagonalTrafficBound
