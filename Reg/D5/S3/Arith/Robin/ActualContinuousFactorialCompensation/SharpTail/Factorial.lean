import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Factorial
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology
open _root_.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Factorial

/- Source-law components for the enrolled DependentFamily.realize template.
The state domains below are infinite; no finite state catalogue is used.
Each law preserves its original telescope and literal arithmetic readout.
Full four-slot registration still requires whole-family variation and
sensitivity, actual observational dependence, and faithful source selectors
with current binding evidence. The residual continuation is unknown.
No Contract.Registration or declared_validated record is asserted. -/

namespace log_factorial_remainder

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
  realize signature (fun _ _ => fun n : ℕ => Real.log (n.factorial : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {n : ℕ} (hn : 0 < n),
    0 ≤ (V.readout () ()) n -
      ((n : ℝ) * Real.log n - n + Real.log n / 2 + L / 2) ∧
    (V.readout () ()) n -
      ((n : ℝ) * Real.log n - n + Real.log n / 2 + L / 2) ≤ 1 / (12 * n)

private theorem actual_law : arena.Law actual := @log_factorial_remainder

private theorem sourceBridge :
    (type_of% (@log_factorial_remainder)) ↔ arena.Law actual := Iff.rfl

end log_factorial_remainder

namespace eta_phase_bound

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => eta) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ} (hx : 1 ≤ x),
    |(V.readout () ()) x - ((1 / 2 - Int.fract x) * Real.log x + L / 2)| ≤ 4 / x

private theorem actual_law : arena.Law actual := @eta_phase_bound

private theorem sourceBridge :
    (type_of% (@eta_phase_bound)) ↔ arena.Law actual := Iff.rfl

end eta_phase_bound

end Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Factorial
