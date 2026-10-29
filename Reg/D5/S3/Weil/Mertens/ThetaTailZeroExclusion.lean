import D5.S3.Weil.Mertens.ThetaTailZeroExclusion
import Reg.Support.SingleDependentReadout

/-! The scalar actual observation and the complete original conditional law.

The actual-law proof and exact source bridge do not supply lawful variation,
sensitivity, or actual observational dependence. Four-slot registration remains
unfinished: https://github.com/the-omega-institute/trureturing/issues/23758.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.Mertens.ThetaTailZeroExclusion

open Set MeasureTheory Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.ActualThetaTailLaplace
open _root_.D5.S3.Weil.Mertens.ThetaTailZeroExclusion

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ u => f u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ {b C : ℝ}, 0 < b → b < 1 / 2 → 0 ≤ C →
      (∀ᶠ u : ℝ in atTop, R.readout () () u ≤ C * Real.exp (-b * u)) →
      ∀ ρ : ℂ, 1 - b < ρ.re → riemannZeta ρ ≠ 0

private theorem source_bridge :
    (type_of% (@actual_theta_tail_exponential_zero_exclusion)) ↔ arena.Law actual := by
  constructor
  · intro h b C hb hb2 hC hbound
    apply h hb hb2 hC
    simpa [actual, realize] using hbound
  · intro h b C hb hb2 hC hbound
    apply h hb hb2 hC
    simpa [actual, realize] using hbound

private theorem actual_law : arena.Law actual :=
  source_bridge.mp (@actual_theta_tail_exponential_zero_exclusion)

#print axioms source_bridge
#print axioms actual_law

end
end Reg.D5.S3.Weil.Mertens.ThetaTailZeroExclusion
