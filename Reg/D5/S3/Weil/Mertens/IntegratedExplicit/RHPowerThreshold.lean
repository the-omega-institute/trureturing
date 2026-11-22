import D5.S3.Weil.Mertens.IntegratedExplicit.RHPowerThreshold
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHPowerThreshold

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHPowerThreshold

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => U x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := RiemannHypothesis → ∀ θ : ℝ,
    Tendsto (fun x : ℝ => V.readout () () x / x ^ θ) atTop (𝓝 0) ↔ 1 / 2 < θ

private theorem actual_law : arena.Law actual := @u_div_rpow_tendsto_zero_iff

private theorem source_bridge :
    (type_of% @u_div_rpow_tendsto_zero_iff) ↔ arena.Law actual := Iff.rfl

/-- Rejecting a whole readout family for this conditional law entails RH. -/
private theorem rejected_law_implies_rh (V : Realization signature) (hv : ¬ arena.Law V) :
    RiemannHypothesis := by
  by_contra h
  exact hv (fun hrh => (h hrh).elim)

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHPowerThreshold
