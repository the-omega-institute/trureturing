import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
import Reg.Support.SingleDependentReadout

/-! The window mass law has an explicit Riemann hypothesis premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => primeTail) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := RiemannHypothesis →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 2 ≤ a → a ≤ b →
      |(∫ x in a..b, max (-V.readout () () x) 0 / Real.sqrt x) - 2 * Real.log (b / a)| ≤ C

private theorem actual_law : arena.Law actual := prime_tail_logarithmic_mass_of_rh

private theorem source_bridge :
    (type_of% @prime_tail_logarithmic_mass_of_rh) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law_implies_rh (V : Realization signature) (hv : ¬ arena.Law V) :
    RiemannHypothesis := by
  by_contra h
  exact hv (fun hrh => (h hrh).elim)

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
