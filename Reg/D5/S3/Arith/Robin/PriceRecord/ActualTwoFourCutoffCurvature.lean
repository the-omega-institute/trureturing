import D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/- SOURCE ONLY. RegUNVALIDATED / UNCOMPILED_UNACCEPTED.
These are full-telescope typed ATTEMPTS, not registrations or validation.
Actual arithmetic realization, actual_law and definitional source_bridge are
provided. Compiled occurrence/sourceSelection binding, lawful enrollment,
rejected lawful families, whole-family intervention and realizability,
anchor/other-readout-fixed sensitivity, actual observational dependence and
axiom closure are UNKNOWN. No .unknown object closes a source proof gap. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.CurvatureConsumed
open Real Filter Finset
open scoped Topology
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace normalized_gain_bounds
/- RegUNVALIDATED. Readout: actual gain. Full dependent telescope below. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j u => gain j u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j : ℕ} (hj : 1 ≤ j) {u : ℝ} (hu : 2 ≤ u),
    1 - 1 / u ≤ ((V.readout ()) j u) * u ^ j ∧ ((V.readout ()) j u) * u ^ j ≤ 1 ∧
      -2 / u ≤ log (((V.readout ()) j u) * u ^ j) ∧ log (((V.readout ()) j u) * u ^ j) ≤ 0

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.normalized_gain_bounds

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.normalized_gain_bounds)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end normalized_gain_bounds

namespace actual_two_four_curvature_tendsto
/- RegUNVALIDATED. Readout: actual cutoff. Full dependent telescope below. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j u => cutoff j u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := Tendsto (fun X : ℝ => log X ^ 2 *
      ((4 * log (((V.readout ()) 4 (referencePrice X))) - log X) -
        2 * (2 * log (((V.readout ()) 2 (referencePrice X))) - log X)))
      atTop (𝓝 (log (2 : ℝ) ^ 2))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.actual_two_four_curvature_tendsto

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.actual_two_four_curvature_tendsto)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end actual_two_four_curvature_tendsto

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.CurvatureConsumed
