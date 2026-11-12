import D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/- These are full-telescope typed law and source-equivalence attempts.
Actual arithmetic realizations, actual laws and definitional source bridges
are provided. Four-slot registration remains unfinished: lawful enrolled-template
application, compiler occurrence/sourceSelection binding, whole-family intervention
and realizability, fixed-anchor sensitivity and actual observational dependence
are absent. No continuation .unknown fills any missing preceding obligation. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.CurvatureConsumed
open Real Filter Finset
open scoped Topology
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
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

namespace actual_root_equation
/- Exact source law only; four-slot registration remains unfinished. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.F x.1 x.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∀ {j : ℕ} (hj : 2 ≤ j),
    ∀ᶠ X : ℝ in atTop, 0 < d j X ∧ 2 < cutoff j (referencePrice X) ∧
      ((W.readout ()) () (log X, d j X)) = log (j : ℝ) + η j X

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.actual_root_equation

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.actual_root_equation)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end actual_root_equation

namespace scaled_root_error
/- Exact source law only; four-slot registration remains unfinished. -/
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
  realize signature (fun _ j X => _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.η j X) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∀ {j : ℕ} (hj : 2 ≤ j) (n : ℕ),
    Tendsto (fun X : ℝ => log X ^ n * ((W.readout ()) j X)) atTop (𝓝 0)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.scaled_root_error

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.scaled_root_error)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end scaled_root_error

namespace F_secant
/- Exact source law only; four-slot registration remains unfinished. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.F x.1 x.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∀ {L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b),
    ∃ q : ℝ, 1 ≤ q ∧ q ≤ 1 + 1 / L ∧ ((W.readout ()) () (L, b)) - ((W.readout ()) () (L, a)) = (b - a) * q

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.F_secant

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.F_secant)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end F_secant

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature.CurvatureConsumed
