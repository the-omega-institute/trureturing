import D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
/- Full-source law and equivalence attempts only. No Contract.Registration is
asserted: original occurrence selectors, exact compiled source reconstruction,
whole-family variation, fixed-other-readout sensitivity and actual observational
dependence remain to be supplied. A continuation of unknown cannot supply them. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator
open Real Filter
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace actual_mixed_denominator_expansions
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun r _ X => if r = 0 then U X else V X) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := Tendsto (fun X : ℝ => log X ^ 3 * ((W.readout 0) () X)) atTop (𝓝 (2 * log 2 ^ 2)) ∧
    Tendsto (fun X : ℝ => log X ^ 3 * ((W.readout 1) () X)) atTop
      (𝓝 (2 * log 2 * (log 3 - log 2))) ∧
    Tendsto (fun X : ℝ => log X ^ 4 *
      ((log 3 - log 2) * ((W.readout 0) () X) - log 2 * ((W.readout 1) () X))) atTop
      (𝓝 (3 * log 2 ^ 2 * log 3 * (log 3 - log 2)))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator.actual_mixed_denominator_expansions

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator.actual_mixed_denominator_expansions)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end actual_mixed_denominator_expansions

namespace eventual_actual_mixed_denominator
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun r _ X => if r = 0 then U X else V X) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∀ (beta C0 rho8 rho12 : ℝ) (barL : ℝ → ℝ) (M N : ℝ → ℕ)
    (hbeta : 37 / 50 ≤ beta) (hbeta' : beta < 3 / 4) (hC0 : 0 ≤ C0)
    (hrho8 : 0 < rho8) (hrho12 : 0 < rho12)
    (hclose : Tendsto (fun X => barL X - log X) atTop (𝓝 0))
    (hpaid8 : ∀ᶠ X : ℝ in atTop,
      rho8 * exp (((1 - beta) / 8 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤
        (M X : ℝ) + 1)
    (hpaid12 : ∀ᶠ X : ℝ in atTop,
      rho12 * exp (((1 - beta) / 12 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤
        (N X : ℝ) + 1),
    ∀ C : ℝ, 0 < C → C < 1 / (2 * log 2 ^ 2 * log 3) →
      ∀ᶠ X : ℝ in atTop, ∀ h u v : ℤ, 1 ≤ h →
        |(h : ℝ) * ((W.readout 0) () X) - u| ≤ C0 / ((M X : ℝ) + 1) →
        |(h : ℝ) * ((W.readout 1) () X) - v| ≤ C0 / ((N X : ℝ) + 1) →
        C * log X ^ 3 * log (log X) < (h : ℝ)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator.eventual_actual_mixed_denominator

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator.eventual_actual_mixed_denominator)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end eventual_actual_mixed_denominator

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffDenominator
