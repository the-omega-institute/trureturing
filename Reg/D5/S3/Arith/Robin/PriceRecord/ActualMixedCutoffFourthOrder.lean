import D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
/- Exact full-telescope law and source-equivalence attempts. Four-slot audit is
unfinished: lawful enrolled-template application, compiler occurrence binding,
whole-family variation, sensitivity and observational dependence are absent.
No registration or declared_validated status is asserted. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
open Real Filter Finset
open scoped Topology
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace actual_mixed_curvature_tendsto
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
  realize signature (fun _ _ X => A X) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := Tendsto (fun X : ℝ => log X ^ 4 * ((V.readout ()) () X)) atTop (𝓝 kappa)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.actual_mixed_curvature_tendsto

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.actual_mixed_curvature_tendsto)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end actual_mixed_curvature_tendsto

namespace kappa_pos
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
  realize signature (fun _ _ x => log x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := 0 < 3 * ((V.readout ()) () 2) * ((V.readout ()) () 3) * ((V.readout ()) () (3 / 2))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.kappa_pos

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.kappa_pos)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end kappa_pos

namespace actual_mixed_curvature_lower
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
  realize signature (fun _ _ X => A X) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ᶠ X : ℝ in atTop,
    0 < log X ∧ kappa / (2 * log X ^ 4) ≤ ((V.readout ()) () X)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.actual_mixed_curvature_lower

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.actual_mixed_curvature_lower)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end actual_mixed_curvature_lower

namespace eventual_integer_determinant_positive
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun r _ X => if r = 0 then theta X else if r = 1 then U X else _root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.V X) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∀ (beta C0 rho3 rho8 rho12 : ℝ) (barL A3 : ℝ → ℝ) (M N : ℝ → ℕ)
    (hbeta : 37 / 50 ≤ beta) (hbeta' : beta < 3 / 4) (hC0 : 0 ≤ C0)
    (hrho3 : 0 < rho3) (hrho8 : 0 < rho8) (hrho12 : 0 < rho12)
    (hclose : Tendsto (fun X => barL X - log X) atTop (𝓝 0))
    (hpaid3 : ∀ᶠ X : ℝ in atTop,
      rho3 * exp (((1 - beta) / 3 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤ A3 X)
    (hpaid8 : ∀ᶠ X : ℝ in atTop,
      rho8 * exp (((1 - beta) / 8 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤
        (M X : ℝ) + 1)
    (hpaid12 : ∀ᶠ X : ℝ in atTop,
      rho12 * exp (((1 - beta) / 12 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤
        (N X : ℝ) + 1),
    ∀ᶠ X : ℝ in atTop, ∀ h p u v : ℤ, 1 ≤ h →
      |(h : ℝ) * ((W.readout 0) () X) - p| ≤ C0 / A3 X →
      |(h : ℝ) * ((W.readout 1) () X) - u| ≤ C0 / ((M X : ℝ) + 1) →
      |(h : ℝ) * ((W.readout 2) () X) - v| ≤ C0 / ((N X : ℝ) + 1) →
      1 ≤ (p - h) * u - h * v

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.eventual_integer_determinant_positive

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder.eventual_integer_determinant_positive)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end eventual_integer_determinant_positive

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
