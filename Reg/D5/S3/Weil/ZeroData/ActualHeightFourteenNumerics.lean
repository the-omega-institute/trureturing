import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZeroData.ActualHeightFourteenNumerics
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenNumerics
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Zeros.CompletedZeta
open LeanInformationAudit
open scoped BigOperators ComplexConjugate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Unit) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ _ =>
    66493177 / 143006288128704000 +
      (4 / 12649365729) * Real.eulerMascheroniConstant -
      Real.log 2 / 1816214400 - (9487 / 40477970332800) * Real.log Real.pi +
      (-deriv riemannZeta (6 : ℂ) / riemannZeta 6).re / 3990729600 - (-deriv riemannZeta (8 : ℂ) / riemannZeta 8).re / 3555377280 +
      (-deriv riemannZeta (10 : ℂ) / riemannZeta 10).re / 6739588800 - (-deriv riemannZeta (12 : ℂ) / riemannZeta 12).re / 24711825600 +
      (-deriv riemannZeta (14 : ℂ) / riemannZeta 14).re / 216459734400) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () () ≤
    72126772613108177 / 15194418113674800000000000000000
theorem source_reconstruction :
    (type_of% (@h14_evaluatedMass_upper)) ↔ arena.Law actual := Iff.rfl
/-- The closed scalar source cannot meet this template's actual-dependence slot. -/
theorem no_actual_dependence : ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy rfl
end Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenNumerics
