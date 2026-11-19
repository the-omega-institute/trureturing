import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory Matrix
open scoped Interval
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision

namespace Derivative
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Unit) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ t => D3 t) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 0 < t → t < Real.log 2 → HasDerivAt D2 (R.readout () () t) t
theorem bridge : (type_of% @D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision.hasDerivAt_D2) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision.hasDerivAt_D2) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision.hasDerivAt_D2, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep

end Derivative

namespace Window
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Unit) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ t => D3 t) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∃ δ : ℝ, 0 < δ ∧ δ < Real.log 2 ∧ δ ≤ Real.exp (-1) ∧
    (∀ t ∈ Ioc 0 δ, K 0 / 2 ≤ K t ∧ D1 t < 0 ∧
      1 / (4*t) ≤ D2 t ∧ D2 t ≤ 1/t ∧ -D1 t ≤ Real.log (1/t) ∧
      0 < K t*D2 t-D1 t^2 ∧ 0 < (-D1 t)*(-R.readout () () t)-(-D2 t)^2) ∧
    (∀ t ∈ Ioo 0 δ, HasDerivAt D2 (R.readout () () t) t) ∧
    StrictConvexOn ℝ (Icc 0 δ) (fun t => Real.log (K t)) ∧
    StrictConvexOn ℝ (Ioo 0 δ) (fun t => Real.log (-D1 t))
theorem bridge : (type_of% @D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision.exists_derivative_control_window) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision.exists_derivative_control_window) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision.exists_derivative_control_window, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep

end Window

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision
