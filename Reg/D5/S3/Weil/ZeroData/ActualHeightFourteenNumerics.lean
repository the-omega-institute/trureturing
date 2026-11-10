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

namespace Kernel
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => h14Weight x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (rho : ℂ) (_h0 : 0 < rho.re) (_h1 : rho.re < 1)
    (_hu : 100 < rho.im ^ 2), 0 < R.readout () () rho ∧
      (rho.im ^ 2 ≤ 196 → 345650537 / 72636763553532703907200 ≤ 2 * h14Weight rho)
private theorem source_reconstruction :
    (type_of% (@h14_kernel_bounds)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h ((1 / 2 : ℂ) + 11 * Complex.I)
    (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [rejected, realize] at hbad
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 / 2 : ℂ), ?_⟩
  norm_num [actual, realize, h14Weight, h14Kernel, Complex.div_re, Complex.normSq]
def family : Registration arena (type_of% (@h14_kernel_bounds)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@h14_kernel_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@h14_kernel_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.h14_kernel_bounds.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenNumerics.Kernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => h14Weight x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualHeightFourteenNumerics
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Kernel

end Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenNumerics
