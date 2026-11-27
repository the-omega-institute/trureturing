import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Complex
open scoped Topology BigOperators
namespace Reg.D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open _root_.D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace DerivativeShift
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ x => reciprocalGamma x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => (1 : ℂ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ z : ℂ, deriv reciprocalGamma (z - 1) =
    R.readout () () z + (z - 1) * deriv reciprocalGamma z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := reciprocal_gamma_deriv_shift 1
  have h1 := reciprocal_gamma_deriv_shift 0
  have hb := h 0
  norm_num [reciprocalGamma] at h0 h1
  norm_num only [rejected, realize, zero_sub, one_mul] at hb
  rw [h0] at h1 hb
  have hh := congrArg Complex.re (hb.symm.trans h1)
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, reciprocalGamma]
def family : Registration arena (type_of% @reciprocal_gamma_deriv_shift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reciprocal_gamma_deriv_shift, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reciprocal_gamma_deriv_shift) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit.reciprocal_gamma_deriv_shift
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit.DerivativeShift.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => reciprocalGamma x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end DerivativeShift

end Reg.D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
