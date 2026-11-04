import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.ProductMarginZhangYeung

noncomputable section
namespace Reg.D5.S3.Quantum.Information.ProductMarginZhangYeung
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.ProductMarginZhangYeung
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Information.QubitNormalFormState
open scoped ComplexOrder MatrixOrder

private def origin : LocalPair := ⟨0, 0, le_refl _, le_refl _, by norm_num⟩
private def zeroCoupling : Coupling origin origin where
  K := 0
  positive := Matrix.PosSemidef.zero
  le_positive := (density_posSemidef (positiveMargin origin origin)).nonneg
  le_negative := (density_posSemidef (negativeMargin origin origin)).nonneg

namespace Identity
abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ p => Real.binEntropy p) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ p => Real.binEntropy p + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c d : LocalPair) (k : Coupling c d),
    zhangYeungGap k = Real.log 2 - R.readout () () k.K.trace.re +
      qubitHolevo c.x c.z c.disk + qubitHolevo d.x d.z d.disk -
        3 * quantumMutualInformation (productMixture c d)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h origin origin zeroCoupling
  have hi := actual_gap_identity origin origin zeroCoupling
  simp only [bad, realize] at hh
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2⁻¹, ?_⟩
  simp only [actual, realize, Real.binEntropy_zero, Real.binEntropy_two_inv]
  exact ne_of_lt (Real.log_pos (by norm_num))
def family : Registration arena (type_of% (@actual_gap_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_gap_identity, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad bad_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_gap_identity) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ProductMarginZhangYeung.Identity.unit
  realizationName := `Reg.D5.S3.Quantum.Information.ProductMarginZhangYeung.Identity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => Real.binEntropy p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ProductMarginZhangYeung
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Identity

namespace Sign
abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ≤ y) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c d : LocalPair) (k : Coupling c d), R.readout () () 0 (zhangYeungGap k)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  exact h origin origin zeroCoupling
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  change ((0 : ℝ) ≤ 0) = (1 ≤ 0) at hh
  norm_num at hh

def family : Registration arena (type_of% (@actual_zhang_yeung_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_zhang_yeung_nonneg, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad bad_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_zhang_yeung_nonneg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ProductMarginZhangYeung.Sign.unit
  realizationName := `Reg.D5.S3.Quantum.Information.ProductMarginZhangYeung.Sign.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ProductMarginZhangYeung
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Sign

#print axioms Identity.registration
#print axioms Sign.registration
end Reg.D5.S3.Quantum.Information.ProductMarginZhangYeung
