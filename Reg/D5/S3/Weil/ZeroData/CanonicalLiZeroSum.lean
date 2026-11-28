import D5.S3.Weil.ZeroData.CanonicalLiZeroSum
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The complete coefficient identity as a degree-dependent real observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZeroData.CanonicalLiZeroSum

open _root_.D5.S3.Weil.ZeroData.CanonicalLiZeroSum
open _root_.D5.S3.Weil.ZeroSum
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open _root_.D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ZeroData (fun _ => ℕ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => canonicalLiCoefficient n) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Z : ZeroData) (n : ℕ), R.readout () Z n = ∑' k : ℕ,
    (Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ n).re)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h zetaZeroData 0
  norm_num [rejected, realize] at hz

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨zetaZeroData, 0, 1, ?_⟩
  change canonicalLiCoefficient 0 ≠ canonicalLiCoefficient 1
  rw [canonical_li_zero]
  exact ne_of_lt canonical_li_one_pos

def family : Registration arena (type_of% @canonical_li_eq_zero_real_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonical_li_eq_zero_real_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@canonical_li_eq_zero_real_sum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.CanonicalLiZeroSum.canonical_li_eq_zero_real_sum.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.CanonicalLiZeroSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => canonicalLiCoefficient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.CanonicalLiZeroSum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Weil.ZeroData.CanonicalLiZeroSum
