import D5.S3.Arith.PrimitiveRoot.ChebyshevThirty
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the Mangoldt prefix and the rational coefficient endpoint. -/

noncomputable section
open _root_.D5.S3.Arith.PrimitiveRoot.ChebyshevThirty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.PrimitiveRoot.ChebyshevThirty

namespace Prefix
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ n => Chebyshev.psi n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -10) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 1 ≤ n →
    coefficient * n - 5 * (1 + Real.log n) ≤ R.readout () () n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 le_rfl
  have hc := coefficient_bounds.1
  norm_num [rejected, realize] at hh
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  have hv := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  norm_num [actual, realize, Chebyshev.psi,
    show Finset.Ioc 0 2 = {1, 2} by decide, hv]
  exact ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
def family : Registration arena (type_of% psi_nat_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨psi_nat_lower, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    psi_nat_lower (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.ChebyshevThirty.psi_nat_lower.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.ChebyshevThirty.Prefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => Chebyshev.psi n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.ChebyshevThirty
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Prefix

namespace Coefficient
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => 921 / x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 1000 ≤ coefficient ∧ coefficient ≤ 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (2 : ℝ) ≤ coefficient ∧ coefficient ≤ 1 at h
  linarith [h.1, h.2]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% coefficient_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coefficient_bounds, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    coefficient_bounds (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.ChebyshevThirty.coefficient_bounds.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.ChebyshevThirty.Coefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 921 / x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.ChebyshevThirty
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Coefficient

#print axioms Prefix.audit
#print axioms Coefficient.audit

end Reg.D5.S3.Arith.PrimitiveRoot.ChebyshevThirty
