import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity

/-! Source bindings for the signed Wu endpoint contractivity and its equality case. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence (relation : ℝ → ℝ → Prop) (probe : ℝ)
    (htrue : relation 0 probe) (hfalse : ¬ relation 1 probe) :
    ObservationalDependence signature
      (realize signature (fun _ _ x => relation x) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact hfalse (Eq.mp (congrFun h probe) htrue)

namespace Strict

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode), X.PosSemidef →
    (¬ ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : TwoMode)) →
    R.readout () () (endpointTraceMoment 4 (A₁ X) ^ 3)
      (endpointTraceMoment 3 X ^ 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let d : Mode → ℂ := fun i => if i = (0, 0) then 1 else 0
  have hpsd : (Matrix.diagonal d).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by unfold d; split <;> simp)
  refine h (Matrix.diagonal d) hpsd ?_
  rintro ⟨c, _, hc⟩
  have h00 := congrArg (fun (M : TwoMode) => M (0, 0) (0, 0)) hc
  have h11 := congrArg (fun (M : TwoMode) => M (1, 1) (1, 1)) hc
  simp [d, Matrix.smul_apply, smul_eq_mul] at h00 h11
  exact one_ne_zero (h00.trans h11.symm)

def family : Registration arena (type_of% @A1_quartic_contractivity_strict) where
  actual := realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@A1_quartic_contractivity_strict, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejected rejected_law
  dependence := dependence (· < ·) 1 (by norm_num) (lt_irrefl 1)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_quartic_contractivity_strict) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity.A1_quartic_contractivity_strict.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity.Strict.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Strict

namespace Contractivity

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode), X.PosSemidef →
    R.readout () () (endpointTraceMoment 4 (A₁ X) ^ 3)
      (endpointTraceMoment 3 X ^ 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 Matrix.PosSemidef.zero

def family : Registration arena (type_of% @A1_quartic_contractivity) where
  actual := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@A1_quartic_contractivity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejected rejected_law
  dependence := dependence (· ≤ ·) 0 le_rfl (by norm_num)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_quartic_contractivity) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity.A1_quartic_contractivity.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity.Contractivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Contractivity

namespace Equality

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode), X.PosSemidef →
    (R.readout () () (endpointTraceMoment 4 (A₁ X) ^ 3)
      (endpointTraceMoment 3 X ^ 4) ↔
      ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : TwoMode))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0 Matrix.PosSemidef.zero).mpr ⟨0, le_rfl, by simp⟩

def family : Registration arena (type_of% @A1_quartic_contractivity_eq_iff) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@A1_quartic_contractivity_eq_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejected rejected_law
  dependence := dependence (· = ·) 0 rfl (by norm_num)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_quartic_contractivity_eq_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity.A1_quartic_contractivity_eq_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity.Equality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Equality

end Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticContractivity
