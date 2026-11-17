import D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility
open _root_.D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => if n = 0 then 2 else 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ (k m : ℕ) (d : ℤ), 0 < d → d ∣ (r.readout () () k : ℤ) →
      d ∣ (r.readout () () (k + m * d.toNat) : ℤ)) ∧
    (∀ k m : ℕ, r.readout () () k ∣ r.readout () () (k + m * r.readout () () k))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.1 0 1 2 (by norm_num) (by change (2 : ℤ) ∣ 2; norm_num)
  change (2 : ℤ) ∣ 1 at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 3, ?_⟩
  change a 0 ≠ a 3
  norm_num [a, triangle]

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "domain", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Arith.Congruence.ReflectedRows.KurkovWeightedEntringerDivisibility
