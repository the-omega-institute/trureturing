import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ZeroPowerSum
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Robin.ZeroPowerSum

open _root_.D5.S3.Arith.Robin.ZeroPowerSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature := Reg.Support.SingleDependentReadout.signature
  (Σ n : ℕ, Fin n → ℂ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p ν => (∑ i, p.2 i ^ ν).re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (z : Fin n → ℂ), (∃ i, z i = 1) →
    ∃ ν : ℕ, 1 ≤ ν ∧ ν ≤ 2 * n + 1 ∧ 1 ≤ R.readout () ⟨n, z⟩ ν

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ν, _, _, hν⟩ := h (fun _ : Fin 1 => (1 : ℂ)) ⟨0, rfl⟩
  change (1 : ℝ) ≤ 0 at hν
  norm_num at hν

def family : Registration arena (type_of% (@exists_pow_sum_re_ge_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_pow_sum_re_ge_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, fun _ => 2⟩, 1, 2, ?_⟩
    change (∑ _ : Fin 1, (2 : ℂ) ^ 1).re ≠ (∑ _ : Fin 1, (2 : ℂ) ^ 2).re
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_pow_sum_re_ge_one) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.ZeroPowerSum.exists_pow_sum_re_ge_one.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ZeroPowerSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ZeroPowerSum
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Robin.ZeroPowerSum
