import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ t => mangoldtPart t) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law F := ∀ {t : ℝ}, 0 ≤ t → ∀ {N : ℕ}, t < N →
    F.readout () () t = ∑ n ∈ Finset.range N, mangoldtRamp n t

def rejected : Realization signature :=
  realize signature (fun _ _ t => mangoldtPart t + 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := hh (t := 0) le_rfl (N := 1) (by norm_num)
  change mangoldtPart 0 + 1 = _ at hb
  have ha := mangoldtPart_eq_range (t := 0) le_rfl (N := 1) (by norm_num)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 3, ?_⟩
  change mangoldtPart 0 ≠ mangoldtPart 3
  have hzero : mangoldtPart 0 = 0 := by
    rw [mangoldtPart_eq_range le_rfl (N := 1) (by norm_num)]
    simp [mangoldtRamp]
  have hpos : 0 < mangoldtPart 3 := by
    rw [mangoldtPart_eq_range (by norm_num : (0 : ℝ) ≤ 3) (N := 4) (by norm_num)]
    have hh : mangoldtRamp 2 3 ≤ ∑ n ∈ Finset.range 4, mangoldtRamp n 3 :=
      Finset.single_le_sum (fun n _ => mangoldtRamp_nonneg n 3) (by norm_num)
    have hr : 0 < mangoldtRamp 2 3 := by
      rw [mangoldtRamp, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num <;> positivity
    linarith
  rw [hzero]
  exact ne_of_lt hpos

def evidence : Registration arena (type_of% @mangoldtPart_eq_range) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mangoldtPart_eq_range, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mangoldtPart_eq_range) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.mangoldtPart_eq_range.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => mangoldtPart t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
