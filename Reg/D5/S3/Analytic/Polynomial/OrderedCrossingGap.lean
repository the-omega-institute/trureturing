import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Polynomial.OrderedCrossingGap
import Reg.Support.SingleDependentReadout

/-! A source-bound audit of the rate difference in the crossing-gap conclusion. -/

namespace Reg.D5.S3.Analytic.Polynomial.OrderedCrossingGap

open _root_.OrderedCrossingGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ a b => b - a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b K L B N k : ℝ}, 0 ≤ a → a ≤ b → 0 < k → k ≤ B → B ≤ N → N ≤ L →
    (B < L → B + 1 ≤ L) → (k < B → k + 1 ≤ B) → (N < L → N + 1 ≤ L) →
    a * L * (L - 1) / 2 ≤ K →
    K ≤ a * N * (N + 1) / 2 + (b - a) * k * (k + 1) / 2 →
    let σ := k * (N - B) - (B - k) * (L - N)
    0 ≤ (K - a * L * B / 2) * σ +
      a * L * B * (L - N) * (N - B) / 2 + L * B * k * R.readout () a b * (B - k) / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (a := 1) (b := 1) (K := 3) (L := 3) (B := 2) (N := 3) (k := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@gap_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gap_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@gap_nonneg) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.Polynomial.OrderedCrossingGap.rate_difference_unit
  realizationName := `Reg.D5.S3.Analytic.Polynomial.OrderedCrossingGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => b - a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Polynomial.OrderedCrossingGap
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Analytic.Polynomial.OrderedCrossingGap
