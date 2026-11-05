import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Latin.PerfectBalanceDimension
import Reg.Support.DependentFamily

/-! Source-bound audit of the observed column count in the dimension conclusion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Latin.PerfectBalanceDimension

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Latin.PerfectBalanceDimension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n : ℕ}, 0 < k → k ≤ n → ∀ L : LatinRectangle k n,
    imbalance L = 0 → R.readout () k n ≤ 2 * k

private def rejected : Realization signature :=
  realize signature (fun _ _ n => n + 2) (fun e => nomatch e)

private def singleton : LatinRectangle 1 1 :=
  ⟨fun _ j => j, ⟨fun _ => Function.injective_id,
    fun _ _ _ _ => Subsingleton.elim _ _⟩⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : imbalance singleton = 0 := by simp [imbalance]
  have hx := h (k := 1) (n := 1) (by decide) (by decide) singleton hz
  change 1 + 2 ≤ 2 * 1 at hx
  omega

def source_registration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change (0 : ℕ) ≠ 1
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Latin.PerfectBalanceDimension.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Latin.PerfectBalanceDimension.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Latin.PerfectBalanceDimension
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Latin.PerfectBalanceDimension
