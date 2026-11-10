import D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity

open Real Finset
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The square-root observation in the quantitative bound, with z retained. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => sqrt d) (fun e => nomatch e)

/-- Intervene on this observation over the complete family of scales and defects. -/
def rejected : Realization signature :=
  realize signature (fun _ z d => -(8 * d + 32 / log z + 1) / 6)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z : ℝ, Z ≤ z → ∀ n : ℕ, 1 ≤ n →
    ∀ H X : Finset ℕ,
    (∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ sqrt 2 * sqrt z ∧ n.factorization p ≤ 1) →
    (∀ p ∈ X, p.Prime ∧ sqrt 2 * sqrt z < (p : ℝ) ∧ 2 ≤ n.factorization p) →
    ((∑ p ∈ H, log p) + ∑ p ∈ X, log p) / sqrt z ≤
      6 * R.readout () z (sqrt z * log z * actualDefect z n) +
        8 * (sqrt z * log z * actualDefect z n) + 32 / log z

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨Z, hZ, h⟩
  have hb := h Z le_rfl 1 le_rfl ∅ ∅ (by simp) (by simp)
  simp only [sum_empty, add_zero, zero_div] at hb
  change (0 : ℝ) ≤
    6 * (-(8 * (sqrt Z * log Z * actualDefect Z 1) + 32 / log Z + 1) / 6) +
      8 * (sqrt Z * log Z * actualDefect Z 1) + 32 / log Z at hb
  linarith only [hb]

def family : Registration arena (type_of% (@eventually_quantitative_actual_occupation_defect)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventually_quantitative_actual_occupation_defect, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(2 : ℝ), 0, 1, ?_⟩
    change sqrt (0 : ℝ) ≠ sqrt 1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventually_quantitative_actual_occupation_defect) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity.eventually_quantitative_actual_occupation_defect.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => sqrt d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
