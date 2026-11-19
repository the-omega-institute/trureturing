import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum

namespace SymmetricSum

abbrev sumSignature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ × ℝ × ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sumSignature :=
  realize sumSignature (fun role h p => if role then
    h (p.1 - p.2.1) + h (p.1 + p.2.1) else
    h (p.1 - p.2.2) + h (p.1 + p.2.2)) (fun e => nomatch e)

def rejected : Realization sumSignature :=
  realize sumSignature (fun _ _ _ => 0) (fun e => nomatch e)

def intervention (i : Bool) : Realization sumSignature :=
  realize sumSignature (fun role h p => if role = i then actual.readout (!i) h p
    else actual.readout role h p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sumSignature
  Law R := ∀ {h : ℝ → ℝ}, StrictConcaveOn ℝ (Set.Ioi 0) h →
    ∀ {r s t : ℝ}, 0 ≤ s → s < t → t < r →
      R.readout false h (r, s, t) < R.readout true h (r, s, t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (_root_.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity.logPowerDifference_concavity
    (κ := 2) (by norm_num)).1
  have hb := h hc (r := 3) (s := 0) (t := 1) (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hb

private theorem intervention_law (i : Bool) : ¬ arena.Law (intervention i) := by
  intro h
  have hc := (_root_.D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity.logPowerDifference_concavity
    (κ := 2) (by norm_num)).1
  have hb := h hc (r := 3) (s := 0) (t := 1) (by norm_num) (by norm_num) (by norm_num)
  cases i <;> exact (lt_irrefl _) hb

def family : Registration arena (type_of% @strictConcave_symmetric_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@strictConcave_symmetric_sum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law i⟩
      intro j hji
      funext h p
      simp only [intervention, realize, ite_eq_right hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨id, (0, 0, 0), (1, 0, 0), ?_⟩
    cases i <;> norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strictConcave_symmetric_sum) (Realization sumSignature) Type Unit where
  unitName := `StrictConcaveSymmetricSum.strictConcave_symmetric_sum.audit
  realizationName := `Reg.D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum.SymmetricSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sumSignature (fun role h p => if role then
    h (p.1 - p.2.1) + h (p.1 + p.2.1) else
    h (p.1 - p.2.2) + h (p.1 + p.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ × ℝ × ℝ)
  sourceSelection := some {
    owner := `D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SymmetricSum

end Reg.D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum
