import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.PolynomialFeedbackDimension
import Reg.Support.DependentFamily

/-! Source-bound audit of the full actual-history polynomial feedback obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.Linear.PolynomialFeedbackDimension

open _root_.D5.S3.Observer.Linear.PolynomialFeedbackDimension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := (k : ℕ) × (d : ℕ) × (m : ℕ) × Protocol
  State p := World p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Answer
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => run p.2.2.2 x.val p.2.2.1 [])
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (k d m : ℕ) (P : Protocol),
    m < k + d + 4 → UniformlyStops (k := k) (d := d) P m →
    ∃ x : World k d, ∃ a,
      R.readout () ⟨k, d, m, P⟩ x = some a ∧ a ≠ target x.val

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let P : Protocol := fun _ _ => .inr (0, 0, 0)
  have hstop : UniformlyStops (k := 0) (d := 0) P 1 := by
    intro x
    exact ⟨(0, 0, 0), rfl⟩
  obtain ⟨x, a, ha, _⟩ := h 0 0 1 P (by omega) hstop
  change (none : Option Answer) = some a at ha
  simp at ha

def family : Registration arena
    (type_of% @unrestricted_polynomial_feedback_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unrestricted_polynomial_feedback_lower_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let P : Protocol := fun w h => .inr (0, 0, Polynomial.C (h ⟨0, by omega⟩))
    let x : World 0 0 := ⟨(1, 1, 1, 0, 0), by norm_num [Legal]⟩
    let y : World 0 0 := ⟨(2, 2, 2, 0, 0), by norm_num [Legal]⟩
    refine ⟨⟨0, 0, 1, P⟩, x, y, ?_⟩
    have hnil : _root_.D5.S3.Observer.Linear.GainRay.acquisition [] = 1 := by
      simp [_root_.D5.S3.Observer.Linear.GainRay.acquisition,
        _root_.D5.S3.Observer.Linear.GainRay.Raw,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
    have hgain (z : Parameters 0 0) : (gain z).eval 0 = 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      simp [gain]
    intro he
    change some (0, 0, Polynomial.C (readAt x.val [] 0)) =
      some (0, 0, Polynomial.C (readAt y.val [] 0)) at he
    have hc := congrArg (fun a : Answer => a.2.2.coeff 0) (Option.some.inj he)
    norm_num [readAt, drift, source, hnil, hgain,
      Matrix.trace, Fin.sum_univ_two, x, y] at hc

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@unrestricted_polynomial_feedback_lower_bound)
    (type_of% (realize signature
      (fun _ p x => run p.2.2.2 x.val p.2.2.1 []) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.PolynomialFeedbackDimension.feedbackUnit
  realizationName := `Reg.D5.S3.Observer.Linear.PolynomialFeedbackDimension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x => run p.2.2.2 x.val p.2.2.1 []) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.PolynomialFeedbackDimension
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family

end Reg.D5.S3.Observer.Linear.PolynomialFeedbackDimension
