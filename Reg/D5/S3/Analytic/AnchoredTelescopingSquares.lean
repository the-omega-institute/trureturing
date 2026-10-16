import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.AnchoredTelescopingSquares
import Reg.Support.DependentFamily

open _root_.D5.S3.Analytic.AnchoredTelescopingSquares
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

namespace Reg.D5.S3.Analytic.AnchoredTelescopingSquares
noncomputable section

abbrev signature : Signature where
  Params := ℂ[X]
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ B z => B.eval z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete source statement, with its native polynomial evaluation operand. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℝ[X]) (m : ℕ)
    (_hdegree : d.natDegree = 2*m) (_hpositive : ∀ t : ℝ, 0 < d.eval t),
    0 < d.coeff (2*m) ∧ ∃ B : ℂ[X], B.Monic ∧ B.natDegree = m ∧
      (∀ z : ℂ, R.readout () B z = 0 → z.im < 0) ∧
      d.map Complex.ofRealHom =
        C (d.coeff (2*m) : ℂ) * (B * B.map (starRingEnd ℂ))

def registration : Registration arena (type_of% exists_monic_lower_factor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_monic_lower_factor, rejected, by
    intro h
    obtain ⟨_, B, _, _, hlower, _⟩ := h 1 0 (by simp) (by intro t; simp)
    have hf := hlower 0 rfl
    simpa using hf⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        obtain ⟨_, B, _, _, hlower, _⟩ := h 1 0 (by simp) (by intro t; simp)
        have hf := hlower 0 rfl
        simpa using hf
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(X : ℂ[X]), (0 : ℂ), (1 : ℂ), ?_⟩
    change (X : ℂ[X]).eval (0 : ℂ) ≠ (X : ℂ[X]).eval (1 : ℂ)
    simp only [Polynomial.eval_X]
    exact zero_ne_one

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exists_monic_lower_factor
    (type_of% (realize signature (fun _ B z => B.eval z) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Analytic.AnchoredTelescopingSquares.exists_monic_lower_factor.audit
  realizationName := `Reg.D5.S3.Analytic.AnchoredTelescopingSquares.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ B z => B.eval z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.AnchoredTelescopingSquares
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body",
        "arg", "arg", "fn", "arg", "body", "domain", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev telescopeSignature : Signature where
  Params := ℝ[X] × ℝ[X]
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def telescopeActual : Realization telescopeSignature :=
  realize telescopeSignature
    (fun _ ps t => (ps.1.eval t)^2 + (ps.2.eval (t+1))^2 - (ps.2.eval t)^2)
    (fun e => nomatch e)

def telescopeRejected : Realization telescopeSignature :=
  realize telescopeSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original theorem, read through its native telescoping expression. -/
def telescopeArena : Arena where
  signature := telescopeSignature
  Law R := ∀ (d : ℝ[X]) (m : ℕ) (_hm : 1 ≤ m)
    (_hdegree : d.natDegree = 2*m) (_hpositive : ∀ t : ℝ, 0 < d.eval t),
    ∃ p s : ℝ[X], p.natDegree = m ∧ s.natDegree ≤ m ∧ s.eval 0 = 0 ∧
      (∀ t : ℝ, d.eval t = R.readout () (p,s) t) ∧
      (p.coeff m)^2 = d.coeff (2*m) ∧ 0 < d.coeff (2*m)

def telescopeRegistration : Registration telescopeArena
    (type_of% exists_anchored_telescoping_squares) where
  actual := telescopeActual
  bridge := Iff.rfl
  variation := ⟨exists_anchored_telescoping_squares, telescopeRejected, by
    intro h
    obtain ⟨p, s, _, _, _, he, _⟩ := h (X^2+C 1) 1 (by omega)
      (by compute_degree <;> norm_num)
      (by intro t; simp only [Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]; positivity)
    have h0 := he 0
    change ((X^2+C 1 : ℝ[X]).eval 0) = 0 at h0
    norm_num at h0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨telescopeRejected, ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        obtain ⟨p, s, _, _, _, he, _⟩ := h (X^2+C 1) 1 (by omega)
          (by compute_degree <;> norm_num)
          (by intro t; simp only [Polynomial.eval_add, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C]; positivity)
        have h0 := he 0
        change ((X^2+C 1 : ℝ[X]).eval 0) = 0 at h0
        norm_num at h0
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨((X : ℝ[X]), (0 : ℝ[X])), (0 : ℝ), (1 : ℝ), ?_⟩
    change ((X : ℝ[X]).eval 0)^2 + ((0 : ℝ[X]).eval (0+1))^2 -
      ((0 : ℝ[X]).eval 0)^2 ≠ ((X : ℝ[X]).eval 1)^2 +
      ((0 : ℝ[X]).eval (1+1))^2 - ((0 : ℝ[X]).eval 1)^2
    simp only [Polynomial.eval_X, Polynomial.eval_zero, ne_eq,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), one_pow, add_zero]
    exact (by norm_num : (0 : ℝ) - 0 ≠ 1 - 0)

def telescopeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exists_anchored_telescoping_squares
    (type_of% (realize telescopeSignature
      (fun _ ps t => (ps.1.eval t)^2 + (ps.2.eval (t+1))^2 - (ps.2.eval t)^2)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Analytic.AnchoredTelescopingSquares.exists_anchored_telescoping_squares.audit
  realizationName := `Reg.D5.S3.Analytic.AnchoredTelescopingSquares.telescopeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨telescopeArena⟩
  objectArena := .source ⟨telescopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source telescopeArena ⟨telescopeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize telescopeSignature
    (fun _ ps t => (ps.1.eval t)^2 + (ps.2.eval (t+1))^2 - (ps.2.eval t)^2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.AnchoredTelescopingSquares
    definition := none
    coordinates := #[5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.AnchoredTelescopingSquares
