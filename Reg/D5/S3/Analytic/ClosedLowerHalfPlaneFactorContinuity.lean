import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity
import Reg.Support.DependentFamily

open _root_.D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

namespace Reg.D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ A : Type u, Σ _B : A → ℂ[X], ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p a => (p.2.1 a).coeff p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} := by
  classical
  exact realize signature (fun _ p a =>
    if h : p.1 = ULift.{u} Bool then
      if (cast h a).down then 1 else 0
    else 0) (fun e => nomatch e)

/-- All source hypotheses and the arbitrary topological parameter space are retained. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [TopologicalSpace A]
    (H B : A → ℂ[X]) (m : ℕ)
    (_hmonic : ∀ a, (B a).Monic)
    (_hdegree : ∀ a, (B a).natDegree = m)
    (_hlower : ∀ a z, (B a).eval z = 0 → z.im ≤ 0)
    (_hfactor : ∀ a, H a = B a * (B a).map (starRingEnd ℂ))
    (_hc : ∀ k, Continuous (fun a => (H a).coeff k)),
    ∀ k, Continuous (fun a => R.readout () ⟨A, B, k⟩ a)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  letI : TopologicalSpace (ULift.{u} Bool) := ⊤
  intro h
  have hc := @h (ULift.{u} Bool) inferInstance
    (fun _ => 1) (fun _ => 1) 0 (fun _ => monic_one)
    (fun _ => by simp) (fun _ z hz => by simp at hz)
    (fun _ => by simp) (fun _ => continuous_const) 0
  have he := ((Inseparable.all (⟨true⟩ : ULift.{u} Bool) ⟨false⟩).map hc).eq
  simpa [rejected, realize] using he

def registration : Registration arena.{u}
    (type_of% (@continuous_coeff_of_monic_closed_lower_factor.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_coeff_of_monic_closed_lower_factor, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, (fun a => if a.down then 1 else 0), 0⟩,
      ⟨true⟩, ⟨false⟩, ?_⟩
    intro he
    change (1 : ℂ[X]).coeff 0 = (0 : ℂ[X]).coeff 0 at he
    simpa using he

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_coeff_of_monic_closed_lower_factor.{u})
    (type_of% (realize signature.{u}
      (fun _ p a => (p.2.1 a).coeff p.2.2) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity.continuous_coeff_of_monic_closed_lower_factor.audit
  realizationName := `Reg.D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p a => (p.2.1 a).coeff p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity
    definition := none
    coordinates := #[0, 3, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Uniqueness

attribute [local instance] Classical.propDecidable

abbrev signature : Signature where
  Params := ℂ[X]
  State _ := ℂ[X]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => decide (p = q)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (p q : ℂ[X]) (hp : p.Monic) (hq : q.Monic)
    (hlp : ∀ z, p.eval z = 0 → z.im ≤ 0)
    (hlq : ∀ z, q.eval z = 0 → z.im ≤ 0)
    (he : p * p.map (starRingEnd ℂ) = q * q.map (starRingEnd ℂ)),
    R.readout () p q = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 1 1 monic_one monic_one (fun z hz => by simp at hz)
    (fun z hz => by simp at hz) rfl
  cases hf

def registration : Registration arena (type_of% closed_lower_factor_unique) where
  actual := actual
  bridge := by
    simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro p q hp hq hlp hlq he
    exact decide_eq_true (closed_lower_factor_unique p q hp hq hlp hlq he),
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(0 : ℂ[X]), (0 : ℂ[X]), (1 : ℂ[X]), ?_⟩
    intro he
    have h : true = false := by simpa [actual, realize] using he
    cases h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    closed_lower_factor_unique
    (type_of% (realize signature (fun _ p q => decide (p = q)) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity.closed_lower_factor_unique.audit
  realizationName := `Reg.D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity.Uniqueness.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p q => decide (p = q)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit
end Uniqueness

#print axioms registration
#print axioms audit
end
end Reg.D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity
