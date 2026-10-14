import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.LowerHalfPlaneFactorContinuity
import Reg.Support.DependentFamily

open _root_.D5.S3.Analytic.LowerHalfPlaneFactorContinuity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

namespace Reg.D5.S3.Analytic.LowerHalfPlaneFactorContinuity
noncomputable section
universe u

structure SourceInputs where
  A : Type u
  topology : TopologicalSpace A

abbrev signature : Signature where
  Params := SourceInputs.{u}
  State p := p.A → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p f => letI := p.topology; Continuous f)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

/-- The law retains the original telescope, including the zero-degree fiber. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [top : TopologicalSpace A] [FirstCountableTopology A]
    (H B : A → ℂ[X]) (m : ℕ)
    (hmonic : ∀ a, (B a).Monic)
    (hdegree : ∀ a, (B a).natDegree = m)
    (hlower : ∀ a z, (B a).eval z = 0 → z.im < 0)
    (hfactor : ∀ a, H a = B a * (B a).map (starRingEnd ℂ))
    (hc : ∀ k, Continuous (fun a => (H a).coeff k)),
    ∀ k, R.readout () ⟨A, top⟩ (fun a => (B a).coeff k)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance
    (fun _ => 1) (fun _ => 1) 0 (fun _ => monic_one)
    (fun _ => by simp) (fun _ z hz => by simp at hz)
    (fun _ => by simp) (fun _ => continuous_const) 0

def twoPointInputs : SourceInputs.{u} := ⟨ULift.{u} Bool, ⊤⟩

def discontinuousReadout : twoPointInputs.{u}.A → ℂ :=
  fun b => if b.down then 1 else 0

private theorem readout_not_continuous :
    ¬ @Continuous twoPointInputs.{u}.A ℂ twoPointInputs.topology inferInstance
      discontinuousReadout := by
  letI : TopologicalSpace (ULift.{u} Bool) := ⊤
  intro h
  have he := ((Inseparable.all (⟨true⟩ : ULift.{u} Bool) ⟨false⟩).map h).eq
  simpa [discontinuousReadout] using he

def registration : Registration arena.{u}
    (type_of% (@continuous_coeff_of_monic_lower_factor.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_coeff_of_monic_lower_factor, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    letI : TopologicalSpace twoPointInputs.{u}.A := twoPointInputs.topology
    intro i
    refine ⟨twoPointInputs, (fun _ => 0), discontinuousReadout, ?_⟩
    intro he
    exact readout_not_continuous (Eq.mp he continuous_const)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_coeff_of_monic_lower_factor.{u})
    (type_of% (realize signature.{u}
      (fun _ p f => letI := p.topology; Continuous f) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Analytic.LowerHalfPlaneFactorContinuity.continuous_coeff_of_monic_lower_factor.audit
  realizationName := `Reg.D5.S3.Analytic.LowerHalfPlaneFactorContinuity.registration
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
    (fun _ p f => letI := p.topology; Continuous f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.LowerHalfPlaneFactorContinuity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit
end
end Reg.D5.S3.Analytic.LowerHalfPlaneFactorContinuity
