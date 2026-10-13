import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
import Reg.Support.DependentFamily

open _root_.D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

namespace Reg.D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation

noncomputable section
universe u

/-- The selected observation is the imaginary part of the final root. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z.im) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Every original parameter, dictionary and premise remains in the law. Only the
imaginary-part observation of the final root is selected for intervention. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [TopologicalSpace A] [PreconnectedSpace A] [CompactSpace A]
    (P : A → Polynomial ℂ) (q : ℕ)
    (hmonic : ∀ x, (P x).Monic) (hdegree : ∀ x, (P x).natDegree = q)
    (hc : ∀ i, Continuous (fun x => (P x).coeff i))
    (d : ℝ) (hd : 0 < d) (hreal : ∀ x i, ((P x).coeff i).im = 0)
    (hsep : ∀ x z w, (P x).eval z = 0 → (P x).eval w = 0 → z ≠ w → d ≤ ‖z - w‖)
    (x0 : A) (hstart : ∀ z, (P x0).eval z = 0 → z.im = 0),
    ∀ x z, (P x).eval z = 0 → R.readout () () z = 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance inferInstance
    (fun _ => (X : Polynomial ℂ)) 1
    (fun _ => monic_X) (fun _ => by simp) (fun _ => continuous_const)
    1 (by norm_num)
    (fun _ i => by by_cases hi : i = 1 <;> simp [Polynomial.coeff_X, hi, eq_comm])
    (fun _ z w hz hw hzw => by
      simp only [eval_X] at hz hw
      exact (hzw (hz.trans hw.symm)).elim)
    ⟨()⟩ (fun z hz => by simpa using congrArg Complex.im hz)
    ⟨()⟩ 0 (by simp)
  change (1 : ℝ) = 0 at hh
  exact one_ne_zero hh

def registration : Registration arena.{u}
    (∀ {A : Type u} [TopologicalSpace A] [PreconnectedSpace A] [CompactSpace A]
      (P : A → Polynomial ℂ) (q : ℕ)
      (hmonic : ∀ x, (P x).Monic) (hdegree : ∀ x, (P x).natDegree = q)
      (hc : ∀ i, Continuous (fun x => (P x).coeff i))
      (d : ℝ) (hd : 0 < d) (hreal : ∀ x i, ((P x).coeff i).im = 0)
      (hsep : ∀ x z w, (P x).eval z = 0 → (P x).eval w = 0 → z ≠ w → d ≤ ‖z - w‖)
      (x0 : A) (hstart : ∀ z, (P x0).eval z = 0 → z.im = 0),
      ∀ x z, (P x).eval z = 0 → z.im = 0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compact_separated_real_family, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℂ), Complex.I, ?_⟩
    change (0 : ℂ).im ≠ Complex.I.im
    norm_num

/-- Complete source reconstruction binds the selected conclusion occurrence. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compact_separated_real_family.{u})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ z => z.im)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation.compact_separated_real_family.audit
  realizationName := `Reg.D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ z => z.im)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end
end Reg.D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation

namespace Reg.D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation.RootBound
open _root_.D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (P : Polynomial ℂ) (hp : P.Monic) (z : ℂ) (hz : P.eval z = 0),
    R.readout () () z ≤ (∑ i ∈ Finset.range P.natDegree, ‖P.coeff i‖)+1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h X monic_X 0 (by simp)
  norm_num [rejected,realize,Polynomial.coeff_X] at hh

def registration : Registration arena
    (type_of% (@monic_root_bound_by_coefficient_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨monic_root_bound_by_coefficient_sum,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),(0 : ℂ),(1 : ℂ),?_⟩
    change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@monic_root_bound_by_coefficient_sum)
    (type_of% (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation.monic_root_bound_by_coefficient_sum.audit
  realizationName := `Reg.D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation.RootBound.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
#print axioms audit
end
end Reg.D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation.RootBound
