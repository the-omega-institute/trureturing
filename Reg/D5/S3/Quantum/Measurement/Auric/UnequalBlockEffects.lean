import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for the attained unequal-capacity entropy maxima. -/

namespace Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects

open _root_.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

set_option autoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), {0}, ∅, ?_⟩
  intro h
  have he : IsGreatest ({0} : Set ℝ) 0 = IsGreatest (∅ : Set ℝ) 0 := congrFun h 0
  exact (Eq.mp he (by simp [IsGreatest, upperBounds])).1

private abbrev directArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (m : Fin 3 → ℕ) (τ w : Fin 3 → ℝ)
    (_ : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (_ : ∀ j, 0 < w j) (_ : ∑ j, w j = 1) (_ : Antitone w)
    (_ : ∀ j, weightMass (fun j => Fintype.card n - m j)
      (Fintype.card n - ∑ k, (Fintype.card n - m k)) w j = τ j),
    R.readout () () {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
      spectralSum Real.negMulLog A hA.1 = v}
      (allocationValue Real.negMulLog (fun j => Fintype.card n - m j)
        (Fintype.card n - ∑ j, (Fintype.card n - m j)) (weightEntries w))

private theorem directRejected : ¬ directArena.{u}.Law rejected := by
  intro h
  let w : Fin 3 → ℝ := fun _ => 1 / 3
  let m : Fin 3 → ℕ := fun _ => 0
  let τ := weightMass (fun _ => 0) 0 w
  exact h (n := ULift.{u} (Fin 0)) m τ w (by simp [m])
    (fun _ => by norm_num [w]) (by norm_num [w, Fin.sum_univ_three]) (fun _ _ _ => le_rfl)
    (by simp [m, τ])

def directRegistration : Registration directArena.{u} (type_of% @isGreatest_direct.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isGreatest_direct.{u}, rejected, directRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    directArena.{u}.Law actual rejected directRejected
  dependence := dependence

def directAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@isGreatest_direct.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.isGreatest_direct.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.directRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨directArena.{u}⟩
  objectArena := .source ⟨directArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source directArena.{u} ⟨directRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev complementArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (m : Fin 3 → ℕ) (τ w : Fin 3 → ℝ) (k : Fin 4 → ℝ)
    (_ : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (_ : ∀ j, 0 < w j) (_ : ∀ c, 0 < k c) (_ : Monotone k)
    (_ : ∀ c, ∑ j, allocation (complementEntries w k) j c = 1)
    (_ : ∀ j, (∑ c, (multiplicity (fun j => Fintype.card n - m j)
      (Fintype.card n - ∑ i, (Fintype.card n - m i)) c : ℝ) *
        allocation (complementEntries w k) j c) = τ j),
    R.readout () () {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
      spectralSum (fun x => Real.negMulLog (1 - x)) A hA.1 = v}
      (allocationValue (fun x => Real.negMulLog (1 - x)) (fun j => Fintype.card n - m j)
        (Fintype.card n - ∑ j, (Fintype.card n - m j)) (complementEntries w k))

private theorem complementRejected : ¬ complementArena.{u}.Law rejected := by
  intro h
  let w : Fin 3 → ℝ := fun _ => 1
  let k : Fin 4 → ℝ := ![1 / 2, 1 / 2, 1 / 2, 2 / 3]
  have hk (c : Fin 4) : 0 < k c := by fin_cases c <;> norm_num [k]
  have hkm : Monotone k := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> (norm_num [Fin.le_def] at hab <;> norm_num [k])
  have hc (c : Fin 4) : ∑ j, allocation (complementEntries w k) j c = 1 := by
    fin_cases c <;> norm_num [Fin.sum_univ_three, allocation, complementEntries, w, k,
      Fin.ext_iff, Fin.val_castSucc, max_def]
  exact h (n := ULift.{u} (Fin 0)) (fun _ => 0) (fun _ => 0) w k (by simp)
    (fun _ => zero_lt_one) hk hkm hc (by
      intro j
      rw [Fin.sum_univ_four]
      simp [_root_.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.multiplicity])

def complementRegistration : Registration complementArena.{u} (type_of% @isGreatest_complement.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isGreatest_complement.{u}, rejected, complementRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    complementArena.{u}.Law actual rejected complementRejected
  dependence := dependence

def complementAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@isGreatest_complement.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.isGreatest_complement.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.complementRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨complementArena.{u}⟩
  objectArena := .source ⟨complementArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source complementArena.{u} ⟨complementRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev exactArena : Arena where
  signature := signature
  Law R :=
    let a := (Real.sqrt 565 - 5) / 18
    R.readout () () {v : ℝ | ∃ A : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ,
      ∃ hA : Feasible ![3, 4, 4] ![15 / 11, 20 / 11, 20 / 11] A,
      spectralSum Real.negMulLog A hA.1 = v}
      (4 * Real.negMulLog (1 / 2) +
        2 * (Real.negMulLog (a / (a + 1)) + Real.negMulLog (1 / (a + 1))) +
        Real.negMulLog (a / (a + 2)) + 2 * Real.negMulLog (1 / (a + 2)))

private theorem exactRejected : ¬ exactArena.Law rejected := fun h => h

def exactRegistration : Registration exactArena (type_of% isGreatest_three_four_four) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨isGreatest_three_four_four, rejected, exactRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    exactArena.Law actual rejected exactRejected
  dependence := dependence

def exactAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    isGreatest_three_four_four (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.isGreatest_three_four_four.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.exactRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨exactArena⟩
  objectArena := .source ⟨exactArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exactArena ⟨exactRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms directAudit
#print axioms complementAudit
#print axioms exactAudit

end
end Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
