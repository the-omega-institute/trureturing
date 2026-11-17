import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.ParticleProcesses.SwitchedTwistedSSEP
import Reg.Support.SingleDependentReadout

/-! Audit the initial-support operand in the complete switched-SSEP answer. -/
namespace Reg.D5.S3.StatisticalMechanics.ParticleProcesses.SwitchedTwistedSSEP
open _root_.D5.S3.StatisticalMechanics.ParticleProcesses.SwitchedTwistedSSEP
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _L : ℕ, ℕ) (fun p => Finset (Configuration p.1 p.2))
    (fun p => Finset (Configuration p.1 p.2))

def actual : Realization signature :=
  realize signature (fun _ _ C => C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N)),
    registeredReachabilityAnswer hL f g ∧
    ((3 ≤ L → (unionConnected hL f g ↔ lAtLeastThreeCriterion f g)) ∧
      (L = 2 → (unionConnected hL f g ↔ lTwoCriterion f g))) ∧
    (∀ (s t : Equiv.Perm (Fin N)) (x y : Configuration L N),
      overlap hL s t x y ↔ 0 < branchingProbability hL s t x y) ∧
    (∀ (start : Bool) (C : Finset (Configuration L N)) (k : ℕ),
      alternatingSupport hL f g start C k =
        switchSupport hL f g start (R.readout () ⟨L, N⟩ C) k)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hb := (h (L := 2) (N := 1) (by decide) 1 1).2.2.2 true {fun _ => 0} 0
  have hx : (fun _ : Fin 2 => (0 : Fin 1)) ∈
      alternatingSupport (by decide) 1 1 true {fun _ => 0} 0 := by
    simp [alternatingSupport]
  rw [hb] at hx
  simpa [rejected, realize, switchSupport, alternatingSectorReach] using hx

private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro role
  refine ⟨⟨2, 1⟩, ∅, {fun _ => 0}, ?_⟩
  change (∅ : Finset (Configuration 2 1)) ≠ {fun _ => 0}
  simp

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit where
  unitName := `SwitchedTwistedSSEP.result.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C => C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.ParticleProcesses.SwitchedTwistedSSEP
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg",
        "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.ParticleProcesses.SwitchedTwistedSSEP
