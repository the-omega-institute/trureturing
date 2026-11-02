import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of second-family data in every dimension. -/

namespace Reg.D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions

open _root_.D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Keep the dimension and the four non-shield coordinates as parameters. -/
abbrev Parameters :=
  Σ d : ℕ, Σ _q : Fin d → Matrix (Fin d) (Fin d) ℝ,
    Σ _qbar : Fin d → Fin d → ℝ, Σ _μ : Fin d → Fin d → Fin d,
      Fin d → Fin d → ℝ

/-- Observe the source requirements while the shield vectors vary. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Fin p.1 → Fin p.1 × Fin p.1 → ℂ) (fun _ => Bool)

private theorem forall_nextFin {n : ℕ} (P : Fin (Nat.succ n) → Prop) :
    (∀ i, P i) ↔ P ⟨0, Nat.zero_lt_succ n⟩ ∧ ∀ i : Fin n,
      P (dsimp% only [Fin.succ, HAdd.hAdd, instHAdd, Add.add, instAddNat, Nat.add] i.succ) := by
  exact Fin.forall_fin_succ

private def finForallDecision : (n : ℕ) → (P : Fin n → Prop) →
    (∀ i, Decidable (P i)) → Decidable (∀ i, P i) :=
  Nat.rec (motive := fun n => (P : Fin n → Prop) →
    (∀ i, Decidable (P i)) → Decidable (∀ i, P i))
    (fun _ _ => isTrue (fun i => Fin.elim0 i))
    (fun n ih P h =>
      letI : Decidable (P ⟨0, Nat.zero_lt_succ n⟩) := h _
      letI : Decidable (∀ i : Fin n,
          P (dsimp% only [Fin.succ, HAdd.hAdd, instHAdd, Add.add, instAddNat, Nat.add] i.succ)) :=
        ih (fun i => P
          (dsimp% only [Fin.succ, HAdd.hAdd, instHAdd, Add.add, instAddNat, Nat.add] i.succ))
          (fun i => h
            (dsimp% only [Fin.succ, HAdd.hAdd, instHAdd, Add.add, instAddNat, Nat.add] i.succ))
      decidable_of_iff (P ⟨0, Nat.zero_lt_succ n⟩ ∧ ∀ i : Fin n,
        P (dsimp% only [Fin.succ, HAdd.hAdd, instHAdd, Add.add, instAddNat, Nat.add] i.succ))
        (forall_nextFin P).symm)

private def finProductDecision (n m : ℕ) (P : Fin n × Fin m → Prop)
    (h : ∀ p, Decidable (P p)) : Decidable (∀ p, P p) :=
  letI : Decidable (∀ i : Fin n, ∀ j : Fin m, P (i, j)) :=
    finForallDecision n _ (fun i => finForallDecision m _ (fun j => h (i, j)))
  decidable_of_iff (∀ i : Fin n, ∀ j : Fin m, P (i, j))
    (by simp only [Prod.forall])

private def dataDecidable (d : ℕ) (q : Fin d → Matrix (Fin d) (Fin d) ℝ)
    (qbar : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (a : Fin d → Fin d → ℝ) (s : Fin d → Fin d × Fin d → ℂ) :
    Decidable (IsSecondFamilyData d q qbar μ a s) := by
  letI : DecidableEq ℂ := fun z w =>
    decidable_of_iff (z.re = w.re ∧ z.im = w.im) Complex.ext_iff.symm
  letI (n : ℕ) (P : Fin n → Prop) [h : DecidablePred P] : Decidable (∀ i, P i) :=
    finForallDecision n P h
  letI (n m : ℕ) (P : Fin n × Fin m → Prop) [h : DecidablePred P] :
      Decidable (∀ i, P i) := finProductDecision n m P h
  letI (n : ℕ) {β : Fin n → Type} [h : ∀ i, DecidableEq (β i)] :
      DecidableEq (∀ i, β i) := fun f g =>
    letI : Decidable (∀ i, f i = g i) :=
      finForallDecision n _ (fun i => h i (f i) (g i))
    decidable_of_iff (∀ i, f i = g i) (funext_iff).symm
  letI (n m : ℕ) {β : Fin n × Fin m → Type} [h : ∀ i, DecidableEq (β i)] :
      DecidableEq (∀ i, β i) := fun f g =>
    letI : Decidable (∀ i, f i = g i) :=
      finProductDecision n m _ (fun i => h i (f i) (g i))
    decidable_of_iff (∀ i, f i = g i) (funext_iff).symm
  unfold IsSecondFamilyData
  infer_instance

def actual : Realization signature :=
  realize signature (fun _ p s =>
    @decide (IsSecondFamilyData p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 s)
      (dataDecidable p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 s)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Retain every dimension, its lower bound, and all five existential witnesses. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, 2 ≤ d →
    ∃ (q : Fin d → Matrix (Fin d) (Fin d) ℝ)
      (qbar : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
      (a : Fin d → Fin d → ℝ) (s : Fin d → Fin d × Fin d → ℂ),
      R.readout () ⟨d, q, qbar, μ, a⟩ s = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, qbar, μ, a, s, hbad⟩ := h 2 (by decide)
  change false = true at hbad
  cases hbad

theorem zero_shield_invalid
    (q : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (qbar : Fin 2 → Fin 2 → ℝ) (μ : Fin 2 → Fin 2 → Fin 2)
    (a : Fin 2 → Fin 2 → ℝ) :
    ¬ IsSecondFamilyData 2 q qbar μ a 0 := by
  rintro ⟨_, _, _, _, hs, _⟩
  have hbad := hs 0 0
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  obtain ⟨q, qbar, μ, a, s, hs⟩ := result 2 (by decide)
  refine ⟨⟨2, q, qbar, μ, a⟩, s, 0, ?_⟩
  change @decide (IsSecondFamilyData 2 q qbar μ a s) (dataDecidable 2 q qbar μ a s) ≠
    @decide (IsSecondFamilyData 2 q qbar μ a 0) (dataDecidable 2 q qbar μ a 0)
  have ht := @decide_eq_true (IsSecondFamilyData 2 q qbar μ a s)
    (dataDecidable 2 q qbar μ a s) hs
  have hf := @decide_eq_false (IsSecondFamilyData 2 q qbar μ a 0)
    (dataDecidable 2 q qbar μ a 0) (zero_shield_invalid q qbar μ a)
  rw [ht, hf]
  decide

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp only [claim, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [claim, actual, realize, decide_eq_true_eq] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.result)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s =>
    @decide (IsSecondFamilyData p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 s)
      (dataDecidable p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions
      name := `D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.claim
      path := #[] }
    coordinates := #[0, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.result
#print _root_.D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions
