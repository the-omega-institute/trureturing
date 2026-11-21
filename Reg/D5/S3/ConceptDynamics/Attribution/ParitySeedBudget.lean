import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
import Reg.Support.DependentFamily

/-! The divisibility criterion observes the seed budget. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
open _root_.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
open scoped Classical
attribute [local instance 10000] Classical.propDecidable

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ budget => budget) (fun e => nomatch e)

def alwaysOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n N : ℕ,
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting (Fin (n + 2))) S) (f : S → Pair n),
      Fintype.card S = N ∧ (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) ∧
      ∃ k : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = k) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = k)) ↔
    2 ^ (n + 3) ∣ R.readout () n N

private theorem always_one_fails : ¬ arena.Law alwaysOne := by
  intro law
  have implementation := (exact_seed_budget 0 8).mpr ⟨1, rfl⟩
  have h : 8 ∣ 1 := (law 0 8).mp implementation
  exact (Nat.not_succ_le_self 1) ((Nat.le_add_right 2 6).trans (Nat.le_of_dvd Nat.one_pos h))

def family : Registration arena (type_of% exact_seed_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_seed_budget, alwaysOne, always_one_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysOne, ?_, rfl, always_one_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    exact ⟨0, 0, 1, Nat.zero_ne_one⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_seed_budget (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget.budget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ budget => budget) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace ProfileFibre

abbrev parameters :=
  Σ n : ℕ, Σ S : Type, Σ _ : Fintype S, Σ _ : ParityClass (n + 2) 0, ParityClass (n + 2) 1

abbrev signature : Signature where
  Params := parameters
  State a := a.2.1 → Pair a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ a f => @profileFibreCount a.1 a.2.1 a.2.2.1 f a.2.2.2.1 a.2.2.2.2)
    (fun e => nomatch e)

def alwaysOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {S : Type} [hS : Fintype S] [MulAction (Acting (Fin (n + 2))) S]
    (f : S → Pair n) (_ : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (k : ℕ)
    (_ : ∀ p, (∑ q, profileFibreCount f p q) = k)
    (_ : ∀ q, (∑ p, profileFibreCount f p q) = k)
    (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1),
    4 ∣ R.readout () ⟨n, S, hS, p, q⟩ f

private def evenZero : ParityClass 2 0 := ⟨0, by simp [parity]⟩

private def evenOnes : ParityClass 2 0 := ⟨1, by
  simp [parity, show (2 : ZMod 2) = 0 by rfl]⟩

private def oddHead : ParityClass 2 1 := ⟨Fin.cons 1 0, by
  simp [parity, Fin.sum_univ_succ]⟩

private theorem always_one_fails : ¬ arena.Law alwaysOne := by
  intro law
  letI : MulAction (Acting (Fin 2)) Empty := {
    smul := fun _ s => s
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  let f : Empty → Pair 0 := Empty.elim
  have h : 4 ∣ (1 : ℕ) := law f (fun _ s => s.elim) 0
    (by simp [profileFibreCount]) (by simp [profileFibreCount]) evenZero oddHead
  exact (Nat.not_succ_le_self 1) ((Nat.le_add_right 2 2).trans (Nat.le_of_dvd Nat.one_pos h))

private theorem actual_dependence : ∃ a : signature.Params, ∃ f g : signature.State a,
    actual.readout () a f ≠ actual.readout () a g := by
  let y := sliceEquiv 2 1 (oddHead, 0)
  let f : Unit → Pair 0 := fun _ => (sliceEquiv 2 0 (evenZero, 0), y)
  let g : Unit → Pair 0 := fun _ => (sliceEquiv 2 0 (evenOnes, 0), y)
  refine ⟨⟨0, Unit, inferInstance, evenZero, oddHead⟩, f, g, ?_⟩
  change profileFibreCount f evenZero oddHead ≠ profileFibreCount g evenZero oddHead
  have matchLeft : (f ()).1.val.profile = (sliceEquiv 2 0 (evenZero, 0)).val.profile := rfl
  have matchRight : (f ()).2.val.profile = (sliceEquiv 2 1 (oddHead, 0)).val.profile := rfl
  have different : (g ()).1.val.profile ≠ (sliceEquiv 2 0 (evenZero, 0)).val.profile := by
    intro h
    have bit := congrFun h 0
    change true = false at bit
    cases bit
  have left : profileFibreCount f evenZero oddHead = 1 := by
    change (∑ s : Unit, if (f s).1.val.profile = (sliceEquiv 2 0 (evenZero, 0)).val.profile ∧
      (f s).2.val.profile = (sliceEquiv 2 1 (oddHead, 0)).val.profile then 1 else 0) = 1
    simp [matchLeft, matchRight]
  have right : profileFibreCount g evenZero oddHead = 0 := by
    change (∑ s : Unit, if (g s).1.val.profile = (sliceEquiv 2 0 (evenZero, 0)).val.profile ∧
      (g s).2.val.profile = (sliceEquiv 2 1 (oddHead, 0)).val.profile then 1 else 0) = 0
    simp [different]
  simpa only [left, right] using Nat.one_ne_zero

def family : Registration arena (type_of% (@profile_fibre_four_dvd)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@profile_fibre_four_dvd, alwaysOne, always_one_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysOne, ?_, rfl, always_one_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    cases role
    exact actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@profile_fibre_four_dvd) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget.profileFibre
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget.ProfileFibre.family
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
    (fun _ a f => @profileFibreCount a.1 a.2.1 a.2.2.1 f a.2.2.2.1 a.2.2.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
    definition := none
    coordinates := #[0, 1, 9, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ProfileFibre

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
