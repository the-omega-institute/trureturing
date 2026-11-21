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
  omega

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

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
