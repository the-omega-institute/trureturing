import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
import Reg.Support.DependentFamily

/-! The sharp coordinate fixed-seed count responds to the budget multiplicity. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
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

private def bestCount (n k : ℕ) : ℕ :=
  let M := k * 2 ^ n
  4 * (M - (M + (n + 2 - 1)) / (n + 2))

def actual : Realization signature :=
  realize signature (fun _ => bestCount) (fun e => nomatch e)

def alwaysOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ, 0 < k →
    let N := 2 ^ (n + 3) * k
    let best := R.readout () n k
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting (Fin (n + 2))) S) (f : S → Pair n),
      Fintype.card S = N ∧ (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) ∧
      (∃ c : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = c)) ∧
      ∀ i, best ≤ fixedSeedCount (n := n) S i) ∧
    ∀ (S : Type) [Fintype S] [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n),
      Fintype.card S = N → (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) →
      (∃ c : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = c)) →
      ∃ i, fixedSeedCount (n := n) S i ≤ best

private theorem always_one_fails : ¬ arena.Law alwaysOne := by
  intro law
  obtain ⟨S, _, _, f, card, equiv, uniform, lower⟩ := (law 0 1 Nat.one_pos).1
  obtain ⟨i, upper⟩ := (best_fixed_seed_count 0 1 Nat.one_pos).2 S f card equiv uniform
  exact (Nat.not_succ_le_zero 0) ((lower i).trans upper)

def family : Registration arena (type_of% best_fixed_seed_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨best_fixed_seed_count, alwaysOne, always_one_fails⟩
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
    refine ⟨0, 1, 2, ?_⟩
    change (0 : ℕ) ≠ 4
    exact (Nat.succ_ne_zero 3).symm

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    best_fixed_seed_count (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization.bestCount
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => bestCount n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev pairSignature : Signature where
  Params := Σ n : ℕ, Fin (n + 2)
  State p := Pair p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def leftBit : Realization pairSignature :=
  realize pairSignature (fun _ p a => a.1.val.profile p.2) (fun e => nomatch e)

def alwaysFalse : Realization pairSignature :=
  realize pairSignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev pairArena : Arena where
  signature := pairSignature
  Law R := ∀ {n : ℕ} (a : Pair n) (i : Fin (n + 2)),
    (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a) ↔
      R.readout () ⟨n, i⟩ a = true ∧ a.2.val.profile i = true

private def fixedPair : Pair 0 :=
  (⟨⟨![true, true], 0⟩, by
    change parity (bitProfile _) = 0
    simp [parity, bitProfile, Fin.sum_univ_two, show (1 : ZMod 2) + 1 = 0 from rfl]⟩,
    ⟨⟨![true, false], 0⟩, by
      change parity (bitProfile _) = 1
      simp [parity, bitProfile, Fin.sum_univ_two]⟩)

private theorem always_false_fails : ¬ pairArena.Law alwaysFalse := by
  intro law
  have fixed := (pair_fixed_coordinate fixedPair 0).mpr ⟨rfl, rfl⟩
  exact Bool.false_ne_true ((law fixedPair 0).mp fixed).1

def pairFamily : Registration pairArena (type_of% (@pair_fixed_coordinate)) where
  actual := leftBit
  bridge := Iff.rfl
  variation := ⟨@pair_fixed_coordinate, alwaysFalse, always_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysFalse, ?_, rfl, always_false_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    let moved : Pair 0 := (⟨⟨![false, false], 0⟩, by
      change parity (bitProfile _) = 0
      simp [parity, bitProfile, Fin.sum_univ_two]⟩, fixedPair.2)
    exact ⟨⟨0, 0⟩, fixedPair, moved, by
      change true ≠ false
      simp⟩

def pairRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pair_fixed_coordinate) (Realization pairSignature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization.pairLeftBit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization.pairFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pairArena⟩
  objectArena := .source ⟨pairArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairArena ⟨pairFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ p a => a.1.val.profile p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
