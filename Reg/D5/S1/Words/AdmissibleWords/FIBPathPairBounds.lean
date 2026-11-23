import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.AdmissibleWords.FIBPathPairBounds
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-! Observations of downward variation in the path occupancy bounds. -/

set_option autoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.FIBPathPairBounds

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S1.Words.AdmissibleWords.FIBPathPairBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

namespace Path

private abbrev signature : Signature where
  Params := (ℕ → ℝ) × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ p k => downwardVariation (flipProb p.1) p.2 k) (fun a => nomatch a)

private def negative : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ → ℝ), (∀ k, 0 ≤ p k ∧ p k ≤ 1) →
    (∀ k, p k + p (k + 1) ≤ 1) → ∀ start : ℕ,
    let q := flipProb p
    (∀ B, HardCoreProfile p B → ∀ k ≥ start,
      volume.real (flipEvent B start \ flipEvent B k) ≤
        min (q start) (min (1 - q k) (R.readout () (p, start) k))) ∧
    ∃ B, HardCoreProfile p B ∧ ∀ k ≥ start,
      volume.real (flipEvent B start \ flipEvent B k) =
        min (q start) (min (1 - q k) (downwardVariation q start k))

private theorem negative_fails : ¬ arena.Law negative := by
  intro h
  have empty : HardCoreProfile (fun _ => 0) (fun _ => ∅) :=
    ⟨fun _ => MeasurableSet.empty, fun _ => empty_subset _, fun _ => measureReal_empty,
      fun _ => by simp⟩
  have bad := (h (fun _ => 0) (by intro k; norm_num) (by intro k; norm_num) 0).1
    (fun _ => ∅) empty 0 le_rfl
  norm_num [flipProb, negative, realize, min_def] at bad

def family : Registration arena (type_of% @sharp_hard_core_difference) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_hard_core_difference, negative, negative_fails⟩
  sensitivity := ⟨fun i => ⟨negative, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative_fails⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    refine ⟨(fun _ => 0, 1), 1, 2, ?_⟩
    norm_num [actual, realize, downwardVariation, flipProb]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sharp_hard_core_difference) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.FIBPathPairBounds.sharp_hard_core_difference.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FIBPathPairBounds.Path.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => downwardVariation (flipProb p.1) p.2 k)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FIBPathPairBounds
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Path

namespace Word

private abbrev Parameters := Σ n : ℕ, (Fin n → ℝ) × Fin n

private abbrev signature : Signature where
  Params := Parameters
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature
    (fun _ p k => downwardVariation (flipProb (extendProfile p.2.1)) p.2.2 k)
    (fun a => nomatch a)

private def negative : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (p : Fin n → ℝ), (∀ k, 0 ≤ p k ∧ p k ≤ 1) →
    (∀ i j, i.val + 1 = j.val → p i + p j ≤ 1) → ∀ start : Fin n,
    let q := flipProb (extendProfile p)
    ∃ w : ℝ → Fin n → Bool, (∀ u, Adm n (w u)) ∧
      (∀ k, MeasurableSet (wordEvent w k) ∧ wordEvent w k ⊆ Ico 0 1 ∧
        volume.real (wordEvent w k) = p k) ∧
      ∀ k : Fin n, start ≤ k →
        volume.real (orientedDifference w start k) =
          min (q start) (min (1 - q k) (R.readout () ⟨n, p, start⟩ k))

private theorem negative_fails : ¬ arena.Law negative := by
  intro h
  obtain ⟨w, _, _, result⟩ := h 1 (fun _ => 0) (by intro k; norm_num)
    (by intro i j hij; norm_num) 0
  have bad := result 0 le_rfl
  norm_num [flipProb, extendProfile, negative, realize, min_def] at bad
  have nonneg : 0 ≤ volume.real (orientedDifference w 0 0) := measureReal_nonneg
  linarith

def family : Registration arena (type_of% @word_attainment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_attainment, negative, negative_fails⟩
  sensitivity := ⟨fun i => ⟨negative, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative_fails⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨3, fun _ => 0, 1⟩, 1, 2, ?_⟩
    norm_num [actual, realize, downwardVariation, extendProfile, flipProb]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@word_attainment) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.FIBPathPairBounds.word_attainment.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FIBPathPairBounds.Word.family
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
    (fun _ p k => downwardVariation (flipProb (extendProfile p.2.1)) p.2.2 k)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FIBPathPairBounds
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg",
        "body", "body", "arg", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Word
end
end Reg.D5.S1.Words.AdmissibleWords.FIBPathPairBounds
