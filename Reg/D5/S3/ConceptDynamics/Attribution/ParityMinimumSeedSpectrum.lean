import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum
import Reg.Support.DependentFamily

/-! The even-word cut threshold affects which vectors can be realized. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
open _root_.D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)

def zeroThreshold : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (z : Fin (n + 2) → ℕ),
    RealizableSeedCounts n 1 z ↔
    ∃ a : Fin (n + 2) → ℕ, (∀ i, a i ≤ 2 ^ n ∧ z i = 4 * (2 ^ n - a i)) ∧
      ∀ e : Profile (n + 2), parity e = 0 →
        R.readout () () n ≤ ∑ i, if e i = 0 then a i else 2 ^ n - a i

private theorem zero_threshold_fails : ¬ arena.Law zeroThreshold := by
  intro law
  have real := (law 0 (fun _ => 0)).mpr
    ⟨fun _ => 1, ⟨fun _ => by norm_num, fun _ _ => Nat.zero_le _⟩⟩
  exact (by decide : ¬ (Odd (0 + 2 : ℕ) ∨ Even (1 : ℕ)))
    ((zero_coordinate_counts_iff 0 1).mp real)

def family : Registration arena (type_of% exact_minimal_budget_fixed_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_minimal_budget_fixed_counts, zeroThreshold, zero_threshold_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroThreshold, ?_, rfl, zero_threshold_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun anchor => nomatch anchor
  dependence := by
    rintro ⟨⟩
    exact ⟨(), 0, 1, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_minimal_budget_fixed_counts (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum.cutThreshold
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum
