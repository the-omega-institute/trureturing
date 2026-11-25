import D5.S3.Arith.Additive.BenfieldLippard.Result
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Additive.BenfieldLippard.Result

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

set_option autoImplicit false

private abbrev signature := Reg.Support.SingleDependentReadout.signature
  (ℕ → Set ℕ) (fun _ => ℕ) (fun _ => Set ℕ)

private def actual : Realization signature :=
  realize signature (fun _ B k => B k) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∃ B : ℕ → Set ℕ,
      (∀ k : ℕ, 2 ≤ k → (B k).Finite ∧
        ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
          R.readout () B k = {s : ℕ | 0 < s ∧
            ¬ (∃ f : Fin j → ℕ, (∀ i, 0 < f i) ∧ j + s = ∑ i, f i ^ k)}) ∧
      ∀ N : ℕ, 2 ≤ N →
        (∃ r : ℕ, N ≤ r ∧ (B r).ncard < (B (r + 1)).ncard) ∧
        (∃ d : ℕ, N ≤ d ∧ (B (d + 1)).ncard < (B d).ncard)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨B, hStable, _⟩ := h
  obtain ⟨_, J, _, hJ⟩ := hStable 2 le_rfl
  have h0 : (0 : ℕ) ∈ rejected.readout () B 2 := Set.mem_univ _
  rw [hJ J le_rfl] at h0
  exact Nat.lt_irrefl 0 h0.1

def family : Registration arena (type_of% BenfieldLippard.conjecture_10_5) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨BenfieldLippard.conjecture_10_5, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨fun k => {k}, 0, 1, ?_⟩
    change ({0} : Set ℕ) ≠ {1}
    intro h
    have h0 : (0 : ℕ) ∈ ({0} : Set ℕ) := by simp
    rw [h] at h0
    simp at h0

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    BenfieldLippard.conjecture_10_5 (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Additive.BenfieldLippard.Result.conjecture_10_5.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.BenfieldLippard.Result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ B k => B k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.BenfieldLippard.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "fn", "arg", "body", "body", "arg", "arg", "body",
        "arg", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Additive.BenfieldLippard.Result
