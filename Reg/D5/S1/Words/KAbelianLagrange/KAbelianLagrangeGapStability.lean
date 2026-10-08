/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeGapStability
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeGapStability
   mirror-E: none(waiver:finite-cut-perturbation)
   anchors: []
   utility: none
   digest: The original gap-error readout registers finite-cut stability. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeGapStability
import Reg.Support.DependentFamily

open D5.S1.Words.KAbelianLagrange
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeGapStability
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (S T : Finset ℝ) {delta : ℝ}
    (_hS0 : 0 ∈ S) (_hS1 : 1 ∈ S) (_hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1)
    (_hT0 : 0 ∈ T) (_hT1 : 1 ∈ T) (_hT : ∀ x ∈ T, 0 ≤ x ∧ x ≤ 1)
    (_hST : ∀ x ∈ S, ∃ y ∈ T, |x - y| ≤ delta)
    (_hTS : ∀ y ∈ T, ∃ x ∈ S, |y - x| ≤ delta),
    ∃ a b c d : ℝ,
      a ∈ S ∧ b ∈ S ∧ a < b ∧ (∀ x ∈ S, x ≤ a ∨ b ≤ x) ∧
      (∀ u ∈ S, ∀ v ∈ S, u < v → (∀ x ∈ S, x ≤ u ∨ v ≤ x) → v - u ≤ b - a) ∧
      c ∈ T ∧ d ∈ T ∧ c < d ∧ (∀ x ∈ T, x ≤ c ∨ d ≤ x) ∧
      (∀ u ∈ T, ∀ v ∈ T, u < v → (∀ x ∈ T, x ≤ u ∨ v ≤ x) → v - u ≤ d - c) ∧
      R.readout () () ((b - a) - (d - c)) ≤ 2 * delta

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      let S : Finset ℝ := {0, 1}
      have hbounds : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1 := by
        intro x hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> norm_num
      have hclose : ∀ x ∈ S, ∃ y ∈ S, |x - y| ≤ (0 : ℝ) := by
        intro x hx
        exact ⟨x, hx, by simp⟩
      obtain ⟨a, b, c, d, _, _, _, _, _, _, _, _, _, _, herr⟩ :=
        @h S S 0 (by simp [S]) (by simp [S]) hbounds
          (by simp [S]) (by simp [S]) hbounds hclose hclose
      change (2 : ℝ) ≤ 2 * 0 at herr
      norm_num at herr
    exact ⟨finite_cut_gap_stability, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      let S : Finset ℝ := {0, 1}
      have hbounds : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1 := by
        intro x hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> norm_num
      have hclose : ∀ x ∈ S, ∃ y ∈ S, |x - y| ≤ (0 : ℝ) := by
        intro x hx
        exact ⟨x, hx, by simp⟩
      obtain ⟨a, b, c, d, _, _, _, _, _, _, _, _, _, _, herr⟩ :=
        @h S S 0 (by simp [S]) (by simp [S]) hbounds
          (by simp [S]) (by simp [S]) hbounds hclose hclose
      change (2 : ℝ) ≤ 2 * 0 at herr
      norm_num at herr
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1 / 2, ?_⟩
    norm_num [actual, realize]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeGapStability
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
    "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg",
    "arg", "arg", "arg", "arg", "fn", "arg", "fn"], functionOperand := true }] }

register_information_theorem finite_cut_gap_stability in arena
  readout via (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeGapStability
