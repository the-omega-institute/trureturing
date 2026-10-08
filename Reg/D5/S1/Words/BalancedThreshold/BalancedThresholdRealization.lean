/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdRealization
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdRealization
   mirror-E: none(waiver:source-bound-return-variation)
   anchors: []
   utility: none
   digest: Mechanical return variation is registered at its entire physical source word. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdRealization
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold D5.S1.Words.Mechanical D5.S1.Words.Complexity
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdRealization
noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ alpha rho => lowerMechanicalWord alpha rho) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {alpha rho : ℝ}, 0 < alpha → alpha < 1 → Irrational alpha →
    let u := R.readout () alpha rho
    ∀ (n : ℕ) (w : Fin n → Bool), (∃ i, wordFactor u n i = w) →
      ∀ r : List Bool, ∃ i j, AdjacentOccurrences u w i j ∧
        List.ofFn (wordFactor u (j - i) i) ≠ r

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => true) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨@mechanical_return_variation, bad, ?_⟩
    intro h
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    have h0 : 0 < Real.sqrt 2 - 1 := by nlinarith
    have h1 : Real.sqrt 2 - 1 < 1 := by nlinarith
    have hi : Irrational (Real.sqrt 2 - 1) := by
      simpa using irrational_sqrt_two.sub_ratCast 1
    obtain ⟨i, j, hadj, hne⟩ := h (rho := 0) h0 h1 hi 0 Fin.elim0
      ⟨0, Subsingleton.elim _ _⟩ [true]
    have hj : j = i + 1 := by
      have hij := hadj.1
      by_contra he
      exact hadj.2.2.2 (i + 1) (by omega) (by omega) (Subsingleton.elim _ _)
    simp [bad, realize, wordFactor, hj, List.ofFn_succ] at hne
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · intro h
        have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have hs0 := Real.sqrt_nonneg (2 : ℝ)
        have h0 : 0 < Real.sqrt 2 - 1 := by nlinarith
        have h1 : Real.sqrt 2 - 1 < 1 := by nlinarith
        have hi : Irrational (Real.sqrt 2 - 1) := by
          simpa using irrational_sqrt_two.sub_ratCast 1
        obtain ⟨a, b, hadj, hne⟩ := h (rho := 0) h0 h1 hi 0 Fin.elim0
          ⟨0, Subsingleton.elim _ _⟩ [true]
        have hb : b = a + 1 := by
          have hab := hadj.1
          by_contra he
          exact hadj.2.2.2 (a + 1) (by omega) (by omega) (Subsingleton.elim _ _)
        simp [bad, realize, wordFactor, hb, List.ofFn_succ] at hne
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1 / 3, 1 / 3, 0, ?_⟩
    intro heq
    have hf := congrFun heq 1
    norm_num [actual, realize, lowerMechanicalWord, lowerMechanicalLetter] at hf

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdRealization
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "value", "fn"]
    functionOperand := true }] }

register_information_theorem mechanical_return_variation in arena
  readout via
    (realize signature (fun _ alpha rho => lowerMechanicalWord alpha rho) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdRealization
