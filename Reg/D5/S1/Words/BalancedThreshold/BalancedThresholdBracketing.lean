/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdBracketing
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdBracketing
   mirror-E: none(waiver:source-bound-return-error-product)
   anchors: []
   utility: none
   digest: Return bracketing is registered at the product of its two physical discrepancies. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdBracketing
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold D5.S1.Words.Mechanical D5.S1.Words.Complexity
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdBracketing
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x * y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 → Irrational alpha →
    ∀ {n : ℕ} (w : Fin n → Bool), BispecialFactor (lowerMechanicalWord alpha alpha) w →
    let u := lowerMechanicalWord alpha alpha
    ∀ i j a b : ℕ, AdjacentOccurrences u w i j → AdjacentOccurrences u w a b →
      List.ofFn (wordFactor u (j - i) i) ≠ List.ofFn (wordFactor u (b - a) a) →
      R.readout () () ((lowerMechanicalWindowTrueCount alpha alpha i (j - i) : ℝ) -
        alpha * (j - i : ℕ))
      ((lowerMechanicalWindowTrueCount alpha alpha a (b - a) : ℝ) -
        alpha * (b - a : ℕ)) < 0

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨@mechanical_return_bracketing, bad, ?_⟩
    intro h
    let alpha := Real.sqrt 2 - 1
    let u := lowerMechanicalWord alpha alpha
    let w : Fin 0 → Bool := Fin.elim0
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    have hlo : 2 / 5 < alpha := by dsimp [alpha]; nlinarith
    have hhi : alpha < 3 / 7 := by dsimp [alpha]; nlinarith
    have hai : Irrational alpha := by
      simpa [alpha] using irrational_sqrt_two.sub_ratCast 1
    have letters : u 0 = false ∧ u 1 = true := by
      have hf1 : ⌊alpha⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
      have hf2 : ⌊2 * alpha⌋ = (0 : ℤ) :=
        Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
      have hf3 : ⌊3 * alpha⌋ = (1 : ℤ) :=
        Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
      have he2 : alpha + alpha = 2 * alpha := by ring
      have he3 : alpha + 2 * alpha = 3 * alpha := by ring
      norm_num [u, lowerMechanicalWord, lowerMechanicalLetter, he2, he3, hf1, hf2, hf3]
    have empty : ∀ i, wordFactor u 0 i = w := fun _ => Subsingleton.elim _ _
    have hw : BispecialFactor u w := by
      constructor
      · refine ⟨1, 2, by omega, by omega, empty 1, empty 2, ?_⟩
        norm_num [letters]
      · refine ⟨0, 1, empty 0, empty 1, ?_⟩
        norm_num [letters]
    have adj : ∀ a, AdjacentOccurrences u w a (a + 1) := by
      intro a
      exact ⟨by omega, empty a, empty (a + 1), by intro k hk hk'; omega⟩
    have ne : List.ofFn (wordFactor u 1 0) ≠ List.ofFn (wordFactor u 1 1) := by
      simp [List.ofFn_succ, wordFactor, letters]
    have impossible := h (by linarith : 0 < alpha) (by linarith : alpha < 1) hai w hw
      0 1 1 2 (adj 0) (adj 1) ne
    norm_num [bad, realize] at impossible
  sensitivity := by
    have refute : ¬ arena.Law bad := by
      intro h
      let alpha := Real.sqrt 2 - 1
      let u := lowerMechanicalWord alpha alpha
      let w : Fin 0 → Bool := Fin.elim0
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hs0 := Real.sqrt_nonneg (2 : ℝ)
      have hlo : 2 / 5 < alpha := by dsimp [alpha]; nlinarith
      have hhi : alpha < 3 / 7 := by dsimp [alpha]; nlinarith
      have hai : Irrational alpha := by
        simpa [alpha] using irrational_sqrt_two.sub_ratCast 1
      have letters : u 0 = false ∧ u 1 = true := by
        have hf1 : ⌊alpha⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
        have hf2 : ⌊2 * alpha⌋ = (0 : ℤ) :=
          Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
        have hf3 : ⌊3 * alpha⌋ = (1 : ℤ) :=
          Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
        have he2 : alpha + alpha = 2 * alpha := by ring
        have he3 : alpha + 2 * alpha = 3 * alpha := by ring
        norm_num [u, lowerMechanicalWord, lowerMechanicalLetter, he2, he3, hf1, hf2, hf3]
      have empty : ∀ i, wordFactor u 0 i = w := fun _ => Subsingleton.elim _ _
      have hw : BispecialFactor u w := by
        constructor
        · refine ⟨1, 2, by omega, by omega, empty 1, empty 2, ?_⟩
          norm_num [letters]
        · refine ⟨0, 1, empty 0, empty 1, ?_⟩
          norm_num [letters]
      have adj : ∀ a, AdjacentOccurrences u w a (a + 1) := by
        intro a
        exact ⟨by omega, empty a, empty (a + 1), by intro k hk hk'; omega⟩
      have ne : List.ofFn (wordFactor u 1 0) ≠ List.ofFn (wordFactor u 1 1) := by
        simp [List.ofFn_succ, wordFactor, letters]
      have impossible := h (by linarith : 0 < alpha) (by linarith : alpha < 1) hai w hw
        0 1 1 2 (adj 0) (adj 1) ne
      norm_num [bad, realize] at impossible
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, refute⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hf := congrFun he 1
    norm_num [actual, realize] at hf

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdBracketing
  coordinates := #[]
  readouts := #[{
    path := #[
      "body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "body",
      "fn", "arg", "fn", "fn"]
    functionOperand := true }] }

register_information_theorem mechanical_return_bracketing in arena
  readout via
    (realize signature (fun _ _ x y => x * y) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdBracketing
