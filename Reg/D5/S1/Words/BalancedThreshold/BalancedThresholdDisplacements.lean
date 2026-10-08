/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdDisplacements
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdDisplacements
   mirror-E: none(waiver:source-bound-occurrence-displacement-counts)
   anchors: []
   utility: none
   digest: Unbounded displacement counts are registered at the physical mechanical source. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdDisplacements
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold D5.S1.Words.Mechanical D5.S1.Words.Complexity
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdDisplacements
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
  Law R := ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 → Irrational alpha →
    ∀ {n : ℕ} (w : Fin n → Bool), BispecialFactor (lowerMechanicalWord alpha alpha) w →
    ∃ r s : List Bool,
      0 < r.length ∧ 0 < s.length ∧
      (r.count true * s.count false + 1 = s.count true * r.count false ∨
        s.count true * r.count false + 1 = r.count true * s.count false) ∧
      (∀ b, r.count b + s.count b = (List.ofFn w).count b + 1) ∧
      ∀ i j, i < j → wordFactor (lowerMechanicalWord alpha alpha) n i = w →
        wordFactor (lowerMechanicalWord alpha alpha) n j = w →
        ∃ k l : ℕ, 0 < k + l ∧
          (∀ b, (List.ofFn (wordFactor (R.readout () alpha alpha)
            (j - i) i)).count b = k * r.count b + l * s.count b) ∧
          |(k : ℝ) * ((r.count true : ℝ) - alpha * r.length) +
            (l : ℝ) * ((s.count true : ℝ) - alpha * s.length)| < 1

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => true) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨@mechanical_return_displacements, bad, ?_⟩
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
      have hfl1 : ⌊alpha⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
      have hfl2 : ⌊2 * alpha⌋ = (0 : ℤ) :=
        Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
      have hfl3 : ⌊3 * alpha⌋ = (1 : ℤ) := by
        apply Int.floor_eq_iff.mpr
        norm_num
        constructor <;> linarith
      have he2 : alpha + alpha = 2 * alpha := by ring
      have he3 : alpha + 2 * alpha = 3 * alpha := by ring
      norm_num [u, lowerMechanicalWord, lowerMechanicalLetter, he2, he3,
        hfl1, hfl2, hfl3]
    have hw : BispecialFactor u w := by
      refine ⟨⟨1, 2, by omega, by omega, Subsingleton.elim _ _,
        Subsingleton.elim _ _, ?_⟩,
        ⟨0, 1, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩⟩
      all_goals norm_num [letters]
    obtain ⟨r, s, _, _, _, _, hall⟩ := h (by linarith) (by linarith) hai w hw
    obtain ⟨k, l, _, hc, herr⟩ := hall 0 4 (by omega)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    have hct : k * r.count true + l * s.count true = 4 := by
      simpa [bad, realize, wordFactor, List.ofFn_succ] using (hc true).symm
    have hcf : k * r.count false + l * s.count false = 0 := by
      simpa [bad, realize, wordFactor, List.ofFn_succ] using (hc false).symm
    have total : ∀ v : List Bool, v.count true + v.count false = v.length := by
      intro v
      induction v with
      | nil => simp
      | cons b v hv => cases b <;> simp_all <;> omega
    have hlen : k * r.length + l * s.length = 4 := by
      rw [← total r, ← total s]
      nlinarith only [hct, hcf]
    have hctR : (k : ℝ) * r.count true + (l : ℝ) * s.count true = 4 := by
      exact_mod_cast hct
    have hlenR : (k : ℝ) * r.length + (l : ℝ) * s.length = 4 := by
      exact_mod_cast hlen
    have he : (k : ℝ) * ((r.count true : ℝ) - alpha * r.length) +
        (l : ℝ) * ((s.count true : ℝ) - alpha * s.length) = 4 - 4 * alpha := by
      calc
        _ = ((k : ℝ) * r.count true + (l : ℝ) * s.count true) -
            alpha * ((k : ℝ) * r.length + (l : ℝ) * s.length) := by ring
        _ = 4 - 4 * alpha := by rw [hctR, hlenR]; ring
    rw [he, abs_lt] at herr
    linarith
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
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
        have hfl1 : ⌊alpha⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
        have hfl2 : ⌊2 * alpha⌋ = (0 : ℤ) :=
          Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
        have hfl3 : ⌊3 * alpha⌋ = (1 : ℤ) := by
          apply Int.floor_eq_iff.mpr
          norm_num
          constructor <;> linarith
        have he2 : alpha + alpha = 2 * alpha := by ring
        have he3 : alpha + 2 * alpha = 3 * alpha := by ring
        norm_num [u, lowerMechanicalWord, lowerMechanicalLetter, he2, he3,
          hfl1, hfl2, hfl3]
      have hw : BispecialFactor u w := by
        refine ⟨⟨1, 2, by omega, by omega, Subsingleton.elim _ _,
          Subsingleton.elim _ _, ?_⟩,
          ⟨0, 1, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩⟩
        all_goals norm_num [letters]
      obtain ⟨r, s, _, _, _, _, hall⟩ := h (by linarith) (by linarith) hai w hw
      obtain ⟨k, l, _, hc, herr⟩ := hall 0 4 (by omega)
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      have hct : k * r.count true + l * s.count true = 4 := by
        simpa [bad, realize, wordFactor, List.ofFn_succ] using (hc true).symm
      have hcf : k * r.count false + l * s.count false = 0 := by
        simpa [bad, realize, wordFactor, List.ofFn_succ] using (hc false).symm
      have total : ∀ v : List Bool, v.count true + v.count false = v.length := by
        intro v
        induction v with
        | nil => simp
        | cons b v hv => cases b <;> simp_all <;> omega
      have hlen : k * r.length + l * s.length = 4 := by
        rw [← total r, ← total s]
        nlinarith only [hct, hcf]
      have hctR : (k : ℝ) * r.count true + (l : ℝ) * s.count true = 4 := by
        exact_mod_cast hct
      have hlenR : (k : ℝ) * r.length + (l : ℝ) * s.length = 4 := by
        exact_mod_cast hlen
      have he : (k : ℝ) * ((r.count true : ℝ) - alpha * r.length) +
          (l : ℝ) * ((s.count true : ℝ) - alpha * s.length) = 4 - 4 * alpha := by
        calc
          _ = ((k : ℝ) * r.count true + (l : ℝ) * s.count true) -
              alpha * ((k : ℝ) * r.length + (l : ℝ) * s.length) := by ring
          _ = 4 - 4 * alpha := by rw [hctR, hlenR]; ring
      rw [he, abs_lt] at herr
      linarith
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1 / 3, 1 / 3, 0, ?_⟩
    intro heq
    have hf := congrFun heq 1
    norm_num [actual, realize, lowerMechanicalWord, lowerMechanicalLetter] at hf

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdDisplacements
  coordinates := #[0]
  readouts := #[{
    path := #[
      "body", "body", "body", "body", "body", "body", "body", "arg",
      "body", "arg", "body", "arg", "arg", "arg", "arg", "body",
      "body", "body", "body", "body", "arg", "body", "arg", "body",
      "arg", "fn", "arg", "body", "fn", "arg", "arg", "arg",
      "fn", "fn", "arg", "fn"]
    functionOperand := true }] }

register_information_theorem mechanical_return_displacements in arena
  readout via
    (realize signature (fun _ alpha rho => lowerMechanicalWord alpha rho) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdDisplacements
