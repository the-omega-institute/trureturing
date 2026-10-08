/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdDescent
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdDescent
   mirror-E: none(waiver:source-bound-bispecial-descent)
   anchors: []
   utility: none
   digest: Bispecial descent is registered at the characteristic mechanical-word operand. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdDescent
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold D5.S1.Words.Mechanical D5.S1.Words.Complexity
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdDescent
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
  Law R := ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 / 2 → ∀ {n : ℕ}, 0 < n →
    ∀ (w : Fin n → Bool), BispecialFactor (lowerMechanicalWord alpha alpha) w →
    let theta := alpha / (1 - alpha)
    let u := R.readout () alpha alpha
    let v := lowerMechanicalWord theta theta
    let pos := Nat.nth (fun i => u i = false)
    ∃ (m : ℕ) (z : Fin m → Bool), m < n ∧ BispecialFactor v z ∧
      List.ofFn w = (List.ofFn z).flatMap
        (fun b => if b then [false, true] else [false]) ++ [false] ∧
      (∀ i, wordFactor u n i = w ↔ ∃ k, pos k = i ∧ wordFactor v m k = z) ∧
      ∀ k, wordFactor v m k = z → pos (k + m) + 1 = pos k + n

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => true) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨@mechanical_bispecial_descent, bad, ?_⟩
    intro h
    let w : Fin 1 → Bool := fun _ => false
    have hw : BispecialFactor (lowerMechanicalWord (1 / 3) (1 / 3)) w := by
      refine ⟨⟨2, 3, by omega, by omega, ?_, ?_, ?_⟩, ⟨0, 2, ?_, ?_, ?_⟩⟩
      all_goals first
        | (funext r; fin_cases r;
            norm_num [w, wordFactor, lowerMechanicalWord, lowerMechanicalLetter])
        | norm_num [lowerMechanicalWord, lowerMechanicalLetter]
    obtain ⟨m, z, hm, _, _, ho, _⟩ :=
      h (alpha := 1 / 3) (by norm_num) (by norm_num) (by omega) w hw
    have hm0 : m = 0 := by omega
    subst m
    have hf := (ho 0).mpr ⟨0, by simp [bad, realize], Subsingleton.elim _ _⟩
    have hh := congrFun hf (0 : Fin 1)
    norm_num [bad, realize, wordFactor, w] at hh
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · intro h
        let w : Fin 1 → Bool := fun _ => false
        have hw : BispecialFactor (lowerMechanicalWord (1 / 3) (1 / 3)) w := by
          refine ⟨⟨2, 3, by omega, by omega, ?_, ?_, ?_⟩, ⟨0, 2, ?_, ?_, ?_⟩⟩
          all_goals first
            | (funext r; fin_cases r;
                norm_num [w, wordFactor, lowerMechanicalWord, lowerMechanicalLetter])
            | norm_num [lowerMechanicalWord, lowerMechanicalLetter]
        obtain ⟨m, z, hm, _, _, ho, _⟩ :=
          h (alpha := 1 / 3) (by norm_num) (by norm_num) (by omega) w hw
        have hm0 : m = 0 := by omega
        subst m
        have hf := (ho 0).mpr ⟨0, by simp [bad, realize], Subsingleton.elim _ _⟩
        have hh := congrFun hf (0 : Fin 1)
        norm_num [bad, realize, wordFactor, w] at hh
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1 / 3, 1 / 3, 0, ?_⟩
    intro heq
    have hf := congrFun heq 1
    norm_num [actual, realize, lowerMechanicalWord, lowerMechanicalLetter] at hf

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdDescent
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "value", "fn"]
    functionOperand := true }] }

register_information_theorem mechanical_bispecial_descent in arena
  readout via
    (realize signature (fun _ alpha rho => lowerMechanicalWord alpha rho) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdDescent
