/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdDesubstitution
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdDesubstitution
   mirror-E: none(waiver:source-bound-characteristic-reconstruction)
   anchors: []
   utility: none
   digest: The majority-rank reconstruction is registered at its mechanical-word operand. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdDesubstitution
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold D5.S1.Words.Mechanical D5.S1.Words.Complexity
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdDesubstitution
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
  Law R := ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 / 2 →
    let theta := alpha / (1 - alpha)
    let u := R.readout () alpha alpha
    let v := lowerMechanicalWord theta theta
    let pos := Nat.nth (fun n => u n = false)
    ∀ k : ℕ,
      pos k = k + (⌊((k + 1 : ℕ) : ℝ) * theta⌋).toNat ∧
      List.ofFn (wordFactor u (pos k) 0) =
        (List.range k).flatMap (fun r => if v r then [false, true] else [false])

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => false) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨fun h0 hh => mechanical_majority_desubstitution h0 hh, bad, ?_⟩
    intro h
    have hf := (h (alpha := 1 / 3) (by norm_num) (by norm_num) 1).1
    norm_num [bad, realize] at hf
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hf := (h (alpha := 1 / 3) (by norm_num) (by norm_num) 1).1
      norm_num [bad, realize] at hf
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
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdDesubstitution
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "value", "fn"]
    functionOperand := true }] }

register_information_theorem mechanical_majority_desubstitution in arena
  readout via
    (realize signature (fun _ alpha rho => lowerMechanicalWord alpha rho) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdDesubstitution
