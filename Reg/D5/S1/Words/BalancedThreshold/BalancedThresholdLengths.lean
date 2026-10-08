/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdLengths
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdLengths
   mirror-E: none(waiver:source-bound-positive-continuant-length)
   anchors: []
   utility: none
   digest: Total continuant growth is registered at its original positive-length addition. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdLengths
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdLengths
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
  realize signature (fun _ _ x y => x + y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : ℕ, 5 ≤ t →
    let g := GenContFract.of (uniformSlope t / (1 - uniformSlope t))
    ∀ n, 0 < R.readout () () (g.contsAux n).a (g.contsAux n).b ∧
      (1 ≤ n → (g.contsAux n).a + (g.contsAux n).b <
        (g.contsAux (n + 1)).a + (g.contsAux (n + 1)).b)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨uniform_continuant_length_growth, bad, ?_⟩
    intro h
    have impossible := (h 5 (by norm_num) 0).1
    norm_num [bad, realize] at impossible
  sensitivity := by
    have refute : ¬ arena.Law bad := by
      intro h
      have impossible := (h 5 (by norm_num) 0).1
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
    have hf := congrFun he 0
    norm_num [actual, realize] at hf

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdLengths
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn"]
    functionOperand := true }] }

register_information_theorem uniform_continuant_length_growth in arena
  readout via
    (realize signature (fun _ _ x y => x + y) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdLengths
