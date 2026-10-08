/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdErrors
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdErrors
   mirror-E: none(waiver:source-bound-error-orbit-multiplication)
   anchors: []
   utility: none
   digest: The complete error orbit is registered at its original discrepancy multiplication. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdErrors
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdErrors
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
  Law R := ∀ t : ℕ, 5 ≤ t →
    let theta := uniformSlope t / (1 - uniformSlope t)
    let g := GenContFract.of theta
    let digit := fun n : ℕ =>
      (if n = 0 then t + 2 else if n = 1 then t
        else if n % 2 = 0 then t - 2 else t + 1 : ℕ)
    let tail := fun n : ℕ =>
      if n = 0 then 1 / ((t : ℝ) + quadraticTail t)
      else if n % 2 = 1 then quadraticTail t
      else 1 / ((t : ℝ) + 1 + quadraticTail t)
    ∀ n, 0 < tail n ∧ tail n < 1 ∧
      (g.contsAux (n + 1)).a - theta * (g.contsAux (n + 1)).b ≠ 0 ∧
      (g.contsAux n).a - theta * (g.contsAux n).b =
        R.readout () () (-((digit n : ℝ) + tail n))
          ((g.contsAux (n + 1)).a - theta * (g.contsAux (n + 1)).b)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨uniform_continuant_errors, bad, ?_⟩
    intro h
    have impossible := (h 5 (by norm_num) 0).2.2.2
    norm_num [bad, realize, GenContFract.contsAux] at impossible
  sensitivity := by
    have refute : ¬ arena.Law bad := by
      intro h
      have impossible := (h 5 (by norm_num) 0).2.2.2
      norm_num [bad, realize, GenContFract.contsAux] at impossible
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
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdErrors
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body",
      "arg", "arg", "arg", "arg", "fn", "fn"]
    functionOperand := true }] }

register_information_theorem uniform_continuant_errors in arena
  readout via
    (realize signature (fun _ _ x y => x * y) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdErrors
