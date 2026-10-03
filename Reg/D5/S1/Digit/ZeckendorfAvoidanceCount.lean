import D5.S1.Digit.ZeckendorfAvoidanceCount
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.ZeckendorfAvoidanceCount
open D5.S1.Digit.ZeckendorfContextualReplacement

namespace Reg.D5.S1.Digit.ZeckendorfAvoidanceCount
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ H => ((legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))).length)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ H : ℕ, (R.readout () () H : ℝ) ≤
    Real.goldenRatio ^ (H + 1) *
      (1 - (Real.goldenRatio ^ (14 : ℕ))⁻¹) ^ (H / 14)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 2) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  have hphi : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  simp [rejected,realize] at hh
  linarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_avoidance_count,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    have avoid (w : List (Fin 2)) (hl : w.length ≤ 1) : ¬ B1 <:+: w := by
      intro h
      have hh := h.length_le
      norm_num [B1] at hh
      omega
    norm_num [actual,realize,legalWords,avoid [] (by simp),
      avoid [0] (by simp),avoid [1] (by simp)]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Digit.ZeckendorfAvoidanceCount
  coordinates := #[]
  readouts := #[{path := #["body","fn","arg","arg"], stateOperand := some #["arg","arg","fn","arg"]}] }

register_information_theorem uniform_avoidance_count in arena
  readout via (realize signature
    (fun _ _ H => ((legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))).length)
    (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfAvoidanceCount
