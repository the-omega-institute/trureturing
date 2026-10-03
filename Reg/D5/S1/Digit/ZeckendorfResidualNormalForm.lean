import D5.S1.Digit.ZeckendorfResidualNormalForm
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.ZeckendorfResidualNormalForm
open D5.S1.Digit.ZeckendorfContextualReplacement

namespace Reg.D5.S1.Digit.ZeckendorfResidualNormalForm
noncomputable section
open Classical

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => List (Fin 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (Fin 2) → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ H w => _root_.D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib H) w)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ H, 14 ≤ H → ∀ w : List (Fin 2), NoAdjacentOnes w →
    ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧
      R.readout () H w = R.readout () H v ∧ ¬ B1 <:+: v.drop 7

def rejected : Realization signature := realize signature
  (fun _ _ w _ => some (decide (w.length = 0))) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v,hv,hl,he⟩ := h 14 le_rfl [] (by simp [NoAdjacentOnes])
  have ee := congrFun he.1 []
  have hvne : v ≠ [] := by intro h; subst v; simp at hl
  simp [rejected,realize,hvne] at ee

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨normalized_state_cover,rejected,rejected_law⟩
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
    refine ⟨0,[],[1],?_⟩
    intro he
    have ee := congrFun he []
    have h0 : D5.S0.Conventions.wdigits 0 = [] := by simp [D5.S0.Conventions.wdigits]
    have h1 : D5.S0.Conventions.wdigits 1 = [2] := by
      symm
      apply D5.S0.Conventions.wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]
    simpa [actual,realize,_root_.D5.S1.Digit.ZeckendorfRawWindow.residual,NoAdjacentOnes,value,
      D5.S1.Digit.GoldenBase4IntervalMachine.fibPair,parity,h0,h1] using ee

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Digit.ZeckendorfResidualNormalForm
  coordinates := #[0]
  readouts := #[{path := #["body","body","body","body","arg","body",
      "arg","arg","fn","arg","fn","arg"], stateOperand := some #["arg"]}] }

register_information_theorem normalized_state_cover in arena
  readout via (realize signature
    (fun _ H w => _root_.D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib H) w)
    (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfResidualNormalForm
