import D5.S1.Digit.ZeckendorfContextualReplacement
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Conventions
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.ZeckendorfContextualReplacement
open D5.S1.Digit.GoldenBase4IntervalMachine

namespace Reg.D5.S1.Digit.ZeckendorfContextualReplacement
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ H : ℕ, List (Fin 2)
  State := fun _ => List (Fin 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (Fin 2) → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p u => residual (Nat.fib p.1) (p.2 ++ B1 ++ u)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ) (p u : List (Fin 2)), 14 ≤ H → 14 + u.length ≤ H →
    NoAdjacentOnes (p ++ B1 ++ u) →
    R.readout () ⟨H, p⟩ u = residual (Nat.fib H) (p ++ B0 ++ u)

def rejected : Realization signature := realize signature
  (fun _ _ _ => fun _ => some false) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 14 [] [] (by norm_num) (by norm_num)
    (by norm_num [NoAdjacentOnes, List.isChain_cons_cons, B1])
  have hv : value B0 = 196 := by
    norm_num [value, fibPair, Nat.fib, B0]
  have hw : wdigits 573 = [14, 12, 9, 7, 5] := by
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]
  have hres : D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) B0 [] = some true := by
    simp only [D5.S1.Digit.ZeckendorfRawWindow.residual, List.append_nil, parity]
    rw [show Nat.fib 14 = 377 by norm_num, hv, hw]
    norm_num [B0, NoAdjacentOnes, List.isChain_cons_cons, value, fibPair]
  have hthis := congrFun hh []
  have hfalse : (some false : Option Bool) =
      D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) B0 [] := by
    simpa [rejected, realize, List.append_nil] using hthis
  rw [hres] at hfalse
  cases hfalse

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨contextual_replacement, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨14, []⟩, [], [0], ?_⟩
    intro he
    have hh := congrFun he []
    have hv0 : value B1 = 225 := by
      norm_num [value, fibPair, Nat.fib, B1]
    have hv1 : value (B1 ++ [0]) = 364 := by
      norm_num [value, fibPair, Nat.fib, B1]
    have hw0 : wdigits 602 = [14, 12, 10, 8, 5] := by
      symm
      apply wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]
    have hw1 : wdigits 741 = [15, 11, 9, 6] := by
      symm
      apply wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]
    have h0 : D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) B1 [] = some true := by
      simp only [D5.S1.Digit.ZeckendorfRawWindow.residual, List.append_nil, parity]
      rw [show Nat.fib 14 = 377 by norm_num, hv0, hw0]
      norm_num [B1, NoAdjacentOnes, List.isChain_cons_cons, value, fibPair]
    have h1 : D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) (B1 ++ [0]) [] = some false := by
      simp only [D5.S1.Digit.ZeckendorfRawWindow.residual, List.append_nil, parity]
      rw [show Nat.fib 14 = 377 by norm_num, hv1, hw1]
      norm_num [B1, NoAdjacentOnes, List.isChain_cons_cons, value, fibPair]
    have hh' : D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) B1 [] =
        D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib 14) (B1 ++ [0]) [] := by
      simpa [actual, realize, List.append_nil, List.nil_append] using hh
    rw [h0, h1] at hh'
    cases hh'

register_information_theorem contextual_replacement in arena
  readout via (realize signature
    (fun _ p u => residual (Nat.fib p.1) (p.2 ++ B1 ++ u)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Digit.ZeckendorfContextualReplacement
    coordinates := #[0, 1]
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 2}]})
  escape continues (open)

#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfContextualReplacement
