import D5.S1.Recurrence.Invariants.CloitreActualSpineCarry
import Reg.Support.DependentFamily

open _root_.D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open _root_.D5.S1.Recurrence.Invariants.CloitreActualEndpointPhase
open _root_.D5.S1.Recurrence.Invariants.CloitreActualSpineCarry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Recurrence.Invariants.CloitreActualSpineCarry

local notation "F" => Nat.fib
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => totalCarry (actualTree n)) (fun e => nomatch e)

def sourceStatement : Prop := ∀ U : ℕ → ℕ, Hyp21_1 U →
(∀ n : ℕ, 1 ≤ n → totalCarry (actualTree n) = (canonicalDefect n : ℤ)) ∧
    ∀ t k : ℕ, 1 ≤ t → threshold t ≤ k →
      (∀ j : ℕ, threshold t ≤ j → SplitFacts t j ∧ CongruenceControl t j) ∧
      ∃ L : ℕ,
        0 < L ∧ rank t k L < threshold t ∧
        (rank t k L = threshold t - 1 ∨ rank t k L = threshold t - 2) ∧
        (∀ i : ℕ, i < L → threshold t ≤ rank t k i ∧
          rank t k (i + 1) = rank t k i - stepSize t (rank t k i) ∧
          (stepSize t (rank t k i) = 1 ∨ stepSize t (rank t k i) = 2)) ∧
        (∀ i : ℕ, i ≤ L →
          subtreeAt (actualTree (F k + t)) (address t k i) =
            some (actualTree (F (rank t k i) + t))) ∧
        (∀ i : ℕ, i < L →
          subtreeAt (actualTree (F k + t))
              (address t k i ++ [!(retainedBit t (rank t k i))]) =
            some (actualTree (F (anchorRank t (rank t k i)))) ∧
          totalCarry (actualTree (F (anchorRank t (rank t k i)))) = 0 ∧
          totalCarry (actualTree (F (rank t k i) + t)) =
            totalCarry (actualTree (F (rank t k (i + 1)) + t))) ∧
        canonicalDefect (F (rank t k L) + t) = widthDefect t ∧
        totalCarry (actualTree (F k + t)) =
          totalCarry (actualTree (F (rank t k L) + t)) ∧
        totalCarry (actualTree (F (rank t k L) + t)) = (widthDefect t : ℤ)

def arena : Arena where
  signature := signature
  Law R := ∀ U : ℕ → ℕ, Hyp21_1 U →
(∀ n : ℕ, 1 ≤ n → R.readout () () n = (canonicalDefect n : ℤ)) ∧
    ∀ t k : ℕ, 1 ≤ t → threshold t ≤ k →
      (∀ j : ℕ, threshold t ≤ j → SplitFacts t j ∧ CongruenceControl t j) ∧
      ∃ L : ℕ,
        0 < L ∧ rank t k L < threshold t ∧
        (rank t k L = threshold t - 1 ∨ rank t k L = threshold t - 2) ∧
        (∀ i : ℕ, i < L → threshold t ≤ rank t k i ∧
          rank t k (i + 1) = rank t k i - stepSize t (rank t k i) ∧
          (stepSize t (rank t k i) = 1 ∨ stepSize t (rank t k i) = 2)) ∧
        (∀ i : ℕ, i ≤ L →
          subtreeAt (actualTree (F k + t)) (address t k i) =
            some (actualTree (F (rank t k i) + t))) ∧
        (∀ i : ℕ, i < L →
          subtreeAt (actualTree (F k + t))
              (address t k i ++ [!(retainedBit t (rank t k i))]) =
            some (actualTree (F (anchorRank t (rank t k i)))) ∧
          R.readout () () (F (anchorRank t (rank t k i))) = 0 ∧
          R.readout () () (F (rank t k i) + t) =
            R.readout () () (F (rank t k (i + 1)) + t)) ∧
        canonicalDefect (F (rank t k L) + t) = widthDefect t ∧
        R.readout () () (F k + t) =
          R.readout () () (F (rank t k L) + t) ∧
        R.readout () () (F (rank t k L) + t) = (widthDefect t : ℤ)

theorem source_bridge : sourceStatement ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := by
  intro U h
  exact full22_2 U h

/-- A negative law on the complete conditional source entails an inhabitant
of its unchanged premise bundle; no such inhabitant is supplied here. -/
theorem variation_requires_hyp_inhabitant (hv : Variation arena actual) :
    ∃ U : ℕ → ℕ, Hyp21_1 U := by
  classical
  obtain ⟨bad, hbad⟩ := hv.2
  by_contra hn
  apply hbad
  intro U h
  exact False.elim (hn ⟨U, h⟩)

#print axioms source_bridge
#print axioms actual_positive
#print axioms variation_requires_hyp_inhabitant


end
end Reg.D5.S1.Recurrence.Invariants.CloitreActualSpineCarry
