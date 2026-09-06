/- GID: D5/S1/Digit/GoldenZeckendorfLanguage
   generality: G
   mirror-B: D5/B/S1/Digit/GoldenZeckendorfLanguage
   mirror-E: none(waiver:arithmetic-language-bridge)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: Canonical dense MSD Zeckendorf words execute in the binary base. -/

import D5.S0.Automata.BinaryZeckendorfLanguage
import D5.S1.Digit.GoldenDFAOMinimalityTargets

/-! # Canonical Arithmetic Inputs Belong to the Base Language

The existing arithmetic oracle renders descending occupied Fibonacci indices
as dense MSD bits. This module transfers Mathlib's gap condition to bit
nonadjacency for every natural number, then proves successful execution for every
radix-four sparse input. It supplies the paper's missing bridge from arithmetic
representations to the successful language of the typed base.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenZeckendorfLanguage

open D5.S0.Conventions
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit.GoldenDFAOMinimalityTargets

/-- Canonical occupied Fibonacci indices never contain two consecutive numbers. -/
theorem canonical_indices_not_adjacent (l : List Nat) (h : l.IsZeckendorfRep)
    (k : Nat) : ¬ (k ∈ l ∧ k + 1 ∈ l) := by
  let : Trans (fun a b : Nat => b + 2 ≤ a)
      (fun a b => b + 2 ≤ a) (fun a b => b + 2 ≤ a) :=
    ⟨by intros; omega⟩
  have hp : l.Pairwise (fun a b => b + 2 ≤ a) := by
    exact (List.pairwise_append.mp (List.isChain_iff_pairwise.mp h)).1
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.pairwise_cons] at hp
    intro ⟨hk, hk1⟩
    simp only [List.mem_cons] at hk hk1
    rcases hk with rfl | hk
    · rcases hk1 with heq | hk1
      · omega
      · have := hp.1 _ hk1; omega
    · rcases hk1 with rfl | hk1
      · have := hp.1 _ hk; omega
      · exact ih (by
          unfold List.IsZeckendorfRep at h ⊢
          exact h.tail) hp.2 ⟨hk, hk1⟩

/-- Every dense canonical MSD word has no adjacent one bits, including zero. -/
theorem zeckendorfMSDWord_noAdjacentOnes (n : Nat) :
    NoAdjacentOnes (zeckendorfMSDWord n) := by
  unfold NoAdjacentOnes zeckendorfMSDWord
  rw [List.isChain_map, List.isChain_reverse, List.isChain_range]
  intro k _
  have h := canonical_indices_not_adjacent (wdigits n) (wdigits_isCanonical n) (k + 2)
  simp only [zeckendorfBit]
  split_ifs <;> simp_all

/-- The arithmetic generator executes successfully for every natural input. -/
theorem zeckendorfMSDWord_base_success (n : Nat) :
    ∃ state, binaryZeckendorfBase.eval (zeckendorfMSDWord n) = some state :=
  (base_success_iff_noAdjacentOnes _).mpr (zeckendorfMSDWord_noAdjacentOnes n)

/-- Every input of the actual radix-four sparse problem executes in its base. -/
theorem base4PowerWord_base_success (i : Nat) :
    ∃ state, base4Problem.base.eval (base4Problem.input i) = some state :=
  zeckendorfMSDWord_base_success (4 ^ i)

end D5.S1.Digit.GoldenZeckendorfLanguage
