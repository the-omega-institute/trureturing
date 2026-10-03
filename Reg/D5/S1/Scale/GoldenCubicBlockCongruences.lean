import D5.S1.Scale.GoldenCubicBlockCongruences
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Scale.GoldenCubicBlockCongruences

open _root_.D5.S1.Scale
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j : ℕ), 1 ≤ j →
    (((r.readout () () j : ℤ) : ZMod 72)) = 4 ∧
      padicValInt 2 (goldenLucas (3 ^ j)) = 2 ∧
      (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 9)) = 1 ∧
      (((goldenLucas (3 ^ j) ^ 2 : ℤ) : ZMod 5)) = 1 ∧
      (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 80)) = 19 ∧
      goldenLucas (3 ^ (j + 1)) =
        goldenLucas (3 ^ j) * (goldenLucas (3 ^ j) ^ 2 + 3)

def registration : Registration arena
    (∀ (j : ℕ), 1 ≤ j →
      ((goldenLucas (3 ^ j) : ℤ) : ZMod 72) = 4 ∧
        padicValInt 2 (goldenLucas (3 ^ j)) = 2 ∧
        (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 9)) = 1 ∧
        (((goldenLucas (3 ^ j) ^ 2 : ℤ) : ZMod 5)) = 1 ∧
        (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 80)) = 19 ∧
        goldenLucas (3 ^ (j + 1)) =
          goldenLucas (3 ^ j) * (goldenLucas (3 ^ j) ^ 2 + 3)) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨golden_cubic_lucas_block, rejected, ?_⟩
    intro h
    have hbad := (h 1 (by omega)).1
    change ((0 : ℤ) : ZMod 72) = 4 at hbad
    exact (by decide : (0 : ZMod 72) ≠ 4) hbad
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hbad := (h 1 (by omega)).1
        change ((0 : ℤ) : ZMod 72) = 4 at hbad
        exact (by decide : (0 : ZMod 72) ≠ 4) hbad
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas (3 ^ (0 : ℕ)) ≠ goldenLucas (3 ^ (1 : ℕ))
    norm_num [actual, realize, goldenLucas, D5.S0.Carrier.trace,
      D5.S0.Carrier.phi, pow_succ]

register_information_theorem _root_.D5.S1.Scale.golden_cubic_lucas_block in arena
  readout via (realize signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Scale.GoldenCubicBlockCongruences
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

abbrev fibonacciSignature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def fibonacciActual : Realization fibonacciSignature :=
  realize fibonacciSignature (fun _ _ (j : ℕ) => Nat.fib (3 ^ j))
    (fun e => nomatch e)

def fibonacciRejected : Realization fibonacciSignature :=
  realize fibonacciSignature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

def fibonacciArena : Arena where
  signature := fibonacciSignature
  Law r := ∀ (j : ℕ), 1 ≤ j →
    ((r.readout () () j : ℕ) : ZMod 4) = 2 ∧
      padicValNat 2 (Nat.fib (3 ^ j)) = 1 ∧
      (Nat.fib (3 ^ (j + 1)) : ℤ) =
        (Nat.fib (3 ^ j) : ℤ) * (goldenLucas (3 ^ j) ^ 2 + 1)

def fibonacciRegistration : Registration fibonacciArena
    (∀ (j : ℕ), 1 ≤ j →
      ((Nat.fib (3 ^ j) : ℕ) : ZMod 4) = 2 ∧
        padicValNat 2 (Nat.fib (3 ^ j)) = 1 ∧
        (Nat.fib (3 ^ (j + 1)) : ℤ) =
          (Nat.fib (3 ^ j) : ℤ) * (goldenLucas (3 ^ j) ^ 2 + 1)) where
  actual := fibonacciActual
  bridge := Iff.rfl
  variation := by
    refine ⟨golden_cubic_fibonacci_block, fibonacciRejected, ?_⟩
    intro h
    have hbad := (h 1 (by omega)).1
    change ((0 : ℕ) : ZMod 4) = 2 at hbad
    exact (by decide : (0 : ZMod 4) ≠ 2) hbad
  sensitivity := by
    constructor
    · intro i
      refine ⟨fibonacciRejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hbad := (h 1 (by omega)).1
        change ((0 : ℕ) : ZMod 4) = 2 at hbad
        exact (by decide : (0 : ZMod 4) ≠ 2) hbad
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change Nat.fib (3 ^ (0 : ℕ)) ≠ Nat.fib (3 ^ (1 : ℕ))
    decide

register_information_theorem _root_.D5.S1.Scale.golden_cubic_fibonacci_block
  in fibonacciArena
  readout via (realize fibonacciSignature
    (fun _ _ (j : ℕ) => Nat.fib (3 ^ j)) (fun e => nomatch e))
  realizes fibonacciRegistration
  escape from source ({
    owner := `D5.S1.Scale.GoldenCubicBlockCongruences
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

def interlevelRejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

def interlevelArena : Arena where
  signature := signature
  Law r := ∀ (i j : ℕ), 1 ≤ i → i < j →
    (r.readout () () j ^ 2 + 3) %
      ((goldenLucas (3 ^ i) ^ 2 + 3) ^ 2) = 3

def interlevelRegistration : Registration interlevelArena
    (∀ (i j : ℕ), 1 ≤ i → i < j →
      (goldenLucas (3 ^ j) ^ 2 + 3) %
        ((goldenLucas (3 ^ i) ^ 2 + 3) ^ 2) = 3) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨golden_cubic_block_interlevel, interlevelRejected, ?_⟩
    intro h
    have hbad := h 1 2 (by omega) (by omega)
    change ((1 : ℤ) ^ 2 + 3) %
      ((goldenLucas (3 ^ (1 : ℕ)) ^ 2 + 3) ^ 2) = 3 at hbad
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ] at hbad
  sensitivity := by
    constructor
    · intro i
      refine ⟨interlevelRejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hbad := h 1 2 (by omega) (by omega)
        change ((1 : ℤ) ^ 2 + 3) %
          ((goldenLucas (3 ^ (1 : ℕ)) ^ 2 + 3) ^ 2) = 3 at hbad
        norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi,
          pow_succ] at hbad
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas (3 ^ (0 : ℕ)) ≠ goldenLucas (3 ^ (1 : ℕ))
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]

register_information_theorem _root_.D5.S1.Scale.golden_cubic_block_interlevel
  in interlevelArena
  readout via (realize signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e))
  realizes interlevelRegistration
  escape from source ({
    owner := `D5.S1.Scale.GoldenCubicBlockCongruences
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

def productArena : Arena where
  signature := signature
  Law r := ∀ (j : ℕ), 1 ≤ j →
    r.readout () () j =
      4 * ∏ i ∈ Finset.Ico 1 j, (goldenLucas (3 ^ i) ^ 2 + 3)

def productRegistration : Registration productArena
    (∀ (j : ℕ), 1 ≤ j →
      goldenLucas (3 ^ j) =
        4 * ∏ i ∈ Finset.Ico 1 j, (goldenLucas (3 ^ i) ^ 2 + 3)) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨golden_cubic_block_product, rejected, ?_⟩
    intro h
    have hbad := h 1 (by omega)
    change (0 : ℤ) = 4 * ∏ i ∈ Finset.Ico 1 1,
      (goldenLucas (3 ^ i) ^ 2 + 3) at hbad
    norm_num at hbad
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hbad := h 1 (by omega)
        change (0 : ℤ) = 4 * ∏ i ∈ Finset.Ico 1 1,
          (goldenLucas (3 ^ i) ^ 2 + 3) at hbad
        norm_num at hbad
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas (3 ^ (0 : ℕ)) ≠ goldenLucas (3 ^ (1 : ℕ))
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]

register_information_theorem _root_.D5.S1.Scale.golden_cubic_block_product
  in productArena
  readout via (realize signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e))
  realizes productRegistration
  escape from source ({
    owner := `D5.S1.Scale.GoldenCubicBlockCongruences
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S1.Scale.GoldenCubicBlockCongruences
