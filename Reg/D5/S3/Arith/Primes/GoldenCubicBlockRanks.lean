import D5.S3.Arith.Primes.GoldenCubicBlockRanks
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks

open _root_.D5.S1.Scale
open _root_.D5.S0.Carrier
open _root_.D5.S3.Arith.Primes.GoldenCubicBlockRanks
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace C

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => 3 ^ (j + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ j => 3 ^ (j + 1) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpC : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1),
    fibonacciRank p = r.readout () () j ∧
      padicValInt p (goldenLucas (3 ^ j) ^ 2 + 1) =
        padicValNat p (Nat.fib (fibonacciRank p))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hdiv : (17 : ℤ) ∣ goldenLucas (3 ^ 1) ^ 2 + 1 := by
    norm_num [goldenLucas, trace, D5.S0.Carrier.phi, pow_succ]
  have hgood := (cubic_block_c_prime_rank 1 17 (by decide) (by decide) hdiv).1
  have hbad := (h 1 17 (by decide) (by decide) hdiv).1
  change fibonacciRank 17 = 3 ^ (1 + 1) at hgood
  change fibonacciRank 17 = 3 ^ (1 + 1) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpC : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1),
      fibonacciRank p = 3 ^ (j + 1) ∧
        padicValInt p (goldenLucas (3 ^ j) ^ 2 + 1) =
          padicValNat p (Nat.fib (fibonacciRank p))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_block_c_prime_rank, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change 3 ^ (1 + 1) ≠ 3 ^ (2 + 1)
    norm_num

register_information_theorem
  _root_.D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_c_prime_rank
  in arena
  readout via (realize signature (fun _ _ j => 3 ^ (j + 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end C

namespace B

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => 2 * 3 ^ (j + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ j => 2 * 3 ^ (j + 1) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpB : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3),
    fibonacciRank p = r.readout () () j ∧
      @legendreSym p ⟨_hp⟩ 5 = 1 ∧
      padicValInt p (goldenLucas (3 ^ j) ^ 2 + 3) =
        padicValNat p (Nat.fib (fibonacciRank p))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hdiv : (19 : ℤ) ∣ goldenLucas (3 ^ 1) ^ 2 + 3 := by
    norm_num [goldenLucas, trace, D5.S0.Carrier.phi, pow_succ]
  have hgood := (cubic_block_b_prime_rank 1 19 (by decide) (by decide) hdiv).1
  have hbad := (h 1 19 (by decide) (by decide) hdiv).1
  change fibonacciRank 19 = 2 * 3 ^ (1 + 1) at hgood
  change fibonacciRank 19 = 2 * 3 ^ (1 + 1) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpB : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3),
      fibonacciRank p = 2 * 3 ^ (j + 1) ∧
        @legendreSym p ⟨_hp⟩ 5 = 1 ∧
        padicValInt p (goldenLucas (3 ^ j) ^ 2 + 3) =
          padicValNat p (Nat.fib (fibonacciRank p))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_block_b_prime_rank, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change 2 * 3 ^ (1 + 1) ≠ 2 * 3 ^ (2 + 1)
    norm_num

register_information_theorem
  _root_.D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_b_prime_rank
  in arena
  readout via (realize signature (fun _ _ j => 2 * 3 ^ (j + 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end B

end Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks
