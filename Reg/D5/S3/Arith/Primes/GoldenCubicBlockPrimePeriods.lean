import D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods

open scoped Matrix
open _root_.D5.S0.Carrier _root_.D5.S1.Scale
open _root_.D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      r.readout () () j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hdiv : (19 : ℤ) ∣ goldenLucas (3 ^ 1) ^ 2 + 3 := by
    norm_num [goldenLucas, trace, D5.S0.Carrier.phi, pow_succ]
  have hgood := cubic_block_b_prime_period 1 19 (by decide) (by decide) hdiv
  have hbad := h 1 19 (by decide) (by decide) hdiv
  change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 19)) =
    2 * 3 ^ (1 + 1) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpB : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3),
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        2 * 3 ^ (j + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_block_b_prime_period, rejected, rejected_law⟩
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
  _root_.D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods.cubic_block_b_prime_period
  in arena
  readout via (realize signature (fun _ _ j => 2 * 3 ^ (j + 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end B

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
  realize signature (fun _ _ j => 4 * 3 ^ (j + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ j => 4 * 3 ^ (j + 1) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpC : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1),
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      r.readout () () j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hdiv : (17 : ℤ) ∣ goldenLucas (3 ^ 1) ^ 2 + 1 := by
    norm_num [goldenLucas, trace, D5.S0.Carrier.phi, pow_succ]
  have hgood := cubic_block_c_prime_period 1 17 (by decide) (by decide) hdiv
  have hbad := h 1 17 (by decide) (by decide) hdiv
  change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 17)) =
    4 * 3 ^ (1 + 1) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpC : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1),
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        4 * 3 ^ (j + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_block_c_prime_period, rejected, rejected_law⟩
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
    change 4 * 3 ^ (1 + 1) ≠ 4 * 3 ^ (2 + 1)
    norm_num

register_information_theorem
  _root_.D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods.cubic_block_c_prime_period
  in arena
  readout via (realize signature (fun _ _ j => 4 * 3 ^ (j + 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end C

end Reg.D5.S3.Arith.Primes.GoldenCubicBlockPrimePeriods
