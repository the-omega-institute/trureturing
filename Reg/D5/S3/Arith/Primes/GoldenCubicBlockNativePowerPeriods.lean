import D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods

open scoped Matrix
open _root_.D5.S1.Scale
open _root_.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p b =>
      let C := (goldenLucas (3 ^ p.1) ^ 2 + 1).natAbs
      let B := (goldenLucas (3 ^ p.1) ^ 2 + 3).natAbs
      4 * 3 ^ (p.1 + 1) * C ^ (p.2 - 1) * B ^ (b - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p b =>
      let C := (goldenLucas (3 ^ p.1) ^ 2 + 1).natAbs
      let B := (goldenLucas (3 ^ p.1) ^ 2 + 3).natAbs
      4 * 3 ^ (p.1 + 1) * C ^ (p.2 - 1) * B ^ (b - 1) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r :=
    let C := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 1).natAbs
    let B := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 3).natAbs
    let π := fun m : ℕ => orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (C i).Coprime (C j)) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (B i).Coprime (B j)) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → (C i).Coprime (B j)) ∧
    (∀ j a b : ℕ, 1 ≤ j → 1 ≤ a → 1 ≤ b →
      π (C j ^ a) = 4 * 3 ^ (j + 1) * C j ^ (a - 1) ∧
      π (B j ^ b) = 2 * 3 ^ (j + 1) * B j ^ (b - 1) ∧
      π (C j ^ a * B j ^ b) = r.readout () ⟨j, a⟩ b)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood := (cubic_block_native_power_periods).2.2.2
    1 1 1 (by decide) (by decide) (by decide)
  have hbad := (h.2.2.2 1 1 1 (by decide) (by decide) (by decide))
  have hcontradiction := hgood.2.2.symm.trans hbad.2.2
  change 4 * 3 ^ (1 + 1) *
      (goldenLucas (3 ^ 1) ^ 2 + 1).natAbs ^ (1 - 1) *
      (goldenLucas (3 ^ 1) ^ 2 + 3).natAbs ^ (1 - 1) =
    4 * 3 ^ (1 + 1) *
      (goldenLucas (3 ^ 1) ^ 2 + 1).natAbs ^ (1 - 1) *
      (goldenLucas (3 ^ 1) ^ 2 + 3).natAbs ^ (1 - 1) + 1 at hcontradiction
  omega

def registration : Registration arena
    (let C := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 1).natAbs
     let B := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 3).natAbs
     let π := fun m : ℕ => orderOf
       (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
     (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (C i).Coprime (C j)) ∧
     (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (B i).Coprime (B j)) ∧
     (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → (C i).Coprime (B j)) ∧
     (∀ j a b : ℕ, 1 ≤ j → 1 ≤ a → 1 ≤ b →
       π (C j ^ a) = 4 * 3 ^ (j + 1) * C j ^ (a - 1) ∧
       π (B j ^ b) = 2 * 3 ^ (j + 1) * B j ^ (b - 1) ∧
       π (C j ^ a * B j ^ b) =
         4 * 3 ^ (j + 1) * C j ^ (a - 1) * B j ^ (b - 1))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_block_native_power_periods, rejected, rejected_law⟩
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
    refine ⟨⟨1, 1⟩, 1, 2, ?_⟩
    change 4 * 3 ^ (1 + 1) *
        (goldenLucas (3 ^ 1) ^ 2 + 1).natAbs ^ (1 - 1) *
        (goldenLucas (3 ^ 1) ^ 2 + 3).natAbs ^ (1 - 1) ≠
      4 * 3 ^ (1 + 1) *
        (goldenLucas (3 ^ 1) ^ 2 + 1).natAbs ^ (1 - 1) *
        (goldenLucas (3 ^ 1) ^ 2 + 3).natAbs ^ (2 - 1)
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]

register_information_theorem
  _root_.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods
  in arena
  readout via (realize signature
    (fun _ p b =>
      let C := (goldenLucas (3 ^ p.1) ^ 2 + 1).natAbs
      let B := (goldenLucas (3 ^ p.1) ^ 2 + 3).natAbs
      4 * 3 ^ (p.1 + 1) * C ^ (p.2 - 1) * B ^ (b - 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
    coordinates := #[3, 4]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg",
        "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

end
end Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
