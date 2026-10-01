import D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon

abbrev signature : Signature where
  Params := Σ _p : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameters value => Nat.gcd value (parameters.1 ^ parameters.2))
    (fun anchor => nomatch anchor)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun anchor => nomatch anchor)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e),
    (∀ j : ℕ, 0 < zeroRank (p ^ j) ∧ p ^ j ∣ Nat.fib (zeroRank (p ^ j)) ∧
      ∀ k : ℕ, 0 < k → p ^ j ∣ Nat.fib k → zeroRank (p ^ j) ≤ k) ∧
    (zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) ∨
      zeroRank (p ^ e) = p * zeroRank (p ^ (e - 1))) ∧
    (∀ n z n2 z2 : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p e →
        Nat.gcd (signedObservation n z k).natAbs (p ^ e) =
          Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e)) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (signedObservation n z k).natAbs (p ^ e) =
          Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e)) ∧
    (∀ a b a2 b2 : ℕ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p e →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) ∧
    (∃ a b a2 b2 : ℕ, a < p ^ e ∧ b < p ^ e ∧ a2 < p ^ e ∧ b2 < p ^ e ∧
      (∀ k : ℕ, 1 ≤ k → k < horizon p e →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) ∧
      Nat.gcd (sourceObservation a b (horizon p e)) (p ^ e) = p ^ e ∧
      observation.readout () ⟨p, e⟩ (sourceObservation a2 b2 (horizon p e)) = p ^ (e - 1))

theorem actual_law : arena.Law actual := sharp_prime_power_gcd_horizon

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨a, b, a2, b2, aBound, bBound, a2Bound, b2Bound, agreement,
    terminal, terminal2⟩ := (law 2 2 Nat.prime_two le_rfl).2.2.2.2
  change 0 = 2 ^ (2 - 1) at terminal2
  norm_num at terminal2

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun role => ⟨rejected,
    fun other different => (different (Subsingleton.elim other role)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨⟨2, 2⟩, 0, 1, ?_⟩
    change Nat.gcd 0 (2 ^ 2) ≠ Nat.gcd 1 (2 ^ 2)
    norm_num

register_information_theorem sharp_prime_power_gcd_horizon in arena
  readout via (realize signature
    (fun _ parameters value => Nat.gcd value (parameters.1 ^ parameters.2))
    (fun anchor => nomatch anchor))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body",
        "arg", "arg", "arg", "arg",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateOperand := some #["fn", "arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
