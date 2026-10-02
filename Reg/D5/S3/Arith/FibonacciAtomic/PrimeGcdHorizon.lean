import D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon

@[reducible] def signature : Signature where
  Params := Σ _p : ℕ, Σ _z : ℤ, ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q n => Nat.gcd (signedObservation q.2.2 n q.2.1).natAbs q.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ q n => if q.2.2 = horizon q.1 + 1 then n.natAbs else 0)
    (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ), p.Prime →
    (∀ n z n' z' : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
        R.readout () ⟨p, z, k⟩ n = R.readout () ⟨p, z', k⟩ n') →
      ∀ k : ℕ, 1 ≤ k →
        R.readout () ⟨p, z, k⟩ n = R.readout () ⟨p, z', k⟩ n') ∧
    (∀ a b c d : ℕ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
    (∃ a b c d : ℕ, a < p ∧ b < p ∧ c < p ∧ d < p ∧
      (∀ k : ℕ, 1 ≤ k → k < horizon p →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
      Nat.gcd (observation (horizon p) a b) p ≠
        Nat.gcd (observation (horizon p) c d) p)

theorem actual_law : arena.Law actual := sharp_prime_gcd_horizon

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hprefix : ∀ k : ℕ, 1 ≤ k → k ≤ horizon 2 →
      rejected.readout () ⟨2, 0, k⟩ 0 = rejected.readout () ⟨2, 0, k⟩ 1 := by
    intro k _ hk
    have hne : k ≠ horizon 2 + 1 := by omega
    simp [rejected, realize, hne]
  have hlast := (h 2 Nat.prime_two).1 0 0 1 0 hprefix (horizon 2 + 1) (by omega)
  simp [rejected, realize] at hlast

def registration : Registration arena
    (∀ (p : ℕ) (hp : p.Prime),
      (∀ n z n' z' : ℤ,
        (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
          Nat.gcd (signedObservation k n z).natAbs p =
            Nat.gcd (signedObservation k n' z').natAbs p) →
        ∀ k : ℕ, 1 ≤ k →
          Nat.gcd (signedObservation k n z).natAbs p =
            Nat.gcd (signedObservation k n' z').natAbs p) ∧
      (∀ a b c d : ℕ,
        (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
          Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) →
        ∀ k : ℕ, 1 ≤ k →
          Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
      (∃ a b c d : ℕ, a < p ∧ b < p ∧ c < p ∧ d < p ∧
        (∀ k : ℕ, 1 ≤ k → k < horizon p →
          Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
        Nat.gcd (observation (horizon p) a b) p ≠
          Nat.gcd (observation (horizon p) c d) p)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨⟨2, 0, 2⟩, 0, 1, ?_⟩
    decide

register_information_theorem sharp_prime_gcd_horizon in arena
  readout via (realize signature
    (fun _ q n => Nat.gcd (signedObservation q.2.2 n q.2.1).natAbs q.1)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
    coordinates := #[0, 3, 6]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "body", "body",
        "domain", "body", "body", "body", "fn", "arg"]
      stateOperand := some #["fn", "arg", "arg", "fn", "arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
