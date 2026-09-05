/- GID: D5/S3/Analytic/PrimeZeckendorf/PrimeRelabelingUnderdetermination
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden layer and Zeckendorf structure remain invariant under arbitrary prime relabeling, so canonical prime localization needs extra arithmetic rigidity. -/

import D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.PrimeZeckendorf.PrimeRelabelingUnderdetermination

open D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfCoordinates

/-- Relabel only the prime-local coordinate by an arbitrary equivalence. -/
def primeRelabeling (relabel : Nat.Primes ≃ Nat.Primes) :
    PrimeGoldenCoordinate ≃ PrimeGoldenCoordinate where
  toFun state := (relabel state.1, state.2)
  invFun state := (relabel.symm state.1, state.2)
  left_inv state := by
    rcases state with ⟨prime, layer⟩
    simp
  right_inv state := by
    rcases state with ⟨prime, layer⟩
    simp

@[simp] theorem prime_relabeling_apply
    (relabel : Nat.Primes ≃ Nat.Primes)
    (state : PrimeGoldenCoordinate) :
    primeRelabeling relabel state = (relabel state.1, state.2) :=
  rfl

/-- Prime relabeling leaves the golden layer coordinate unchanged. -/
@[simp] theorem prime_relabeling_preserves_layer
    (relabel : Nat.Primes ≃ Nat.Primes)
    (state : PrimeGoldenCoordinate) :
    (primeRelabeling relabel state).2 = state.2 :=
  rfl

/-- It consequently leaves the Zeckendorf component of the faithful address
unchanged. -/
@[simp] theorem prime_relabeling_preserves_zeckendorf
    (relabel : Nat.Primes ≃ Nat.Primes)
    (state : PrimeGoldenCoordinate) :
    (primeZeckendorfReadout (primeRelabeling relabel state)).2 =
      (primeZeckendorfReadout state).2 :=
  rfl

/-- Relabeling the prime axis does not destroy the faithfulness of the joint
prime-Zeckendorf coordinates. -/
theorem relabeled_prime_zeckendorf_readout_injective
    (relabel : Nat.Primes ≃ Nat.Primes) :
    Function.Injective
      (fun state : PrimeGoldenCoordinate =>
        primeZeckendorfReadout (primeRelabeling relabel state)) :=
  prime_zeckendorf_readout_injective.comp (primeRelabeling relabel).injective

/-- Any genuinely nonidentity prime relabeling changes some prime coordinate
while preserving the complete layer and Zeckendorf data. -/
theorem nontrivial_prime_relabeling_changes_only_local_label
    (relabel : Nat.Primes ≃ Nat.Primes)
    (hnontrivial : ∃ prime, relabel prime ≠ prime) :
    ∃ state : PrimeGoldenCoordinate,
      (primeRelabeling relabel state).1 ≠ state.1 ∧
      (primeRelabeling relabel state).2 = state.2 ∧
      (primeZeckendorfReadout (primeRelabeling relabel state)).2 =
        (primeZeckendorfReadout state).2 := by
  rcases hnontrivial with ⟨prime, hprime⟩
  exact ⟨(prime, 0), hprime, rfl, rfl⟩

/-- An observation separates prime relabelings when invariance under a
relabeling forces that relabeling to fix every prime. This is a precise
requirement for a canonical geometric-to-prime localization observable. -/
def SeparatesPrimeRelabelings {Observation : Type*}
    (observe : PrimeGoldenCoordinate → Observation) : Prop :=
  ∀ relabel : Nat.Primes ≃ Nat.Primes,
    (∀ state, observe (primeRelabeling relabel state) = observe state) →
      ∀ prime, relabel prime = prime

/-- The explicit prime-coordinate readout has the required rigidity. -/
theorem prime_readout_separates_prime_relabelings :
    SeparatesPrimeRelabelings
      (fun state : PrimeGoldenCoordinate => state.1) := by
  intro relabel hinvariant prime
  exact hinvariant (prime, 0)

/-- Layer-only observation is invariant under every prime relabeling. Thus a
nontrivial relabeling is a finite failure certificate for deriving canonical
prime labels from golden depth alone. -/
theorem layer_readout_prime_relabeling_invariant
    (relabel : Nat.Primes ≃ Nat.Primes) :
    ∀ state : PrimeGoldenCoordinate,
      (primeRelabeling relabel state).2 = state.2 :=
  prime_relabeling_preserves_layer relabel

#print axioms prime_relabeling_preserves_layer
#print axioms prime_relabeling_preserves_zeckendorf
#print axioms relabeled_prime_zeckendorf_readout_injective
#print axioms nontrivial_prime_relabeling_changes_only_local_label
#print axioms prime_readout_separates_prime_relabelings
#print axioms layer_readout_prime_relabeling_invariant

end D5.S3.Analytic.PrimeZeckendorf.PrimeRelabelingUnderdetermination
