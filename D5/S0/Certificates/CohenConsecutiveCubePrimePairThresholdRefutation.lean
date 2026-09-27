/- GID: D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat, mathlib/module/Mathlib.Data.Nat.Prime.Defs]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.claim28; result=D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result28; claim=D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.claim28
   digest: Refutes Cohen Conjectures 28 and 29 at n = 11 and n = 12. -/

/- Formalization classification:
   proof_shape: result28: bind-only; result29: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #9016)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Prime.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.CohenConsecutiveCubePrimePairThresholdRefutation

/-- The decidable primality instance used by the counts is `Nat.decidablePrime'`, which performs
trial division. The default instance did not finish `twinPairCount 11` in 67 s. -/
private local instance primeDecidable (p : ℕ) : Decidable (Nat.Prime p) :=
  Nat.decidablePrime' p

/-- Pairs of twin primes between `n³` and `(n+1)³`: `n³ < p`, `p + 2 < (n+1)³`, both prime. -/
def twinPairCount (n : ℕ) : ℕ :=
  ((Finset.Ico (n ^ 3 + 1) ((n + 1) ^ 3)).filter
    (fun p => p + 2 < (n + 1) ^ 3 ∧ Nat.Prime p ∧ Nat.Prime (p + 2))).card

/-- Pairs of cousin primes (consecutive primes at distance 4) between `n³` and `(n+1)³`. -/
def cousinPairCount (n : ℕ) : ℕ :=
  ((Finset.Ico (n ^ 3 + 1) ((n + 1) ^ 3)).filter
    (fun p => p + 4 < (n + 1) ^ 3 ∧ Nat.Prime p ∧ Nat.Prime (p + 4) ∧
      ¬ Nat.Prime (p + 1) ∧ ¬ Nat.Prime (p + 2) ∧ ¬ Nat.Prime (p + 3))).card

/-- Conjecture 28 as printed: the two general sentences and all seventeen
"Specifically" thresholds. -/
def claim28 : Prop :=
  (∀ n, 1 ≤ n → 2 ≤ twinPairCount n) ∧
  (∀ k, 1 ≤ k → ∃ N, ∀ n, N ≤ n → k ≤ twinPairCount n) ∧
  (∀ n, 1 ≤ n → 1 ≤ twinPairCount n) ∧
  (∀ n, 1 ≤ n → 2 ≤ twinPairCount n) ∧
  (∀ n, 3 ≤ n → 3 ≤ twinPairCount n) ∧
  (∀ n, 5 ≤ n → 4 ≤ twinPairCount n) ∧
  (∀ n, 8 ≤ n → 5 ≤ twinPairCount n) ∧
  (∀ n, 10 ≤ n → 6 ≤ twinPairCount n) ∧
  (∀ n, 10 ≤ n → 7 ≤ twinPairCount n) ∧
  (∀ n, 10 ≤ n → 8 ≤ twinPairCount n) ∧
  (∀ n, 10 ≤ n → 9 ≤ twinPairCount n) ∧
  (∀ n, 11 ≤ n → 10 ≤ twinPairCount n) ∧
  (∀ n, 13 ≤ n → 11 ≤ twinPairCount n) ∧
  (∀ n, 15 ≤ n → 12 ≤ twinPairCount n) ∧
  (∀ n, 15 ≤ n → 13 ≤ twinPairCount n) ∧
  (∀ n, 15 ≤ n → 14 ≤ twinPairCount n) ∧
  (∀ n, 15 ≤ n → 15 ≤ twinPairCount n) ∧
  (∀ n, 15 ≤ n → 16 ≤ twinPairCount n) ∧
  (∀ n, 20 ≤ n → 17 ≤ twinPairCount n)

/-- Conjecture 29 as printed: the two general sentences and all ten "Specifically" thresholds. -/
def claim29 : Prop :=
  (∀ n, 2 ≤ n → 2 ≤ cousinPairCount n) ∧
  (∀ k, 1 ≤ k → ∃ N, ∀ n, N ≤ n → k ≤ cousinPairCount n) ∧
  (∀ n, 2 ≤ n → 1 ≤ cousinPairCount n) ∧
  (∀ n, 2 ≤ n → 2 ≤ cousinPairCount n) ∧
  (∀ n, 8 ≤ n → 3 ≤ cousinPairCount n) ∧
  (∀ n, 9 ≤ n → 4 ≤ cousinPairCount n) ∧
  (∀ n, 9 ≤ n → 5 ≤ cousinPairCount n) ∧
  (∀ n, 9 ≤ n → 6 ≤ cousinPairCount n) ∧
  (∀ n, 9 ≤ n → 7 ≤ cousinPairCount n) ∧
  (∀ n, 12 ≤ n → 8 ≤ cousinPairCount n) ∧
  (∀ n, 12 ≤ n → 9 ≤ cousinPairCount n) ∧
  (∀ n, 12 ≤ n → 10 ≤ cousinPairCount n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Trial-division evaluation of every candidate below 1728 exceeds the default heartbeat limit.
/-- Conjecture 28 is false at `n = 11`. -/
theorem result28 : ¬ claim28 := by
  intro h
  have hthreshold : ∀ n, 11 ≤ n → 10 ≤ twinPairCount n :=
    h.2.2.2.2.2.2.2.2.2.2.2.1
  have hcount : twinPairCount 11 = 9 := by decide +kernel
  have hbad := hthreshold 11 (by decide)
  rw [hcount] at hbad
  exact (by decide : ¬ (10 ≤ 9)) hbad

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Trial-division evaluation of every candidate below 2197 exceeds the default heartbeat limit.
/-- Conjecture 29 is false at `n = 12`. -/
theorem result29 : ¬ claim29 := by
  intro h
  have hthreshold : ∀ n, 12 ≤ n → 8 ≤ cousinPairCount n :=
    h.2.2.2.2.2.2.2.2.2.1
  have hcount : cousinPairCount 12 = 7 := by decide +kernel
  have hbad := hthreshold 12 (by decide)
  rw [hcount] at hbad
  exact (by decide : ¬ (8 ≤ 7)) hbad

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This kernel calculation checks the counterexample count independently of the theorem proof.
example : twinPairCount 11 = 9 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This kernel calculation checks the counterexample count independently of the theorem proof.
example : cousinPairCount 12 = 7 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This kernel calculation checks the paper's first listed twin-prime count.
example : twinPairCount 1 = 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This kernel calculation checks the paper's second listed twin-prime count.
example : twinPairCount 2 = 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This kernel calculation checks the paper's second listed cousin-prime count.
example : cousinPairCount 2 = 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This kernel calculation checks the paper's twelfth listed twin-prime count.
example : twinPairCount 12 = 12 := by decide +kernel

#print axioms result28
#print axioms result29

end D5.S0.Certificates.CohenConsecutiveCubePrimePairThresholdRefutation
