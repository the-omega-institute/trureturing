/- GID: D5/S3/Arith/Robin/PrimeSupportModes
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PrimeSupportModes
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: none
   digest: A five-way prime-support stratification isolates the 5040 Robin regime.
   -/

import D5.S3.Arith.GoldenResource.GoldenCell5040Shape
import D5.S3.Arith.Robin.FewDistinctPrimes

/-! A small classification layer for the actual Robin family.

The five bins separate empty support, prime powers, the already closed eight-prime
region, the unresolved nine-to-eleven region, and the twelve-prime tail.  The
classification itself is elementary, but keeping it as a named type prevents the
cardinality thresholds from being duplicated by later Euler-layer arguments.
-/

namespace D5.S3.Arith.Robin.PrimeSupportModes

open D5.S3.Arith.Robin.FewDistinctPrimes

/-- The five support-size regimes used by the Robin reduction. -/
inductive PrimeSupportMode where
  | empty
  | singleton
  | twoToEight
  | nineToEleven
  | twelvePlus
  deriving DecidableEq, Repr

/-- Classify an integer by the number of distinct prime divisors. -/
def primeSupportMode (n : ℕ) : PrimeSupportMode :=
  let c := n.primeFactors.card
  if c = 0 then
    .empty
  else if c = 1 then
    .singleton
  else if c ≤ 8 then
    .twoToEight
  else if c ≤ 11 then
    .nineToEleven
  else
    .twelvePlus

theorem primeSupportMode_spec (n : ℕ) :
    match primeSupportMode n with
    | .empty => n.primeFactors.card = 0
    | .singleton => n.primeFactors.card = 1
    | .twoToEight => 2 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 8
    | .nineToEleven => 9 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 11
    | .twelvePlus => 12 ≤ n.primeFactors.card := by
  by_cases h0 : n.primeFactors.card = 0
  · simp [primeSupportMode, h0]
  by_cases h1 : n.primeFactors.card = 1
  · simp [primeSupportMode, h0, h1]
  by_cases h8 : n.primeFactors.card ≤ 8
  · have h2 : 2 ≤ n.primeFactors.card := by omega
    simp [primeSupportMode, h0, h1, h8, h2]
  by_cases h11 : n.primeFactors.card ≤ 11
  · have h9 : 9 ≤ n.primeFactors.card := by omega
    simp [primeSupportMode, h0, h1, h8, h11, h9]
  · have h12 : 12 ≤ n.primeFactors.card := by omega
    simp [primeSupportMode, h0, h1, h8, h11, h12]

/-- The five support-size cases are exhaustive, with no analytic assumptions. -/
theorem primeSupportMode_cases (n : ℕ) :
    n.primeFactors.card = 0 ∨
      n.primeFactors.card = 1 ∨
      (2 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 8) ∨
      (9 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 11) ∨
      12 ≤ n.primeFactors.card := by
  by_cases h0 : n.primeFactors.card = 0
  · exact Or.inl h0
  by_cases h1 : n.primeFactors.card = 1
  · exact Or.inr (Or.inl h1)
  by_cases h8 : n.primeFactors.card ≤ 8
  · right; right; left
    omega
  by_cases h11 : n.primeFactors.card ≤ 11
  · right; right; right; left
    omega
  · right; right; right; right
    omega

/-- A number above `5040` cannot be in the empty-support bin. -/
theorem mode_ne_empty_of_gt_5040 {n : ℕ} (hn : 5040 < n) :
    primeSupportMode n ≠ .empty := by
  intro hmode
  have hspec := primeSupportMode_spec n
  rw [hmode] at hspec
  have hcard := hspec
  have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard
  have h01 : n = 0 ∨ n = 1 := (Nat.primeFactors_eq_empty.mp hempty)
  omega

/-- The `twoToEight` bin is already covered by the formal Robin theorem. -/
theorem robin_of_twoToEight {n : ℕ} (hn : 5040 < n)
    (hmode : primeSupportMode n = .twoToEight) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  have hspec := primeSupportMode_spec n
  rw [hmode] at hspec
  exact robin_of_card_primeFactors_le_eight hn hspec.2

/-- Any strict Robin failure above `5040` is forced into the two unresolved bins. -/
theorem robin_failure_mode {n : ℕ} (hn : 5040 < n)
    (hfail : ¬ ((ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)))) :
    primeSupportMode n = .nineToEleven ∨ primeSupportMode n = .twelvePlus := by
  by_cases h8 : n.primeFactors.card ≤ 8
  · exact (hfail (robin_of_card_primeFactors_le_eight hn h8)).elim
  by_cases h11 : n.primeFactors.card ≤ 11
  · have h9 : 9 ≤ n.primeFactors.card := by omega
    have h0 : ¬ n.primeFactors.card = 0 := by omega
    have h1 : ¬ n.primeFactors.card = 1 := by omega
    left
    simp [primeSupportMode, h0, h1, h8, h11]
  · have h12 : 12 ≤ n.primeFactors.card := by omega
    have h0 : ¬ n.primeFactors.card = 0 := by omega
    have h1 : ¬ n.primeFactors.card = 1 := by omega
    right
    simp [primeSupportMode, h0, h1, h8, h11, h12]

private theorem support_card_le_four_add {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : r ≠ 0) :
    (2 ^ a * 3 ^ b * 5 * 7 * r).primeFactors.card ≤ 4 + r.primeFactors.card := by
  have hsub : (2 ^ a * 3 ^ b * 5 * 7 * r).primeFactors ⊆
      ({2, 3, 5, 7} : Finset ℕ) ∪ r.primeFactors := by
    rw [Nat.primeFactors_mul (by positivity) hr]
    rw [Nat.primeFactors_mul (by positivity) (by norm_num)]
    rw [Nat.primeFactors_mul (by positivity) (by norm_num)]
    rw [Nat.primeFactors_mul (by positivity) (by norm_num)]
    rw [Nat.primeFactors_prime_pow ha.ne' Nat.prime_two]
    rw [Nat.primeFactors_prime_pow hb.ne' Nat.prime_three]
    rw [(by decide : Nat.Prime 5).primeFactors]
    rw [(by decide : Nat.Prime 7).primeFactors]
    simp
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le ({2, 3, 5, 7} : Finset ℕ) r.primeFactors
  calc
    _ ≤ ({2, 3, 5, 7} : Finset ℕ).card + r.primeFactors.card := hc.trans hu
    _ ≤ 4 + r.primeFactors.card := by simp

/-- In the `5040` shape, a residual with at most five distinct primes gives at most
nine distinct primes in total.  This is the support-count interface for the next
residual branch; it does not estimate the divisor ratio. -/
theorem modEq_2241_card_le_nine_of_residual_card_le_five {n : ℕ}
    (hshape : ∃ a b r : ℕ, n = 2 ^ a * 3 ^ b * 5 * 7 * r ∧
      4 ≤ a ∧ a ≤ 6 ∧ 2 ≤ b ∧ b ≤ 3 ∧
      Nat.Coprime r (2 * 3 * 5 * 7 * 83) ∧ r.primeFactors.card ≤ 5) :
    n.primeFactors.card ≤ 9 := by
  obtain ⟨a, b, r, hn, ha, _, hb, _, _, hcard⟩ := hshape
  subst n
  by_cases hr : r = 0
  · subst r
    norm_num
  · have hs := support_card_le_four_add (a := a) (b := b) (r := r) (by omega) (by omega) hr
    omega

/-- A Robin failure in the five-prime residual branch must use all five residual
primes and has exactly nine distinct primes in total. -/
theorem robin_failure_residual_card_eq_five {n : ℕ} (hn : 5040 < n)
    (hshape : ∃ a b r : ℕ, n = 2 ^ a * 3 ^ b * 5 * 7 * r ∧
      4 ≤ a ∧ a ≤ 6 ∧ 2 ≤ b ∧ b ≤ 3 ∧
      Nat.Coprime r (2 * 3 * 5 * 7 * 83) ∧ r.primeFactors.card ≤ 5)
    (hfail : ¬ ((ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)))) :
    ∃ a b r : ℕ, n = 2 ^ a * 3 ^ b * 5 * 7 * r ∧
      4 ≤ a ∧ a ≤ 6 ∧ 2 ≤ b ∧ b ≤ 3 ∧
      Nat.Coprime r (2 * 3 * 5 * 7 * 83) ∧
      r.primeFactors.card = 5 ∧ n.primeFactors.card = 9 := by
  obtain ⟨a, b, r, hnshape, ha, hahi, hb, hbhi, hcop, hcard⟩ := hshape
  have htotal_le : n.primeFactors.card ≤ 9 :=
    modEq_2241_card_le_nine_of_residual_card_le_five
      ⟨a, b, r, hnshape, ha, hahi, hb, hbhi, hcop, hcard⟩
  have hmode := robin_failure_mode hn hfail
  have htotal_ge : 9 ≤ n.primeFactors.card := by
    rcases hmode with h9 | h12
    · have hspec := primeSupportMode_spec n
      rw [h9] at hspec
      exact hspec.1
    · have hspec := primeSupportMode_spec n
      rw [h12] at hspec
      omega
  have htotal : n.primeFactors.card = 9 := by omega
  have hsum : n.primeFactors.card ≤ 4 + r.primeFactors.card := by
    rw [hnshape]
    by_cases hr : r = 0
    · subst r
      norm_num
    · exact support_card_le_four_add (a := a) (b := b) (r := r) (by omega) (by omega) hr
  have hresidual : r.primeFactors.card = 5 := by omega
  exact ⟨a, b, r, hnshape, ha, hahi, hb, hbhi, hcop, hresidual, htotal⟩

/-- The literal `5040` congruence shape feeds the five-prime residual reduction. -/
theorem robin_failure_modEq_2241_residual_card_le_five {n : ℕ} (hn : 5040 < n)
    (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241)
    (hcard : ∀ a b r : ℕ, n = 2 ^ a * 3 ^ b * 5 * 7 * r →
      r.primeFactors.card ≤ 5)
    (hfail : ¬ ((ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)))) :
    ∃ a b r : ℕ, n = 2 ^ a * 3 ^ b * 5 * 7 * r ∧
      4 ≤ a ∧ a ≤ 6 ∧ 2 ≤ b ∧ b ≤ 3 ∧
      Nat.Coprime r (2 * 3 * 5 * 7 * 83) ∧
      r.primeFactors.card = 5 ∧ n.primeFactors.card = 9 := by
  obtain ⟨a, b, r, hnshape, ha, hahi, hb, hbhi, hcop⟩ :=
    D5.S3.Arith.GoldenResource.GoldenCell5040Shape.modEq_2241_shape h5040 hmod
  exact robin_failure_residual_card_eq_five hn
    ⟨a, b, r, hnshape, ha, hahi, hb, hbhi, hcop, hcard a b r hnshape⟩ hfail

end D5.S3.Arith.Robin.PrimeSupportModes
