/- GID: D5/S3/ArithSums/SpeziaA320043RowProduct
   generality: G
   mirror-B: D5/B/S3/ArithSums/SpeziaA320043RowProduct
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Row n of A320043 multiplies to B(n+1)³, B(N)=∏ k/gcd(k,N), and B(p)=(p-1)! at primes. -

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#98)
escape_witness: row_product (with N = n + 1 and g = gcd(k, N), each term X(n, k) splits as
  ((N - k)/gcd(N - k, N))² · (k/g) by X_split, and the reflection k ↦ N - k of {1, …, n} carries
  the first factor's product onto the second's by reflect, so the row product is the cube of
  ∏_{k=1}^{n} k/gcd(k, N) = B(N)).
proof_shape:
  X, B, claim: source definitions; consumers: the theorems below.
  X_split: content (gcd(N - k, k) = gcd(N - k, N) = gcd(k, N) and exact division); consumer:
    row_product.
  reflect: content (reflection bijection on {1, …, n}); consumer: row_product.
  row_product: content; consumer: result.
  result: content (the cube-root form by Real.finsetProd_rpow, the diagonal X(2m - 1, m) = 1,
    and B(p) = (p - 1)! from gcd(k, p) = 1 for k < p).
Direct frozen dependencies: none (Mathlib-only imports).
Search record (§3.1): D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation and
  SpeziaA320043PrimeRowCriterion treat the row sums a(n), not the row product; no D5
  declaration defines ∏ k/gcd(k, N). Mathlib supplies Finset.prod_nbij',
  Finset.prod_Ico_id_eq_factorial, Nat.coprime_of_lt_prime and Real.finsetProd_rpow.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-! # The row product of A320043

Row `n` of A320043 has terms `X(n, k) = (n+1-k)² k / gcd(n+1-k, k)³` for `1 ≤ k ≤ n`. With
`B(N) = ∏_{k=1}^{N} k / gcd(k, N)`, the terms multiply to `B(n+1)³`; equivalently, their positive
real cube roots multiply to `B(n+1)`. The diagonal term `X(2m-1, m)` equals `1`, and for a prime
`p`, `B(p) = (p-1)!`.
-/

set_option autoImplicit false

namespace D5.S3.ArithSums.SpeziaA320043RowProduct

/-- The `k`-th term of row `n` of A320043: `X(n,k) = (n+1-k)² k / gcd(n+1-k, k)³`. -/
def X (n k : ℕ) : ℕ := (n + 1 - k) ^ 2 * k / Nat.gcd (n + 1 - k) k ^ 3

/-- `B(N) = ∏_{k=1}^{N} k / gcd(k, N)`. -/
def B (N : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 N, k / Nat.gcd k N

/-- The diagonal term, the integer row product, its cube-root form, and `B` at primes. -/
def claim : Prop :=
  (∀ m : ℕ, 1 ≤ m → X (2 * m - 1) m = 1) ∧
  (∀ n : ℕ, 1 ≤ n → ∏ k ∈ Finset.Icc 1 n, X n k = B (n + 1) ^ 3) ∧
  (∀ n : ℕ, 1 ≤ n → ∏ k ∈ Finset.Icc 1 n, ((X n k : ℝ) ^ ((1 : ℝ) / 3)) = B (n + 1)) ∧
  (∀ p : ℕ, p.Prime → B p = (p - 1).factorial)

/-- Each term splits as `(j/g)² (k/g)` with `j = N - k` and `g = gcd(k, N)`. -/
private theorem X_split {n k : ℕ} (hk : k ≤ n) :
    X n k = ((n + 1 - k) / Nat.gcd (n + 1 - k) (n + 1)) ^ 2 * (k / Nat.gcd k (n + 1)) := by
  have hN : n + 1 = (n + 1 - k) + k := by omega
  have hj : Nat.gcd (n + 1 - k) k = Nat.gcd (n + 1 - k) (n + 1) := by
    set j := n + 1 - k
    rw [hN, Nat.gcd_self_add_right]
  have hk' : Nat.gcd (n + 1 - k) k = Nat.gcd k (n + 1) := by
    set j := n + 1 - k
    rw [hN, Nat.gcd_comm j k, Nat.gcd_add_self_right]
  set g := Nat.gcd (n + 1 - k) k with hg
  have hgj : g ∣ n + 1 - k := Nat.gcd_dvd_left _ _
  have hgk : g ∣ k := Nat.gcd_dvd_right _ _
  rw [← hj, ← hk']
  unfold X
  rw [← hg]
  obtain ⟨a, ha⟩ := hgj
  obtain ⟨b, hb⟩ := hgk
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · simp [h0]
  · rw [ha, hb, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]
    rw [show (g * a) ^ 2 * (g * b) = a ^ 2 * b * g ^ 3 by ring]
    exact Nat.mul_div_cancel _ (pow_pos hpos 3)

/-- Reflection `k ↦ N - k` preserves the product of `k / gcd(k, N)` over `1 ≤ k ≤ N - 1`. -/
private theorem reflect (n : ℕ) :
    ∏ k ∈ Finset.Icc 1 n, (n + 1 - k) / Nat.gcd (n + 1 - k) (n + 1) =
      ∏ k ∈ Finset.Icc 1 n, k / Nat.gcd k (n + 1) := by
  refine Finset.prod_nbij' (fun k => n + 1 - k) (fun k => n + 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k _; rfl

private theorem row_product (n : ℕ) :
    ∏ k ∈ Finset.Icc 1 n, X n k = B (n + 1) ^ 3 := by
  have hB : B (n + 1) = ∏ k ∈ Finset.Icc 1 n, k / Nat.gcd k (n + 1) := by
    unfold B
    rw [Finset.prod_Icc_succ_top (by omega), Nat.gcd_self, Nat.div_self (by omega), mul_one]
  rw [Finset.prod_congr rfl fun k hk => X_split (Finset.mem_Icc.mp hk).2, Finset.prod_mul_distrib,
    Finset.prod_pow, reflect, hB]
  ring

/-- The row-product identities hold. -/
theorem result : claim := by
  refine ⟨fun m hm => ?_, fun n _ => row_product n, fun n _ => ?_, fun p hp => ?_⟩
  · unfold X
    rw [show 2 * m - 1 + 1 - m = m by omega, Nat.gcd_self,
      show m ^ 2 * m = m ^ 3 by ring, Nat.div_self (pow_pos (by omega) 3)]
  · rw [Real.finsetProd_rpow _ _ (fun k _ => Nat.cast_nonneg _), ← Nat.cast_prod, row_product]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  · unfold B
    have hp1 := hp.one_lt
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Finset.prod_Icc_succ_top (by omega), Nat.gcd_self, Nat.div_self (by omega), mul_one,
      Nat.add_sub_cancel, ← Finset.prod_Ico_id_eq_factorial]
    have hI : Finset.Ico 1 (q + 1) = Finset.Icc 1 q := rfl
    rw [hI]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk := Finset.mem_Icc.mp hk
    have hcop : Nat.gcd k (q + 1) = 1 := by
      rw [Nat.gcd_comm]
      exact (Nat.coprime_of_lt_prime (by omega) (by omega) hp)
    rw [hcop, Nat.div_one]
end D5.S3.ArithSums.SpeziaA320043RowProduct
