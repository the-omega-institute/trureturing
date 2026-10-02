/- GID: D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The coefficients f_{N,k}(q) of the D_N-type spin chain with PSRO are polynomials. -/

/-
proof_shape: result: content (the q-Pascal rules for [a+b, a]_{q^2} in RatFunc Q, polynomiality
  of the Gaussian binomials by induction on a + b, and the identity
  (q^b + q^a) [a+b, a]_{q^2} = (1 + q^(a+b)) (q^b [a+b-1, a-1]_{q^2} + q^a [a+b-1, a]_{q^2}),
  which produces the polynomial on the live proof path)
escape_witness: form (2), the public conclusion `result` itself, produced by the induction and the
  identity above; pinned Mathlib has no Gaussian binomial coefficients
admission_basis: open-problem-resolution (issue #12062; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.SpinChains.PolarizedSpinReversalCoefficientPolynomial

open Polynomial

/-- `(q²)_j = ∏_{i=1}^{j} (1 - q^{2i})` in the field `RatFunc ℚ` of rational functions in
`q = RatFunc.X`. -/
noncomputable def qPoch (j : ℕ) : RatFunc ℚ :=
  ∏ i ∈ Finset.range j, (1 - RatFunc.X ^ (2 * (i + 1)))

/-- The `q`-binomial coefficient `[N, k]_{q²} = (q²)_N / ((q²)_k (q²)_{N-k})`. -/
noncomputable def qBinom (N k : ℕ) : RatFunc ℚ := qPoch N / (qPoch k * qPoch (N - k))

/-- The coefficient `f_{N,k}(q) = (q^{N-k} + q^k) / (1 + q^N) · [N, k]_{q²}` of the partition
function of the `D_N`-type Polychronakos–Frahm spin chain with polarized spin reversal
operators (arXiv:1503.08231, Eq. (m39)). -/
noncomputable def coeffF (N k : ℕ) : RatFunc ℚ :=
  (RatFunc.X ^ (N - k) + RatFunc.X ^ k) / (1 + RatFunc.X ^ N) * qBinom N k

/-- The conjecture of Basu-Mallick, Datta, Finkel and González-López (arXiv:1503.08231):
for every `N` and every `k ≤ N`, `f_{N,k}(q)` is a polynomial in `q`. -/
def claim : Prop :=
  ∀ N k : ℕ, k ≤ N → ∃ p : ℚ[X], coeffF N k = algebraMap ℚ[X] (RatFunc ℚ) p

/-- The conjecture holds: `f_{N,k} = 1` for `k = 0` and `k = N`, and otherwise
`f_{N,k} = q^{N-k} [N-1, k-1]_{q²} + q^k [N-1, k]_{q²}`, where the Gaussian binomials are
polynomials by the `q`-Pascal rules. -/
theorem result : claim := by
  -- abbreviations
  set x : RatFunc ℚ := RatFunc.X with hx
  have hpoch0 : qPoch 0 = 1 := by simp [qPoch]
  have hpochS : ∀ j, qPoch (j + 1) = qPoch j * (1 - x ^ (2 * (j + 1))) := by
    intro j; simp [qPoch, Finset.prod_range_succ, hx]
  -- nonvanishing of 1 - x^m for m ≥ 1 and of 1 + x^N
  have hfac : ∀ m : ℕ, 0 < m → (1 - x ^ m : RatFunc ℚ) ≠ 0 := by
    intro m hm h
    have h' : algebraMap ℚ[X] (RatFunc ℚ) (1 - Polynomial.X ^ m) = 0 := by
      rw [map_sub, map_one, map_pow, RatFunc.algebraMap_X]; exact h
    rw [map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)] at h'
    have := congrArg (Polynomial.eval 0) h'
    simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)] at this
  have hplus : ∀ m : ℕ, (1 + x ^ m : RatFunc ℚ) ≠ 0 := by
    intro m h
    have h' : algebraMap ℚ[X] (RatFunc ℚ) (1 + Polynomial.X ^ m) = 0 := by
      rw [map_add, map_one, map_pow, RatFunc.algebraMap_X]; exact h
    rw [map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)] at h'
    have := congrArg (Polynomial.eval 0) h'
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num at this
    · simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)] at this
  have hpochne : ∀ j, qPoch j ≠ 0 := by
    intro j; induction j with
    | zero => simp [hpoch0]
    | succ j ih => rw [hpochS]; exact mul_ne_zero ih (hfac _ (by omega))
  -- B a b := [a+b, a]_{q²}
  let B : ℕ → ℕ → RatFunc ℚ := fun a b => qPoch (a + b) / (qPoch a * qPoch b)
  have hB0 : ∀ b, B 0 b = 1 := by
    intro b; simp only [B, Nat.zero_add, hpoch0, one_mul]; exact div_self (hpochne b)
  have hB0' : ∀ a, B a 0 = 1 := by
    intro a; simp only [B, Nat.add_zero, hpoch0, mul_one]; exact div_self (hpochne a)
  have hpascal1 : ∀ a b, B (a + 1) (b + 1) = B a (b + 1) + x ^ (2 * (a + 1)) * B (a + 1) b := by
    intro a b
    simp only [B]
    have e1 : a + 1 + (b + 1) = (a + b + 1) + 1 := by ring
    have e2 : a + (b + 1) = a + b + 1 := by ring
    have e3 : a + 1 + b = a + b + 1 := by ring
    rw [e1, e2, e3, hpochS (a + b + 1), hpochS a, hpochS b]
    have := hpochne (a + b + 1); have := hpochne a; have := hpochne b
    have := hfac (2 * (a + 1)) (by omega); have := hfac (2 * (b + 1)) (by omega)
    field_simp
    ring
  have hpascal2 : ∀ a b, B (a + 1) (b + 1) = x ^ (2 * (b + 1)) * B a (b + 1) + B (a + 1) b := by
    intro a b
    simp only [B]
    have e1 : a + 1 + (b + 1) = (a + b + 1) + 1 := by ring
    have e2 : a + (b + 1) = a + b + 1 := by ring
    have e3 : a + 1 + b = a + b + 1 := by ring
    rw [e1, e2, e3, hpochS (a + b + 1), hpochS a, hpochS b]
    have := hpochne (a + b + 1); have := hpochne a; have := hpochne b
    have := hfac (2 * (a + 1)) (by omega); have := hfac (2 * (b + 1)) (by omega)
    field_simp
    ring
  have hpoly : ∀ n a b, a + b = n → ∃ p : ℚ[X], B a b = algebraMap ℚ[X] (RatFunc ℚ) p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b hab
      rcases a with _ | a
      · exact ⟨1, by rw [hB0]; simp⟩
      rcases b with _ | b
      · exact ⟨1, by rw [hB0']; simp⟩
      obtain ⟨p1, hp1⟩ := ih (a + (b + 1)) (by omega) a (b + 1) rfl
      obtain ⟨p2, hp2⟩ := ih (a + 1 + b) (by omega) (a + 1) b rfl
      refine ⟨p1 + X ^ (2 * (a + 1)) * p2, ?_⟩
      rw [hpascal1, hp1, hp2]; simp [hx]
  intro N k hk
  obtain ⟨b, rfl⟩ : ∃ b, N = k + b := ⟨N - k, by omega⟩
  have hsub : k + b - k = b := by omega
  have hF : coeffF (k + b) k = (x ^ b + x ^ k) / (1 + x ^ (k + b)) * B k b := by
    simp only [coeffF, qBinom, B, hsub, hx]
  rcases k with _ | a
  · refine ⟨1, ?_⟩
    rw [hF, hB0]; simp only [pow_zero, Nat.zero_add]
    rw [add_comm (x ^ b) 1, div_self (hplus b)]; simp
  rcases b with _ | b
  · refine ⟨1, ?_⟩
    rw [hF, hB0']; simp only [pow_zero, Nat.add_zero]
    rw [div_self (hplus (a + 1))]; simp
  obtain ⟨p1, hp1⟩ := hpoly _ a (b + 1) rfl
  obtain ⟨p2, hp2⟩ := hpoly _ (a + 1) b rfl
  refine ⟨X ^ (b + 1) * p1 + X ^ (a + 1) * p2, ?_⟩
  have key : (x ^ (b + 1) + x ^ (a + 1)) * B (a + 1) (b + 1) =
      (1 + x ^ (a + 1 + (b + 1))) * (x ^ (b + 1) * B a (b + 1) + x ^ (a + 1) * B (a + 1) b) := by
    have h1 := hpascal1 a b
    have h2 := hpascal2 a b
    calc (x ^ (b + 1) + x ^ (a + 1)) * B (a + 1) (b + 1)
        = x ^ (b + 1) * B (a + 1) (b + 1) + x ^ (a + 1) * B (a + 1) (b + 1) := by ring
      _ = x ^ (b + 1) * (B a (b + 1) + x ^ (2 * (a + 1)) * B (a + 1) b) +
            x ^ (a + 1) * (x ^ (2 * (b + 1)) * B a (b + 1) + B (a + 1) b) := by
          rw [← h1, ← h2]
      _ = _ := by ring
  rw [hF, div_mul_eq_mul_div, key, mul_div_cancel_left₀ _ (hplus _), hp1, hp2]
  simp [hx]

end D5.S3.Quantum.SpinChains.PolarizedSpinReversalCoefficientPolynomial
