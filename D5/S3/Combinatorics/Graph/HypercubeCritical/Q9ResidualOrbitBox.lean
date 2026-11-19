import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Integer certificates for cardinality bounds on residual orbit counts.
A leaf combines degree rows and variable bounds. A split divides a range
of possible counts into two integer intervals. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitBox

open Finset

/-- A finite tree of integer interval splits and nonnegative row multipliers. -/
inductive Certificate (dimension rows : ℕ) where
  | bound (weights : Fin rows → ℕ)
  | split (index : Fin dimension) (cut : ℤ)
      (lower upper : Certificate dimension rows)

variable {n m : ℕ}

private def surplus (a : Fin m → Fin n → ℤ) (scale : ℤ)
    (weights : Fin m → ℕ) (j : Fin n) : ℤ :=
  scale - ∑ i, (weights i : ℤ) * a i j

private def leafBound (a : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (scale : ℤ)
    (lo hi : Fin n → ℤ) (weights : Fin m → ℕ) : ℤ :=
  (∑ i, (weights i : ℤ) * b i) + ∑ j,
    max (surplus a scale weights j * lo j) (surplus a scale weights j * hi j)

/-- Check only integer arithmetic at the leaves of the supplied interval
partition. The scale is shared across the row multipliers. -/
def check (a : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (scale target : ℤ)
    (lo hi : Fin n → ℤ) : Certificate n m → Bool
  | .bound weights => decide (leafBound a b scale lo hi weights < scale * target)
  | .split j k left right =>
    check a b scale target lo (Function.update hi j k) left &&
      check a b scale target (Function.update lo j (k + 1)) hi right

private theorem leafBound_sound (a : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (scale : ℤ)
    (lo hi x : Fin n → ℤ) (weights : Fin m → ℕ)
    (hlo : ∀ j, lo j ≤ x j) (hhi : ∀ j, x j ≤ hi j)
    (hrows : ∀ i, (∑ j, a i j * x j) ≤ b i) :
    scale * (∑ j, x j) ≤ leafBound a b scale lo hi weights := by
  have hrow : (∑ j, (∑ i, (weights i : ℤ) * a i j) * x j) ≤ ∑ i, (weights i : ℤ) * b i := by
    calc
      _ = ∑ i, (weights i : ℤ) * ∑ j, a i j * x j := by
        simp_rw [sum_mul, mul_sum, mul_assoc]
        rw [sum_comm]
      _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrows i) (by positivity)
  have hsurplus :
      (∑ j, surplus a scale weights j * x j) ≤
        ∑ j, max (surplus a scale weights j * lo j) (surplus a scale weights j * hi j) := by
    apply sum_le_sum
    intro j _
    by_cases hs : 0 ≤ surplus a scale weights j
    · exact (mul_le_mul_of_nonneg_left (hhi j) hs).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left (hlo j) (le_of_not_ge hs)).trans (le_max_left _ _)
  calc
    _ = (∑ j, (∑ i, (weights i : ℤ) * a i j) * x j) +
        ∑ j, surplus a scale weights j * x j := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      unfold surplus
      ring
    _ ≤ _ := add_le_add hrow hsurplus

/-- A valid certificate excludes every feasible integer vector at or
above the target cardinality. -/
theorem sum_lt_of_check (a : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (scale target : ℤ)
    (hscale : 0 < scale) (x : Fin n → ℤ)
    (hrows : ∀ i, (∑ j, a i j * x j) ≤ b i)
    (certificate : Certificate n m) (lo hi : Fin n → ℤ)
    (hlo : ∀ j, lo j ≤ x j) (hhi : ∀ j, x j ≤ hi j)
    (hcheck : check a b scale target lo hi certificate = true) : (∑ j, x j) < target := by
  induction certificate generalizing lo hi with
  | bound weights =>
    have hb : leafBound a b scale lo hi weights < scale * target := of_decide_eq_true hcheck
    by_contra! h
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left h hscale.le))
      ((leafBound_sound a b scale lo hi x weights hlo hhi hrows).trans_lt hb)
  | split j k left right ihleft ihright =>
    have hc := Bool.and_eq_true_iff.mp hcheck
    by_cases h : x j ≤ k
    · apply ihleft lo (Function.update hi j k) hlo _ hc.1
      intro i
      by_cases hij : i = j
      · simpa [hij] using h
      · simpa [Function.update_of_ne hij] using hhi i
    · apply ihright (Function.update lo j (k + 1)) hi _ hhi hc.2
      intro i
      by_cases hij : i = j
      · simpa [hij] using (show k + 1 ≤ x j by omega)
      · simpa [Function.update_of_ne hij] using hlo i

#print axioms sum_lt_of_check

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitBox
