/- GID: D5/S3/Arith/RobinExponentSwap
   generality: G
   mirror-B: D5/B/S3/Arith/RobinExponentSwap
   mirror-E: none(waiver:general-inequality-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Assigning the larger exponent to the smaller real base strictly increases the product of reciprocal geometric sums. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.RobinExponentSwap

noncomputable section

/-- The reciprocal geometric sum, including the terms with exponents zero and `k`. -/
def reciprocalGeomSum (r : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), r⁻¹ ^ i

/-- Pairing the larger exponent with the smaller base strictly increases the product.
This is the local normalized divisor-sum comparison used in the classical
nonincreasing-exponent argument for superabundant numbers. -/
theorem reciprocal_geom_sum_swap_strict {p q : ℝ} {a b : ℕ}
    (hp : 1 < p) (hpq : p < q) (hab : a < b) :
    reciprocalGeomSum p a * reciprocalGeomSum q b <
      reciprocalGeomSum p b * reciprocalGeomSum q a := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := hp0.trans hpq
  have hx : 0 < p⁻¹ := inv_pos.mpr hp0
  have hy : 0 < q⁻¹ := inv_pos.mpr hq0
  have hyx : q⁻¹ < p⁻¹ := (inv_lt_inv₀ hq0 hp0).mpr hpq
  -- Every new tail term has a strictly larger gain against the fixed prefix.
  have increment (k : ℕ) (hak : a < k) :
      reciprocalGeomSum p a * q⁻¹ ^ k < p⁻¹ ^ k * reciprocalGeomSum q a := by
    unfold reciprocalGeomSum
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos a)⟩
    intro i hi
    have hik : i < k := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hak
    have hsplit (r : ℝ) : r ^ k = r ^ i * r ^ (k - i) := by
      rw [← pow_add, Nat.add_sub_of_le hik.le]
    have hpow : q⁻¹ ^ (k - i) < p⁻¹ ^ (k - i) :=
      pow_lt_pow_left₀ hyx hy.le (Nat.sub_ne_zero_of_lt hik)
    calc
      p⁻¹ ^ i * q⁻¹ ^ k = (p⁻¹ ^ i * q⁻¹ ^ i) * q⁻¹ ^ (k - i) := by
        rw [hsplit q⁻¹]
        ring
      _ < (p⁻¹ ^ i * q⁻¹ ^ i) * p⁻¹ ^ (k - i) :=
        mul_lt_mul_of_pos_left hpow (mul_pos (pow_pos hx i) (pow_pos hy i))
      _ = p⁻¹ ^ k * q⁻¹ ^ i := by
        rw [hsplit p⁻¹]
        ring
  have sum_succ (r : ℝ) (k : ℕ) :
      reciprocalGeomSum r (k + 1) = reciprocalGeomSum r k + r⁻¹ ^ (k + 1) :=
    Finset.sum_range_succ _ _
  refine Nat.le_induction ?_ ?_ b hab
  · rw [sum_succ, sum_succ]
    nlinarith [increment (a + 1) (Nat.lt_succ_self a)]
  · intro k hk ih
    rw [sum_succ, sum_succ]
    nlinarith [increment (k + 1) (by omega)]

end

end D5.S3.Arith.RobinExponentSwap
