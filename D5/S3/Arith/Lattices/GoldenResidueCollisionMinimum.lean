/- GID: D5/S3/Arith/Lattices/GoldenResidueCollisionMinimum
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/GoldenResidueCollisionMinimum
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Balanced residue populations exactly minimize pairwise collisions. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.Lattices.GoldenResidueCollisionMinimum

open Finset

/-- If `n` objects occupy `m` residue classes, their pair-collision cost is
minimized by populations differing by at most one. The cost is doubled to
keep the formula integral. -/
theorem balanced_collision_cost_minimum (m n : ℕ) (hm : 0 < m) :
    (∀ c : Fin m → ℕ, (∑ i, c i) = n →
      (m : ℤ) * ((n / m : ℕ) : ℤ) * (((n / m : ℕ) : ℤ) - 1) +
          2 * ((n % m : ℕ) : ℤ) * ((n / m : ℕ) : ℤ) ≤
        ∑ i, (c i : ℤ) * ((c i : ℤ) - 1)) ∧
    (∃ c : Fin m → ℕ, (∑ i, c i) = n ∧
      (∑ i, (c i : ℤ) * ((c i : ℤ) - 1)) =
        (m : ℤ) * ((n / m : ℕ) : ℤ) * (((n / m : ℕ) : ℤ) - 1) +
          2 * ((n % m : ℕ) : ℤ) * ((n / m : ℕ) : ℤ)) := by
  let q := n / m
  let r := n % m
  have hr : r < m := Nat.mod_lt n hm
  have hdiv : r + m * q = n := Nat.mod_add_div n m
  have hdivZ : (r : ℤ) + (m : ℤ) * (q : ℤ) = n := by exact_mod_cast hdiv
  have hsupport (x : ℕ) :
      2 * (q : ℤ) * (x : ℤ) - (q : ℤ) * ((q : ℤ) + 1) ≤
        (x : ℤ) * ((x : ℤ) - 1) := by
    by_cases hx : x ≤ q
    · have hxi : (x : ℤ) ≤ q := by exact_mod_cast hx
      have ha : 0 ≤ (q : ℤ) - x := by omega
      have hb : 0 ≤ (q : ℤ) + 1 - x := by omega
      nlinarith [mul_nonneg ha hb]
    · have hxi : (q : ℤ) + 1 ≤ x := by exact_mod_cast (show q + 1 ≤ x by omega)
      have ha : 0 ≤ (x : ℤ) - q := by omega
      have hb : 0 ≤ (x : ℤ) - q - 1 := by omega
      nlinarith [mul_nonneg ha hb]
  constructor
  · intro c hsum
    have hsumZ : (∑ i, (c i : ℤ)) = n := by exact_mod_cast hsum
    have hpoint :
        (∑ i, (2 * (q : ℤ) * (c i : ℤ) - (q : ℤ) * ((q : ℤ) + 1))) ≤
          ∑ i, (c i : ℤ) * ((c i : ℤ) - 1) :=
      Finset.sum_le_sum (fun i _ => hsupport (c i))
    have hleft :
        (∑ i : Fin m, (2 * (q : ℤ) * (c i : ℤ) -
          (q : ℤ) * ((q : ℤ) + 1))) =
          2 * (q : ℤ) * n - (m : ℤ) * (q : ℤ) * ((q : ℤ) + 1) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumZ]
      simp
      ring
    change (m : ℤ) * (q : ℤ) * ((q : ℤ) - 1) +
        2 * (r : ℤ) * (q : ℤ) ≤ _
    rw [hleft] at hpoint
    nlinarith [hdivZ]
  · let c : Fin m → ℕ := fun i => q + if i.val < r then 1 else 0
    have hfilter :
        (Finset.univ.filter (fun i : Fin m => i.val < r)) =
          Finset.Iio (⟨r, hr⟩ : Fin m) := by
      ext i
      simp [Fin.lt_def]
    have hcount : (∑ i : Fin m, if i.val < r then (1 : ℕ) else 0) = r := by
      rw [Finset.sum_boole]
      rw [hfilter]
      exact Fin.card_Iio _
    have hsum : (∑ i, c i) = n := by
      calc
        (∑ i, c i) = m * q + r := by
          simp [c, Finset.sum_add_distrib, hcount]
        _ = n := by omega
    have hcountZ : (∑ i : Fin m, if i.val < r then (1 : ℤ) else 0) = r := by
      exact_mod_cast hcount
    have hcost (i : Fin m) :
        (c i : ℤ) * ((c i : ℤ) - 1) =
          (q : ℤ) * ((q : ℤ) - 1) +
            if i.val < r then 2 * (q : ℤ) else 0 := by
      dsimp [c]
      split_ifs <;> push_cast <;> ring
    refine ⟨c, hsum, ?_⟩
    simp_rw [hcost]
    rw [Finset.sum_add_distrib]
    have hweighted :
        (∑ i : Fin m, if i.val < r then 2 * (q : ℤ) else 0) =
          2 * (q : ℤ) * r := by
      calc
        _ = 2 * (q : ℤ) *
            (∑ i : Fin m, if i.val < r then (1 : ℤ) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              split_ifs <;> ring
        _ = _ := by rw [hcountZ]
    rw [hweighted]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Int.nsmul_eq_mul, Int.natCast_ediv, Int.natCast_emod]
    conv_rhs => rw [← Int.natCast_div, ← Int.natCast_mod]
    ring

end D5.S3.Arith.Lattices.GoldenResidueCollisionMinimum
