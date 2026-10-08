/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedCountingArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedCountingArithmetic
   mirror-E: none(waiver:weighted-congruence)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: An odd multiple of the vertex-label sum is nonzero modulo an even order. -/

import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedCountingArithmetic

open Finset
open scoped BigOperators

theorem weighted_parity_obstruction {n r : ℕ} (hn : 0 < n)
    (hne : n % 2 = 0) (hre : r % 2 = 1) :
    ¬n ∣ r * (∑ v : Fin n, v.val) := by
  intro hdiv
  let S := ∑ v : Fin n, v.val
  have hS : 2 * S = n * (n - 1) := by
    have heq : S = ∑ i ∈ range n, i := Fin.sum_univ_eq_sum_range (fun i => i) n
    rw [heq]
    simpa [Nat.mul_comm] using sum_range_id_mul_two n
  obtain ⟨d, hd⟩ := hdiv
  change r * S = n * d at hd
  have heq : 2 * d = r * (n - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hn
    calc
      n * (2 * d) = 2 * (n * d) := by ac_rfl
      _ = 2 * (r * S) := by rw [← hd]
      _ = r * (2 * S) := by ac_rfl
      _ = n * (r * (n - 1)) := by rw [hS]; ac_rfl
  have hodd : (r * (n - 1)) % 2 = 1 := by
    rw [Nat.mul_mod, hre]
    omega
  omega

end D5.S3.Combinatorics.DihedralRamsey.NestedCountingArithmetic
