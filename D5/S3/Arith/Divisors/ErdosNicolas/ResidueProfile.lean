/- GID: D5/S3/Arith/Divisors/ErdosNicolas/ResidueProfile
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Rounded reciprocal profiles bound finite one two and three period residue sums. -/

import D5.S3.Arith.Divisors.ErdosNicolas.PairChecker
import D5.S3.Arith.Divisors.ErdosNicolas.ResidueChains

/-! Exact finite profiles and integer rounding for the residue-tree initial vector. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- A short-distance residual written as a reciprocal and two polynomial corrections. -/
private theorem w_expand {L g : ℕ} (hg : 0 < g) (hLg : g ≤ L) :
    w L g = (g : ℚ)⁻¹ - 2 / L + (g : ℚ) / (L : ℚ) ^ 2 := by
  have hL : (L : ℚ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  rw [w, Nat.cast_sub hLg]
  field_simp
  <;> ring

/-- One period has the same constant correction as all longer integral periods. -/
private theorem f_one_period_eq_profile {p r : ℕ} (hr : 0 < r) (hrp : r < p) :
    f p p r = (r : ℚ)⁻¹ + ((p - r : ℕ) : ℚ)⁻¹ - 3 / p := by
  rw [(f_eq_two_terms hrp.le).2 (Or.inr (by omega)), w_expand hr hrp.le,
    w_expand (by omega : 0 < p - r) (by omega : p - r ≤ p)]
  rw [Nat.cast_sub hrp.le]
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  field_simp
  <;> ring

private theorem w_zero_outside {L : ℕ} {z : ℤ}
    (h : (L : ℤ) ≤ z ∨ z ≤ -(L : ℤ)) : w L z.natAbs = 0 := by
  apply w_eq_zero_iff.mpr ∘ Or.inr
  have hz : (L : ℤ) ≤ (z.natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    rcases h with h | h
    · exact h.trans (le_abs_self z)
    · have := neg_le_abs z
      omega
  exact_mod_cast hz

/-- Six lattice sites give the exact three-period finite residue sum. -/
private theorem f_eq_six_terms {p r : ℕ} (hr : 0 < r) (hrp : r < p) :
    f p (3 * p) r =
      w (3 * p) (2 * p + r) + w (3 * p) (p + r) + w (3 * p) r +
      w (3 * p) (p - r) + w (3 * p) (2 * p - r) + w (3 * p) (3 * p - r) := by
  have hp : (0 : ℤ) < p := by omega
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have hrp' : (r : ℤ) < p := by exact_mod_cast hrp
  have hsub : ({-2, -1, 0, 1, 2, 3} : Finset ℤ) ⊆
      Icc (-((3 * p : ℕ) : ℤ)) ((3 * p : ℕ) : ℤ) := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [mem_Icc] <;> push_cast <;> omega
  have he : f p (3 * p) r = ∑ k ∈ ({-2, -1, 0, 1, 2, 3} : Finset ℤ),
      w (3 * p) (((p : ℤ) * k - (r : ℤ)).natAbs) := by
    symm
    apply sum_subset hsub
    intro k _ hk
    apply w_zero_outside
    have hk' : k ≠ -2 ∧ k ≠ -1 ∧ k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 := by
      simpa using hk
    push_cast
    by_cases hk0 : k < 0
    · right
      have := mul_nonneg hp.le (by omega : 0 ≤ -k - 3)
      nlinarith
    · left
      have := mul_nonneg hp.le (by omega : 0 ≤ k - 4)
      nlinarith
  have habsneg (a : ℕ) :
      ((p : ℤ) * -(a : ℤ) - (r : ℤ)).natAbs = a * p + r := by
    have hz : (p : ℤ) * -(a : ℤ) - (r : ℤ) = -((a * p + r : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hz, Int.natAbs_neg, Int.natAbs_natCast]
  have habspos (a : ℕ) (ha : 1 ≤ a) :
      ((p : ℤ) * (a : ℤ) - (r : ℤ)).natAbs = a * p - r := by
    rw [show (p : ℤ) * (a : ℤ) = ((a * p : ℕ) : ℤ) by push_cast; ring]
    apply Int.natAbs_natCast_sub_natCast_of_ge
    have := Nat.mul_le_mul_right p ha
    omega
  rw [he]
  rw [sum_insert (by decide : (-2 : ℤ) ∉ ({-1, 0, 1, 2, 3} : Finset ℤ)),
    sum_insert (by decide : (-1 : ℤ) ∉ ({0, 1, 2, 3} : Finset ℤ)),
    sum_insert (by decide : (0 : ℤ) ∉ ({1, 2, 3} : Finset ℤ)),
    sum_insert (by decide : (1 : ℤ) ∉ ({2, 3} : Finset ℤ)),
    sum_insert (by decide : (2 : ℤ) ∉ ({3} : Finset ℤ)), sum_singleton]
  rw [show (-2 : ℤ) = -(2 : ℕ) by norm_num,
    show (-1 : ℤ) = -(1 : ℕ) by norm_num,
    habsneg 2, habsneg 1]
  simp only [mul_zero, zero_sub, Int.natAbs_neg, Int.natAbs_natCast, one_mul]
  have hp1 : ((p : ℤ) * 1 - (r : ℤ)).natAbs = p - r := by
    simpa using habspos 1 (by decide)
  have hp2 : ((p : ℤ) * 2 - (r : ℤ)).natAbs = 2 * p - r := by
    simpa using habspos 2 (by decide)
  have hp3 : ((p : ℤ) * 3 - (r : ℤ)).natAbs = 3 * p - r := by
    simpa using habspos 3 (by decide)
  rw [hp1, hp2, hp3]
  ring

/-- Three periods retain the correction `-3/p` after the six residuals are added. -/
private theorem f_three_periods_eq_profile {p r : ℕ} (hr : 0 < r) (hrp : r < p) :
    f p (3 * p) r =
      (r : ℚ)⁻¹ + ((p - r : ℕ) : ℚ)⁻¹ + ((p + r : ℕ) : ℚ)⁻¹ +
      ((2 * p - r : ℕ) : ℚ)⁻¹ + ((2 * p + r : ℕ) : ℚ)⁻¹ +
      ((3 * p - r : ℕ) : ℚ)⁻¹ - 3 / p := by
  rw [f_eq_six_terms hr hrp]
  rw [w_expand (by omega : 0 < 2 * p + r) (by omega : 2 * p + r ≤ 3 * p),
    w_expand (by omega : 0 < p + r) (by omega : p + r ≤ 3 * p),
    w_expand hr (by omega : r ≤ 3 * p),
    w_expand (by omega : 0 < p - r) (by omega : p - r ≤ 3 * p),
    w_expand (by omega : 0 < 2 * p - r) (by omega : 2 * p - r ≤ 3 * p),
    w_expand (by omega : 0 < 3 * p - r) (by omega : 3 * p - r ≤ 3 * p)]
  rw [Nat.cast_sub hrp.le, Nat.cast_sub (by omega : r ≤ 2 * p),
    Nat.cast_sub (by omega : r ≤ 3 * p)]
  push_cast
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  field_simp
  <;> ring

/-- The reciprocal distances in (17), ordered by increasing periods. -/
def residueGaps (p ell r : ℕ) : List ℕ :=
  if ell = 1 then [r, p - r] else
  if ell = 2 then [r, p - r, p + r, 2 * p - r] else
  [r, p - r, p + r, 2 * p - r, 2 * p + r, 3 * p - r]

/-- A common list interface for the three exact initial profiles. -/
private theorem f_eq_residueGaps {p ell r : ℕ} (hell : ell = 1 ∨ ell = 2 ∨ ell = 3)
    (hr : 0 < r) (hrp : r < p) :
    f p (ell * p) r =
      ((residueGaps p ell r).map fun g : ℕ => (g : ℚ)⁻¹).sum - 3 / p := by
  rcases hell with rfl | rfl | rfl
  · simpa [residueGaps] using f_one_period_eq_profile hr hrp
  · rw [f_two_periods_eq_profile hrp.le, if_neg (by omega), add_zero]
    simp only [residueGaps, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold residueProfile
    rw [Nat.cast_sub hrp.le, Nat.cast_sub (by omega : r ≤ 2 * p)]
    push_cast
    ring
  · simpa [residueGaps, add_assoc] using f_three_periods_eq_profile hr hrp

/-- Every denominator in an actual profile is strictly positive. -/
private theorem residueGaps_pos {p ell r g : ℕ} (hr : 0 < r) (hrp : r < p)
    (hg : g ∈ residueGaps p ell r) : 0 < g := by
  unfold residueGaps at hg
  split_ifs at hg <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  all_goals rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- The rounded numerator (17); subtraction is natural because the exact profile is nonnegative. -/
def roundedResidueNumerator (p ell Q r : ℕ) : ℕ :=
  p * ((residueGaps p ell r).map (ceilDiv Q)).sum - 3 * Q

private theorem list_reciprocal_le (Q : ℕ) (ds : List ℕ)
    (hds : ∀ g ∈ ds, 0 < g) :
    (Q : ℚ) * (ds.map fun g : ℕ => (g : ℚ)⁻¹).sum ≤
      ((ds.map (ceilDiv Q)).sum : ℕ) := by
  induction ds with
  | nil => simp
  | cons g ds ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add]
    have hg := reciprocal_le_ceil Q g
    have ht := ih (by intro d hd; exact hds d (by simp [hd]))
    linarith

/-- The executable ceiling numerator is a rigorous upper bound on the actual finite residual. -/
theorem roundedResidueNumerator_sound {p ell Q r : ℕ}
    (hell : ell = 1 ∨ ell = 2 ∨ ell = 3) (hr : 0 < r) (hrp : r < p) :
    (p * Q : ℕ) * f p (ell * p) r ≤ (roundedResidueNumerator p ell Q r : ℚ) := by
  let U := ((residueGaps p ell r).map (ceilDiv Q)).sum
  let S := ((residueGaps p ell r).map fun g : ℕ => (g : ℚ)⁻¹).sum
  have hceil : (Q : ℚ) * S ≤ U :=
    list_reciprocal_le Q _ (fun g hg => residueGaps_pos hr hrp hg)
  have hp : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hnonneg : 0 ≤ f p (ell * p) r := by
    exact sum_nonneg fun k hk => w_nonneg _ _
  have heq : f p (ell * p) r = S - 3 / p := f_eq_residueGaps hell hr hrp
  have hmul : (p * Q : ℕ) * f p (ell * p) r ≤ (p : ℚ) * U - 3 * Q := by
    calc
      _ = (p : ℚ) * ((Q : ℚ) * S) - 3 * Q := by
        rw [heq]
        push_cast
        field_simp
        <;> ring
      _ ≤ (p : ℚ) * U - 3 * Q := by
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left hceil hp.le) _
  have hsub : 3 * Q ≤ p * U := by
    have hz : (0 : ℚ) ≤ (p : ℚ) * U - 3 * Q :=
      (mul_nonneg (by positivity) hnonneg).trans hmul
    exact_mod_cast (by linarith : (3 : ℚ) * Q ≤ (p : ℚ) * U)
  change (p * Q : ℕ) * f p (ell * p) r ≤ ((p * U - 3 * Q : ℕ) : ℚ)
  rw [Nat.cast_sub hsub]
  push_cast
  simpa only [Nat.cast_mul] using hmul

#print axioms f_eq_residueGaps
#print axioms residueGaps_pos
#print axioms roundedResidueNumerator_sound

#print axioms w_expand
#print axioms f_one_period_eq_profile
#print axioms f_eq_six_terms
#print axioms f_three_periods_eq_profile

end D5.S3.Arith.ErdosNicolas
