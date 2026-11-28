module

import OmegaBuild.Commands
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Basic
meta import Mathlib.Tactic.Linarith.Frontend

/-!
Omega original.

Attainable differences between two nonnegative readings of a normalized three-point Gram form.
-/

compile_only_with_mathlib

public section

namespace Omega.Geometry.ThreeReadingContrast

/-- At fixed mutual reading `r`, the differences `d` between nonnegative readings
against a third point are exactly those satisfying `r ^ 2 + d ^ 2 ≤ 1`.
The Gram form is required to be nonnegative on every weight vector over `R`. -/
theorem exists_nonnegative_readings_iff {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (r d : R) :
    (∃ a b : R, 0 ≤ a ∧ 0 ≤ b ∧ a - b = d ∧
      ∀ x y z : R, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * (r * x * y + a * x * z + b * y * z)) ↔
    r ^ 2 + d ^ 2 ≤ 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl, gram⟩
    have hr : r ≤ 1 := by nlinarith only [gram 1 (-1) 0]
    rcases le_total b a with hab | hba
    · have residual := gram 1 (-r) (-(a - b))
      have correction := mul_nonneg (mul_nonneg (sub_nonneg.mpr hr) hb) (sub_nonneg.mpr hab)
      nlinarith only [residual, correction]
    · have residual := gram (-r) 1 (a - b)
      have correction := mul_nonneg (mul_nonneg (sub_nonneg.mpr hr) ha) (sub_nonneg.mpr hba)
      nlinarith only [residual, correction]
  · intro hd
    have slack : 0 ≤ 1 - r ^ 2 - d ^ 2 := by linarith
    rcases le_total 0 d with h | h
    · refine ⟨d, 0, h, le_rfl, sub_zero _, ?_⟩
      intro x y z
      nlinarith only [sq_nonneg (y + r * x), sq_nonneg (z + d * x), mul_nonneg slack (sq_nonneg x)]
    · refine ⟨0, -d, le_rfl, neg_nonneg.mpr h, by rw [zero_sub, neg_neg], ?_⟩
      intro x y z
      nlinarith only [sq_nonneg (x + r * y), sq_nonneg (z - d * y), mul_nonneg slack (sq_nonneg y)]

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

private abbrev GramNonneg (r a b : R) : Prop :=
  ∀ x y z : R, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * (r * x * y + a * x * z + b * y * z)

private theorem gramNonneg_swap {r a b : R} (h : GramNonneg r a b) : GramNonneg r b a := by
  intro x y z
  nlinarith only [h y x z]

-- Inside the interval the leading two-by-two minor is positive, so its factor can be cancelled.
private theorem gramNonneg_iff_det {r a b : R} (lo : -1 < r) (hi : r < 1) :
    GramNonneg r a b ↔ 0 ≤ 1 - r ^ 2 - (a - b) ^ 2 - 2 * (1 - r) * a * b := by
  have minor : 0 < 1 - r ^ 2 := by
    have h := mul_pos (sub_pos.mpr hi) (show 0 < 1 + r by linarith)
    nlinarith only [h]
  constructor
  · intro gram
    let y := -(b - r * a)
    let z := 1 - r ^ 2
    have test := gram (-(r * y + a * z)) y z
    apply nonneg_of_mul_nonneg_right (a := 1 - r ^ 2) _ minor
    dsimp [y, z] at test
    nlinarith only [test]
  · intro det x y z
    apply nonneg_of_mul_nonneg_right (a := 1 - r ^ 2) _ minor
    nlinarith only [mul_nonneg minor.le (sq_nonneg (x + r * y + a * z)),
      sq_nonneg ((1 - r ^ 2) * y + (b - r * a) * z), mul_nonneg det (sq_nonneg z)]

private theorem gramNonneg_one_iff {a b : R} :
    GramNonneg 1 a b ↔ a = b ∧ a ^ 2 ≤ 1 := by
  constructor
  · intro gram
    refine ⟨?_, by nlinarith only [gram 1 0 (-a)]⟩
    have h : (a - b) ^ 2 = 0 := by nlinarith only [gram 1 (-1) (-(a - b)), sq_nonneg (a - b)]
    exact sub_eq_zero.mp (by simpa using h)
  · rintro ⟨rfl, ha⟩ x y z
    nlinarith only [sq_nonneg (x + y + a * z), mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg z)]

private theorem floor_iff_of_nonneg {r d m : R} (hd : 0 ≤ d) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (lo : -1 ≤ r) (hi : r ≤ 1) :
    (∃ a b, m ≤ a ∧ m ≤ b ∧ a - b = d ∧ GramNonneg r a b) ↔
      r ^ 2 + d ^ 2 + 2 * (1 - r) * m * (m + d) ≤ 1 := by
  rcases eq_or_lt_of_le hi with h | hhi
  · subst r
    constructor
    · rintro ⟨a, b, _, _, hab, gram⟩
      obtain ⟨rfl, _⟩ := gramNonneg_one_iff.mp gram
      simp [show d = 0 by linarith]
    · intro bound
      have hz : d ^ 2 = 0 := by nlinarith only [bound, sq_nonneg d]
      have hd0 : d = 0 := by simpa using hz
      have hmSq : m ^ 2 ≤ 1 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hm1) (show 0 ≤ 1 + m by linarith)]
      exact ⟨m, m, le_rfl, le_rfl, by rw [hd0, sub_self], gramNonneg_one_iff.mpr ⟨rfl, hmSq⟩⟩
  rcases eq_or_lt_of_le lo with h | hlo
  · rw [← h]
    constructor
    · rintro ⟨a, b, ha, hb, hab, gram⟩
      have hz : (a + b) ^ 2 = 0 := by nlinarith only [gram 1 1 (-(a + b)), sq_nonneg (a + b)]
      have he : a + b = 0 := by simpa using hz
      have hm0 : m = 0 := by linarith
      have hd0 : d = 0 := by linarith
      simp [hm0, hd0]
    · intro bound
      have hz : d ^ 2 = 0 := by
        nlinarith only [bound, sq_nonneg d, mul_nonneg hm (add_nonneg hm hd)]
      have hd0 : d = 0 := by simpa using hz
      subst d
      have hmz : m ^ 2 = 0 := by nlinarith only [bound, sq_nonneg m]
      have hm0 : m = 0 := by simpa using hmz
      subst m
      refine ⟨0, 0, le_rfl, le_rfl, sub_self _, ?_⟩
      intro x y z
      nlinarith only [sq_nonneg (x - y), sq_nonneg z]
  constructor
  · rintro ⟨a, b, _, hb, hab, gram⟩
    have det := (gramNonneg_iff_det hlo hhi).mp gram
    have product : m * (m + d) ≤ a * b := by
      have h := mul_le_mul hb (show m + d ≤ a by linarith) (add_nonneg hm hd) (le_trans hm hb)
      nlinarith only [h]
    rw [← hab] at product ⊢
    nlinarith only [det, mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr product)]
  · intro bound
    refine ⟨m + d, m, by linarith, le_rfl, by simp, (gramNonneg_iff_det hlo hhi).mpr ?_⟩
    nlinarith only [bound]

private theorem floor_iff_of_bounds (r d m : R) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (lo : -1 ≤ r) (hi : r ≤ 1) :
    (∃ a b, m ≤ a ∧ m ≤ b ∧ a - b = d ∧ GramNonneg r a b) ↔
      r ^ 2 + d ^ 2 + 2 * (1 - r) * m * (m + |d|) ≤ 1 := by
  by_cases hd : 0 ≤ d
  · simpa [abs_of_nonneg hd] using floor_iff_of_nonneg hd hm hm1 lo hi
  · have swap : (∃ a b, m ≤ a ∧ m ≤ b ∧ a - b = d ∧ GramNonneg r a b) ↔
        (∃ a b, m ≤ a ∧ m ≤ b ∧ a - b = -d ∧ GramNonneg r a b) := by
      constructor <;> rintro ⟨a, b, ha, hb, hab, gram⟩ <;>
        exact ⟨b, a, hb, ha, by linarith, gramNonneg_swap gram⟩
    rw [swap, floor_iff_of_nonneg (neg_nonneg.mpr (le_of_not_ge hd)) hm hm1 lo hi,
      abs_of_neg (lt_of_not_ge hd), neg_sq]

/-- For a nonnegative common floor `m`, attainable three-point contrasts are characterized by
the upper bounds on the floor and mutual reading and one polynomial inequality involving `|d|`.
The witnesses are `(m + d, m)` for `d ≥ 0` and `(m, m - d)` for `d < 0`. -/
theorem exists_readings_at_floor_iff (r d m : R) (hm : 0 ≤ m) :
    (∃ a b : R, m ≤ a ∧ m ≤ b ∧ a - b = d ∧
      ∀ x y z : R, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * (r * x * y + a * x * z + b * y * z)) ↔
      m ≤ 1 ∧ r ≤ 1 ∧ r ^ 2 + d ^ 2 + 2 * (1 - r) * m * (m + |d|) ≤ 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, gram⟩
    have hm1 : m ≤ 1 := by nlinarith only [ha, gram 1 0 (-1)]
    have lo : -1 ≤ r := by nlinarith only [gram 1 1 0]
    have hi : r ≤ 1 := by nlinarith only [gram 1 (-1) 0]
    exact ⟨hm1, hi, (floor_iff_of_bounds r d m hm hm1 lo hi).mp ⟨a, b, ha, hb, hab, gram⟩⟩
  · rintro ⟨hm1, hi, bound⟩
    have correction := mul_nonneg (mul_nonneg (sub_nonneg.mpr hi) hm) (add_nonneg hm (abs_nonneg d))
    have lo : -1 ≤ r := by nlinarith only [bound, correction, sq_nonneg d, sq_nonneg (r + 1)]
    exact (floor_iff_of_bounds r d m hm hm1 lo hi).mpr bound

end Omega.Geometry.ThreeReadingContrast
