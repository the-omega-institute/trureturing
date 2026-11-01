/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryInteger
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-integer-chart-transport)
   anchors: [mathlib/module/Mathlib.Tactic.Qify]
   utility: none
   digest: Integer transport of the unbounded rounded-chamber sign charts. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryRoundingAlgebra
import Mathlib.Tactic.Qify

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open private first_less_signs first_greater_signs first_equal_signs peak_middle_low peak_middle_high peak_last_equal peak_last_adjacent peak_last_capacity peak_last_rounding peak_first_lower peak_first_adjacent peak_first_far peak_tied_bc
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryRoundingAlgebra

private theorem first_less_signs_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    let x : ℤ := (((u * 4) * r) * s)
    let y : ℤ := u
    let z : ℤ := ((u * 2) * r)
    let t : ℤ := (x * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    let p : ℤ := r
    0 ≤ ((B - 1) - (A * 4)) ∧
      0 ≤ (A - ((((x * y) + x) + 1) * 2)) ∧
      0 ≤ ((L - A) - (p * B)) ∧
      0 ≤ ((Lp - (A * 2)) - (p * Bp)) ∧
      0 ≤ ((((A * 2) + ((p * 2) * B)) - L) - 1) ∧
      0 ≤ (M - A) ∧
      0 ≤ (Mp - (A * 2)) ∧
      0 ≤ (((A * 2) - M) - 1) := by
  dsimp only
  qify
  obtain ⟨h0,h1,_,ht⟩ := first_less_signs (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)
  exact ⟨h0,h1,ht⟩

private theorem first_greater_signs_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    let x : ℤ := (((u * 4) * r) * s)
    let y : ℤ := ((u * 2) * r)
    let z : ℤ := u
    let t : ℤ := (x * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    let h : ℤ := (s * 2)
    0 ≤ (A - ((((x * y) + x) + 1) * 2)) ∧
      0 ≤ (L - (h * A)) ∧
      0 ≤ (Lp - ((h * 2) * A)) ∧
      0 ≤ ((((h * 2) * A) - L) - 1) ∧
      0 ≤ (M - A) ∧
      0 ≤ (Mp - (A * 2)) ∧
      0 ≤ (((A * 2) - M) - 1) ∧
      0 ≤ ((B - 1) - ((h * 2) * A)) := by
  dsimp only
  qify
  exact first_greater_signs (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem first_equal_signs_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 1 ≤ r) (hs : 0 ≤ s) :
    let x : ℤ := ((u * 2) * r)
    let y : ℤ := u
    let z : ℤ := u
    let t : ℤ := (x * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    let h : ℤ := (r * 2)
    0 ≤ (A - ((((x * y) + x) + 1) * 2)) ∧
      0 ≤ (L - (h * A)) ∧
      0 ≤ (Lp - ((h * 2) * A)) ∧
      0 ≤ ((((h * 2) * A) - L) - 1) ∧
      0 ≤ (M - A) ∧
      0 ≤ (Mp - (A * 2)) ∧
      0 ≤ (((A * 2) - M) - 1) ∧
      0 ≤ (B - (h * A)) ∧
      0 ≤ (Bp - ((h * 2) * A)) ∧
      0 ≤ ((((h * 2) * A) - B) - 1) ∧
      0 ≤ ((B - 1) - (h * A)) ∧
      0 ≤ (((h * 2) * A) - B) := by
  dsimp only
  qify
  exact first_equal_signs (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_middle_low_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    let x : ℤ := (u * r)
    let y : ℤ := ((u * r) * s)
    let z : ℤ := u
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ (L - A) ∧
      0 ≤ (Lp - (A * 2)) ∧
      0 ≤ (((A * 2) - L) - 1) := by
  dsimp only
  qify
  exact peak_middle_low (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_middle_high_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    let x : ℤ := u
    let y : ℤ := (((u * 2) * r) * s)
    let z : ℤ := ((u * 2) * r)
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ (L - (A * 2)) ∧
      0 ≤ (Lp - (A * 4)) ∧
      0 ≤ (((A * 4) - L) - 1) := by
  dsimp only
  qify
  exact peak_middle_high (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_last_equal_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 1 ≤ r) (hs : 0 ≤ s) :
    let x : ℤ := (u * r)
    let y : ℤ := (u * r)
    let z : ℤ := u
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ (M - A) ∧
      0 ≤ (Mp - (A * 2)) ∧
      0 ≤ (((A * 2) - M) - 1) := by
  dsimp only
  qify
  exact peak_last_equal (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_last_adjacent_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 4 ≤ r) (hs : 0 ≤ s) :
    let x : ℤ := u
    let y : ℤ := (u * 2)
    let z : ℤ := r
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ ((M - A) - L) ∧
      0 ≤ ((Mp - (A * 2)) - Lp) ∧
      0 ≤ ((((A * 2) + (L * 2)) - M) - 1) := by
  dsimp only
  qify
  exact peak_last_adjacent (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_last_capacity_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 4 ≤ r) (hs : 1 ≤ s) :
    let x : ℤ := u
    let y : ℤ := ((u * 2) * s)
    let z : ℤ := r
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ (M - (A * 2)) ∧
      0 ≤ (((y - 2) * L) - ((M + 1) - (A * 2))) := by
  dsimp only
  qify
  exact peak_last_capacity (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_last_rounding_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 4 ≤ r) (hs : 1 ≤ s) :
    let x : ℤ := u
    let y : ℤ := ((u * 4) * s)
    let z : ℤ := r
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ (((M - D) - 1) - (L * 2)) := by
  dsimp only
  qify
  exact peak_last_rounding (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_first_lower_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 4 ≤ r) (hs : 1 ≤ s) :
    let x : ℤ := u
    let y : ℤ := ((r * 2) * s)
    let z : ℤ := r
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ ((B - 1) - (A * 2)) ∧
      0 ≤ (A - ((((x * y) + x) + 1) * 2)) := by
  dsimp only
  qify
  exact peak_first_lower (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_first_adjacent_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 4 ≤ r) (hs : 0 ≤ s) :
    let x : ℤ := u
    let y : ℤ := (r * 2)
    let z : ℤ := r
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ (((A * 4) - B) - 1) := by
  dsimp only
  qify
  exact peak_first_adjacent (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_first_far_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 4 ≤ r) (hs : 1 ≤ s) :
    let x : ℤ := u
    let y : ℤ := ((r * 4) * s)
    let z : ℤ := r
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ ((B - 1) - (A * 4)) := by
  dsimp only
  qify
  exact peak_first_far (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

private theorem peak_tied_bc_int (u r s : ℤ)
    (hu : 4 ≤ u) (hr : 1 ≤ r) (hs : 0 ≤ s) :
    let x : ℤ := u
    let y : ℤ := ((u * 2) * r)
    let z : ℤ := ((u * 2) * r)
    let t : ℤ := (y * 2)
    let A : ℤ := (((((x * y) * z) + (x * y)) + x) + 1)
    let B : ℤ := ((t * (((x * y) + x) + 1)) + 1)
    let L : ℤ := ((((t * z) * (x + 1)) + z) + 1)
    let M : ℤ := (((((t * y) * z) + (y * z)) + y) + 1)
    let D : ℤ := (((y * z) + y) + 1)
    let Bp : ℤ := ((B * 2) - 1)
    let Lp : ℤ := (((L * 2) - z) - 1)
    let Mp : ℤ := ((M * 2) - D)
    0 ≤ ((B - 1) - (A * 2)) ∧
      0 ≤ (((A * 4) - B) - 1) := by
  dsimp only
  qify
  exact peak_tied_bc (u:ℚ) (r:ℚ) (s:ℚ) (by exact_mod_cast hu) (by exact_mod_cast hr) (by exact_mod_cast hs)

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
