/- GID: D5/S3/Geometry/Hyperideal/HighFaceNeighbourBudgets
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/HighFaceNeighbourBudgets
   mirror-E: none(waiver:continuous-six-coordinate-envelope)
   anchors: []
   utility: none
   digest: Five uniform high-face cosine bounds by neighbouring colour count. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.HighFaceNeighbourBudgets

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-- Count all four neighbouring positions, including repeated global labels. -/
def highCount (bY bZ bV bW : Bool) : Nat :=
  bY.toNat + bZ.toNat + bV.toNat + bW.toNat

/-- The five high-face cosine bounds, indexed by the number of high neighbours. -/
def q : Nat → ℝ
  | 0 => 31 / 33
  | 1 => 25 / Real.sqrt 726
  | 2 => 81 / 88
  | 3 => 61 / Real.sqrt 4752
  | _ => 23 / 27

/-- Each high neighbour is at most 5/4, and each low neighbour at most 2. -/
theorem high_face_neighbour_budgets (bY bZ bV bW : Bool) (y z o v w : ℝ)
    (hy : y ∈ Set.Icc 1 (if bY then 5 / 4 else 2))
    (hz : z ∈ Set.Icc 1 (if bZ then 5 / 4 else 2))
    (ho : o ∈ Set.Icc 1 2)
    (hv : v ∈ Set.Icc 1 (if bV then 5 / 4 else 2))
    (hw : w ∈ Set.Icc 1 (if bW then 5 / 4 else 2)) :
    cosine (5 / 4) y z o v w ≤ q (highCount bY bZ bV bW) := by
  have htarget : (5 / 4 : ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hone : (1 : ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hbound (b : Bool) : (if b then (5 / 4 : ℝ) else 2) ∈ Set.Icc 1 2 := by
    cases b <;> norm_num
  have hY : y ∈ Set.Icc (1:ℝ) 2 := ⟨hy.1, hy.2.trans (hbound bY).2⟩
  have hZ : z ∈ Set.Icc (1:ℝ) 2 := ⟨hz.1, hz.2.trans (hbound bZ).2⟩
  have hV : v ∈ Set.Icc (1:ℝ) 2 := ⟨hv.1, hv.2.trans (hbound bV).2⟩
  have hW : w ∈ Set.Icc (1:ℝ) 2 := ⟨hw.1, hw.2.trans (hbound bW).2⟩
  have quotient_le : ∀ (A B P r : ℝ), 0 < A → 0 < B → 0 ≤ r →
      P^2 ≤ r^2 * (A * B) → P / Real.sqrt A / Real.sqrt B ≤ r := by
    intro A B P r hA hB hr hs
    let d := Real.sqrt A * Real.sqrt B
    have hd : 0 < d := mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
    have hdsq : d^2 = A*B := by
      dsimp [d]
      rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    rw [div_div]
    change P / d ≤ r
    apply (div_le_iff₀ hd).2
    apply le_of_sq_le_sq
    · rw [mul_pow, hdsq]
      exact hs
    · exact mul_nonneg hr hd.le
  let Y : ℝ := if bY then 5 / 4 else 2
  let Z : ℝ := if bZ then 5 / 4 else 2
  let V : ℝ := if bV then 5 / 4 else 2
  let W : ℝ := if bW then 5 / 4 else 2
  have hrA : 0 < rad (5 / 4) Y W := by
    cases bY <;> cases bW <;> norm_num [Y, W, rad]
  have hrB : 0 < rad (5 / 4) Z V := by
    cases bZ <;> cases bV <;> norm_num [Z, V, rad]
  have hq : 0 ≤ q (highCount bY bZ bV bW) := by
    cases bY <;> cases bZ <;> cases bV <;> cases bW <;>
      norm_num [q, highCount] <;> positivity
  have hsquared : (numerator (5 / 4) Y Z 1 V W)^2 ≤
      (q (highCount bY bZ bV bW))^2 *
        (rad (5 / 4) Y W * rad (5 / 4) Z V) := by
    cases bY <;> cases bZ <;> cases bV <;> cases bW <;>
      norm_num [Y, Z, V, W, q, highCount, numerator, rad, div_pow,
        Real.sq_sqrt]
  calc
    cosine (5 / 4) y z o v w ≤ cosine (5 / 4) Y Z 1 V W :=
      cosine_mixed_comparison (5 / 4) y z o v w Y Z 1 V W
        htarget hY hZ ho hV hW (hbound bY) (hbound bZ) hone
        (hbound bV) (hbound bW) hy.2 hz.2 ho.1 hv.2 hw.2
    _ ≤ q (highCount bY bZ bV bW) := by
      unfold cosine
      exact quotient_le _ _ _ _ hrA hrB hq hsquared

#print axioms high_face_neighbour_budgets

end D5.S3.Geometry.Hyperideal.HighFaceNeighbourBudgets
