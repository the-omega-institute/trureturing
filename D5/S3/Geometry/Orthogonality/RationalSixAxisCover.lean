/- GID: D5/S3/Geometry/Orthogonality/RationalSixAxisCover
   generality: G
   mirror-B: D5/B/S3/Geometry/Orthogonality/RationalSixAxisCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Six rational axes give a relatively open orthogonality-free cover of the real unit two-sphere. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The construction addresses the upper-bound part of Feldman--Wilce,
arXiv:2608.13320v1, Question 3. The rational-axis certificate is the
repository derivation stated in issue #23716; mathematical priority is unresolved.
The lower bound and the full open covering number are outside this module.

The helpers are consumed by `rational_six_axis_open_cover`. Bessel's inequality
is reused from Mathlib; the covering step uses the explicit nonnegative
polynomial certificate in `cyclic_max_square`. Utility is none because the
result quantifies over the entire real unit sphere, not a finite sample.
-/

noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Orthogonality.RationalSixAxisCover

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev UnitSphere := Metric.sphere (0 : Space) 1

/-- The six unnormalized rational axes, all of squared norm five. -/
def axis : Fin 6 → Space :=
  ![WithLp.toLp 2 ![1, 2, 0], WithLp.toLp 2 ![1, -2, 0],
    WithLp.toLp 2 ![0, 1, 2], WithLp.toLp 2 ![0, 1, -2],
    WithLp.toLp 2 ![2, 0, 1], WithLp.toLp 2 ![-2, 0, 1]]

/-- Strict projection superlevels with the sphere's ordinary subspace topology. -/
def color (i : Fin 6) : Set UnitSphere :=
  {x | 5 < 2 * (inner ℝ (x : Space) (axis i)) ^ 2}

private theorem inner_axis (x : Space) (i : Fin 6) :
    inner ℝ x (axis i) =
      ![x 0 + 2*x 1, x 0 - 2*x 1, x 1 + 2*x 2,
        x 1 - 2*x 2, x 2 + 2*x 0, x 2 - 2*x 0] i := by
  fin_cases i <;> simp [axis, PiLp.inner_apply, Fin.sum_univ_succ, RCLike.inner_apply] <;> ring

private theorem axis_norm_sq (i : Fin 6) : ‖axis i‖ ^ 2 = 5 := by
  fin_cases i <;> norm_num [axis, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

private theorem sphere_norm (x : UnitSphere) : ‖(x : Space)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

/-- The signed forms recover the absolute-coordinate expression exactly. -/
private theorem signed_square (s t : ℝ) :
    (|s| + 2*|t|)^2 = (s+2*t)^2 ∨ (|s| + 2*|t|)^2 = (s-2*t)^2 := by
  rcases le_total 0 s with hs | hs <;> rcases le_total 0 t with ht | ht
  · left; rw [abs_of_nonneg hs, abs_of_nonneg ht]
  · right; rw [abs_of_nonneg hs, abs_of_nonpos ht]; ring
  · right; rw [abs_of_nonpos hs, abs_of_nonneg ht]; ring
  · left; rw [abs_of_nonpos hs, abs_of_nonpos ht]; ring

/-- The nonnegative polynomial certificate for the three cyclic forms. -/
private theorem cyclic_max_square (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    3 * (a^2+b^2+c^2) ≤ (max (a+2*b) (max (b+2*c) (c+2*a)))^2 := by
  let M := max (a+2*b) (max (b+2*c) (c+2*a))
  let u := M-a-2*b
  let v := M-b-2*c
  let w := M-c-2*a
  have hu : 0 ≤ u := by dsimp [u]; linarith [le_max_left (a+2*b) (max (b+2*c) (c+2*a))]
  have hv : 0 ≤ v := by
    dsimp [v]; linarith [le_trans (le_max_left (b+2*c) (c+2*a))
      (le_max_right (a+2*b) (max (b+2*c) (c+2*a)))]
  have hw : 0 ≤ w := by
    dsimp [w]; linarith [le_trans (le_max_right (b+2*c) (c+2*a))
      (le_max_right (a+2*b) (max (b+2*c) (c+2*a)))]
  have hid : 3*M^2-9*(a^2+b^2+c^2) =
      u*v+v*w+w*u+6*(a*w+b*u+c*v) +
        ((a-b)^2+(b-c)^2+(c-a)^2)/2 := by
    dsimp [u, v, w]; ring
  have hpos : 0 ≤ u*v+v*w+w*u+6*(a*w+b*u+c*v) +
      ((a-b)^2+(b-c)^2+(c-a)^2)/2 := by positivity
  dsimp [M] at hid
  linarith

private theorem large_projection (x : Space) :
    ∃ i : Fin 6, 3 * ‖x‖^2 ≤ (inner ℝ x (axis i))^2 := by
  let a := |x 0|
  let b := |x 1|
  let c := |x 2|
  let M := max (a+2*b) (max (b+2*c) (c+2*a))
  have hQ : a^2+b^2+c^2 = ‖x‖^2 := by
    simp [a, b, c, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, sq_abs, add_assoc]
  have hM : 3 * ‖x‖^2 ≤ M^2 := by
    rw [← hQ]
    exact cyclic_max_square a b c (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  have hm : M = a+2*b ∨ M = b+2*c ∨ M = c+2*a := by
    rcases max_cases (a+2*b) (max (b+2*c) (c+2*a)) with h | h
    · exact Or.inl h.1
    · rcases max_cases (b+2*c) (c+2*a) with h' | h'
      · exact Or.inr (Or.inl (h.1.trans h'.1))
      · exact Or.inr (Or.inr (h.1.trans h'.1))
  rcases hm with hm | hm | hm
  · rw [hm] at hM
    rcases signed_square (x 0) (x 1) with h | h
    · exact ⟨0, by simpa [inner_axis, a, b, h] using hM⟩
    · exact ⟨1, by simpa [inner_axis, a, b, h] using hM⟩
  · rw [hm] at hM
    rcases signed_square (x 1) (x 2) with h | h
    · exact ⟨2, by simpa [inner_axis, b, c, h] using hM⟩
    · exact ⟨3, by simpa [inner_axis, b, c, h] using hM⟩
  · rw [hm] at hM
    rcases signed_square (x 2) (x 0) with h | h
    · exact ⟨4, by simpa [inner_axis, c, a, h] using hM⟩
    · exact ⟨5, by simpa [inner_axis, c, a, h] using hM⟩

/-- Six explicit relatively open sets cover the real unit two-sphere, and no
one of them contains an orthogonal pair. -/
theorem rational_six_axis_open_cover :
    (∀ i : Fin 6, IsOpen (color i)) ∧
    (∀ (i : Fin 6) (x : UnitSphere), x ∈ color i →
      ∀ (y : UnitSphere), y ∈ color i → inner ℝ (x : Space) (y : Space) ≠ 0) ∧
    (⋃ i : Fin 6, color i) = Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact isOpen_lt continuous_const
      (continuous_const.mul ((continuous_subtype_val.inner continuous_const).pow 2))
  · intro i x hx y hy hxy
    have ho : Orthonormal ℝ (![ (x : Space), (y : Space)] : Fin 2 → Space) := by
      simp [orthonormal_vecCons_iff, sphere_norm, hxy]
    have hB := ho.sum_inner_products_le (s := Finset.univ) (axis i)
    have hb : (inner ℝ (x : Space) (axis i))^2 +
        (inner ℝ (y : Space) (axis i))^2 ≤ 5 := by
      simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, axis_norm_sq] using hB
    change 5 < 2 * (inner ℝ (x : Space) (axis i))^2 at hx
    change 5 < 2 * (inner ℝ (y : Space) (axis i))^2 at hy
    linarith
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := large_projection (x : Space)
    have hn := sphere_norm x
    have hx : x ∈ color i := by
      change 5 < 2 * (inner ℝ (x : Space) (axis i))^2
      rw [hn] at hi
      linarith
    exact Set.mem_iUnion.mpr ⟨i, hx⟩

end D5.S3.Geometry.Orthogonality.RationalSixAxisCover
