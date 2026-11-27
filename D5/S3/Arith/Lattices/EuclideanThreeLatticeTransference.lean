/- GID: D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/EuclideanThreeLatticeTransference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shortest-vector projection and reduced planar covering give the squared product 11/12. -/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
Project off a shortest vector twice, retaining the separation bound at each step.
The final image is generated over the integers by a shortest vector. Its
normalization gives an integral dual vector. After rounding its direction once,
the reduced lattice in the perpendicular plane gives the remaining correction.
In dimension four, two reduced planes and a bound on three successive shortest
lengths give the squared product `43 / 36`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Module Set Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference

section ReducedPlanarCover

-- The triangle covering proof comes from the completed ReducedPlanarCover.lean packet.
private theorem norm_sq_orthogonal_smul_add {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (hab : ⟪a, b⟫_ℝ = 0) (u v : ℝ) :
    ‖u • a + v • b‖ ^ 2 = u ^ 2 * ‖a‖ ^ 2 + v ^ 2 * ‖b‖ ^ 2 := by
  simp only [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hab,
    mul_zero, add_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

private noncomputable def reduced_plane_radius_sq (A B α : ℝ) : ℝ :=
  (B + α ^ 2 * A) * (B + (1 - α) ^ 2 * A) / (4 * B)

private theorem reduced_radius_product_le (A B α : ℝ)
    (hA : 0 ≤ A) (hα : 0 ≤ α) (hhalf : α ≤ 1 / 2)
    (hreduced : A ≤ B + α ^ 2 * A) :
    (B + α ^ 2 * A) * (B + (1 - α) ^ 2 * A) ≤ 2 * B ^ 2 := by
  let slack : ℝ := B - (1 - α ^ 2) * A
  have hslack : 0 ≤ slack := by
    calc
      0 ≤ B + α ^ 2 * A - A := sub_nonneg.mpr hreduced
      _ = slack := by
        dsimp only [slack]
        ring
  have hone : 0 ≤ 1 - α := by linarith only [hhalf]
  have htwo : 0 ≤ 1 - 2 * α := by linarith only [hhalf]
  have hαprod : 0 ≤ α * (1 - α) := mul_nonneg hα hone
  have htail : 0 ≤ 1 - α - α ^ 2 := by
    calc
      0 ≤ (1 - 2 * α) + α * (1 - α) := add_nonneg htwo hαprod
      _ = 1 - α - α ^ 2 := by ring
  have hlinear : 0 ≤ 1 + 2 * α * (1 - 2 * α) :=
    add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num) hα) htwo)
  have hboundary : 0 ≤ 2 * A ^ 2 * (α * (1 - α)) * (1 - α - α ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A)) hαprod) htail
  -- The constant term is the defect at B = (1 - α²) A.
  apply sub_nonneg.mp
  calc
    0 ≤ slack ^ 2 + slack * (A * (1 + 2 * α * (1 - 2 * α))) +
        2 * A ^ 2 * (α * (1 - α)) * (1 - α - α ^ 2) :=
      add_nonneg (add_nonneg (sq_nonneg slack) (mul_nonneg hslack (mul_nonneg hA hlinear)))
        hboundary
    _ = 2 * B ^ 2 - (B + α ^ 2 * A) * (B + (1 - α) ^ 2 * A) := by
      dsimp only [slack]
      ring

private theorem reduced_plane_radius_sq_le_half (A B α : ℝ)
    (hA : 0 ≤ A) (hB : 0 < B) (hα : 0 ≤ α) (hhalf : α ≤ 1 / 2)
    (hreduced : A ≤ B + α ^ 2 * A) :
    reduced_plane_radius_sq A B α ≤ B / 2 := by
  unfold reduced_plane_radius_sq
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hB)).2
  calc
    _ ≤ 2 * B ^ 2 := reduced_radius_product_le A B α hA hα hhalf hreduced
    _ = (B / 2) * (4 * B) := by ring

private theorem reduced_plane_length_le_of_le_sixth (A B α : ℝ)
    (hA : 0 ≤ A) (hα : 0 ≤ α) (hsixth : α ≤ 1 / 6)
    (hreduced : A ≤ B + α ^ 2 * A) : A ≤ 36 * B / 35 := by
  have hsquare := pow_le_pow_left₀ hα hsixth 2
  have hscaled := mul_le_mul_of_nonneg_right hsquare hA
  linarith only [hreduced, hscaled]

private theorem reduced_plane_radius_sq_le_four_ninths (A B α : ℝ)
    (hA : 0 ≤ A) (hB : 0 < B) (hsixth : 1 / 6 ≤ α) (hhalf : α ≤ 1 / 2)
    (hreduced : A ≤ B + α ^ 2 * A) :
    reduced_plane_radius_sq A B α ≤ 4 * B / 9 := by
  have hα : 0 ≤ α := by linarith only [hsixth]
  have hgap : 0 < 1 - α ^ 2 := by
    have hsquare := pow_le_pow_left₀ hα hhalf 2
    linarith only [hsquare]
  let t : ℝ := A / B
  let u : ℝ := 1 / (1 - α ^ 2)
  have ht : 0 ≤ t := div_nonneg hA hB.le
  have hu : 0 ≤ u := div_nonneg zero_le_one hgap.le
  have htB : t * B = A := div_mul_cancel₀ A hB.ne'
  have htu : t ≤ u := by
    apply (le_div_iff₀ hgap).2
    change (A / B) * (1 - α ^ 2) ≤ 1
    rw [div_mul_eq_mul_div₀]
    apply (div_le_iff₀ hB).2
    rw [one_mul]
    calc
      A * (1 - α ^ 2) = A - α ^ 2 * A := by ring
      _ ≤ B := by linarith only [hreduced]
  have hprod :
      (1 + α ^ 2 * t) * (1 + (1 - α) ^ 2 * t) ≤
        (1 + α ^ 2 * u) * (1 + (1 - α) ^ 2 * u) :=
    mul_le_mul
      (add_le_add_right (mul_le_mul_of_nonneg_left htu (sq_nonneg α)) 1)
      (add_le_add_right (mul_le_mul_of_nonneg_left htu (sq_nonneg (1 - α))) 1)
      (add_nonneg zero_le_one (mul_nonneg (sq_nonneg (1 - α)) ht))
      (add_nonneg zero_le_one (mul_nonneg (sq_nonneg α) hu))
  let d : ℝ := (1 - α) * (1 + α) ^ 2
  have hminus : 0 < 1 - α := by linarith only [hhalf]
  have hplus : 0 < 1 + α := by linarith only [hα]
  have hd : 0 < d := mul_pos hminus (pow_pos hplus 2)
  have hend : (1 + α ^ 2 * u) * (1 + (1 - α) ^ 2 * u) / 4 = 1 / (2 * d) := by
    dsimp only [u, d]
    field_simp [hgap.ne', hminus.ne', hplus.ne'] <;> ring
  have hdenom : (9 / 8 : ℝ) ≤ d := by
    apply sub_nonneg.mp
    calc
      0 ≤ (1 / 2 - α) * (α ^ 2 + 3 * α / 2 - 1 / 4) :=
        mul_nonneg (sub_nonneg.mpr hhalf) (by linarith only [sq_nonneg α, hsixth])
      _ = d - 9 / 8 := by
        dsimp only [d]
        ring
  have hbound : 1 / (2 * d) ≤ (4 / 9 : ℝ) :=
    (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hd)).2
      (by linarith only [hdenom])
  calc
    reduced_plane_radius_sq A B α = B * ((1 + α ^ 2 * t) * (1 + (1 - α) ^ 2 * t) / 4) := by
      rw [← htB]
      unfold reduced_plane_radius_sq
      field_simp [hB.ne'] <;> ring
    _ ≤ B * ((1 + α ^ 2 * u) * (1 + (1 - α) ^ 2 * u) / 4) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod (by norm_num)) hB.le
    _ = B * (1 / (2 * d)) := by rw [hend]
    _ ≤ B * (4 / 9) := mul_le_mul_of_nonneg_left hbound hB.le
    _ = 4 * B / 9 := by ring

/-- The lattice generated by `a` and `α • a + b` covers their real plane with
squared distance at most the squared circumradius of the triangle with vertices
`0`, `a`, and `α • a + b`. -/
private theorem exists_int_norm_sq_le_radius_of_reduced_plane {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (A B α : ℝ) (ha : ‖a‖ ^ 2 = A) (hb : ‖b‖ ^ 2 = B)
    (hB : 0 < B) (hab : ⟪a, b⟫_ℝ = 0) (s t : ℝ) :
    ∃ m n : ℤ, ‖(s - (m : ℝ)) • a + (t - (n : ℝ)) • (α • a + b)‖ ^ 2 ≤
      reduced_plane_radius_sq A B α := by
  let g : E := α • a + b
  change ∃ m n : ℤ, ‖(s - (m : ℝ)) • a + (t - (n : ℝ)) • g‖ ^ 2 ≤
    reduced_plane_radius_sq A B α
  let q (u v : ℝ) : ℝ := u ^ 2 * A + v ^ 2 * B
  have hnorm (u v : ℝ) : ‖u • a + v • b‖ ^ 2 = q u v := by
    simpa only [q, ha, hb] using norm_sq_orthogonal_smul_add a b hab u v
  have hcoords (u v : ℝ) : ‖u • a + v • g‖ ^ 2 = q (u + v * α) v := by
    have heq : u • a + v • g = (u + v * α) • a + v • b := by
      dsimp only [g]
      rw [smul_add, smul_smul, ← add_assoc, ← add_smul]
    exact (congrArg (fun x : E => ‖x‖ ^ 2) heq).trans (hnorm (u + v * α) v)
  let centerB : ℝ := (B + α ^ 2 * A - α * A) / (2 * B)
  let c : E := (1 / 2 : ℝ) • a + centerB • b
  let radiusSq : ℝ := q (1 / 2) centerB
  have hcenter : 2 * B * centerB = B + α ^ 2 * A - α * A :=
    mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hB))
  have hcenter_dist (u v : ℝ) :
      ‖(u • a + v • b) - c‖ ^ 2 = q (u - 1 / 2) (v - centerB) := by
    have heq : (u • a + v • b) - c = (u - 1 / 2) • a + (v - centerB) • b := by
      simp only [c, add_sub_add_comm, sub_smul]
    exact (congrArg (fun x : E => ‖x‖ ^ 2) heq).trans (hnorm (u - 1 / 2) (v - centerB))
  -- The first two vertices have equal squared distances by symmetry in the a-coordinate.
  have hcenter_g : q (α - 1 / 2) (1 - centerB) = radiusSq := by
    calc
      q (α - 1 / 2) (1 - centerB) =
          radiusSq + (B + α ^ 2 * A - α * A - 2 * B * centerB) := by
        dsimp only [radiusSq, q]
        ring
      _ = radiusSq := by rw [hcenter, sub_self, add_zero]
  have hradius : radiusSq = reduced_plane_radius_sq A B α := by
    unfold reduced_plane_radius_sq
    apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 4) hB))).2
    calc
      radiusSq * (4 * B) = B * A + (2 * B * centerB) ^ 2 := by
        dsimp only [radiusSq, q]
        ring
      _ = (B + α ^ 2 * A) * (B + (1 - α) ^ 2 * A) := by
        rw [hcenter]
        ring
  have htriangle (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hcut : u + v ≤ 1) :
      ∃ i j : ℤ, ‖(u - (i : ℝ)) • a + (v - (j : ℝ)) • g‖ ^ 2 ≤
        reduced_plane_radius_sq A B α := by
    let d₀ : ℝ := ‖u • a + v • g‖ ^ 2
    let d₁ : ℝ := ‖(u - 1) • a + v • g‖ ^ 2
    let d₂ : ℝ := ‖u • a + (v - 1) • g‖ ^ 2
    -- Expand the weighted squared distances in orthogonal coordinates.
    have hmean :
        (1 - u - v) * d₀ + u * d₁ + v * d₂ =
          radiusSq - ‖((u + v * α) • a + v • b) - c‖ ^ 2 := by
      simp only [d₀, d₁, d₂, hcoords, hcenter_dist]
      calc
        _ = (1 - v) * radiusSq + v * q (α - 1 / 2) (1 - centerB) -
            q (u + v * α - 1 / 2) (v - centerB) := by
          dsimp only [radiusSq, q]
          ring
        _ = _ := by
          rw [hcenter_g]
          ring
    have hmean_le : (1 - u - v) * d₀ + u * d₁ + v * d₂ ≤ radiusSq :=
      hmean.le.trans (sub_le_self _ (sq_nonneg _))
    let nearestSq : ℝ := min d₀ (min d₁ d₂)
    have hmin₀ : nearestSq ≤ d₀ := min_le_left d₀ (min d₁ d₂)
    have hmin₁ : nearestSq ≤ d₁ := (min_le_right d₀ (min d₁ d₂)).trans (min_le_left d₁ d₂)
    have hmin₂ : nearestSq ≤ d₂ := (min_le_right d₀ (min d₁ d₂)).trans (min_le_right d₁ d₂)
    have hweight : 0 ≤ 1 - u - v := by linarith only [hcut]
    have hmin_mean : nearestSq ≤ (1 - u - v) * d₀ + u * d₁ + v * d₂ := by
      calc
        nearestSq = (1 - u - v) * nearestSq + u * nearestSq + v * nearestSq := by ring
        _ ≤ _ := add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hmin₀ hweight)
            (mul_le_mul_of_nonneg_left hmin₁ hu))
          (mul_le_mul_of_nonneg_left hmin₂ hv)
    have hmin_bound : min d₀ (min d₁ d₂) ≤ reduced_plane_radius_sq A B α :=
      hmin_mean.trans (hmean_le.trans hradius.le)
    rcases min_le_iff.mp hmin_bound with h₀ | hother
    · refine ⟨0, 0, ?_⟩
      simpa only [d₀, Int.cast_zero, sub_zero] using h₀
    · rcases min_le_iff.mp hother with h₁ | h₂
      · refine ⟨1, 0, ?_⟩
        simpa only [d₁, Int.cast_one, Int.cast_zero, sub_zero] using h₁
      · refine ⟨0, 1, ?_⟩
        simpa only [d₂, Int.cast_zero, Int.cast_one, sub_zero] using h₂
  let m₀ : ℤ := ⌊s⌋
  let n₀ : ℤ := ⌊t⌋
  let u : ℝ := s - (m₀ : ℝ)
  let v : ℝ := t - (n₀ : ℝ)
  have hu : 0 ≤ u := Int.fract_nonneg s
  have hv : 0 ≤ v := Int.fract_nonneg t
  have hu_lt : u < 1 := Int.fract_lt_one s
  have hv_lt : v < 1 := Int.fract_lt_one t
  by_cases hcut : u + v ≤ 1
  · obtain ⟨i, j, hij⟩ := htriangle u v hu hv hcut
    refine ⟨m₀ + i, n₀ + j, ?_⟩
    simpa only [Int.cast_add, u, v, sub_sub] using hij
  · -- Reflect through the midpoint of the diagonal from 0 to a + g.
    obtain ⟨i, j, hij⟩ :=
      htriangle (1 - u) (1 - v) (sub_nonneg.mpr hu_lt.le) (sub_nonneg.mpr hv_lt.le)
        (by linarith only [lt_of_not_ge hcut])
    refine ⟨m₀ + (1 - i), n₀ + (1 - j), ?_⟩
    have hs : s - ((m₀ + (1 - i) : ℤ) : ℝ) = -((1 - u) - (i : ℝ)) := by
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, u]
      ring
    have ht : t - ((n₀ + (1 - j) : ℤ) : ℝ) = -((1 - v) - (j : ℝ)) := by
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, v]
      ring
    simpa only [hs, ht, neg_smul, ← neg_add, norm_neg] using hij

/-- The cover for a centered lift `e`, with the basis sign chosen so the scalar
radius estimates apply to its coefficient. -/
private theorem exists_int_norm_sq_le_radius_of_reduced_lift {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b e : E) (α : ℝ) (hB : 0 < ‖b‖ ^ 2) (hab : ⟪a, b⟫_ℝ = 0)
    (he : e = α • a + b) (s t : ℝ) :
    ∃ m n : ℤ, ‖(s - (m : ℝ)) • a + (t - (n : ℝ)) • e‖ ^ 2 ≤
      reduced_plane_radius_sq (‖a‖ ^ 2) (‖b‖ ^ 2) |α| := by
  by_cases hα : 0 ≤ α
  · simpa only [← he, abs_of_nonneg hα] using
      exists_int_norm_sq_le_radius_of_reduced_plane a b (‖a‖ ^ 2) (‖b‖ ^ 2)
        α rfl rfl hB hab s t
  · have ha' : ‖-a‖ ^ 2 = ‖a‖ ^ 2 := by rw [norm_neg]
    have hab' : inner ℝ (-a) b = 0 := by rw [inner_neg_left, hab, neg_zero]
    have he' : (-α) • (-a) + b = e := by
      simpa only [neg_smul, smul_neg, neg_neg] using he.symm
    obtain ⟨m, n, hbound⟩ := exists_int_norm_sq_le_radius_of_reduced_plane (-a) b
      (‖a‖ ^ 2) (‖b‖ ^ 2) (-α) ha' rfl hB hab' (-s) t
    rw [he'] at hbound
    refine ⟨-m, n, ?_⟩
    have hs : -(-s - (m : ℝ)) = s - ((-m : ℤ) : ℝ) := by
      push_cast
      ring
    simpa only [smul_neg, ← neg_smul, hs, abs_of_neg (lt_of_not_ge hα)] using hbound

/-- The head and tail radii together, using the projected shortest-length ratio. -/
private theorem reduced_plane_outer_radii_sum_le (a₁ a₂ a₃ a₄ α₁ α₃ : ℝ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 < a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 < a₄)
    (hα₁ : 0 ≤ α₁) (hhalf₁ : α₁ ≤ 1 / 2)
    (hα₃ : 0 ≤ α₃) (hhalf₃ : α₃ ≤ 1 / 2)
    (hred₁ : a₁ ≤ a₂ + α₁ ^ 2 * a₁) (hred₃ : a₃ ≤ a₄ + α₃ ^ 2 * a₃)
    (hsep₂ : 3 * a₂ / 4 ≤ a₃) (hratio : a₂ ≤ 3 * a₄ / 2) :
    reduced_plane_radius_sq a₁ a₂ α₁ + reduced_plane_radius_sq a₃ a₄ α₃ ≤
      (43 / 36 : ℝ) * a₄ := by
  have hfirst := reduced_plane_radius_sq_le_half a₁ a₂ α₁ ha₁ ha₂ hα₁ hhalf₁ hred₁
  by_cases hsmall : α₃ ≤ 1 / 6
  · have hlength := reduced_plane_length_le_of_le_sixth a₃ a₄ α₃ ha₃ hα₃ hsmall hred₃
    have hlast := reduced_plane_radius_sq_le_half a₃ a₄ α₃ ha₃ ha₄ hα₃ hhalf₃ hred₃
    calc
      _ ≤ (83 / 70 : ℝ) * a₄ := by linarith only [hfirst, hlast, hsep₂, hlength]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) ha₄.le
  · have hlast := reduced_plane_radius_sq_le_four_ninths a₃ a₄ α₃ ha₃ ha₄
      (le_of_lt (lt_of_not_ge hsmall)) hhalf₃ hred₃
    linarith only [hfirst, hlast, hratio]

end ReducedPlanarCover

section Projection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private noncomputable def projectOff (a : V) : V →ₗ[ℝ] V :=
  (ℝ ∙ a)ᗮ.starProjection.toLinearMap

private noncomputable def projected (L : Submodule ℤ V) (a : V) : Submodule ℤ V :=
  L.map ((projectOff a).restrictScalars ℤ)

omit [FiniteDimensional ℝ V] in
private theorem sub_projectOff_mem_span (a x : V) : x - projectOff a x ∈ ℝ ∙ a := by
  have hsplit : (ℝ ∙ a).starProjection x + projectOff a x = x :=
    Submodule.starProjection_add_starProjection_orthogonal (K := ℝ ∙ a) x
  rw [← eq_sub_of_add_eq hsplit]
  exact Submodule.starProjection_apply_mem (ℝ ∙ a) x

omit [FiniteDimensional ℝ V] in
private theorem span_projected_eq_map (L : Submodule ℤ V) (a : V) :
    Submodule.span ℝ (projected L a : Set V) =
      (Submodule.span ℝ (L : Set V)).map (projectOff a) := by
  rw [projected, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.map_span]

private theorem span_projected (L : Submodule ℤ V) {a : V}
    (ha : a ∈ Submodule.span ℝ (L : Set V)) :
    Submodule.span ℝ (projected L a : Set V) =
      (ℝ ∙ a)ᗮ ⊓ Submodule.span ℝ (L : Set V) := by
  rw [span_projected_eq_map]
  have hline : (ℝ ∙ a) ≤ Submodule.span ℝ (L : Set V) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr ha
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_inf.mpr
      ⟨Submodule.starProjection_apply_mem (ℝ ∙ a)ᗮ x, ?_⟩
    simpa only [sub_sub_cancel] using
      Submodule.sub_mem _ hx (hline (sub_projectOff_mem_span a x))
  · intro y hy
    obtain ⟨hyOrthogonal, hySpan⟩ := Submodule.mem_inf.mp hy
    exact Submodule.mem_map.mpr ⟨y, hySpan, Submodule.starProjection_eq_self_iff.mpr hyOrthogonal⟩

private theorem finrank_span_projected (L : Submodule ℤ V) {a : V}
    (ha : a ∈ L) (ha0 : a ≠ 0) :
    1 + finrank ℝ (Submodule.span ℝ (projected L a : Set V)) =
      finrank ℝ (Submodule.span ℝ (L : Set V)) := by
  have haR : a ∈ Submodule.span ℝ (L : Set V) := Submodule.subset_span ha
  rw [span_projected L haR]
  have hline : (ℝ ∙ a) ≤ Submodule.span ℝ (L : Set V) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr haR
  simpa only [finrank_span_singleton (K := ℝ) ha0] using
    Submodule.finrank_add_inf_finrank_orthogonal hline

omit [FiniteDimensional ℝ V] in
private theorem inner_projectOff {a y : V} (hy : y ∈ (ℝ ∙ a)ᗮ) (x : V) :
    inner ℝ y (projectOff a x) = inner ℝ y x := by
  change inner ℝ y ((ℝ ∙ a)ᗮ.starProjection x) = inner ℝ y x
  rw [← Submodule.inner_starProjection_left_eq_right (ℝ ∙ a)ᗮ y x,
    Submodule.starProjection_eq_self_iff.mpr hy]

omit [FiniteDimensional ℝ V] in
private theorem rounded_smul_sq_le (a : V) (t : ℝ) :
    ‖(t - (round t : ℝ)) • a‖ ^ 2 ≤ ‖a‖ ^ 2 / 4 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_sub_round t) 2
  rw [norm_smul, Real.norm_eq_abs, mul_pow]
  calc
    _ ≤ ((1 : ℝ) / 2) ^ 2 * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = _ := by ring

/-- Lift an image vector and center its coefficient along the projection direction. -/
private theorem lift_projected (L : Submodule ℤ V) {a : V} (ha : a ∈ L)
    {v : V} (hv : v ∈ projected L a) :
    ∃ e ∈ L, projectOff a e = v ∧
      ∃ α : ℝ, |α| ≤ 1 / 2 ∧ e = α • a + v ∧
        ‖e‖ ^ 2 = α ^ 2 * ‖a‖ ^ 2 + ‖v‖ ^ 2 := by
  change v ∈ L.map ((projectOff a).restrictScalars ℤ) at hv
  obtain ⟨z, hz, hp⟩ := Submodule.mem_map.mp hv
  change projectOff a z = v at hp
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_projectOff_mem_span a z)
  let k : ℤ := round t
  have hzero : projectOff a a = 0 :=
    Submodule.starProjection_orthogonalComplement_singleton_eq_zero (𝕜 := ℝ) a
  have heq : z - k • a = (t - (k : ℝ)) • a + v := by
    rw [sub_smul, Int.cast_smul_eq_zsmul ℝ, ht, hp]
    abel
  have hav : inner ℝ a v = 0 := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← hp]
    exact Submodule.starProjection_apply_mem (ℝ ∙ a)ᗮ z
  refine ⟨z - k • a, L.sub_mem hz (L.smul_mem k ha), ?_,
    t - (k : ℝ), abs_sub_round t, heq, ?_⟩
  · rw [map_sub, map_zsmul, hp, hzero, zsmul_zero, sub_zero]
  · rw [heq]
    simpa only [one_smul, one_pow, one_mul] using
      norm_sq_orthogonal_smul_add a v hav (t - (k : ℝ)) 1

/-- The projected image has a uniform gap around zero whenever the direction is shortest. -/
private theorem projected_separation (L : Submodule ℤ V) {a : V} (ha : a ∈ L)
    (hmin : ∀ z ∈ L, z ≠ 0 → ‖a‖ ^ 2 ≤ ‖z‖ ^ 2)
    {u : V} (hu : u ∈ projected L a) (hu0 : u ≠ 0) :
    3 * ‖a‖ ^ 2 / 4 ≤ ‖u‖ ^ 2 := by
  obtain ⟨e, he, hp, α, hα, _, henorm⟩ := lift_projected L ha hu
  have he0 : e ≠ 0 := by
    intro h
    apply hu0
    rw [← hp, h, map_zero]
  have hαsq : α ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [← sq_abs α]
    exact pow_le_pow_left₀ (abs_nonneg _) hα 2
  have hshort := hmin e he he0
  rw [henorm] at hshort
  linarith only [hshort, mul_le_mul_of_nonneg_right hαsq (sq_nonneg ‖a‖)]

/-- The scalar bound obtained by comparing two fractional lifts and their difference. -/
private theorem shortest_projection_ratio_scalar (A B C r q p : ℝ)
    (hA : 0 < A) (hAB : 3 * A / 4 ≤ B) (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hreduced : B ≤ C + r ^ 2 * B)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hq : A ≤ q ^ 2 * A + B) (hq' : A ≤ (1 - q) ^ 2 * A + B)
    (hp : A ≤ p ^ 2 * A + (C + r ^ 2 * B))
    (hp' : A ≤ (1 - p) ^ 2 * A + (C + r ^ 2 * B))
    (hdiff : A ≤ (p - q) ^ 2 * A + (C + (1 - r) ^ 2 * B)) :
    A ≤ 3 * C / 2 := by
  by_contra! hAC
  have hB0 : 0 ≤ B := by linarith only [hA, hAB]
  have hrthird : 1 / 3 < r := by
    by_contra! hr
    have hrB := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 hr 2) hB0
    nlinarith only [hAC, hAB, hreduced, hrB]
  have hrSq := pow_le_pow_left₀ hr0 hrhalf 2
  have hscale : 0 < 1 - r ^ 2 := by linarith only [hrSq]
  have hscaledB : (1 - r ^ 2) * B ≤ C := by nlinarith only [hreduced]
  have hscaledE : (1 - r ^ 2) * (C + r ^ 2 * B) ≤ C := by
    have h := mul_le_mul_of_nonneg_left hreduced (sq_nonneg r)
    nlinarith only [h]
  let s : ℝ := 5 / 6 - r
  have hs : s = 5 / 6 - r := rfl
  -- This keeps both fractional lifts in the same interval near 1/2.
  have hproduct : (2 : ℝ) / 3 ≤ (1 - r ^ 2) * (1 - s ^ 2) := by
    have htail : 0 ≤ 13 + 5 * r - 6 * r ^ 2 := by
      linarith only [hr0, hrSq]
    have hfact : 0 ≤ (1 - 2 * r) * (3 * r - 1) * (13 + 5 * r - 6 * r ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith only [hrhalf])
        (by linarith only [hrthird])) htail
    have hid : (1 - r ^ 2) * (1 - s ^ 2) - 2 / 3 =
        (1 - 2 * r) * (3 * r - 1) * (13 + 5 * r - 6 * r ^ 2) / 36 := by
      rw [hs]
      ring
    linarith only [hid, hfact]
  have hcutoff : C < (1 - r ^ 2) * (A * (1 - s ^ 2)) := by
    calc
      C < (2 / 3) * A := by linarith only [hAC]
      _ ≤ ((1 - r ^ 2) * (1 - s ^ 2)) * A := mul_le_mul_of_nonneg_right hproduct hA.le
      _ = _ := by ring
  have hinterval (X t : ℝ) (hX : (1 - r ^ 2) * X ≤ C) (ht0 : 0 ≤ t) (ht1 : t < 1)
      (ht : A ≤ t ^ 2 * A + X) (ht' : A ≤ (1 - t) ^ 2 * A + X) :
      s < t ∧ t < 1 - s := by
    have hshort : X < A * (1 - s ^ 2) :=
      (mul_lt_mul_iff_right₀ hscale).mp (hX.trans_lt hcutoff)
    constructor
    · by_contra! h
      have hsq := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 h 2) hA.le
      nlinarith only [ht, hsq, hshort]
    · by_contra! h
      have hle : 1 - t ≤ s := by linarith only [h]
      have hsq := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (sub_nonneg.mpr ht1.le) hle 2) hA.le
      nlinarith only [ht', hsq, hshort]
  obtain ⟨hqs, hsq⟩ := hinterval B q hscaledB hq0 hq1 hq hq'
  obtain ⟨hps, hsp⟩ := hinterval (C + r ^ 2 * B) p hscaledE hp0 hp1 hp hp'
  let d : ℝ := r - 1 / 3
  have hd : d = r - 1 / 3 := rfl
  have hd0 : 0 ≤ d := by linarith only [hd, hrthird]
  have hdmax : d ≤ 1 / 6 := by linarith only [hd, hrhalf]
  have hclose : |p - q| < 2 * d := by
    apply abs_lt.mpr
    constructor <;> linarith only [hs, hd, hqs, hsq, hps, hsp]
  have hcloseSq : (p - q) ^ 2 ≤ 4 * d ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hclose.le 2
    rw [sq_abs] at h
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hr1 : 0 ≤ 1 - r := by linarith only [hrhalf]
  have hdiffScale : (1 + r) * (C + (1 - r) ^ 2 * B) ≤ 2 * C := by
    have h := mul_le_mul_of_nonneg_left hscaledB hr1
    nlinarith only [h]
  have hrpos : 0 < 1 + r := by linarith only [hr0]
  have hdSq : 4 * d ^ 2 ≤ (2 / 3) * d := by
    have h := mul_nonneg hd0 (show 0 ≤ (2 : ℝ) / 3 - 4 * d by linarith only [hdmax])
    nlinarith only [h]
  have hbudget : (1 + r) * (4 * d ^ 2) + 4 / 3 ≤ 1 + r := by
    have hrmax : 1 + r ≤ 3 / 2 := by linarith only [hrhalf]
    have hsmall : 0 ≤ (2 / 3) * d := mul_nonneg (by norm_num) hd0
    have h := (mul_le_mul_of_nonneg_left hdSq hrpos.le).trans
      (mul_le_mul_of_nonneg_right hrmax hsmall)
    linarith only [h, hd]
  have htooShort : (1 + r) * ((p - q) ^ 2 * A + (C + (1 - r) ^ 2 * B)) <
      (1 + r) * A := by
    calc
      _ = (1 + r) * ((p - q) ^ 2 * A) + (1 + r) * (C + (1 - r) ^ 2 * B) := by ring
      _ ≤ (1 + r) * ((4 * d ^ 2) * A) + 2 * C :=
        add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcloseSq hA.le) hrpos.le) hdiffScale
      _ < (1 + r) * ((4 * d ^ 2) * A) + (4 / 3) * A := by linarith only [hAC]
      _ = ((1 + r) * (4 * d ^ 2) + 4 / 3) * A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hA.le
  exact (not_lt_of_ge hdiff) ((mul_lt_mul_iff_right₀ hrpos).mp htooShort)

/-- A nonzero vector in the second projection has squared norm at least two thirds
of the original shortest squared norm. Both projection directions are shortest. -/
private theorem shortest_projection_ratio (L : Submodule ℤ V) {a b c : V}
    (ha : a ∈ L) (ha0 : a ≠ 0)
    (hamin : ∀ z ∈ L, z ≠ 0 → ‖a‖ ^ 2 ≤ ‖z‖ ^ 2)
    (hb : b ∈ projected L a) (hb0 : b ≠ 0)
    (hbmin : ∀ z ∈ projected L a, z ≠ 0 → ‖b‖ ^ 2 ≤ ‖z‖ ^ 2)
    (hc : c ∈ projected (projected L a) b) (hc0 : c ≠ 0) :
    ‖a‖ ^ 2 ≤ 3 * ‖c‖ ^ 2 / 2 := by
  have horth {M : Submodule ℤ V} {u v : V} (hv : v ∈ projected M u) :
      inner ℝ u v = 0 := by
    change v ∈ M.map ((projectOff u).restrictScalars ℤ) at hv
    obtain ⟨z, _, hz⟩ := Submodule.mem_map.mp hv
    change projectOff u z = v at hz
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← hz]
    exact Submodule.starProjection_apply_mem (ℝ ∙ u)ᗮ z
  have hzero (v : V) : projectOff v v = 0 :=
    Submodule.starProjection_orthogonalComplement_singleton_eq_zero (𝕜 := ℝ) v
  have hnorm {u v : V} (huv : inner ℝ u v = 0) (t : ℝ) :
      ‖t • u + v‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    simpa only [one_smul, one_pow, one_mul] using norm_sq_orthogonal_smul_add u v huv t 1

  -- Negating the centered lift and its projection preserves the squared lengths.
  obtain ⟨e₀, he₀, hPe₀, r₀, hr₀, heq₀, _⟩ := lift_projected (projected L a) hb hc
  have horient : ∃ c' ∈ projected (projected L a) b, c' ≠ 0 ∧ ‖c'‖ ^ 2 = ‖c‖ ^ 2 ∧
      ∃ e ∈ projected L a, projectOff b e = c' ∧
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 ∧ e = r • b + c' := by
    by_cases hr : 0 ≤ r₀
    · exact ⟨c, hc, hc0, rfl, e₀, he₀, hPe₀, r₀, hr, (le_abs_self r₀).trans hr₀, heq₀⟩
    · refine ⟨-c, (projected (projected L a) b).neg_mem hc, neg_ne_zero.mpr hc0, by rw [norm_neg],
        -e₀, (projected L a).neg_mem he₀, by rw [map_neg, hPe₀],
        -r₀, neg_nonneg.mpr (le_of_not_ge hr), (neg_le_abs r₀).trans hr₀, ?_⟩
      rw [heq₀, neg_add, neg_smul]
  obtain ⟨c', hc', hc'0, hc'norm, e, he, hPe, r, hr0, hrhalf, heq⟩ := horient
  have he_ne : e ≠ 0 := by
    intro h
    apply hc'0
    rw [← hPe, h, map_zero]
  have heb_ne : e - b ≠ 0 := by
    intro h
    have hPeb : projectOff b (e - b) = c' := by rw [map_sub, hPe, hzero, sub_zero]
    apply hc'0
    rw [← hPeb, h, map_zero]
  have heNorm : ‖e‖ ^ 2 = ‖c‖ ^ 2 + r ^ 2 * ‖b‖ ^ 2 := by
    rw [heq, hnorm (horth hc'), hc'norm, add_comm]
  have hebEq : e - b = (r - 1) • b + c' := by
    rw [heq, sub_smul, one_smul]
    abel
  have hebNorm : ‖e - b‖ ^ 2 = ‖c‖ ^ 2 + (1 - r) ^ 2 * ‖b‖ ^ 2 := by
    have hsq : (r - 1) ^ 2 = (1 - r) ^ 2 := by ring
    rw [hebEq, hnorm (horth hc'), hc'norm, hsq, add_comm]
  have hreduced := hbmin e he he_ne
  rw [heNorm] at hreduced

  -- Both the fractional lift and its translate by subtracting a project to u.
  have hfractional (u : V) (hu : u ∈ projected L a) (hu0 : u ≠ 0) :
      ∃ z ∈ L, projectOff a z = u ∧
        ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = t • a + u ∧
          ‖a‖ ^ 2 ≤ t ^ 2 * ‖a‖ ^ 2 + ‖u‖ ^ 2 ∧
          ‖a‖ ^ 2 ≤ (1 - t) ^ 2 * ‖a‖ ^ 2 + ‖u‖ ^ 2 := by
    obtain ⟨w, hw, hPw, α, _, hwEq, _⟩ := lift_projected L ha hu
    let k : ℤ := ⌊α⌋
    let t : ℝ := Int.fract α
    let z := w - k • a
    have hz : z ∈ L := L.sub_mem hw (L.smul_mem k ha)
    have hPz : projectOff a z = u := by
      dsimp only [z]
      rw [map_sub, map_zsmul, hPw, hzero, zsmul_zero, sub_zero]
    have hPz' : projectOff a (z - a) = u := by rw [map_sub, hPz, hzero, sub_zero]
    have hne (v : V) (hv : projectOff a v = u) : v ≠ 0 := by
      intro h
      apply hu0
      rw [← hv, h, map_zero]
    have hzEq : z = t • a + u := by
      dsimp only [z, t, Int.fract, k]
      rw [hwEq, sub_smul, Int.cast_smul_eq_zsmul ℝ]
      abel
    have hzEq' : z - a = (t - 1) • a + u := by
      rw [hzEq, sub_smul, one_smul]
      abel
    have hfirst := hamin z hz (hne z hPz)
    have hsecond := hamin (z - a) (L.sub_mem hz ha) (hne (z - a) hPz')
    have hsq : (t - 1) ^ 2 = (1 - t) ^ 2 := by ring
    rw [hzEq, hnorm (horth hu)] at hfirst
    rw [hzEq', hnorm (horth hu), hsq] at hsecond
    exact ⟨z, hz, hPz, t, Int.fract_nonneg α, Int.fract_lt_one α, hzEq, hfirst, hsecond⟩
  obtain ⟨zB, hzB, hPzB, q, hq0, hq1, hzBEq, hq, hq'⟩ := hfractional b hb hb0
  obtain ⟨zE, hzE, hPzE, p, hp0, hp1, hzEEq, hp, hp'⟩ := hfractional e he he_ne
  have hPdiff : projectOff a (zE - zB) = e - b := by rw [map_sub, hPzE, hPzB]
  have hdiff_ne : zE - zB ≠ 0 := by
    intro h
    apply heb_ne
    rw [← hPdiff, h, map_zero]
  have hdiffEq : zE - zB = (p - q) • a + (e - b) := by
    rw [hzEEq, hzBEq, sub_smul]
    abel
  have hdiff := hamin (zE - zB) (L.sub_mem hzE hzB) hdiff_ne
  rw [hdiffEq, hnorm (horth ((projected L a).sub_mem he hb)), hebNorm] at hdiff
  rw [heNorm] at hp hp'
  exact shortest_projection_ratio_scalar (‖a‖ ^ 2) (‖b‖ ^ 2) (‖c‖ ^ 2) r q p
    (sq_pos_of_pos (norm_pos_iff.mpr ha0)) (projected_separation L ha hamin hb hb0)
    hr0 hrhalf hreduced hq0 hq1 hp0 hp1 hq hq' hp hp' hdiff

private theorem discrete_projected (L : Submodule ℤ V) {a : V} (ha : a ∈ L) (ha0 : a ≠ 0)
    (hmin : ∀ z ∈ L, z ≠ 0 → ‖a‖ ^ 2 ≤ ‖z‖ ^ 2) :
    DiscreteTopology (projected L a) := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  refine discreteTopology_iff_isOpen_singleton_zero.mpr
    ⟨ball 0 (‖a‖ / 2), isOpen_ball, ?_⟩
  ext u
  change (u : V) ∈ ball 0 (‖a‖ / 2) ↔ u ∈ ({0} : Set (projected L a))
  rw [mem_ball_zero_iff, Set.mem_singleton_iff]
  constructor
  · intro hu
    apply Subtype.ext
    change (u : V) = 0
    by_contra hu0
    have hsep := projected_separation L ha hmin u.property hu0
    have hsq := pow_le_pow_left₀ (norm_nonneg (u : V)) hu.le 2
    nlinarith only [hsep, hsq, sq_pos_of_pos hapos]
  · rintro rfl
    simpa using (half_pos hapos)

private theorem exists_shortest (L : Submodule ℤ V) [DiscreteTopology L]
    (hL : 0 < finrank ℝ (Submodule.span ℝ (L : Set V))) :
    ∃ a ∈ L, a ≠ 0 ∧ ∀ z ∈ L, z ≠ 0 → ‖a‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  classical
  have hne : L ≠ ⊥ := by
    intro hz
    have hs : Submodule.span ℝ (L : Set V) = ⊥ := by
      apply Submodule.span_eq_bot.mpr
      intro z hzL
      change z ∈ L at hzL
      rw [hz] at hzL
      simpa only [Submodule.mem_bot] using hzL
    rw [hs, finrank_bot] at hL
    exact (lt_irrefl 0) hL
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let S : Set V := (closedBall 0 ‖u‖ ∩ (L : Set V)) \ {0}
  let : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
  have hclosed : IsClosed (L : Set V) := L.toAddSubgroup.isClosed_of_discreteTopology
  have hfinite : S.Finite :=
    (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall
      hclosed).subset Set.sdiff_subset
  have huS : u ∈ S := ⟨⟨mem_closedBall_zero_iff.mpr le_rfl, hu⟩, by simpa using hu0⟩
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S (fun z => ‖z‖ ^ 2) hfinite ⟨u, huS⟩
  refine ⟨a, ha.1.2, by simpa using ha.2, ?_⟩
  intro z hz hz0
  by_cases hball : z ∈ closedBall 0 ‖u‖
  · exact hmin z ⟨⟨hball, hz⟩, by simpa using hz0⟩
  · have hn : ‖u‖ ≤ ‖z‖ :=
      le_of_lt (lt_of_not_ge fun h => hball (mem_closedBall_zero_iff.mpr h))
    exact (hmin u huS).trans (pow_le_pow_left₀ (norm_nonneg u) hn 2)

private theorem exists_cyclic_generator (L : Submodule ℤ V) [DiscreteTopology L]
    (hdim : finrank ℝ (Submodule.span ℝ (L : Set V)) = 1) :
    ∃ c ∈ L, c ≠ 0 ∧ Submodule.span ℝ (L : Set V) = ℝ ∙ c ∧ L ≤ ℤ ∙ c := by
  have hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set V)) := by
    simpa only [hdim] using Nat.zero_lt_one
  obtain ⟨c, hc, hc0, hmin⟩ := exists_shortest L hpos
  have hspan : Submodule.span ℝ (L : Set V) = ℝ ∙ c :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim (Submodule.subset_span hc) hc0
  refine ⟨c, hc, hc0, hspan, ?_⟩
  intro z hz
  have hzR : z ∈ (ℝ ∙ c) := by
    rw [← hspan]
    exact Submodule.subset_span hz
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hzR
  let k : ℤ := round t
  refine Submodule.mem_span_singleton.mpr ⟨k, ?_⟩
  suffices hzero : z - k • c = 0 by exact (sub_eq_zero.mp hzero).symm
  by_contra herr
  have hshort := hmin (z - k • c) (L.sub_mem hz (L.smul_mem k hc)) herr
  have herror : z - k • c = (t - (k : ℝ)) • c := by
    rw [sub_smul, Int.cast_smul_eq_zsmul ℝ, ht]
  rw [herror] at hshort
  linarith only [hshort, rounded_smul_sq_le c t, sq_pos_of_pos (norm_pos_iff.mpr hc0)]

omit [FiniteDimensional ℝ V] in
/-- Normalize a generator of a cyclic projected image when the projection preserves
pairing against that generator. -/
private theorem normalized_mem_dual_of_cyclic_image (L : Submodule ℤ V) (P : V →ₗ[ℝ] V)
    {c : V} (hc0 : c ≠ 0) (hpair : ∀ z, inner ℝ c (P z) = inner ℝ c z)
    (hcyclic : L.map (P.restrictScalars ℤ) ≤ ℤ ∙ c) :
    let y := (‖c‖ ^ 2)⁻¹ • c
    y ∈ LinearMap.BilinForm.dualSubmodule (innerₗ V) L ∧ y ≠ 0 ∧ ‖y‖ ^ 2 = 1 / ‖c‖ ^ 2 := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  dsimp only
  refine ⟨?_, smul_ne_zero (inv_ne_zero (pow_ne_zero _ hcpos.ne')) hc0, ?_⟩
  · apply (LinearMap.BilinForm.mem_dualSubmodule (innerₗ V)).mpr
    intro z hz
    have hzP : P z ∈ ℤ ∙ c :=
      hcyclic (Submodule.mem_map_of_mem (f := P.restrictScalars ℤ) hz)
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hzP
    refine Submodule.mem_one.mpr ⟨k, ?_⟩
    change (k : ℝ) = inner ℝ ((‖c‖ ^ 2)⁻¹ • c) z
    rw [real_inner_smul_left, ← hpair z, ← hk, ← Int.cast_smul_eq_zsmul ℝ,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hcpos.ne']
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (‖c‖ ^ 2)⁻¹)]
    field_simp [hcpos.ne']

/-- A centered lift and the first basis vector correct the component removed by
two successive orthogonal projections. -/
private theorem exists_pair_cover (L : Submodule ℤ V) {a b : V} (ha : a ∈ L)
    (hamin : ∀ z ∈ L, z ≠ 0 → ‖a‖ ^ 2 ≤ ‖z‖ ^ 2)
    (hb : b ∈ projected L a) (hb0 : b ≠ 0) :
    ∃ α : ℝ, |α| ≤ 1 / 2 ∧ ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 + |α| ^ 2 * ‖a‖ ^ 2 ∧
      ∀ x : V, ∃ v ∈ L, ‖x - v‖ ^ 2 ≤
        ‖projectOff b (projectOff a x)‖ ^ 2 +
          reduced_plane_radius_sq (‖a‖ ^ 2) (‖b‖ ^ 2) |α| := by
  obtain ⟨e, he, hPe, α, hα, heq, henorm⟩ := lift_projected L ha hb
  have he0 : e ≠ 0 := by
    intro hz
    apply hb0
    rw [← hPe, hz, map_zero]
  have hreduced : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 + |α| ^ 2 * ‖a‖ ^ 2 := by
    rw [sq_abs, add_comm, ← henorm]
    exact hamin e he he0
  have hab : inner ℝ a b = 0 := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← hPe]
    exact Submodule.starProjection_apply_mem (ℝ ∙ a)ᗮ e
  have hba : a ∈ (ℝ ∙ b)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hab
  refine ⟨α, hα, hreduced, ?_⟩
  intro x
  let p := projectOff a x
  let q := projectOff b p
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (sub_projectOff_mem_span a x)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_projectOff_mem_span b p)
  have hbEq : b = e - α • a := by
    rw [heq]
    abel
  have hdecomp : (s - t * α) • a + t • e = x - q := by
    calc
      (s - t * α) • a + t • e = s • a + t • b := by
        rw [hbEq, smul_sub, smul_smul, sub_smul]
        abel
      _ = x - q := by
        rw [hs, ht]
        change (x - p) + (p - q) = x - q
        abel
  obtain ⟨m, n, hplanar⟩ := exists_int_norm_sq_le_radius_of_reduced_lift a b e α
    (sq_pos_of_pos (norm_pos_iff.mpr hb0)) hab heq (s - t * α) t
  let v : V := m • a + n • e
  have herr : x - v = q + ((s - t * α - (m : ℝ)) • a + (t - (n : ℝ)) • e) := by
    calc
      x - v = q + ((x - q) - v) := by abel
      _ = _ := by
        simp only [← hdecomp, v, add_sub_add_comm, sub_smul, Int.cast_smul_eq_zsmul ℝ]
  have hqa : inner ℝ q a = 0 := by
    rw [real_inner_comm a q]
    change inner ℝ a (projectOff b p) = 0
    rw [inner_projectOff hba]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (Submodule.starProjection_apply_mem (ℝ ∙ a)ᗮ x)
  have hqb : inner ℝ q b = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp
      (Submodule.starProjection_apply_mem (ℝ ∙ b)ᗮ p)
  have horth : inner ℝ q ((s - t * α - (m : ℝ)) • a + (t - (n : ℝ)) • e) = 0 := by
    simp only [heq, inner_add_right, real_inner_smul_right, hqa, hqb, mul_zero, add_zero]
  refine ⟨v, L.add_mem (L.smul_mem m ha) (L.smul_mem n he), ?_⟩
  change ‖x - v‖ ^ 2 ≤ ‖q‖ ^ 2 + _
  have hpythagoras := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  simp only [← pow_two] at hpythagoras
  rw [herr, hpythagoras]
  exact add_le_add_right hplanar _

omit [FiniteDimensional ℝ V] in
private theorem exists_lift_projected_pair (L : Submodule ℤ V) {a b w : V}
    (hw : w ∈ projected (projected L a) b) :
    ∃ v ∈ L, projectOff b (projectOff a v) = w := by
  obtain ⟨u, hu, hpu⟩ := Submodule.mem_map.mp
    (show w ∈ (projected L a).map ((projectOff b).restrictScalars ℤ) from hw)
  obtain ⟨v, hv, hpv⟩ := Submodule.mem_map.mp
    (show u ∈ L.map ((projectOff a).restrictScalars ℤ) from hu)
  change projectOff b u = w at hpu
  change projectOff a v = u at hpv
  exact ⟨v, hv, by rw [hpv, hpu]⟩

end Projection

public section

private abbrev E := EuclideanSpace ℝ (Fin 3)

/-- A discrete full three-dimensional lattice has a fixed nonzero integral-dual vector
whose squared length times the squared pointwise covering error is at most `11 / 12`. -/
theorem exists_dual_covering (L : Submodule ℤ (EuclideanSpace ℝ (Fin 3)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ y ∈ LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin 3))) L, y ≠ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), ∃ v ∈ L, ‖x - v‖ ^ 2 * ‖y‖ ^ 2 ≤ 11 / 12 := by
  classical
  have hfull : Submodule.span ℝ (L : Set E) = ⊤ :=
    (inferInstance : IsZLattice ℝ L).span_top
  have hdim : finrank ℝ (Submodule.span ℝ (L : Set E)) = 3 := by
    rw [hfull, finrank_top, finrank_euclideanSpace_fin]
  have hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set E)) := by rw [hdim]; decide
  obtain ⟨a, ha, ha0, hamin⟩ := exists_shortest L hpos
  let L₁ := projected L a
  let : DiscreteTopology L₁ := discrete_projected L ha ha0 hamin
  have hadim : 1 + finrank ℝ (Submodule.span ℝ (L₁ : Set E)) = 3 :=
    (finrank_span_projected L ha ha0).trans hdim
  have hpos₁ : 0 < finrank ℝ (Submodule.span ℝ (L₁ : Set E)) := by omega
  obtain ⟨b, hb, hb0, hbmin⟩ := exists_shortest L₁ hpos₁
  let L₂ := projected L₁ b
  let : DiscreteTopology L₂ := discrete_projected L₁ hb hb0 hbmin
  have hbdim : 1 + finrank ℝ (Submodule.span ℝ (L₂ : Set E)) =
      finrank ℝ (Submodule.span ℝ (L₁ : Set E)) :=
    finrank_span_projected L₁ hb hb0
  have hcdim : finrank ℝ (Submodule.span ℝ (L₂ : Set E)) = 1 := by omega
  obtain ⟨c, hc, hc0, hspan, hcyclic⟩ := exists_cyclic_generator L₂ hcdim
  have hc₂ : c ∈ (ℝ ∙ b)ᗮ ⊓ Submodule.span ℝ (L₁ : Set E) := by
    rw [← span_projected L₁ (Submodule.subset_span hb)]
    exact Submodule.subset_span hc
  have hc₁ : c ∈ (ℝ ∙ a)ᗮ ⊓ Submodule.span ℝ (L : Set E) := by
    rw [← span_projected L (Submodule.subset_span ha)]
    exact (Submodule.mem_inf.mp hc₂).2
  have hcbound := projected_separation L₁ hb hbmin hc hc0
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  let R := (projectOff b).comp (projectOff a)
  have hpair (z : E) : inner ℝ c (R z) = inner ℝ c z := by
    simp only [R, LinearMap.comp_apply, inner_projectOff (Submodule.mem_inf.mp hc₂).1,
      inner_projectOff (Submodule.mem_inf.mp hc₁).1]
  have hcyclicR : L.map (R.restrictScalars ℤ) ≤ ℤ ∙ c := by
    simpa only [R, L₂, L₁, projected, LinearMap.restrictScalars_comp, Submodule.map_comp]
      using hcyclic
  obtain ⟨hy, hy0, hynorm⟩ := normalized_mem_dual_of_cyclic_image L R hc0 hpair hcyclicR

  obtain ⟨α, hα, hreduced, hplane⟩ := exists_pair_cover L ha hamin hb hb0
  have hradius := reduced_plane_radius_sq_le_half (‖a‖ ^ 2) (‖b‖ ^ 2) |α|
    (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hb0)) (abs_nonneg α) hα hreduced
  obtain ⟨v₀, hv₀, hRc⟩ := exists_lift_projected_pair L (a := a) (b := b) hc
  change R v₀ = c at hRc

  refine ⟨(‖c‖ ^ 2)⁻¹ • c, hy, hy0, ?_⟩
  intro x
  have hx₁ : projectOff a x ∈ Submodule.span ℝ (L₁ : Set E) := by
    dsimp only [L₁]
    rw [span_projected_eq_map]
    exact Submodule.mem_map_of_mem (by rw [hfull]; exact Submodule.mem_top)
  have hx₂ : R x ∈ Submodule.span ℝ (L₂ : Set E) := by
    dsimp only [L₂]
    rw [span_projected_eq_map]
    exact Submodule.mem_map_of_mem hx₁
  rw [hspan] at hx₂
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx₂
  let k : ℤ := round t
  let p : E := x - k • v₀
  have hRp : R p = (t - (k : ℝ)) • c := by
    dsimp only [p]
    rw [map_sub, map_zsmul, hRc, ← ht, sub_smul, Int.cast_smul_eq_zsmul ℝ]
  have hnormal : ‖R p‖ ^ 2 ≤ ‖c‖ ^ 2 / 4 := by
    rw [hRp]
    exact rounded_smul_sq_le c t

  obtain ⟨w, hw, hplanar⟩ := hplane p
  change ‖p - w‖ ^ 2 ≤ ‖R p‖ ^ 2 + _ at hplanar
  refine ⟨k • v₀ + w, L.add_mem (L.smul_mem k hv₀) hw, ?_⟩
  rw [sub_add_eq_sub_sub, hynorm, mul_one_div]
  apply (div_le_iff₀ (sq_pos_of_pos hcpos)).mpr
  change ‖p - w‖ ^ 2 ≤ (11 / 12 : ℝ) * ‖c‖ ^ 2
  linarith only [hplanar, hnormal, hradius, hcbound]

private abbrev E₄ := EuclideanSpace ℝ (Fin 4)

/-- A discrete full four-dimensional lattice has a fixed nonzero integral-dual vector
whose squared length times the squared pointwise covering error is at most `43 / 36`. -/
theorem exists_dual_covering_four (L : Submodule ℤ (EuclideanSpace ℝ (Fin 4)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ y ∈ LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin 4))) L, y ≠ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin 4), ∃ v ∈ L, ‖x - v‖ ^ 2 * ‖y‖ ^ 2 ≤ 43 / 36 := by
  classical
  have hfull : Submodule.span ℝ (L : Set E₄) = ⊤ :=
    (inferInstance : IsZLattice ℝ L).span_top
  have hdim : finrank ℝ (Submodule.span ℝ (L : Set E₄)) = 4 := by
    rw [hfull, finrank_top, finrank_euclideanSpace_fin]
  have hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set E₄)) := by omega
  obtain ⟨a, ha, ha0, hamin⟩ := exists_shortest L hpos
  let L₁ := projected L a
  let : DiscreteTopology L₁ := discrete_projected L ha ha0 hamin
  have hadim : 1 + finrank ℝ (Submodule.span ℝ (L₁ : Set E₄)) = 4 :=
    (finrank_span_projected L ha ha0).trans hdim
  have hpos₁ : 0 < finrank ℝ (Submodule.span ℝ (L₁ : Set E₄)) := by omega
  obtain ⟨b, hb, hb0, hbmin⟩ := exists_shortest L₁ hpos₁
  let L₂ := projected L₁ b
  let : DiscreteTopology L₂ := discrete_projected L₁ hb hb0 hbmin
  have hbdim : 1 + finrank ℝ (Submodule.span ℝ (L₂ : Set E₄)) =
      finrank ℝ (Submodule.span ℝ (L₁ : Set E₄)) :=
    finrank_span_projected L₁ hb hb0
  have hpos₂ : 0 < finrank ℝ (Submodule.span ℝ (L₂ : Set E₄)) := by omega
  obtain ⟨c, hc, hc0, hcmin⟩ := exists_shortest L₂ hpos₂
  let L₃ := projected L₂ c
  let : DiscreteTopology L₃ := discrete_projected L₂ hc hc0 hcmin
  have hcdim : 1 + finrank ℝ (Submodule.span ℝ (L₃ : Set E₄)) =
      finrank ℝ (Submodule.span ℝ (L₂ : Set E₄)) :=
    finrank_span_projected L₂ hc hc0
  have hddim : finrank ℝ (Submodule.span ℝ (L₃ : Set E₄)) = 1 := by omega
  obtain ⟨d, hd, hd0, hspan, hcyclic⟩ := exists_cyclic_generator L₃ hddim

  -- The final lattice is generated over ℤ by d. The three projections
  -- preserve the inner product against d.
  have hd₃ : d ∈ (ℝ ∙ c)ᗮ ⊓ Submodule.span ℝ (L₂ : Set E₄) := by
    rw [← span_projected L₂ (Submodule.subset_span hc)]
    exact Submodule.subset_span hd
  have hd₂ : d ∈ (ℝ ∙ b)ᗮ ⊓ Submodule.span ℝ (L₁ : Set E₄) := by
    rw [← span_projected L₁ (Submodule.subset_span hb)]
    exact (Submodule.mem_inf.mp hd₃).2
  have hd₁ : d ∈ (ℝ ∙ a)ᗮ ⊓ Submodule.span ℝ (L : Set E₄) := by
    rw [← span_projected L (Submodule.subset_span ha)]
    exact (Submodule.mem_inf.mp hd₂).2
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  let R := (projectOff b).comp (projectOff a)
  let P := (projectOff c).comp R
  have hpair (z : E₄) : inner ℝ d (P z) = inner ℝ d z := by
    simp only [P, R, LinearMap.comp_apply, inner_projectOff (Submodule.mem_inf.mp hd₃).1,
      inner_projectOff (Submodule.mem_inf.mp hd₂).1, inner_projectOff (Submodule.mem_inf.mp hd₁).1]
  have hcyclicP : L.map (P.restrictScalars ℤ) ≤ ℤ ∙ d := by
    simpa only [P, R, L₃, L₂, L₁, projected, LinearMap.restrictScalars_comp, Submodule.map_comp]
      using hcyclic
  obtain ⟨hy, hy0, hynorm⟩ := normalized_mem_dual_of_cyclic_image L P hd0 hpair hcyclicP

  obtain ⟨α, hα, hredHead, hhead⟩ := exists_pair_cover L ha hamin hb hb0
  obtain ⟨β, hβ, hredTail, htail⟩ := exists_pair_cover L₂ hc hcmin hd hd0
  have hsep := projected_separation L₁ hb hbmin hc hc0
  have hratio : ‖b‖ ^ 2 ≤ 3 * ‖d‖ ^ 2 / 2 :=
    shortest_projection_ratio L₁ hb hb0 hbmin hc hc0 hcmin hd hd0
  have hbudget := reduced_plane_outer_radii_sum_le (‖a‖ ^ 2) (‖b‖ ^ 2) (‖c‖ ^ 2) (‖d‖ ^ 2)
    (|α|) (|β|) (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hb0))
    (sq_nonneg _) (sq_pos_of_pos hdpos) (abs_nonneg α) hα (abs_nonneg β) hβ
    hredHead hredTail hsep hratio

  refine ⟨(‖d‖ ^ 2)⁻¹ • d, hy, hy0, ?_⟩
  intro x
  have hx₁ : projectOff a x ∈ Submodule.span ℝ (L₁ : Set E₄) := by
    dsimp only [L₁]
    rw [span_projected_eq_map]
    exact Submodule.mem_map_of_mem (by rw [hfull]; exact Submodule.mem_top)
  have hx₂ : R x ∈ Submodule.span ℝ (L₂ : Set E₄) := by
    dsimp only [L₂]
    rw [span_projected_eq_map]
    exact Submodule.mem_map_of_mem hx₁
  have hx₃ : projectOff c (R x) ∈ Submodule.span ℝ (L₃ : Set E₄) := by
    dsimp only [L₃]
    rw [span_projected_eq_map]
    exact Submodule.mem_map_of_mem hx₂
  rw [hspan] at hx₃
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx₃
  have htailZero : projectOff d (projectOff c (R x)) = 0 := by
    have hzero : projectOff d d = 0 :=
      Submodule.starProjection_orthogonalComplement_singleton_eq_zero (𝕜 := ℝ) d
    rw [← ht, map_smul, hzero, smul_zero]

  -- Correct the tail in the projected integer lattice and lift its correction.
  obtain ⟨w, hw, htailBound⟩ := htail (R x)
  rw [htailZero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at htailBound
  obtain ⟨v₀, hv₀, hRv₀⟩ := exists_lift_projected_pair L (a := a) (b := b) hw
  change R v₀ = w at hRv₀
  obtain ⟨u, hu, hheadBound⟩ := hhead (x - v₀)
  change ‖x - v₀ - u‖ ^ 2 ≤ ‖R (x - v₀)‖ ^ 2 + _ at hheadBound
  rw [map_sub, hRv₀] at hheadBound
  refine ⟨v₀ + u, L.add_mem hv₀ hu, ?_⟩
  rw [sub_add_eq_sub_sub, hynorm, mul_one_div]
  apply (div_le_iff₀ (sq_pos_of_pos hdpos)).mpr
  linarith only [hheadBound, htailBound, hbudget]

end

end D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference
