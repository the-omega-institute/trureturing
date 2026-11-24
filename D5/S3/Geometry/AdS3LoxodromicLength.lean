import D5.S3.Geometry.AdS3ModularBoundary

/-!
# Translation length of an AdS₃ filling

The explicit loxodromic deck maps are isometries of hyperbolic upper half-space.
Their minimum displacement is attained on the vertical axis, which projects
to the core of the solid torus. For modular fillings the boundary marking
gives the denominator in the core translation length.
-/

set_option autoImplicit false

open scoped MatrixGroups UpperHalfPlane

namespace D5.S3.Geometry.AdS3LoxodromicQuotient.Loxodromic

open HyperbolicUpperHalfSpace (height hyperbolicDist sinh_half_hyperbolicDist
  HyperbolicThreeSpace)

private theorem ambient_dist (x y : UpperHalfSpace) :
    dist x.val y.val =
      √(dist (coordinates x).1 (coordinates y).1 ^ 2 + (height x - height y) ^ 2) := by
  rw [WithLp.prod_dist_eq_of_L2, Real.dist_eq, sq_abs]
  rfl

private theorem height_act (g : Loxodromic) (n : ℤ) (x : UpperHalfSpace) :
    height (g.act n x) = g.rho ^ n * height x :=
  rfl

private theorem norm_multiplier (g : Loxodromic) (n : ℤ) :
    ‖g.multiplier n‖ = g.rho ^ n := by
  simp only [multiplier, phase, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos g.rho_pos n), mul_one]

private theorem sqrt_scale (a b : ℝ) (ha : 0 ≤ a) :
    √(a ^ 2 * b) = a * √b := by
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- Each explicit deck map preserves the hyperbolic distance. -/
theorem hyperbolicDist_act (g : Loxodromic) (n : ℤ) (x y : UpperHalfSpace) :
    hyperbolicDist (g.act n x) (g.act n y) = hyperbolicDist x y := by
  have ha : 0 < g.rho ^ n := zpow_pos g.rho_pos n
  have hh : dist (coordinates (g.act n x)).1 (coordinates (g.act n y)).1 =
      g.rho ^ n * dist (coordinates x).1 (coordinates y).1 := by
    simp only [coordinates_act, dist_eq_norm, ← mul_sub, norm_mul, norm_multiplier]
  have hd : dist (g.act n x).val (g.act n y).val = g.rho ^ n * dist x.val y.val := by
    rw [ambient_dist, ambient_dist, hh, height_act, height_act, ← mul_sub, ← sqrt_scale _ _ ha.le]
    congr 1
    ring
  have hv : √(height (g.act n x) * height (g.act n y)) = g.rho ^ n * √(height x * height y) := by
    rw [height_act, height_act, ← sqrt_scale _ _ ha.le]
    congr 1
    ring
  rw [← div_left_inj' (by norm_num : (2 : ℝ) ≠ 0), ← Real.sinh_inj,
    sinh_half_hyperbolicDist, sinh_half_hyperbolicDist, hd, hv, ← mul_left_comm,
    mul_div_mul_left _ _ ha.ne']

/-- The isometric equivalence of hyperbolic three-space induced by a deck power. -/
noncomputable def deckIsometry (g : Loxodromic) (n : ℤ) :
    HyperbolicThreeSpace ≃ᵢ HyperbolicThreeSpace where
  toFun x := ⟨g.act n x.coordinates⟩
  invFun x := ⟨g.act (-n) x.coordinates⟩
  left_inv x := by
    cases x with
    | mk x => simp only [← g.act_add, neg_add_cancel, g.act_zero]
  right_inv x := by
    cases x with
    | mk x => simp only [← g.act_add, add_neg_cancel, g.act_zero]
  isometry_toFun := Isometry.of_dist_eq fun x y => g.hyperbolicDist_act n x.coordinates y.coordinates

private theorem vertical_half_displacement (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    Real.sinh (|Real.log a| / 2) = |r - a * r| / (2 * √(r * (a * r))) := by
  have hroot : √(r * (a * r)) = r * √a := by
    rw [← sqrt_scale _ _ hr.le]
    congr 1
    ring
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have hsub : r - a * r = r * (1 - a) := by ring
  calc
    Real.sinh (|Real.log a| / 2) = |Real.sinh (Real.log (√a))| := by
      rw [Real.abs_sinh, Real.log_sqrt ha.le, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ = |a - 1| / (2 * √a) := by
      have hd : √a - (√a)⁻¹ = (a - 1) / √a := by
        rw [sub_div, Real.div_sqrt, one_div]
      rw [Real.sinh_log hs, hd, div_div, mul_comm (√a), abs_div,
        abs_of_pos (by positivity : 0 < 2 * √a)]
    _ = _ := by
      rw [hroot, hsub, abs_mul, abs_of_pos hr, abs_sub_comm a 1]
      field_simp

private theorem sinh_half_deck_length (g : Loxodromic) (n : ℤ) (x : UpperHalfSpace) :
    Real.sinh (|(n : ℝ)| * |Real.log g.rho| / 2) =
      |height x - height (g.act n x)| / (2 * √(height x * height (g.act n x))) := by
  rw [← abs_mul, ← Real.log_zpow, height_act]
  exact vertical_half_displacement _ _ (zpow_pos g.rho_pos n) x.property

/-- The translation length of the n-th deck map bounds every displacement from below. -/
theorem deck_length_le_displacement (g : Loxodromic) (n : ℤ) (x : UpperHalfSpace) :
    |(n : ℝ)| * |Real.log g.rho| ≤ hyperbolicDist x (g.act n x) := by
  have hx : 0 < height x := x.property
  have hy : 0 < height (g.act n x) := (g.act n x).property
  rw [← div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2),
    ← Real.sinh_le_sinh, g.sinh_half_deck_length, sinh_half_hyperbolicDist,
    div_le_div_iff_of_pos_right (by positivity), ambient_dist, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

private theorem displacement_eq_length_iff_horizontal (g : Loxodromic) (n : ℤ)
    (x : UpperHalfSpace) :
    hyperbolicDist x (g.act n x) = |(n : ℝ)| * |Real.log g.rho| ↔
      (coordinates x).1 = (coordinates (g.act n x)).1 := by
  have hx : 0 < height x := x.property
  have hy : 0 < height (g.act n x) := (g.act n x).property
  rw [← div_left_inj' (by norm_num : (2 : ℝ) ≠ 0), ← Real.sinh_inj,
    sinh_half_hyperbolicDist, g.sinh_half_deck_length,
    div_left_inj' (by positivity), ambient_dist, ← Real.sqrt_sq_eq_abs]
  rw [← sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.sq_sqrt (sq_nonneg _)]
  nth_rw 2 [← zero_add ((height x - height (g.act n x)) ^ 2)]
  rw [add_right_cancel_iff, pow_eq_zero_iff (by norm_num), dist_eq_zero]

/-- Every point of the vertical axis realizes the translation length. -/
theorem displacement_eq_length_of_axis (g : Loxodromic) (n : ℤ) (x : UpperHalfSpace)
    (hx : (coordinates x).1 = 0) :
    hyperbolicDist x (g.act n x) = |(n : ℝ)| * |Real.log g.rho| := by
  rw [g.displacement_eq_length_iff_horizontal, coordinates_act]
  simp [hx]

/-- For a nonidentity deck power, the minimizing locus is exactly the vertical axis. -/
theorem displacement_eq_length_iff_axis (g : Loxodromic) {n : ℤ} (hn : n ≠ 0)
    (x : UpperHalfSpace) :
    hyperbolicDist x (g.act n x) = |(n : ℝ)| * |Real.log g.rho| ↔
      (coordinates x).1 = 0 := by
  refine ⟨fun h => ?_, g.displacement_eq_length_of_axis n x⟩
  have hfixed := (g.displacement_eq_length_iff_horizontal n x).mp h
  rw [coordinates_act] at hfixed
  change (coordinates x).1 = g.multiplier n * (coordinates x).1 at hfixed
  have hmul : g.multiplier n ≠ 1 := by
    intro hm
    apply hn
    apply (zpow_eq_one_iff_right₀ g.rho_pos.le g.rho_lt_one.ne).mp
    rw [← g.norm_multiplier n, hm, norm_one]
  have hprod : (g.multiplier n - 1) * (coordinates x).1 = 0 := by
    rw [sub_mul, one_mul, ← hfixed, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hmul)

/-- The minimizing locus projects to the center of the disk in the solid torus chart. -/
theorem displacement_eq_length_iff_core (g : Loxodromic) {n : ℤ} (hn : n ≠ 0)
    (x : UpperHalfSpace) :
    hyperbolicDist x (g.act n x) = |(n : ℝ)| * |Real.log g.rho| ↔
      (g.solidTorusHomeomorph (Quotient.mk g.compactOrbitSetoid (interiorPoint x))).1.val = 0 := by
  rw [g.displacement_eq_length_iff_axis hn, g.solidTorusHomeomorph_mk]
  change (coordinates x).1 = 0 ↔ (g.compactCoverHomeomorph (interiorPoint x)).2.val = 0
  rw [(g.compactCoverHomeomorph_apply (interiorPoint x)).2]
  change (coordinates x).1 = 0 ↔
    phase (-g.theta * g.compactTime (interiorPoint x)) * (coordinates x).1 /
      (radius (interiorPoint x) : ℂ) = 0
  have hx : 0 < height x := x.property
  have hr : 0 < radius (interiorPoint x) := by
    change 0 < √(‖(coordinates x).1‖ ^ 2 + (height x) ^ 2)
    positivity
  simp [phase, hr.ne']

/-- The infimum of n-th deck displacements is attained and has the stated value. -/
theorem isLeast_deck_displacement (g : Loxodromic) (n : ℤ) :
    IsLeast (Set.range fun x : UpperHalfSpace => hyperbolicDist x (g.act n x))
      (|(n : ℝ)| * |Real.log g.rho|) := by
  let x : UpperHalfSpace := ⟨WithLp.toLp 2 (0, 1), zero_lt_one⟩
  exact ⟨⟨x, g.displacement_eq_length_of_axis n x rfl⟩,
    fun _ ⟨y, hy⟩ => hy ▸ g.deck_length_le_displacement n y⟩

/-- The translation length of the n-th deck map as an infimum over the cover. -/
theorem sInf_deck_displacement (g : Loxodromic) (n : ℤ) :
    sInf (Set.range fun x : UpperHalfSpace => hyperbolicDist x (g.act n x)) =
      |(n : ℝ)| * |Real.log g.rho| :=
  (g.isLeast_deck_displacement n).csInf_eq

/-- The generator's translation length in the filling with the given modular boundary marking. -/
theorem modular_core_translation_length (γ : SL(2, ℤ)) (τ : ℍ) :
    sInf (Set.range fun x : UpperHalfSpace =>
      hyperbolicDist x ((modularFilling (γ • τ)).act 1 x)) =
        2 * Real.pi * τ.im / ‖modularFactor γ τ‖ ^ 2 := by
  have him : (γ • τ).im = τ.im / ‖modularFactor γ τ‖ ^ 2 := by
    simpa only [ModularGroup.denom_apply, modularFactor, Complex.normSq_eq_norm_sq] using
      ModularGroup.im_smul_eq_div_normSq γ τ
  rw [sInf_deck_displacement]
  simp only [Int.cast_one, abs_one, one_mul]
  change |Real.log (Real.exp (-(2 * Real.pi * (γ • τ).im)))| = _
  rw [Real.log_exp, abs_neg,
    abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (γ • τ).im_pos), him]
  ring

end D5.S3.Geometry.AdS3LoxodromicQuotient.Loxodromic
