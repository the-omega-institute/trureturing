/- GID: D5/S3/Topology/JBAmbientSupport
   generality: G
   mirror-B: D5/B/S3/Topology/JBAmbientSupport
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Algebra.Jordan.Basic]
   utility: none
   digest: Uniform quadratic square bounds force ambient idempotent support. -/

module

public import D5.S3.Topology.JBComplexification

/-! Ambient idempotent support on the complete original JB carrier. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.JBAmbientSupport
open JBAlgebra JBPositiveShift JBComplexification

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}

/-- Domination by a scalar multiple of an actual idempotent forces support in its
ambient Peirce two-space. Positivity means an actual square in the original carrier. -/
theorem support_of_squares (A : Data X S u) (p x : X) (hp : S p p = p)
    (c : ℝ) (hplus : ∃ a : X, S a a = c • p + x)
    (hminus : ∃ b : X, S b b = c • p - x) : S p x = x := by
  let q := u - p
  let g (t : ℝ) := quadratic S (u + t • q) (c • p + x)
  let h (t : ℝ) := quadratic S (u + t • q) (c • p - x)
  have hright (v : X) : S v u = v := (A.symm v u).trans (A.unit_mul v)
  have hsum (t : ℝ) : g t + h t = (2 : ℝ) • (c • p) := by
    dsimp [g, h, q, quadratic]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, A.unit_mul, hright, hp]
    module
  have hdiff (t : ℝ) : g t - g (-t) = (4 * t) • S q x := by
    dsimp [g, q, quadratic]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, A.unit_mul, hright, hp]
    module
  have hbound (t : ℝ) : ‖g t‖ ≤ 2 * ‖c • p‖ := by
    obtain ⟨a, ha⟩ := hplus
    obtain ⟨b, hb⟩ := hminus
    obtain ⟨v, hv⟩ := quadratic_preserves_squares A (u + t • q) a
    obtain ⟨w, hw⟩ := quadratic_preserves_squares A (u + t • q) b
    rw [ha] at hv
    rw [hb] at hw
    have hm := A.square_mono v w
    change g t = S v v at hv
    change h t = S w w at hw
    rw [← hv, ← hw, hsum, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hm
    exact hm
  have huniform (t : ℝ) : |t| * ‖S q x‖ ≤ ‖c • p‖ := by
    have hn := norm_sub_le (g t) (g (-t))
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hn
    have ht := hbound t
    have hm := hbound (-t)
    nlinarith
  have hz : S q x = 0 := by
    by_contra hz
    have hn : 0 < ‖S q x‖ := norm_pos_iff.mpr hz
    let t := (‖c • p‖ + 1) / ‖S q x‖
    have ht : 0 ≤ t := le_of_lt (div_pos (by positivity) hn)
    have hc := huniform t
    rw [abs_of_nonneg ht] at hc
    have he : t * ‖S q x‖ = ‖c • p‖ + 1 := div_mul_cancel₀ _ (ne_of_gt hn)
    linarith
  dsimp [q] at hz
  exact (sub_eq_zero.mp (by simpa only [map_sub, LinearMap.sub_apply, A.unit_mul] using hz)).symm

/-- A supported vector has the original ambient order bounds with radius its norm. -/
theorem squares_of_supported (A : Data X S u) (p x : X) (hp : S p p = p)
    (hx : S p x = x) :
    (∃ a : X, S a a = ‖x‖ • p + x) ∧
    (∃ b : X, S b b = ‖x‖ • p - x) := by
  have hright (v : X) : S v u = v := (A.symm v u).trans (A.unit_mul v)
  constructor
  · obtain ⟨a, ha⟩ := square_of_ambient_center A (‖x‖ • u + x) ‖x‖ (norm_nonneg _)
      (by simpa only [add_sub_cancel_left] using le_rfl : ‖‖x‖ • u + x - ‖x‖ • u‖ ≤ ‖x‖)
    obtain ⟨b, hb⟩ := quadratic_preserves_squares A p a
    refine ⟨b, ?_⟩
    rw [ha] at hb
    rw [← hb]
    simp only [quadratic, map_add, map_smul, hright, hp, hx]
    module
  · obtain ⟨a, ha⟩ := square_of_ambient_center A (‖x‖ • u - x) ‖x‖ (norm_nonneg _)
      (by simpa only [sub_sub_cancel_left, norm_neg] using le_rfl : ‖‖x‖ • u - x - ‖x‖ • u‖ ≤ ‖x‖)
    obtain ⟨b, hb⟩ := quadratic_preserves_squares A p a
    refine ⟨b, ?_⟩
    rw [ha] at hb
    rw [← hb]
    simp only [quadratic, map_sub, map_smul, hright, hp, hx]
    module

/-- The square of a supported vector has the exact ambient upper bound at the
square of its original norm. -/
theorem corner_square_bound (A : Data X S u) (p a : X) (hp : S p p = p)
    (ha : S p a = a) : ∃ b : X, S b b = ‖a‖ ^ 2 • p - S a a := by
  have hab : S a p = a := (A.symm _ _).trans ha
  have hpol := polarized A p p a a
  simp only [bracket, hp, ha, hab] at hpol
  have hs : S p (S a a) = S a a := by
    apply sub_eq_zero.mp
    convert hpol using 1 <;> module
  obtain ⟨b, hb⟩ := (squares_of_supported A p (S a a) hp hs).2
  exact ⟨b, by simpa only [A.square_norm] using hb⟩

#print axioms support_of_squares

end D5.S3.Topology.JBAmbientSupport
