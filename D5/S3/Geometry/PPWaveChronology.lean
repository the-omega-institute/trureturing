/- GID: D5/S3/Geometry/PPWaveChronology
   generality: G
   mirror-B: none(waiver:covered-by-perturbed-causal-order-weyl4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Timelike reachability from the axis of a plane wave with a quadratic Brinkmann profile. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
Omega original.

Timelike reachability from the axis of a plane wave with a quadratic Brinkmann profile.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.PPWaveDiamond

open Real Set

/-- A future timelike graph from the transverse axis, parametrized by the null coordinate. -/
def reachableFromAxis (ω L x y v : ℝ) : Prop :=
  ∃ X Y V : ℝ → ℝ,
    X 0 = 0 ∧ Y 0 = 0 ∧ V 0 = 0 ∧ X L = x ∧ Y L = y ∧ V L = v ∧
    ∀ t ∈ Icc 0 L, ∃ dx dy dv : ℝ,
      HasDerivAt X dx t ∧ HasDerivAt Y dy t ∧ HasDerivAt V dv t ∧
      dx ^ 2 + dy ^ 2 + ω ^ 2 * (X t ^ 2 - Y t ^ 2) < 2 * dv

/-- Forward null boundary through the first axial endpoint. -/
def axisHeight (ω L x y : ℝ) : ℝ :=
  (ω * (cosh (ω * L) / sinh (ω * L)) * x ^ 2 +
    ω * (cos (ω * L) / sin (ω * L)) * y ^ 2) / 2

private def xExt (ω L x t : ℝ) : ℝ := x / sinh (ω * L) * sinh (ω * t)
private def yExt (ω L y t : ℝ) : ℝ := y / sin (ω * L) * sin (ω * t)
private def xExt' (ω L x t : ℝ) : ℝ := x / sinh (ω * L) * (ω * cosh (ω * t))
private def yExt' (ω L y t : ℝ) : ℝ := y / sin (ω * L) * (ω * cos (ω * t))

private theorem xExt_deriv (ω L x t : ℝ) : HasDerivAt (xExt ω L x) (xExt' ω L x t) t := by
  have hh := (hasDerivAt_sinh (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  convert hh.const_mul (x / sinh (ω * L)) using 1 <;>
    first | rfl | (simp only [xExt', mul_one]; ring)

private theorem yExt_deriv (ω L y t : ℝ) : HasDerivAt (yExt ω L y) (yExt' ω L y t) t := by
  have hh := (hasDerivAt_sin (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  convert hh.const_mul (y / sin (ω * L)) using 1 <;>
    first | rfl | (simp only [yExt', mul_one]; ring)

private theorem xExt'_deriv (ω L x t : ℝ) :
    HasDerivAt (xExt' ω L x) (ω ^ 2 * xExt ω L x t) t := by
  have hh := (hasDerivAt_cosh (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  convert (hh.const_mul ω).const_mul (x / sinh (ω * L)) using 1 <;>
    first | rfl | (simp only [xExt, mul_one]; ring)

private theorem yExt'_deriv (ω L y t : ℝ) :
    HasDerivAt (yExt' ω L y) (-ω ^ 2 * yExt ω L y t) t := by
  have hh := (hasDerivAt_cos (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  convert (hh.const_mul ω).const_mul (y / sin (ω * L)) using 1 <;>
    first | rfl | (simp only [yExt, mul_one]; ring)

private theorem xExt_endpoint {ω L x : ℝ} (hω : 0 < ω) (hL : 0 < L) :
    xExt ω L x L = x := by
  exact div_mul_cancel₀ _ (sinh_pos_iff.mpr (mul_pos hω hL)).ne'

private theorem yExt_endpoint {ω L y : ℝ} (hω : 0 < ω) (hL : 0 < L) (hπ : ω * L < π) :
    yExt ω L y L = y := by
  exact div_mul_cancel₀ _ (sin_pos_of_pos_of_lt_pi (mul_pos hω hL) hπ).ne'

private def xWeight (ω t : ℝ) : ℝ := cosh (ω * t)
private def xWeight' (ω t : ℝ) : ℝ := ω * sinh (ω * t)
private def yWeight (ω L t : ℝ) : ℝ := cos (ω * (t - L / 2))
private def yWeight' (ω L t : ℝ) : ℝ := -ω * sin (ω * (t - L / 2))

private theorem xWeight_deriv (ω t : ℝ) :
    HasDerivAt (xWeight ω) (xWeight' ω t) t := by
  convert (hasDerivAt_cosh (ω * t)).comp t ((hasDerivAt_id t).const_mul ω) using 1 <;>
    first | rfl | (simp only [xWeight', mul_one]; ring)

private theorem xWeight'_deriv (ω t : ℝ) :
    HasDerivAt (xWeight' ω) (ω ^ 2 * xWeight ω t) t := by
  have hh := (hasDerivAt_sinh (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
  convert hh.const_mul ω using 1 <;>
    first | rfl | (simp only [xWeight, mul_one]; ring)

private theorem yWeight_deriv (ω L t : ℝ) :
    HasDerivAt (yWeight ω L) (yWeight' ω L t) t := by
  have hh := (hasDerivAt_cos (ω * (t - L / 2))).comp t
    (((hasDerivAt_id t).sub_const (L / 2)).const_mul ω)
  convert hh using 1 <;>
    first | rfl | (simp only [yWeight', mul_one]; ring)

private theorem yWeight'_deriv (ω L t : ℝ) :
    HasDerivAt (yWeight' ω L) (-ω ^ 2 * yWeight ω L t) t := by
  have hh := (hasDerivAt_sin (ω * (t - L / 2))).comp t
    (((hasDerivAt_id t).sub_const (L / 2)).const_mul ω)
  convert hh.const_mul (-ω) using 1 <;>
    first | rfl | (simp only [yWeight, mul_one]; ring)

private theorem yWeight_pos {ω L t : ℝ} (hω : 0 < ω) (hπ : ω * L < π) (ht : t ∈ Icc 0 L) :
    0 < yWeight ω L t := by
  have ha := mul_nonneg hω.le ht.1
  have hb := mul_le_mul_of_nonneg_left ht.2 hω.le
  apply cos_pos_of_mem_Ioo
  constructor <;> nlinarith only [ha, hb, hπ]

private def correctedAction (W W' Z Z' F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Z t * Z' t + 2 * Z' t * (F t - Z t) + W' t / W t * (F t - Z t) ^ 2

private theorem correctedAction_deriv
    {W W' Z Z' F : ℝ → ℝ} {k t d : ℝ}
    (hW : HasDerivAt W (W' t) t)
    (hW' : HasDerivAt W' (k * W t) t)
    (hnW : W t ≠ 0)
    (hZ : HasDerivAt Z (Z' t) t)
    (hZ' : HasDerivAt Z' (k * Z t) t)
    (hF : HasDerivAt F d t) :
    HasDerivAt (correctedAction W W' Z Z' F)
      (d ^ 2 + k * F t ^ 2 - (d - Z' t - W' t / W t * (F t - Z t)) ^ 2) t := by
  have h := ((hZ.mul hZ').add ((hZ'.const_mul 2).mul (hF.sub hZ))).add
    ((hW'.div hW hnW).mul ((hF.sub hZ).pow 2))
  convert h using 1
  · ext a
    rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Nat.reduceSubDiff, pow_one,
      Nat.cast_ofNat]
    field_simp
    ring

private theorem action_endpoint_value (ω L x y : ℝ) (hω : 0 < ω) (hL : 0 < L)
    (hπ : ω * L < π) :
    (xExt ω L x L * xExt' ω L x L + yExt ω L y L * yExt' ω L y L) / 2 =
      axisHeight ω L x y := by
  rw [xExt_endpoint hω hL, yExt_endpoint hω hL hπ]
  unfold xExt' yExt' axisHeight
  ring

/-- The strict endpoint inequality characterizes timelike reachability from the axis. -/
theorem reachableFromAxis_iff {ω L x y v : ℝ}
    (hω : 0 < ω) (hL : 0 < L) (hπ : ω * L < π) :
    reachableFromAxis ω L x y v ↔ axisHeight ω L x y < v := by
  constructor
  · rintro ⟨X, Y, V, hX0, hY0, hV0, hXL, hYL, hVL, ht⟩
    let Qx := correctedAction (xWeight ω) (xWeight' ω) (xExt ω L x) (xExt' ω L x) X
    let Qy := correctedAction (yWeight ω L) (yWeight' ω L) (yExt ω L y) (yExt' ω L y) Y
    let J := fun t => V t - (Qx t + Qy t) / 2
    have hJ t (hm : t ∈ Icc 0 L) : ∃ d, 0 < d ∧ HasDerivAt J d t := by
      obtain ⟨dx, dy, dv, hdx, hdy, hdv, htt⟩ := ht t hm
      have hx := correctedAction_deriv (xWeight_deriv ω t) (xWeight'_deriv ω t)
        (cosh_pos _).ne' (xExt_deriv ω L x t) (xExt'_deriv ω L x t) hdx
      have hy := correctedAction_deriv (yWeight_deriv ω L t) (yWeight'_deriv ω L t)
        (yWeight_pos hω hπ hm).ne' (yExt_deriv ω L y t) (yExt'_deriv ω L y t) hdy
      have hD := hdv.sub ((hx.add hy).div_const 2)
      have hsx :=
        sq_nonneg (dx - xExt' ω L x t - xWeight' ω t / xWeight ω t * (X t - xExt ω L x t))
      have hsy :=
        sq_nonneg (dy - yExt' ω L y t - yWeight' ω L t / yWeight ω L t * (Y t - yExt ω L y t))
      refine ⟨_, ?_, hD⟩
      nlinarith only [htt, hsx, hsy]

    have hmono := strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) L)
      (f := J) (fun t hm => (hJ t hm).choose_spec.2.continuousAt.continuousWithinAt)
      (fun t hm => by
        rw [interior_Icc] at hm
        obtain ⟨d, hpos, hd⟩ := hJ t ⟨hm.1.le, hm.2.le⟩
        simpa [hd.deriv] using hpos)
    have hJ0 : J 0 = 0 := by simp [J, Qx, Qy, correctedAction, hX0, hY0, hV0, xExt, yExt]
    have hJL : J L = v - axisHeight ω L x y := by
      rw [← action_endpoint_value ω L x y hω hL hπ]
      simp [J, Qx, Qy, correctedAction, hVL, hXL, hYL,
        xExt_endpoint hω hL, yExt_endpoint hω hL hπ]

    have h := hmono ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
    rw [hJ0, hJL] at h
    exact sub_pos.mp h
  · intro hv
    let slack := (v - axisHeight ω L x y) / L
    let V := fun t =>
      (xExt ω L x t * xExt' ω L x t + yExt ω L y t * yExt' ω L y t) / 2 + slack * t
    refine ⟨xExt ω L x, yExt ω L y, V, by simp [xExt], by simp [yExt],
      by simp [V, xExt, yExt], xExt_endpoint hω hL, yExt_endpoint hω hL hπ, ?_, ?_⟩
    · dsimp [V, slack]
      rw [action_endpoint_value ω L x y hω hL hπ, div_mul_cancel₀ _ hL.ne']
      ring
    · intro t _
      have hx := xExt_deriv ω L x t
      have hy := yExt_deriv ω L y t
      have hdv := (((hx.mul (xExt'_deriv ω L x t)).add
        (hy.mul (yExt'_deriv ω L y t))).div_const 2).add ((hasDerivAt_id t).const_mul slack)
      have hslack : 0 < slack := div_pos (sub_pos.mpr hv) hL
      refine ⟨_, _, _, hx, hy, hdv, ?_⟩
      simp only [mul_one]
      nlinarith only [hslack]

/-- The axial null boundary in flat spacetime. -/
def flatAxisHeight (L x y : ℝ) : ℝ := (x ^ 2 + y ^ 2) / (2 * L)

/-- The flat endpoint inequality follows by completing the square about the constant velocity. -/
theorem reachableFromAxis_flat_iff {L x y v : ℝ} (hL : 0 < L) :
    reachableFromAxis 0 L x y v ↔ flatAxisHeight L x y < v := by
  have hcost : ((x / L) ^ 2 + (y / L) ^ 2) * L / 2 = flatAxisHeight L x y := by
    unfold flatAxisHeight
    field_simp
  constructor
  · rintro ⟨X, Y, V, hX0, hY0, hV0, hXL, hYL, hVL, ht⟩
    let J := fun t => V t - ((x / L) * X t + (y / L) * Y t) +
      (((x / L) ^ 2 + (y / L) ^ 2) / 2) * t
    have hJ t (hm : t ∈ Icc 0 L) : ∃ d, 0 < d ∧ HasDerivAt J d t := by
      obtain ⟨dx, dy, dv, hdx, hdy, hdv, htt⟩ := ht t hm
      have hD := (hdv.sub ((hdx.const_mul (x / L)).add (hdy.const_mul (y / L)))).add
        ((hasDerivAt_id t).const_mul (((x / L) ^ 2 + (y / L) ^ 2) / 2))
      have hlt : dx ^ 2 + dy ^ 2 < 2 * dv := by simpa using htt
      refine ⟨_, ?_, hD⟩
      simp only [mul_one]
      nlinarith [sq_nonneg (dx - x / L), sq_nonneg (dy - y / L)]
    have hmono := strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) L)
      (f := J) (fun t hm => (hJ t hm).choose_spec.2.continuousAt.continuousWithinAt)
      (fun t hm => by
        rw [interior_Icc] at hm
        obtain ⟨d, hpos, hd⟩ := hJ t ⟨hm.1.le, hm.2.le⟩
        rwa [hd.deriv])
    have hJ0 : J 0 = 0 := by simp [J, hX0, hY0, hV0]
    have hJL : J L = v - flatAxisHeight L x y := by
      rw [← hcost]
      dsimp [J]
      rw [hXL, hYL, hVL]
      field_simp
      ring
    simpa only [hJ0, hJL, sub_pos] using hmono ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
  · intro hv
    refine ⟨fun t => (x / L) * t, fun t => (y / L) * t, fun t => (v / L) * t,
      by simp, by simp, by simp, div_mul_cancel₀ x hL.ne', div_mul_cancel₀ y hL.ne',
      div_mul_cancel₀ v hL.ne', ?_⟩
    intro t _
    have hd (z : ℝ) : HasDerivAt (fun t => (z / L) * t) (z / L) t := by
      simpa using (hasDerivAt_id t).const_mul (z / L)
    refine ⟨_, _, _, hd x, hd y, hd v, ?_⟩
    simp only [zero_pow two_ne_zero, zero_mul, add_zero]
    rw [← mul_div_assoc, lt_div_iff₀ hL]
    rw [← hcost] at hv
    linarith

/-- The axial chronological diamond, with the second reachability condition time-reversed. -/
def axialDiamond (ω T V : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Ioo 0 T ∧ reachableFromAxis ω p.1 p.2.1 p.2.2.1 p.2.2.2 ∧
    reachableFromAxis ω (T - p.1) p.2.1 p.2.2.1 (V - p.2.2.2)}

/-- The exact longitudinal interval in each transverse slice of the chronological diamond. -/
theorem mem_axialDiamond_iff {ω T V u x y v : ℝ} (hω : 0 < ω) (hπ : ω * T < π) :
    (u, x, y, v) ∈ axialDiamond ω T V ↔
      u ∈ Ioo 0 T ∧ v ∈ Ioo (axisHeight ω u x y) (V - axisHeight ω (T - u) x y) := by
  change (u ∈ Ioo 0 T ∧ reachableFromAxis ω u x y v ∧
    reachableFromAxis ω (T - u) x y (V - v)) ↔ _
  constructor
  · rintro ⟨hu, hx, hy⟩
    have h₁ := (reachableFromAxis_iff hω hu.1
      ((mul_lt_mul_of_pos_left hu.2 hω).trans hπ)).mp hx
    have h₂ := (reachableFromAxis_iff hω (sub_pos.mpr hu.2)
      ((mul_lt_mul_of_pos_left (sub_lt_self _ hu.1) hω).trans hπ)).mp hy
    exact ⟨hu, h₁, by linarith⟩
  · rintro ⟨hu, hv⟩
    refine ⟨hu, (reachableFromAxis_iff hω hu.1
      ((mul_lt_mul_of_pos_left hu.2 hω).trans hπ)).mpr hv.1, ?_⟩
    exact (reachableFromAxis_iff hω (sub_pos.mpr hu.2)
      ((mul_lt_mul_of_pos_left (sub_lt_self _ hu.1) hω).trans hπ)).mpr (by linarith [hv.2])

/-- The exact longitudinal interval in the flat axial diamond. -/
theorem mem_axialDiamond_flat_iff {T V u x y v : ℝ} :
    (u, x, y, v) ∈ axialDiamond 0 T V ↔
      u ∈ Ioo 0 T ∧ v ∈ Ioo (flatAxisHeight u x y) (V - flatAxisHeight (T - u) x y) := by
  change (u ∈ Ioo 0 T ∧ reachableFromAxis 0 u x y v ∧
    reachableFromAxis 0 (T - u) x y (V - v)) ↔ _
  constructor
  · rintro ⟨hu, hx, hy⟩
    have h₁ := (reachableFromAxis_flat_iff hu.1).mp hx
    have h₂ := (reachableFromAxis_flat_iff (sub_pos.mpr hu.2)).mp hy
    exact ⟨hu, h₁, by linarith⟩
  · rintro ⟨hu, hv⟩
    exact ⟨hu, (reachableFromAxis_flat_iff hu.1).mpr hv.1,
      (reachableFromAxis_flat_iff (sub_pos.mpr hu.2)).mpr (by linarith [hv.2])⟩

end Omega.PPWaveDiamond
