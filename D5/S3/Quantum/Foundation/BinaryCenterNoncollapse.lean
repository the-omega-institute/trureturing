/- GID: D5/S3/Quantum/Foundation/BinaryCenterNoncollapse
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/BinaryCenterNoncollapse
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Binary original compatibility bounds center variation on each fixed sphere. -/

import D5.S3.Quantum.Foundation.BinaryCenterGeometry
import D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation

/-! Quantitative variation and attained distance on each fixed original sphere. -/

noncomputable section
open Set Metric Filter Topology
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.BinaryCenterNoncollapse

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity SingleLabelNormalBody ContinuousFrameSum BinaryCenterGeometry
open ReciprocalExclusionLimits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

variable (hc : IsClosed (C : Set V))
  (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)

include hc hs hg hB in
/-- On each actual chart sphere, BC alone gives a quantitative Lipschitz
bound for the original centers. No global center-continuity assumption is used. -/
theorem sphere_center_lipschitz (hBC : binaryCompatible hB)
    (p : pure C u) (b : ExclusionChart C u p) :
    LipschitzWith ⟨Metric.diam (base C u) / 2, by positivity⟩
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin b.dim)) 1 =>
        center hB (chartPure hc hs hg hB p b x (by simpa using x.property))) := by
  let E := EuclideanSpace ℝ (Fin b.dim)
  let label (z : E) (hz : ‖z‖ = 1) := chartPure hc hs hg hB p b z hz
  have memK (r : pure C u) : center hB r ∈ base C u :=
    (chart_mem (hB r).some (by simp)).1
  have mapCombo (x y : E) (t : ℝ) :
      b.param (t • x + (1-t) • y) = t • b.param x + (1-t) • b.param y :=
    Convex.combo_affine_apply (by ring)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : ‖(x : E)‖ = 1 := by simpa using x.property
  have hy : ‖(y : E)‖ = 1 := by simpa using y.property
  by_cases hxy : (x : E) = y
  · have he : x = y := Subtype.ext hxy
    subst y
    simp
  let d : ℝ := ‖(x : E) - y‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hd2 : d ≤ 2 := by
    calc
      d ≤ ‖(x : E)‖ + ‖(y : E)‖ := norm_sub_le _ _
      _ = 2 := by rw [hx, hy]; norm_num
  let k : E := d⁻¹ • ((x : E) - y)
  have hk : ‖k‖ = 1 := by
    simp [k, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le), d, hd.ne']
  have hdk : d • k = (x : E) - y := by simp [k, smul_smul, hd.ne']
  let v : ℝ := (2+d)/4
  have hv : v ∈ Icc (0 : ℝ) 1 := by dsimp [v]; constructor <;> linarith
  let a := label x hx
  let c := label y hy
  let nc := label (-(y : E)) (by simpa using hy)
  let z := label k hk
  let nz := label (-k) (by simpa using hk)
  have orig : (1/2 : ℝ) • (a : V) + (1-1/2 : ℝ) • (nc : V) =
      v • (z : V) + (1-v) • (nz : V) := by
    change (1/2 : ℝ) • b.param x + (1-1/2 : ℝ) • b.param (-(y : E)) =
      v • b.param k + (1-v) • b.param (-k)
    rw [← mapCombo, ← mapCombo]
    congr 1
    calc
      (1/2 : ℝ) • (x : E) + (1-1/2 : ℝ) • (-(y : E)) =
          (1/2 : ℝ) • ((x : E) - y) := by module
      _ = (d/2) • k := by rw [← hdk]; module
      _ = v • k + (1-v) • (-k) := by dsimp [v]; module
  have origAnti : (1/2 : ℝ) • (c : V) + (1-1/2 : ℝ) • (nc : V) =
      (1/2 : ℝ) • (z : V) + (1-1/2 : ℝ) • (nz : V) := by
    change (1/2 : ℝ) • b.param y + (1-1/2 : ℝ) • b.param (-(y : E)) =
      (1/2 : ℝ) • b.param k + (1-1/2 : ℝ) • b.param (-k)
    rw [← mapCombo, ← mapCombo]
    congr 1
    module
  have bc := hBC a nc z nz (1/2) v (by norm_num) hv orig
  have ba := hBC c nc z nz (1/2) (1/2) (by norm_num) (by norm_num) origAnti
  have hsum : center hB a + center hB nc =
      (2*v) • center hB z + (2*(1-v)) • center hB nz := by
    have h := congrArg (fun w : V => (2 : ℝ) • w) bc
    convert h using 1 <;> module
  have hanti : center hB c + center hB nc = center hB z + center hB nz := by
    have h := congrArg (fun w : V => (2 : ℝ) • w) ba
    convert h using 1 <;> module
  have hdiff : center hB a - center hB c =
      (d/2) • (center hB z - center hB nz) := by
    calc
      center hB a - center hB c =
          (center hB a + center hB nc) - (center hB c + center hB nc) := by abel
      _ = (2*v) • center hB z + (2*(1-v)) • center hB nz -
          (center hB z + center hB nz) := by rw [hsum, hanti]
      _ = _ := by dsimp [v]; module
  have hbound : ‖center hB z - center hB nz‖ ≤ Metric.diam (base C u) := by
    simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem'
      (base_compact hc hs).isBounded.ediam_ne_top (memK z) (memK nz)
  change dist (center hB a) (center hB c) ≤ (Metric.diam (base C u) / 2) * dist x y
  rw [dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg (div_nonneg hd.le (by norm_num))]
  calc
    d/2 * ‖center hB z - center hB nz‖ ≤ d/2 * Metric.diam (base C u) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (Metric.diam (base C u) / 2) * dist x y := by
      rw [Subtype.dist_eq, dist_eq_norm]
      dsimp [d]
      ring

include hc hs hg in
/-- The fixed-sphere minimum is attained and strictly positive. Its own
constant bounds every whole exclusion with label on that sphere, and a
diameter-zero sequence eventually avoids that fixed sphere. -/
theorem fixed_sphere_noncollapse (h3 : threeBallExclusions C u)
    (hBC : binaryCompatible (CommonOldExclusionConfirmation.three_implies_balls h3))
    (p : pure C u) :
    ∃ δ : ℝ, 0 < δ ∧
      (∃ q₀ : pure C u, (q₀ : V) ∈ exclusion C u p ∧
        δ = 2 * ‖(p : V) - center (CommonOldExclusionConfirmation.three_implies_balls h3) q₀‖ ∧
        ∀ q : pure C u, (q : V) ∈ exclusion C u p →
          δ ≤ 2 * ‖(p : V) - center (CommonOldExclusionConfirmation.three_implies_balls h3) q‖) ∧
      (∀ q : pure C u, (q : V) ∈ exclusion C u p → δ ≤ Metric.diam (exclusion C u q)) ∧
      ∀ an : ℕ → pure C u,
        Tendsto (fun n => Metric.diam (exclusion C u (an n))) atTop (𝓝 0) →
        ∀ᶠ n in atTop, (an n : V) ∉ exclusion C u p := by
  classical
  let B := CommonOldExclusionConfirmation.three_implies_balls h3
  let b := (B p).some
  let E := EuclideanSpace ℝ (Fin b.dim)
  let S := Metric.sphere (0 : E) 1
  let label (x : S) := chartPure hc hs hg B p b x (by simpa using x.property)
  let f (x : S) := ‖(p : V) - center B (label x)‖
  have hcont : Continuous f :=
    (continuous_const.sub (sphere_center_lipschitz hc hs hg B hBC p b).continuous).norm
  have : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  obtain ⟨z, hz⟩ := exists_norm_eq E zero_le_one
  have hSne : (Set.univ : Set S).Nonempty := ⟨⟨z, by simpa [S] using hz⟩, mem_univ _⟩
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  obtain ⟨x₀, _, hmin⟩ := isCompact_univ.exists_isMinOn hSne hcont.continuousOn
  have hpos : 0 < f x₀ := by
    apply norm_pos_iff.mpr
    intro hzero
    have he : (p : V) = center B (label x₀) := sub_eq_zero.mp hzero
    have hm := (MixedExclusionGeometry.centerSection hc hs hg B (label x₀)).property.1
    apply hm
    change center B (label x₀) ∈ pure C u
    rw [← he]
    exact p.property
  let δ := 2 * f x₀
  have hδ : 0 < δ := mul_pos (by norm_num) hpos
  have onSphere (q : pure C u) (hq : (q : V) ∈ exclusion C u p) :
      ∃ x : S, label x = q := by
    have hh : (q : V) ∈ exclusion C u p ∩ pure C u := ⟨hq, q.property⟩
    rw [chart_boundary hc hs hg B p b] at hh
    obtain ⟨x, hx, hxe⟩ := hh
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hminq (q : pure C u) (hq : (q : V) ∈ exclusion C u p) :
      δ ≤ 2 * ‖(p : V) - center B q‖ := by
    obtain ⟨x, rfl⟩ := onSphere q hq
    exact mul_le_mul_of_nonneg_left (hmin (mem_univ x)) (by norm_num)
  have oldCenter_eq (q : pure C u) : CommonOldExclusionConfirmation.oldCenter h3 q = center B q := by
    let g := CommonOldExclusionConfirmation.oldChart h3 q
    have gd (x) : g x = g 0 + g.linear.toContinuousLinearMap x := by
      simpa [add_comm] using congrFun g.decomp x
    have bd (x) : (B q).some.param x = (B q).some.param 0 +
        (B q).some.param.linear.toContinuousLinearMap x := by
      simpa [add_comm] using congrFun (B q).some.param.decomp x
    apply D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq
      (g 0) ((B q).some.param 0) g.linear.toContinuousLinearMap
      (B q).some.param.linear.toContinuousLinearMap
    have whole : g '' closedBall 0 1 =
        (B q).some.param '' closedBall 0 1 :=
      (h3 q).choose_spec.2.trans (B q).some.whole.symm
    rw [show (fun x => g 0 + g.linear.toContinuousLinearMap x) = g from
      funext (fun x => (gd x).symm)]
    rw [show (fun x => (B q).some.param 0 +
        (B q).some.param.linear.toContinuousLinearMap x) = (B q).some.param from
      funext (fun x => (bd x).symm)]
    exact whole
  have bound (q : pure C u) (hq : (q : V) ∈ exclusion C u p) :
      δ ≤ Metric.diam (exclusion C u q) := by
    have hp := (exclusion_symmetric p q).mp hq
    have hr := (CommonOldExclusionConfirmation.old_geometry hc hs hg h3 q).2.1 p hp
    rw [oldCenter_eq] at hr
    have hdiam := Metric.dist_le_diam_of_mem'
      ((exclusion_ball_faces hc hs hg B).1 q).2.1.isBounded.ediam_ne_top hp hr
    have he : dist (p : V) ((2 : ℝ) • center B q - p) =
        2 * ‖(p : V) - center B q‖ := by
      rw [dist_eq_norm, show (p : V) - ((2 : ℝ) • center B q - p) =
        (2 : ℝ) • ((p : V) - center B q) by module, norm_smul]
      norm_num
    exact (hminq q hq).trans (he ▸ hdiam)
  refine ⟨δ, hδ, ⟨label x₀, chart_mem b (by simpa using (le_of_eq (Metric.mem_sphere_zero_iff_norm.mp x₀.property))), rfl, hminq⟩,
    bound, ?_⟩
  intro an han
  have hsmall : ∀ᶠ n in atTop, Metric.diam (exclusion C u (an n)) < δ :=
    han.eventually (gt_mem_nhds hδ)
  exact hsmall.mono (fun n hn hnp => (not_lt_of_ge (bound (an n) hnp)) hn)

end D5.S3.Quantum.Foundation.BinaryCenterNoncollapse
