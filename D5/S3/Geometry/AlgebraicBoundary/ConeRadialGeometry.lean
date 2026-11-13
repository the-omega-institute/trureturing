/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeRadialGeometry
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeRadialGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entire relative cone sections have quantitative radial sphere parametrizations. -/

import D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Tactic

/-! Quantitative gauge coordinates on entire compact cone sections. -/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace D5.S3.Geometry.AlgebraicBoundary.ConeRadialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem gauge_bounds {A : Set E} (hA : Convex ℝ A) {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hin : closedBall (0 : E) r ⊆ A) (hout : A ⊆ closedBall 0 R) :
    (∀ v : E, ‖v‖ / R ≤ gauge A v ∧ gauge A v ≤ ‖v‖ / r) ∧
      ∀ v w : E, |gauge A v - gauge A w| ≤ ‖v - w‖ / r := by
  have hball : ball (0 : E) r ⊆ A := ball_subset_closedBall.trans hin
  have h0 : A ∈ 𝓝 (0 : E) := mem_of_superset (ball_mem_nhds _ hr) hball
  refine ⟨fun v => ⟨le_gauge_of_subset_closedBall (absorbent_nhds_zero h0) hR.le hout,
    (le_div_iff₀ hr).mpr (by simpa [mul_comm] using mul_gauge_le_norm (x := v) hball)⟩, ?_⟩
  intro v w
  have hh := (hA.lipschitzWith_gauge (r := ⟨r, hr.le⟩) hr hball).dist_le_mul v w
  change dist (gauge A v) (gauge A w) ≤ r⁻¹ * dist v w at hh
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, div_eq_inv_mul] using hh

/-- The normalized endpoints obey a uniform estimate even for nonsymmetric bodies. -/
private theorem radial_distance_bound {A : Set E} (hA : Convex ℝ A) {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hin : closedBall (0 : E) r ⊆ A) (hout : A ⊆ closedBall 0 R)
    {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    dist ((gauge A v)⁻¹ • v) ((gauge A w)⁻¹ • w) ≤
      (R + R ^ 2 / r) * dist v w := by
  obtain ⟨hb, hlip⟩ := gauge_bounds hA hr hR hin hout
  have hvb : 1 / R ≤ gauge A v := by simpa [hv] using (hb v).1
  have hwb : 1 / R ≤ gauge A w := by simpa [hw] using (hb w).1
  have hvp : 0 < gauge A v := (one_div_pos.mpr hR).trans_le hvb
  have hwp : 0 < gauge A w := (one_div_pos.mpr hR).trans_le hwb
  have hvi : (gauge A v)⁻¹ ≤ R := by
    simpa only [one_div] using (one_div_le hvp hR).mpr hvb
  have hwi : (gauge A w)⁻¹ ≤ R := by
    simpa only [one_div] using (one_div_le hwp hR).mpr hwb
  have hinvdiff : |(gauge A v)⁻¹ - (gauge A w)⁻¹| ≤
      R ^ 2 * (‖v - w‖ / r) := by
    have hid : (gauge A v)⁻¹ - (gauge A w)⁻¹ =
        (gauge A w - gauge A v) * (gauge A v)⁻¹ * (gauge A w)⁻¹ := by
      field_simp
      <;> ring
    rw [hid, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hvp),
      abs_of_pos (inv_pos.mpr hwp)]
    calc
      |gauge A w - gauge A v| * (gauge A v)⁻¹ * (gauge A w)⁻¹ ≤
          (‖v - w‖ / r) * R * R := by
        exact mul_le_mul (mul_le_mul (by simpa [abs_sub_comm] using hlip v w)
          hvi (inv_nonneg.mpr hvp.le) (div_nonneg (norm_nonneg _) hr.le))
          hwi (inv_nonneg.mpr hwp.le)
            (mul_nonneg (div_nonneg (norm_nonneg _) hr.le) hR.le)
      _ = R ^ 2 * (‖v - w‖ / r) := by ring
  have hsplit : (gauge A v)⁻¹ • v - (gauge A w)⁻¹ • w =
      (gauge A v)⁻¹ • (v - w) + ((gauge A v)⁻¹ - (gauge A w)⁻¹) • w := by module
  rw [dist_eq_norm, hsplit]
  calc
    ‖(gauge A v)⁻¹ • (v - w) + ((gauge A v)⁻¹ - (gauge A w)⁻¹) • w‖ ≤
        ‖(gauge A v)⁻¹ • (v - w)‖ + ‖((gauge A v)⁻¹ - (gauge A w)⁻¹) • w‖ := norm_add_le _ _
    _ = (gauge A v)⁻¹ * ‖v - w‖ + |(gauge A v)⁻¹ - (gauge A w)⁻¹| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hvp), hw, mul_one]
    _ ≤ R * ‖v - w‖ + R ^ 2 * (‖v - w‖ / r) :=
      add_le_add (mul_le_mul_of_nonneg_right hvi (norm_nonneg _)) hinvdiff
    _ = (R + R ^ 2 / r) * dist v w := by rw [dist_eq_norm]; ring

private theorem body_radial_geometry {A : Set E} (hA : Convex ℝ A) (hAc : IsClosed A)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hin : closedBall (0 : E) r ⊆ A) (hout : A ⊆ closedBall 0 R) :
    (∀ v : E, ‖v‖ / R ≤ gauge A v ∧ gauge A v ≤ ‖v‖ / r) ∧
      (∀ v w : E, |gauge A v - gauge A w| ≤ ‖v - w‖ / r) ∧
      ∃ h : sphere (0 : E) 1 ≃ₜ frontier A,
        (∀ v, (h v : E) = (gauge A (v : E))⁻¹ • (v : E)) ∧
        ∀ v w, dist (h v : E) (h w : E) ≤ (R + R ^ 2 / r) * dist (v : E) (w : E) := by
  have h0 : A ∈ 𝓝 (0 : E) := mem_of_superset (closedBall_mem_nhds _ hr) hin
  have hAb := NormedSpace.isVonNBounded_of_isBounded ℝ (isBounded_closedBall.subset hout)
  let e := gaugeRescaleHomeomorph (closedBall (0 : E) 1) A
    (convex_closedBall _ _) (closedBall_mem_nhds _ zero_lt_one)
    (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall) hA h0 hAb
  have him : e '' closedBall (0 : E) 1 = A := by
    simpa only [isClosed_closedBall.closure_eq, hAc.closure_eq] using
      image_gaugeRescaleHomeomorph_closure (convex_closedBall (0 : E) 1)
        (closedBall_mem_nhds _ zero_lt_one)
        (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall) hA h0 hAb
  have hfr : e '' sphere (0 : E) 1 = frontier A := by
    rw [← frontier_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0), e.image_frontier, him]
  let h : sphere (0 : E) 1 ≃ₜ frontier A :=
    (e.image (sphere (0 : E) 1)).trans (Homeomorph.setCongr hfr)
  have hformula : ∀ v, (h v : E) = (gauge A (v : E))⁻¹ • (v : E) := by
    intro v
    have hv : ‖(v : E)‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using v.property
    change gaugeRescale (closedBall (0 : E) 1) A v = _
    simp [gaugeRescale, gauge_closedBall, hv]
  obtain ⟨hb, hlip⟩ := gauge_bounds hA hr hR hin hout
  refine ⟨hb, hlip, h, hformula, ?_⟩
  intro v w
  rw [hformula, hformula]
  exact radial_distance_bound hA hr hR hin hout
    (by simpa [mem_sphere, dist_eq_norm] using v.property)
    (by simpa [mem_sphere, dist_eq_norm] using w.property)

private def sectionChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E →L[ℝ] ℝ) (a : E) (ha : u a = 1) :
    u.ker ≃ₜ {x : E | u x = 1} where
  toFun v := ⟨a + (v : E), by simp [ha, v.property]⟩
  invFun x := ⟨(x : E) - a, by
    change u ((x : E) - a) = 0
    rw [map_sub, ha]
    exact sub_eq_zero.mpr x.property⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp
  continuous_toFun := (continuous_const.add continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

/-- The original positive unit is retained, as is every relative interior center. -/
private theorem section_radial_geometry [FiniteDimensional ℝ E]
    (C : ProperCone ℝ E) (u : E →L[ℝ] ℝ)
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (a : {x : E | u x = 1})
    (ha : a ∈ interior {x : {y : E | u y = 1} | (x : E) ∈ C}) :
    let A : Set u.ker := {v | (a : E) + (v : E) ∈ C}
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      closedBall (0 : u.ker) r ⊆ A ∧ A ⊆ closedBall 0 R ∧
      (∀ v : u.ker, ‖v‖ / R ≤ gauge A v ∧ gauge A v ≤ ‖v‖ / r) ∧
      (∀ v w : u.ker, |gauge A v - gauge A w| ≤ ‖v - w‖ / r) ∧
      ∃ h : sphere (0 : u.ker) 1 ≃ₜ
          frontier {x : {y : E | u y = 1} | (x : E) ∈ C},
        (∀ v, ((h v : {y : E | u y = 1}) : E) =
          (a : E) + ((gauge A (v : u.ker))⁻¹ • ((v : u.ker) : E))) ∧
        ∀ v w, dist ((h v : {y : E | u y = 1}) : E)
            ((h w : {y : E | u y = 1}) : E) ≤
          (R + R ^ 2 / r) * dist (v : u.ker) (w : u.ker) := by
  dsimp only
  let A : Set u.ker := {v | (a : E) + (v : E) ∈ C}
  let K : Set {y : E | u y = 1} := {x | (x : E) ∈ C}
  let e := sectionChart u a a.property
  have hpre : e ⁻¹' K = A := rfl
  have h0 : (0 : u.ker) ∈ interior A := by
    rw [← hpre, ← e.preimage_interior]
    simpa [e, sectionChart, K] using ha
  have hAc : IsClosed A := C.isClosed.preimage
    (continuous_const.add continuous_subtype_val)
  have hAv : Convex ℝ A :=
    (C.convex.translate_preimage_right (a : E)).linear_preimage u.ker.subtype
  have hKc : IsCompact K := by
    have he := (isClosed_eq u.continuous
      (continuous_const : Continuous (fun _ : E => (1 : ℝ)))).isClosedEmbedding_subtypeVal
    have hh := he.isCompact_preimage
      (D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.base_compact C.isClosed hu)
    convert hh using 1
    ext x
    simp only [K, mem_setOf_eq, mem_preimage,
      D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.base, x.property, and_true]
  have hAcpt : IsCompact A := hpre ▸ e.isClosedEmbedding.isCompact_preimage hKc
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  let r := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hin : closedBall (0 : u.ker) r ⊆ A :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hεA
  obtain ⟨R, hrR, hout⟩ := hAcpt.isBounded.subset_closedBall_lt r 0
  obtain ⟨hb, hlip, h, hformula, hdist⟩ :=
    body_radial_geometry hAv hAc hr (hr.trans hrR) hin hout
  have him : e '' A = K := by rw [← hpre]; exact image_preimage_eq K e.surjective
  have hfr : e '' frontier A = frontier K := by rw [e.image_frontier, him]
  let H := h.trans ((e.image (frontier A)).trans (Homeomorph.setCongr hfr))
  have hH : ∀ v, ((H v : {y : E | u y = 1}) : E) =
      (a : E) + (gauge A (v : u.ker))⁻¹ • ((v : u.ker) : E) := by
    intro v
    change (a : E) + ((h v : u.ker) : E) = _
    rw [hformula]
    rfl
  refine ⟨r, R, hr, hrR, hin, hout, hb, hlip, H, hH, ?_⟩
  intro v w
  rw [hH, hH, dist_add_left]
  exact hdist v w

end D5.S3.Geometry.AlgebraicBoundary.ConeRadialGeometry
