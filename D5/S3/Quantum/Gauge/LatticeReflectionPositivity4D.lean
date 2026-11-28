/- GID: D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/LatticeReflectionPositivity4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wilson gauge invariance, reflection positivity, positive transfer, and the strong-coupling rectangular area law. -/

import D5.S3.LatticeGauge.TransferOperator
import D5.S3.LatticeGauge.StrongCouplingAreaLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Matrix Filter

namespace D5.S3.Quantum.Gauge.LatticeReflectionPositivity4D

open Omega.LatticeGauge

variable {n : Fin 4 → ℕ} {G : Type*} [Group G] {d : ℕ}
variable [MeasurableSpace G]

/-- Each square in a half has a gauge invariant Wilson weight. -/
theorem wilson_plaquette_gauge_invariant (D : GaugeData G d) (g : Vertex n → G)
    (u : Link n → G) (p : Plaquette n) :
    (D.rep (squareHolonomy (gauge g u) p)).trace.re = (D.rep (squareHolonomy u p)).trace.re := by
  rw [gauge_square, trace_conjugate]

/-- The Wilson weight of each plaquette crossing the reflection plane is gauge invariant. -/
theorem wilson_seam_plaquette_gauge_invariant (D : GaugeData G d)
    (g k : Vertex n → G) (u : Box n G) (e : BoundaryLink n) :
    (D.rep (seamHolonomy (boundary (siteGauge g k u).1.1)
      (boundary (siteGauge g k u).1.2) (siteGauge g k u).2 e)).trace.re =
    (D.rep (seamHolonomy (boundary u.1.1) (boundary u.1.2) u.2 e)).trace.re := by
  rw [gauge_seam, trace_conjugate]

theorem wilson_action_gauge_invariant (D : GaugeData G d) (g k : Vertex n → G) (u : Box n G) :
    wilsonAction D (siteGauge g k u) = wilsonAction D u := by
  simp only [wilsonAction, halfAction, wilson_seam_plaquette_gauge_invariant]
  change (∑ p, (D.rep (squareHolonomy (gauge g u.1.1) p)).trace.re) +
    (∑ p, (D.rep (squareHolonomy (gauge k u.1.2) p)).trace.re) + _ = _
  simp_rw [wilson_plaquette_gauge_invariant]

theorem wilson_action_reflection_invariant (D : GaugeData G d) (u : Box n G) :
    wilsonAction D (reflect u) = wilsonAction D u := by
  unfold wilsonAction reflect
  rw [add_comm (halfAction D u.1.2)]
  congr 1
  exact Finset.sum_congr rfl fun e _ =>
    seamWeight_reflect D (boundary u.1.1) (boundary u.1.2) u.2 e

section Haar

variable [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]

/-- The Wilson reflected expectation belongs to the nonnegative real axis for every
integrable half-space observable, with all seam links integrated against Haar. -/
theorem wilson_reflection_positivity (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (F : (Link n → G) → ℂ) (hF : Integrable F (configMeasure μ (Link n))) :
    ∃ r : ℝ, 0 ≤ r ∧ wilsonOS μ D β F = (r : ℂ) := by
  obtain ⟨r, hr, heq⟩ := wilson_reflected_integral_nonneg μ D β hβ F hF
  refine ⟨r / partition (n := n) μ D β, div_nonneg hr (partition_pos μ D β).le, ?_⟩
  rw [wilsonOS, heq, Complex.ofReal_div]

/-- The Wilson transfer operator has a nonnegative quadratic form on the OS quotient. -/
theorem wilson_physical_transfer_nonneg (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (ψ : wilsonPhysicalSpace (n := n) μ D β hβ) :
    0 ≤ (inner ℂ ψ (wilsonPhysicalTransfer μ D β hβ ψ)).re := by
  obtain ⟨f, rfl⟩ := physicalClass_surjective _ _ ψ
  unfold wilsonPhysicalTransfer
  rw [physical_transfer_square]
  exact integral_nonneg fun x => sq_nonneg _

theorem wilson_os_norm (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (F : integrableObservables (configMeasure μ (Link n))) :
    ‖wilsonHalfClass μ D β hβ F‖ =
      Real.sqrt ((wilsonOS μ D β F.1 * (partition (n := n) μ D β : ℂ)).re) := by
  change ‖physicalClass (wilsonBoundaryKernel μ D β) (wilsonBoundaryKernel_pos μ D β hβ)
    (boundaryReduction μ D β (pullbackHalf μ F))‖ = _
  rw [norm_physicalClass, ← wilsonOS_boundary]
  congr 4
  exact funext fun x => by simp [pullbackHalf, Function.comp_apply]

theorem wilson_os_seminorm (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (F : integrableObservables (configMeasure μ (Link n))) :
    wilsonOSSeminorm μ D β hβ F = Real.sqrt (wilsonOS μ D β F.1).re := by
  have hZ := partition_pos (n := n) μ D β
  have h : 0 ≤ (wilsonOS μ D β F.1).re := by
    obtain ⟨r, hr, hr'⟩ := wilson_reflection_positivity μ D β hβ F.1 (observable_integrable F)
    simpa [hr'] using hr
  rw [wilsonOSSeminorm, _root_.smul_apply, Seminorm.comp_apply, coe_normSeminorm, wilson_os_norm]
  rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Real.sqrt_mul h]
  rw [smul_eq_mul, mul_left_comm, inv_mul_cancel₀ (Real.sqrt_pos.2 hZ).ne', mul_one]

/-- The unnormalized physical inner product descends from the mixed Gibbs pairing. -/
theorem wilson_os_pairing (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (F H : integrableObservables (configMeasure μ (Link n))) :
    inner ℂ (wilsonHalfClass μ D β hβ F) (wilsonHalfClass μ D β hβ H) =
      wilsonOSPair μ D β F.1 H.1 * (partition (n := n) μ D β : ℂ) := by
  change osPair (wilsonBoundaryKernel μ D β) (boundaryReduction μ D β (pullbackHalf μ F))
    (boundaryReduction μ D β (pullbackHalf μ H)) = _
  rw [← wilsonOS_boundary_pair]
  have hF : ((pullbackHalf μ F).1 ∘ halfSplit) = F.1 :=
    funext fun x => by simp [pullbackHalf, Function.comp_apply]
  have hH : ((pullbackHalf μ H).1 ∘ halfSplit) = H.1 :=
    funext fun x => by simp [pullbackHalf, Function.comp_apply]
  rw [hF, hH]

/-- Cauchy–Schwarz for integrable positive-half observables under the Wilson probability. -/
theorem wilson_os_cauchy_schwarz (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (F H : integrableObservables (configMeasure μ (Link n))) :
    ‖wilsonOSPair μ D β F.1 H.1‖ ≤ wilsonOSSeminorm μ D β hβ F * wilsonOSSeminorm μ D β hβ H := by
  let Z := partition (n := n) μ D β
  have hZ : 0 < Z := partition_pos μ D β
  have heq := wilson_os_pairing μ D β hβ F H
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [(eq_div_iff hz).mpr heq.symm]
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  calc
    _ ≤ (‖wilsonHalfClass μ D β hβ F‖ * ‖wilsonHalfClass μ D β hβ H‖) / Z :=
      div_le_div_of_nonneg_right (norm_inner_le_norm _ _) hZ.le
    _ = _ := by
      rw [wilsonOSSeminorm, _root_.smul_apply, _root_.smul_apply, Seminorm.comp_apply, Seminorm.comp_apply,
        coe_normSeminorm]
      have h : 0 ≤ (Real.sqrt Z)⁻¹ := by positivity
      change _ = (Real.toNNReal ((Real.sqrt Z)⁻¹) • ‖wilsonHalfClass μ D β hβ F‖) *
        (Real.toNNReal ((Real.sqrt Z)⁻¹) • ‖wilsonHalfClass μ D β hβ H‖)
      simp only [NNReal.smul_def, Real.coe_toNNReal _ h, smul_eq_mul]
      have hsq : (Real.sqrt Z) ^ 2 = Z := Real.sq_sqrt hZ.le
      field_simp [hZ.ne', (Real.sqrt_pos.2 hZ).ne']
      linear_combination (‖wilsonHalfClass μ D β hβ F‖ * ‖wilsonHalfClass μ D β hβ H‖) * hsq


/-- The finite-volume bound retains the actual rooted components that cover the rectangle. -/
theorem wilson_strong_coupling_finite_bound (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < d) (z : Subgroup.center G) (ζ : ℂ) (hz : D.rep z = ζ • 1) (hζ : ζ ≠ 1)
    (r : Rectangle n) (hw : 0 < r.width) (hh : 0 < r.height) :
    ‖wilsonLoop μ D β r‖ ≤ min 1
      (∑ S ∈ rectangleComponents r hw, (Real.exp (β * d) - 1) ^ S.card) := by
  classical
  have hL : 0 < r.perimeter := by unfold Rectangle.perimeter; omega
  let k : Fin r.perimeter := ⟨0, hL⟩
  have hm : (r.cycleEdge k).1 = r.horizontal 0 (Nat.zero_le _) ⟨0, hw⟩ := by
    have hk : k.val < r.width := hw
    simp [Rectangle.cycleEdge, hk, k]
  apply le_min (wilsonLoop_norm_le_one μ D β hβ hd r)
  let : IsProbabilityMeasure (configMeasure μ (Link n)) := by unfold configMeasure; infer_instance
  exact strong_coupling_finite_component_bound _ (plaquetteCharacter D) β
    (incidentSquares (r.horizontal 0 (Nat.zero_le _) ⟨0, hw⟩)) squareAdj
    (rectangleCharacter D r) (Nat.cast_nonneg d) hβ
    (fun p => (measurable_character D).comp (measurable_square p)) (fun p u => norm_trace_le D _)
    (rectangleCharacter_measurable D r) (rectangleCharacter_norm_le D hd r) (coversRectangle r)
    (local_central_change μ D z hz hζ _) (fun S _ hS => by
      rw [← hm]
      exact rectangle_central_change μ D z hz hζ r r.cycleVertex r.cycleEdge
        (r.cycleVertex_injective hw hh) r.cycleEdge_start (r.cycleEdge_end hw hh) r.cycleEdge_eq k S hS)

/-- The explicit finite geometric estimate, with the number of available plaquettes as cutoff. -/
theorem wilson_strong_coupling_geometric_finite_bound (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < d) (z : Subgroup.center G) (ζ : ℂ) (hz : D.rep z = ζ • 1) (hζ : ζ ≠ 1)
    (r : Rectangle n) (hw : 0 < r.width) (hh : 0 < r.height)
    (hq : 80 * (Real.exp (β * d) - 1) < 1) :
    let q := 80 * (Real.exp (β * d) - 1)
    ‖wilsonLoop μ D β r‖ ≤ min 1
      ((6 / 80) * q ^ (r.width * r.height) *
        ((1 - q ^ (Fintype.card (Plaquette n) - r.width * r.height + 1)) / (1 - q))) := by
  classical
  let e := r.horizontal 0 (Nat.zero_le _) ⟨0, hw⟩
  let δ := Real.exp (β * d) - 1
  have hδ : 0 ≤ δ := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hβ (Nat.cast_nonneg d)))
  have h := wilson_strong_coupling_finite_bound μ D β hβ hd z ζ hz hζ r hw hh
  apply le_min (h.trans (min_le_left _ _))
  refine (h.trans (min_le_right _ _)).trans ?_
  have hsub : rectangleComponents r hw ⊆ componentFamily (incidentSquares e) squareAdj (r.width * r.height) := by
    intro S hS
    simp only [rectangleComponents, componentFamily, componentFamilyWhere, Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, hS.2.1, coversRectangle_area r S hS.2.2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun S _ _ => pow_nonneg hδ S.card)).trans ?_
  exact componentFamily_finite_geometric_le squareAdj (incidentSquares e)
    (incidentSquares_card_le e) adjacentSquares_card_le
    (fun p hp q hq => incidentSquares_clique e p q hp hq)
    (Nat.mul_pos hw hh) hδ (by norm_num) hq

/-- The volume-uniform strong-coupling rectangular area law in an open 4D box.
The representation must have a nontrivial scalar central character. -/
theorem wilson_strong_coupling_area_bound (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < d) (z : Subgroup.center G) (ζ : ℂ) (hz : D.rep z = ζ • 1) (hζ : ζ ≠ 1)
    (r : Rectangle n) (hw : 0 < r.width) (hh : 0 < r.height)
    (hq : 80 * (Real.exp (β * d) - 1) < 1) :
    let q := 80 * (Real.exp (β * d) - 1)
    ‖wilsonLoop μ D β r‖ ≤ 6 * q ^ (r.width * r.height) / (80 * (1 - q)) := by
  let q := 80 * (Real.exp (β * d) - 1)
  have hq₀ : 0 ≤ q := mul_nonneg (by norm_num)
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hβ (Nat.cast_nonneg d))))
  have h := wilson_strong_coupling_geometric_finite_bound μ D β hβ hd z ζ hz hζ r hw hh hq
  dsimp only at h
  refine (h.trans (min_le_right _ _)).trans ?_
  change (6 / 80) * q ^ (r.width * r.height) *
      ((1 - q ^ (Fintype.card (Plaquette n) - r.width * r.height + 1)) / (1 - q)) ≤
    6 * q ^ (r.width * r.height) / (80 * (1 - q))
  calc
    _ ≤ (6 / 80) * q ^ (r.width * r.height) * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg hq₀ _)) (by linarith))
        (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

end Haar

end D5.S3.Quantum.Gauge.LatticeReflectionPositivity4D
