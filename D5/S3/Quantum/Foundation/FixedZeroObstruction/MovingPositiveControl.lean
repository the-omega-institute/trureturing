/- GID: D5/S3/Quantum/Foundation/FixedZeroObstruction/MovingPositiveControl
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FixedZeroObstruction/MovingPositiveControl
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Uniform original-unit control of moving positive annihilators. -/

import D5.S3.Quantum.Foundation.FixedZeroObstruction
import D5.S3.Quantum.Foundation.SingleLabelNormalBody

/-! Positive functionals are defined on the entire original cone, without an upper unit bound. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.FixedZeroObstruction

open Set Filter Topology TopologicalSpace
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ContinuousFrameSum ExclusionIncidence SingleLabelNormalBody

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- All original cone-positive linear functionals exactly zero at the given label. -/
def positiveZeros (t : pure C u) : Set (V →ₗ[ℝ] ℝ) :=
  {b | (∀ x ∈ C, 0 ≤ b x) ∧ b t = 0}

/-- Maximum of a linear functional on the entire original normalized base. -/
def baseMaximum (b : V →ₗ[ℝ] ℝ) : ℝ := sSup (b '' base C u)

/-- One-sided distance of the entire moving exclusion to the fixed original source ball. -/
def exclusionDeviation (p t : pure C u) : ℝ :=
  sSup ((fun x => Metric.infDist x (exclusion C u p)) '' exclusion C u t)

/-- The original-unit truncation uses the same global base maximum. -/
def unitTruncation (b : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] ℝ :=
  (max 1 (baseMaximum (C := C) (u := u) b))⁻¹ • b

private theorem dual_norm_control
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ A : ℝ, 0 < A ∧ ∀ b : V →ₗ[ℝ] ℝ,
      ‖b.toContinuousLinearMap‖ ≤ A * stateNorm hc hs b := by
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  let R : (V →L[ℝ] ℝ) →ₗ[ℝ] C(base C u, ℝ) :=
    { toFun := fun b => stateReadout b.toLinearMap
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  have hi : Function.Injective R := by
    intro b d h
    apply ContinuousLinearMap.coe_injective
    exact LinearMap.ext_on (pure_span (base_compact hc hs) hs hg)
      (fun x hx => ContinuousMap.congr_fun h ⟨x, pure_mem ⟨x, hx⟩⟩)
  obtain ⟨A, hA, hb⟩ := R.exists_antilipschitzWith hi
  refine ⟨A, by exact_mod_cast hA, fun b => ?_⟩
  exact ZeroHomClass.bound_of_antilipschitz R hb b.toContinuousLinearMap

private theorem positive_state_norm
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (p : pure C u) (b : V →ₗ[ℝ] ℝ) (hb : ∀ x ∈ C, 0 ≤ b x) :
    stateNorm hc hs b = baseMaximum (C := C) (u := u) b := by
  letI : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  have hK := base_compact hc hs
  have hne : (base C u).Nonempty := ⟨p, pure_mem p⟩
  obtain ⟨x, hx, hm⟩ := hK.exists_sSup_image_eq hne b.continuous_of_finiteDimensional.continuousOn
  have hnon : 0 ≤ baseMaximum (C := C) (u := u) b := by
    change 0 ≤ sSup (b '' base C u)
    rw [hm]
    exact hb x hx.1
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ hnon).mpr
    intro z
    change ‖b z‖ ≤ baseMaximum (C := C) (u := u) b
    rw [Real.norm_eq_abs, abs_of_nonneg (hb z z.property.1)]
    exact le_csSup (hK.bddAbove_image b.continuous_of_finiteDimensional.continuousOn)
      (mem_image_of_mem b z.property)
  · have hh := (stateReadout (C := C) (u := u) b).norm_coe_le_norm ⟨x, hx⟩
    change ‖b x‖ ≤ stateNorm hc hs b at hh
    simpa only [baseMaximum, hm, Real.norm_eq_abs, abs_of_nonneg (hb x hx.1)] using hh

private theorem deviation_nonneg
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p t : pure C u) : 0 ≤ exclusionDeviation p t := by
  have ht := (exclusion_ball_faces hc hs hg hB).1 t
  obtain ⟨x, hx⟩ := ht.1.nonempty
  exact (Metric.infDist_nonneg : 0 ≤ Metric.infDist x (exclusion C u p)).trans
    (le_csSup (ht.2.1.bddAbove_image (Metric.continuous_infDist_pt _).continuousOn)
      (mem_image_of_mem _ hx))

private theorem deviation_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (tn : ℕ → pure C u) (ht : Tendsto tn atTop (𝓝 p)) :
    Tendsto (fun n => exclusionDeviation p (tn n)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (deviation_nonneg hc hs hg hB p (tn n))
  · intro a ha
    filter_upwards [exclusion_upper_eventually hc hs hg ht (half_pos ha)] with n hn
    have hD := (exclusion_ball_faces hc hs hg hB).1 (tn n)
    apply lt_of_le_of_lt (csSup_le (hD.1.nonempty.image _) ?_) (half_lt_self ha)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hdist⟩ := hn x hx
    exact (Metric.infDist_le_dist_of_mem hz).trans hdist.le

/-- One constant works for every pure source, moving label and whole-cone positive
annihilator. The deviation converges at every pure limiting label, without Inj. -/
theorem moving_positive_control
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    ∃ A : ℝ, 0 < A ∧
      (∀ b : V →ₗ[ℝ] ℝ, ‖b.toContinuousLinearMap‖ ≤ A * stateNorm hc hs b) ∧
      (∀ (p : pure C u) (tn : ℕ → pure C u), Tendsto tn atTop (𝓝 p) →
        Tendsto (fun n => exclusionDeviation p (tn n)) atTop (𝓝 0)) ∧
      ∀ (p t : pure C u) (b : V →ₗ[ℝ] ℝ), b ∈ positiveZeros t →
        A * exclusionDeviation p t < 1 →
        baseMaximum (C := C) (u := u) b ≤ faceMaximum p b / (1 - A * exclusionDeviation p t) := by
  obtain ⟨A, hA, hbound⟩ := dual_norm_control hc hs hg
  refine ⟨A, hA, hbound, deviation_tendsto hc hs hg hB, ?_⟩
  intro p t b hb hsmall
  have all := (exclusion_ball_faces hc hs hg hB).1
  have hF := all p
  have hD := all t
  have hden : 0 < 1 - A * exclusionDeviation p t := sub_pos.mpr hsmall
  apply (le_div_iff₀ hden).mpr
  by_cases hb0 : b = 0
  · have hzero (S : Set V) (hS : S.Nonempty) : (0 : V →ₗ[ℝ] ℝ) '' S = {0} :=
      (Set.image_const hS 0)
    simp only [hb0, baseMaximum, faceMaximum, hzero _ ⟨p, pure_mem p⟩,
      hzero _ hF.1.nonempty, csSup_singleton, zero_mul, le_refl]
  obtain ⟨x, hxD, _, hxmax⟩ := positive_annihilator_maximum hc hs hg t b hb0 hb.1 hb.2
  have hBmax : baseMaximum (C := C) (u := u) b = b x :=
    le_antisymm (csSup_le ⟨b x, mem_image_of_mem b (pure_mem x)⟩
      (by rintro _ ⟨z, hz, rfl⟩; exact hxmax z hz))
      (le_csSup ((base_compact hc hs).bddAbove_image b.continuous_of_finiteDimensional.continuousOn)
        (mem_image_of_mem b (pure_mem x)))
  obtain ⟨z, hz, hdist⟩ := hF.2.1.exists_infDist_eq_dist hF.1.nonempty (x : V)
  have hdev : dist (x : V) z ≤ exclusionDeviation p t := by
    rw [← hdist]
    exact le_csSup (hD.2.1.bddAbove_image (Metric.continuous_infDist_pt _).continuousOn)
      (mem_image_of_mem _ hxD)
  have hsource : b z ≤ faceMaximum p b :=
    le_csSup (hF.2.1.bddAbove_image b.continuous_of_finiteDimensional.continuousOn)
      (mem_image_of_mem b hz)
  have hnorm := hbound b
  rw [positive_state_norm hc hs p b hb.1, hBmax] at hnorm
  have hd : b x - b z ≤ A * b x * exclusionDeviation p t := calc
    b x - b z ≤ ‖b.toContinuousLinearMap ((x : V) - z)‖ := by
      rw [map_sub, Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ ‖b.toContinuousLinearMap‖ * ‖(x : V) - z‖ := b.toContinuousLinearMap.le_opNorm _
    _ ≤ (A * b x) * exclusionDeviation p t :=
      mul_le_mul hnorm (by simpa only [dist_eq_norm] using hdev)
        (norm_nonneg _) (mul_nonneg hA.le (hb.1 x (pure_mem x).1))
  rw [hBmax]
  nlinarith

end D5.S3.Quantum.Foundation.FixedZeroObstruction
