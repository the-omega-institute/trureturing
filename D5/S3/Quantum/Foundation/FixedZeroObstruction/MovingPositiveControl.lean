/- GID: D5/S3/Quantum/Foundation/FixedZeroObstruction/MovingPositiveControl
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FixedZeroObstruction/MovingPositiveControl
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Finite common source tests obstruct low-dimensional positive zero lifts. -/

import D5.S3.Quantum.Foundation.FixedZeroObstruction
import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.FixedZeroObstruction.LocalPureLimit
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Order.Filter.Finite

/-! Positive functionals are defined on the entire original cone, without an upper unit bound. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.FixedZeroObstruction

open Set Filter Topology TopologicalSpace
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ContinuousFrameSum ExclusionIncidence SingleLabelNormalBody OriginalFacePolarity

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
  let : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  let R : (V →L[ℝ] ℝ) →ₗ[ℝ] C(base C u, ℝ) :=
    { toFun := fun b => stateReadout b.toLinearMap
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  have hi : Function.Injective R := by
    intro b d h
    apply ContinuousLinearMap.coe_injective
    exact LinearMap.ext_on (pure_span (base_compact hc hs) hs hg)
      (fun x hx => ContinuousMap.congr_fun h ⟨x, pure_mem ⟨x, hx⟩⟩)
  obtain ⟨A, hA, hb⟩ := R.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨A, by exact_mod_cast hA, fun b => ?_⟩
  exact ZeroHomClass.bound_of_antilipschitz R hb b.toContinuousLinearMap

private theorem positive_state_norm
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (p : pure C u) (b : V →ₗ[ℝ] ℝ) (hb : ∀ x ∈ C, 0 ≤ b x) :
    stateNorm hc hs b = baseMaximum (C := C) (u := u) b := by
  let : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
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
  · have hzero (S : Set V) (hS : S.Nonempty) : (0 : V →ₗ[ℝ] ℝ) '' S = {0} := by
      simpa using hS.image_const (0 : ℝ)
    change baseMaximum (C := C) (u := u) b * _ ≤ faceMaximum p b
    rw [hb0, baseMaximum, faceMaximum, hzero (base C u) ⟨p, pure_mem p⟩,
      hzero _ hF.1.nonempty]
    simp
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

private theorem unit_truncation_proper
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (t : pure C u) (b : V →ₗ[ℝ] ℝ) (hb : b ∈ positiveZeros t) :
    proper C u (unitTruncation (C := C) (u := u) b) ∧
      unitTruncation (C := C) (u := u) b t = 0 := by
  have hcap : 0 < max 1 (baseMaximum (C := C) (u := u) b) :=
    zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨cone_bound (base_compact hc hs) hs (fun r => ?_), ?_⟩
  · change 0 ≤ (max 1 (baseMaximum (C := C) (u := u) b))⁻¹ * b r ∧
      (max 1 (baseMaximum (C := C) (u := u) b))⁻¹ * b r ≤ 1
    refine ⟨mul_nonneg (inv_nonneg.mpr hcap.le) (hb.1 r (pure_mem r).1), ?_⟩
    rw [← div_eq_inv_mul, div_le_one hcap]
    exact (le_csSup ((base_compact hc hs).bddAbove_image
      b.continuous_of_finiteDimensional.continuousOn)
      (mem_image_of_mem b (pure_mem r))).trans (le_max_right _ _)
  · simp [unitTruncation, hb.2]

/-- Arbitrary uniformly limiting source functions in [0,1] admit the prescribed
normalization; the source function need not be specified by a linear extension. -/
theorem moving_positive_normalization
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (tn : ℕ → pure C u) (ht : Tendsto tn atTop (𝓝 p))
    (bn : ℕ → (V →ₗ[ℝ] ℝ)) (hb : ∀ n, bn n ∈ positiveZeros (tn n))
    (ell : exclusion C u p → ℝ) (hell : ∀ x, 0 ≤ ell x ∧ ell x ≤ 1)
    (hconv : TendstoUniformly (fun n (x : exclusion C u p) => bn n x) ell atTop) :
    (∀ n, proper C u (unitTruncation (C := C) (u := u) (bn n)) ∧
      unitTruncation (C := C) (u := u) (bn n) (tn n) = 0) ∧
    TendstoUniformly (fun n (x : exclusion C u p) =>
      unitTruncation (C := C) (u := u) (bn n) x) ell atTop ∧
    Tendsto (fun n => stateNorm hc hs (unitTruncation (C := C) (u := u) (bn n) - bn n))
      atTop (𝓝 0) ∧
    (sSup (Set.range ell) = 1 →
      Tendsto (fun n => baseMaximum (C := C) (u := u) (bn n)) atTop (𝓝 1)) := by
  let : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  have hF := (exclusion_ball_faces hc hs hg hB).1 p
  let B (n : ℕ) := baseMaximum (C := C) (u := u) (bn n)
  let cap (n : ℕ) := max 1 (B n)
  let f (n : ℕ) := unitTruncation (C := C) (u := u) (bn n)
  have hf := fun n => unit_truncation_proper hc hs (tn n) (bn n) (hb n)
  obtain ⟨A, hA, _, hdev, hbound⟩ := moving_positive_control hc hs hg hB
  have halpha : Tendsto (fun n => A * exclusionDeviation p (tn n)) atTop (𝓝 0) := by
    simpa using (hdev p tn ht).const_mul A
  have hsmall : ∀ᶠ n in atTop, A * exclusionDeviation p (tn n) < 1 :=
    halpha.eventually (gt_mem_nhds zero_lt_one)
  have hu (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop, B n < 1 + ε := by
    have hratio : Tendsto (fun n => (1 + ε / 2) / (1 - A * exclusionDeviation p (tn n)))
        atTop (𝓝 (1 + ε / 2)) := by
      convert tendsto_const_nhds.div (tendsto_const_nhds.sub halpha) (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1 <;> simp
    filter_upwards [hsmall, (Metric.tendstoUniformly_iff.mp hconv) (ε / 2) (half_pos hε),
      hratio.eventually (gt_mem_nhds (by linarith : 1 + ε / 2 < 1 + ε))] with n hn hnear hratio'
    have hm : faceMaximum p (bn n) ≤ 1 + ε / 2 := by
      apply csSup_le (hF.1.nonempty.image _)
      rintro _ ⟨x, hx, rfl⟩
      have hd := hnear ⟨x, hx⟩
      rw [Real.dist_eq] at hd
      have hh := (abs_lt.mp hd).1
      linarith [(hell ⟨x, hx⟩).2]
    exact ((hbound p (tn n) (bn n) (hb n) hn).trans
      (div_le_div_of_nonneg_right hm (sub_pos.mpr hn).le)).trans_lt hratio'
  have hcap : Tendsto cap atTop (𝓝 1) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => ha.trans_le (le_max_left _ _)
    · intro a ha
      filter_upwards [hu (a - 1) (sub_pos.mpr ha)] with n hn
      exact max_lt ha (by dsimp [B] at hn ⊢; linarith)
  have herror (n : ℕ) : stateNorm hc hs (f n - bn n) ≤ cap n - 1 := by
    apply (ContinuousMap.norm_le _ (sub_nonneg.mpr (le_max_left _ _))).mpr
    intro x
    change ‖f n x - bn n x‖ ≤ cap n - 1
    have hproper : 0 ≤ f n x ∧ f n x ≤ 1 := by
      simpa [x.property.2] using (hf n).1 x x.property.1
    have hpos : 0 < cap n := zero_lt_one.trans_le (le_max_left _ _)
    have heq : f n x - bn n x = (1 - cap n) * f n x := by
      change (cap n)⁻¹ * bn n x - bn n x = (1 - cap n) * ((cap n)⁻¹ * bn n x)
      field_simp
      <;> ring
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith [le_max_left (1 : ℝ) (B n)]),
      abs_of_nonneg hproper.1]
    nlinarith [le_max_left (1 : ℝ) (B n)]
  have herr : Tendsto (fun n => stateNorm hc hs (f n - bn n)) atTop (𝓝 0) := by
    have hc0 : Tendsto (fun n => cap n - 1) atTop (𝓝 0) := by simpa using hcap.sub_const 1
    exact squeeze_zero (fun n => norm_nonneg (stateReadout (C := C) (u := u) (f n - bn n))) herror hc0
  refine ⟨hf, Metric.tendstoUniformly_iff.mpr (fun ε hε => ?_), herr, ?_⟩
  · filter_upwards [(Metric.tendstoUniformly_iff.mp hconv) (ε / 2) (half_pos hε),
      herr.eventually (gt_mem_nhds (half_pos hε))] with n hn he x
    have hd := (stateReadout (C := C) (u := u) (f n - bn n)).norm_coe_le_norm ⟨x, x.property.1⟩
    change ‖f n x - bn n x‖ ≤ stateNorm hc hs (f n - bn n) at hd
    have hd' : dist (bn n x) (f n x) ≤ stateNorm hc hs (f n - bn n) := by
      simpa only [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hd
    exact (dist_triangle (ell x) (bn n x) (f n x)).trans_lt (by linarith [hn x])
  · intro hmax
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [(Metric.tendstoUniformly_iff.mp hconv) ((1 - a) / 2) (by linarith)] with n hn
      have hh : sSup (Set.range ell) ≤ B n + (1 - a) / 2 := by
        apply csSup_le (by obtain ⟨x, hx⟩ := hF.1.nonempty; exact ⟨ell ⟨x, hx⟩, mem_range_self _⟩)
        rintro _ ⟨x, rfl⟩
        have hbx : bn n x ≤ B n :=
          le_csSup ((base_compact hc hs).bddAbove_image (bn n).continuous_of_finiteDimensional.continuousOn)
            (mem_image_of_mem (bn n) x.property.1)
        have hd := (abs_lt.mp (show |ell x - bn n x| < (1 - a) / 2 by simpa only [Real.dist_eq] using hn x)).2
        linarith
      rw [hmax] at hh
      linarith
    · intro a ha
      filter_upwards [hu (a - 1) (by linarith)] with n hn
      linarith


/-- One finite original pure test set spans the whole source ball and retains a
relative neighborhood of the prescribed interior point. -/
private theorem finite_source_tests
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p)) :
    ∃ S : Finset V,
      (S : Set V) ⊆ exclusion C u p ∩ pure C u ∧
      affineSpan ℝ (S : Set V) = affineSpan ℝ (exclusion C u p) ∧
      y ∈ intrinsicInterior ℝ (convexHull ℝ (S : Set V)) := by
  classical
  let F : Set V := exclusion C u p
  have hHull : convexHull ℝ (F ∩ pure C u) = F := by
    obtain ⟨b⟩ := hB p
    haveI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
    change convexHull ℝ (exclusion C u p ∩ pure C u) = exclusion C u p
    rw [chart_boundary hc hs hg hB p b, ← b.param.image_convexHull,
      convexHull_sphere_eq_closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) zero_le_one,
      b.whole]
  obtain ⟨a, ha, hay⟩ := mem_intrinsicInterior.mp hy
  let A : AffineSubspace ℝ V := affineSpan ℝ F
  haveI : Nonempty A := ⟨a⟩
  let E := A.direction
  let e : E ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ a
  let f : E →ᵃ[ℝ] V := A.subtype.comp e.toAffineEquiv.toAffineMap
  have he0 : e 0 = a := by simp [e]
  have h0 : (0 : E) ∈ interior (f ⁻¹' F) := by
    have h : e 0 ∈ interior (((↑) : A → V) ⁻¹' F) := he0.symm ▸ ha
    change (0 : E) ∈ e.toHomeomorph ⁻¹' interior (((↑) : A → V) ⁻¹' F) at h
    rw [e.toHomeomorph.preimage_interior] at h
    change (0 : E) ∈ interior (f ⁻¹' F) at h
    exact h
  obtain ⟨b, hb0, hbF⟩ :=
    exists_mem_interior_convexHull_affineBasis (mem_interior_iff_mem_nhds.mp h0)
  have hfinite (i : Fin (Module.finrank ℝ E + 1)) :
      ∃ s : Finset V, (s : Set V) ⊆ F ∩ pure C u ∧
        f (b i) ∈ convexHull ℝ (s : Set V) := by
    have hmem : f (b i) ∈ convexHull ℝ (F ∩ pure C u) := by
      rw [hHull]
      exact hbF (subset_convexHull ℝ (range b) (mem_range_self i))
    rw [convexHull_eq_union_convexHull_finite_subsets] at hmem
    simpa only [mem_iUnion, exists_prop] using hmem
  choose s hsS hbs using hfinite
  let S : Finset V := Finset.univ.biUnion s
  have hsSub (i : Fin (Module.finrank ℝ E + 1)) : (s i : Set V) ⊆ (S : Set V) := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩
  have hS : (S : Set V) ⊆ F ∩ pure C u := by
    intro z hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    exact hsS i hi
  have hbS : f '' range b ⊆ convexHull ℝ (S : Set V) := by
    rintro z ⟨v, ⟨i, rfl⟩, rfl⟩
    exact convexHull_mono (hsSub i) (hbs i)
  have hpoly : f '' convexHull ℝ (range b) ⊆ convexHull ℝ (S : Set V) := by
    rw [f.image_convexHull]
    exact convexHull_min hbS (convex_convexHull ℝ _)
  have hpre : convexHull ℝ (range b) ⊆ f ⁻¹' convexHull ℝ (S : Set V) := by
    intro v hv
    exact hpoly ⟨v, hv, rfl⟩
  have h0S : (0 : E) ∈ interior (f ⁻¹' convexHull ℝ (S : Set V)) :=
    interior_mono hpre hb0
  have haS : a ∈ interior (((↑) : A → V) ⁻¹' convexHull ℝ (S : Set V)) := by
    have h : (0 : E) ∈ e.toHomeomorph ⁻¹'
        interior (((↑) : A → V) ⁻¹' convexHull ℝ (S : Set V)) := by
      rw [e.toHomeomorph.preimage_interior]
      change (0 : E) ∈ interior (f ⁻¹' convexHull ℝ (S : Set V))
      exact h0S
    change e 0 ∈ interior (((↑) : A → V) ⁻¹' convexHull ℝ (S : Set V)) at h
    exact he0 ▸ h
  have hfSpan : affineSpan ℝ (f '' range b) = A := by
    rw [← AffineSubspace.map_span, b.tot]
    apply SetLike.coe_injective
    change f '' (univ : Set E) = (A : Set V)
    apply Subset.antisymm
    · rintro z ⟨v, _, rfl⟩
      exact (e v).property
    · intro z hz
      refine ⟨e.symm ⟨z, hz⟩, mem_univ _, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)
  have hSpan : affineSpan ℝ (S : Set V) = A := by
    apply le_antisymm
    · exact affineSpan_mono ℝ (fun z hz => (hS hz).1)
    · rw [← hfSpan]
      calc
        affineSpan ℝ (f '' range b) ≤ affineSpan ℝ (convexHull ℝ (S : Set V)) :=
          affineSpan_mono ℝ hbS
        _ = affineSpan ℝ (S : Set V) := affineSpan_convexHull _
  have hAHull : affineSpan ℝ (convexHull ℝ (S : Set V)) = A := by
    rw [affineSpan_convexHull, hSpan]
  refine ⟨S, hS, hSpan, ?_⟩
  unfold intrinsicInterior
  rw [hAHull]
  exact ⟨a, haS, hay⟩


private theorem local_full_zero_one_face
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (s : pure C u) (hsingle : SingleLabel C u s)
    {h : V →ₗ[ℝ] ℝ} (hh : h ∈ fullZeroConfirmers C u s) :
    {x | x ∈ base C u ∧ h x = 1} = {(s : V)} := by
  have geom := (exclusion_ball_faces hc hs hg hB).1
  have hpure (v : pure C u) (hv : h v = 1) : v = s := by
    have hsub : exclusion C u s ⊆ exclusion C u v := by
      intro x hx
      exact ⟨hx.1, h, ⟨hh.1.1, hv⟩, hh.2 x hx⟩
    obtain ⟨b⟩ := hB v
    have he : exclusion C u s = exclusion C u v :=
      chart_face_eq b (geom s).2.2.1
        ((geom s).2.2.2.2.1.mono (geom v).2.2.2.2.1.subset hsub) (geom s).1
    exact hsingle v he.symm
  let L := h.toContinuousLinearMap
  let F := L.toExposed (base C u)
  have hex : IsExposed ℝ (base C u) F := ContinuousLinearMap.toExposed.isExposed
  have hF : F = {x | x ∈ base C u ∧ h x = 1} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, le_antisymm
        (by simpa [hx.1.2] using (hh.1.1 x hx.1.1).2)
        (by
          have hb := hx.2 s (pure_mem s)
          change h s ≤ h x at hb
          simpa [hh.1.2] using hb)⟩
    · rintro ⟨hx, hx1⟩
      refine ⟨hx, fun y hy => ?_⟩
      change h y ≤ h x
      rw [hx1]
      simpa [hy.2] using (hh.1.1 y hy.1).2
  have hpoints : F.extremePoints ℝ ⊆ {(s : V)} := by
    intro v hv
    have hvp := hex.isExtreme.extremePoints_subset_extremePoints hv
    have hv1 := (hF ▸ hv.1).2
    exact congrArg Subtype.val (hpure ⟨v, hvp⟩ hv1)
  have hFs : F ⊆ {(s : V)} := by
    rw [← closure_convexHull_extremePoints (hex.isCompact (base_compact hc hs))
      (hex.convex (base_convex C u))]
    exact closure_minimal (convexHull_min hpoints (convex_singleton _)) isClosed_singleton
  rw [← hF]
  exact Set.Subset.antisymm hFs (Set.singleton_subset_iff.mpr
    (hF.symm ▸ (show (s : V) ∈ {x | x ∈ base C u ∧ h x = 1} from
      ⟨pure_mem s, hh.1.2⟩)))

/-- Uniform approximation of one complete original source confirmer by arbitrary
positive annihilators recovers its labelled pure point in the same returned balls. -/
private theorem positive_source_pure_recovery
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    (a : pure C u) (ha : (a : V) ∈ exclusion C u p)
    {h : V →ₗ[ℝ] ℝ} (hh : h ∈ fullZeroConfirmers C u a)
    (tn : ℕ → pure C u) (ht : Tendsto tn atTop (𝓝 p))
    (bn : ℕ → (V →ₗ[ℝ] ℝ)) (hb : ∀ n, bn n ∈ positiveZeros (tn n))
    (hconv : TendstoUniformly (fun n (x : exclusion C u p) => bn n x)
      (fun x => h x) atTop) :
    ∃ xn : ℕ → pure C u, (∀ n, (xn n : V) ∈ exclusion C u (tn n)) ∧
      Tendsto (fun n => (xn n : V)) atTop (𝓝 (a : V)) := by
  classical
  let f (n : ℕ) := unitTruncation (C := C) (u := u) (bn n)
  have hell (x : exclusion C u p) : 0 ≤ h x ∧ h x ≤ 1 := by
    simpa only [x.property.1.2] using hh.1.1 x x.property.1.1
  obtain ⟨hf, hfu, _, _⟩ := moving_positive_normalization hc hs hg hB p tn ht bn hb
    (fun x => h x) hell hconv
  have hfzero (n : ℕ) : f n ∈ zeroEffects C u (tn n) := hf n
  choose xn hxn hmax using fun n => zero_effect_maximizer hc hs hg hB (tn n) (hfzero n)
  have hfa : Tendsto (fun n => f n a) atTop (𝓝 1) := by
    simpa only [hh.1.2] using hfu.tendsto_at ⟨a, ha⟩
  have hfx : Tendsto (fun n => f n (xn n)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hfa tendsto_const_nhds
    · exact fun n => hmax n a (pure_mem a)
    · intro n
      simpa only [(pure_mem (xn n)).2] using ((hfzero n).1 (xn n) (pure_mem (xn n)).1).2
  refine ⟨xn, hxn, ?_⟩
  apply (base_compact hc hs).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => pure_mem (xn n))
  intro x hxK hcluster
  obtain ⟨φ, hφ, hφx⟩ := hcluster.tendsto_subseq
  have hxF : x ∈ exclusion C u p := exclusion_upper_limit hc hs hg
    (ht.comp hφ.tendsto_atTop) hφx (fun n => hxn (φ n))
  obtain ⟨e, he, ψ, hψ, hfe⟩ := (effects_compact hs hg).tendsto_subseq
    (fun n => (show (f (φ n)).toContinuousLinearMap ∈ effects C u from (hfzero (φ n)).1))
  have ev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have hex1 : e x = 1 := by
    apply tendsto_nhds_unique ((ev.tendsto (e, x)).comp
      (hfe.prodMk_nhds (hφx.comp hψ.tendsto_atTop)))
    exact hfx.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  have hexh : e x = h x := by
    apply tendsto_nhds_unique
      ((ev.tendsto (e, x)).comp (hfe.prodMk_nhds tendsto_const_nhds))
    exact (hfu.tendsto_at ⟨x, hxF⟩).comp
      (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  have hx1 : h x = 1 := hexh.symm.trans hex1
  have hxone : x ∈ ({(a : V)} : Set V) := by
    rw [← local_full_zero_one_face hc hs hg hB a
      (single_label_neighbor hc hs hg hB p a hp ha) hh]
    exact ⟨hxK, hx1⟩
  exact hxone


private theorem ball_span_direction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : E →ᵃ[ℝ] V) :
    (affineSpan ℝ (a '' Metric.closedBall 0 1)).direction = a.linear.range := by
  have hspan : affineSpan ℝ (Metric.closedBall (0 : E) 1) = ⊤ := by
    apply top_unique
    rw [← Metric.isOpen_ball.affineSpan_eq_top (show (Metric.ball (0 : E) 1).Nonempty from ⟨0, by simp⟩)]
    exact affineSpan_mono ℝ Metric.ball_subset_closedBall
  rw [← AffineSubspace.map_span, hspan, AffineSubspace.map_direction,
    AffineSubspace.direction_top, Submodule.map_top]

private theorem chart_dimension (t : pure C u) (b : ExclusionChart C u t) :
    Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction = b.dim := by
  rw [← b.whole, ball_span_direction,
    LinearMap.finrank_range_of_inj (b.param.linear_injective_iff.mpr b.injective)]
  simp

private theorem chart_at_dimension {t : pure C u} (b : ExclusionChart C u t)
    {d : ℕ} (h : b.dim = d) :
    ∃ a : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] V,
      Function.Injective a ∧ a '' Metric.closedBall 0 1 = exclusion C u t := by
  rcases b with ⟨d', hd', a, ha, hw⟩
  dsimp only at h
  subst d'
  exact ⟨a, ha, hw⟩

private theorem low_dimension_common_ball_impossible
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (S : Finset V)
    (hS : affineSpan ℝ (S : Set V) = affineSpan ℝ (exclusion C u p))
    {y : V} (hy : y ∈ intrinsicInterior ℝ (convexHull ℝ (S : Set V)))
    (rn tn : ℕ → pure C u)
    (hr : Tendsto (fun n => (rn n : V)) atTop (𝓝 y))
    (ht : Tendsto tn atTop (𝓝 p))
    (hret : ∀ n, (rn n : V) ∈ exclusion C u (tn n))
    (hdim : ∀ n, Module.finrank ℝ (affineSpan ℝ (exclusion C u (tn n))).direction ≤
      Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction)
    (hrec : ∀ a ∈ S, ∃ xn : ℕ → V, (∀ n, xn n ∈ exclusion C u (tn n)) ∧
      Tendsto xn atTop (𝓝 a)) : False := by
  classical
  let k := Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction
  let b (n : ℕ) := Classical.choice (hB (tn n))
  have hb (n : ℕ) : (b n).dim ≤ k := by
    rw [← chart_dimension (tn n) (b n)]
    exact hdim n
  have hf : ∃ᶠ n in atTop, ∃ d ∈ Finset.range (k + 1), (b n).dim = d :=
    (Eventually.of_forall fun n => ⟨(b n).dim, Finset.mem_range.mpr (by have h := hb n; omega), rfl⟩).frequently
  obtain ⟨d, hd, hdf⟩ := (Filter.frequently_exists_finset (Finset.range (k + 1))).mp hf
  obtain ⟨φ, hφ, hdeq⟩ := extraction_of_frequently_atTop hdf
  have hdle : d ≤ k := by have h := Finset.mem_range.mp hd; omega
  have hdpos : 0 < d := by rw [← hdeq 0]; exact (b (φ 0)).dim_pos
  haveI : Nonempty (Fin d) := ⟨⟨0, hdpos⟩⟩
  choose a ha hw using fun n => chart_at_dimension (b (φ n)) (hdeq n)
  let E := EuclideanSpace ℝ (Fin d)
  let F (n : ℕ) : NonemptyCompacts V :=
    ⟨⟨exclusion C u (tn (φ n)), ((exclusion_ball_faces hc hs hg hB).1 _).2.1⟩,
      ((exclusion_ball_faces hc hs hg hB).1 _).1.nonempty⟩
  obtain ⟨G, hGK, ψ, hψ, hFG⟩ :=
    (NonemptyCompacts.isCompact_subsets_of_isCompact (base_compact hc hs)).tendsto_subseq
      (fun n => (show (F n : Set V) ⊆ base C u from fun z hz => hz.1))
  have ht' : Tendsto (fun n => tn (φ (ψ n))) atTop (𝓝 p) :=
    ht.comp (hφ.comp hψ).tendsto_atTop
  have hsub : (G : Set V) ⊆ exclusion C u p := by
    apply (exclusion_limit_labels hc hs hg hB (fun n => tn (φ (ψ n)))
      ((continuous_subtype_val.tendsto p).comp ht') G (tendsto_iff_dist_tendsto_zero.mp hFG)).2 p.property
  have hSG : (S : Set V) ⊆ (G : Set V) := by
    intro z hz
    obtain ⟨xn, hxn, hxt⟩ := hrec z hz
    exact mem_compact_limit (fun n => F (ψ n)) G hFG
      (fun n => hxn (φ (ψ n))) (hxt.comp (hφ.comp hψ).tendsto_atTop)
  have hspan : affineSpan ℝ (G : Set V) = affineSpan ℝ (exclusion C u p) :=
    le_antisymm (affineSpan_mono ℝ hsub) (by rw [← hS]; exact affineSpan_mono ℝ hSG)
  let c (n : ℕ) := a (ψ n) 0
  let L (n : ℕ) := (a (ψ n)).linear.toContinuousLinearMap
  have hball (n : ℕ) : ballImage (c n) (L n) = F (ψ n) := by
    apply NonemptyCompacts.ext
    change (fun x => c n + L n x) '' Metric.closedBall 0 1 = _
    have he (x : E) : c n + L n x = a (ψ n) x := by
      simpa [c, L, add_comm] using (congrFun (a (ψ n)).decomp x).symm
    simp_rw [he]
    exact hw (ψ n)
  obtain ⟨q, χ, hχ, hq, hqG⟩ := parameter_subsequence c L G (by simpa only [hball, Function.comp_def] using hFG)
  let f : E →ᵃ[ℝ] V :=
    (AffineEquiv.constVAdd ℝ V q.1).toAffineMap.comp q.2.toLinearMap.toAffineMap
  have hfG : f '' Metric.closedBall 0 1 = (G : Set V) := by
    change (ballImage q.1 q.2 : Set V) = _
    rw [hqG]
  have hrank : Module.finrank ℝ f.linear.range = k := by
    rw [← ball_span_direction, hfG, hspan]
  have hnull := f.linear.finrank_range_add_finrank_ker
  have hEdim : Module.finrank ℝ E = d := by simp [E]
  have hinj : Function.Injective f := by
    apply f.linear_injective_iff.mp
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    rw [hEdim, hrank] at hnull
    omega
  have hconv : Convex ℝ (G : Set V) := by
    rw [← hfG]
    exact (convex_closedBall (0 : E) 1).affine_image f
  have hInt : y ∈ intrinsicInterior ℝ (G : Set V) := by
    have hspanS : affineSpan ℝ (convexHull ℝ (S : Set V)) = affineSpan ℝ (G : Set V) := by
      rw [affineSpan_convexHull, hspan, hS]
    have hinc : convexHull ℝ (S : Set V) ⊆ (G : Set V) := convexHull_min hSG hconv
    unfold intrinsicInterior at hy ⊢
    rw [hspanS] at hy
    obtain ⟨yA, hyA, rfl⟩ := hy
    exact ⟨yA, interior_mono (preimage_mono hinc) hyA, rfl⟩
  have hfront (n : ℕ) : (rn (φ (ψ n)) : V) ∈ intrinsicFrontier ℝ
      (a (ψ n) '' Metric.closedBall 0 1) := by
    rw [hw]
    obtain ⟨bb⟩ := hB (tn (φ (ψ n)))
    have he : intrinsicFrontier ℝ (exclusion C u (tn (φ (ψ n)))) =
        exclusion C u (tn (φ (ψ n))) ∩ pure C u := by
      rw [← bb.whole, intrinsic_image _ bb.injective, intrinsic_ball]
      simpa only [bb.whole] using (chart_boundary hc hs hg hB _ bb).symm
    rw [he]
    exact ⟨hret _, (rn _).property⟩
  have hyfront := (affine_ball_boundary_limit (fun n => a (ψ n)) f
    (fun n => ha _) hinj (by
      have hh := tendsto_iff_dist_tendsto_zero.mp hFG
      change Tendsto (fun n => Metric.hausdorffDist
        (exclusion C u (tn (φ (ψ n)))) (G : Set V)) atTop (𝓝 0) at hh
      simpa only [hw, hfG] using hh)).2
      (fun n => (rn (φ (ψ n)) : V)) y hfront (hr.comp (hφ.comp hψ).tendsto_atTop)
  rw [hfG, ← closure_sdiff_intrinsicInterior] at hyfront
  exact hyfront.2 hInt


/-- Supremum seminorm on the entire fixed original source exclusion. -/
def sourceNorm (p : pure C u) (b : V →ₗ[ℝ] ℝ) : ℝ :=
  sSup ((fun x => |b x|) '' exclusion C u p)

/-- Infimum over all whole-cone positive extensions exactly zero at the same label. -/
def positiveSourceDistance (p t : pure C u) (h : V →ₗ[ℝ] ℝ) : ℝ :=
  sInf ((fun b => sourceNorm p (b - h)) '' positiveZeros t)

private theorem source_norm_eval_le
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (b : V →ₗ[ℝ] ℝ) {x : V} (hx : x ∈ exclusion C u p) :
    |b x| ≤ sourceNorm p b := by
  exact le_csSup (((exclusion_ball_faces hc hs hg hB).1 p).2.1.bddAbove_image
    (by fun_prop)) (mem_image_of_mem _ hx)

private theorem returned_labels_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p) {y : V}
    (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (rn tn : ℕ → pure C u) (hr : Tendsto (fun n => (rn n : V)) atTop (𝓝 y))
    (htn : ∀ n, (tn n : V) ∈ exclusion C u (rn n)) :
    Tendsto tn atTop (𝓝 p) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (local_single_label_collapse hc hs hg hB p hp hy rn hr)
  exact le_csSup (((exclusion_ball_faces hc hs hg hB).1 (rn n)).2.1.bddAbove_image
    (by fun_prop)) (mem_image_of_mem _ (htn n))

/-- One finite original test family precedes every nearby pure input and its
single returned pure label. Small source infimum errors force dimension growth;
all fixed test readouts are uniformly small at every such return. -/
theorem common_positive_source_obstruction
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p) {y : V}
    (hy : y ∈ intrinsicInterior ℝ (exclusion C u p)) :
    ∃ (S : Finset V) (a : S → pure C u) (h : S → (V →ₗ[ℝ] ℝ)),
      S.Nonempty ∧
      (∀ i, (a i : V) = (i : V) ∧ (a i : V) ∈ exclusion C u p ∧
        h i ∈ fullZeroConfirmers C u (a i)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
        (∀ r : pure C u, ‖(r : V) - y‖ < ε →
          ∀ t : pure C u, (t : V) ∈ exclusion C u r →
          Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction + 1 ≤
            Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction ∨
          δ ≤ sSup (Set.range fun i => positiveSourceDistance p t (h i))) ∧
        ∀ τ : ℝ, 0 < τ → ∃ ετ : ℝ, 0 < ετ ∧
          ∀ r : pure C u, ‖(r : V) - y‖ < ετ →
            ∀ t : pure C u, (t : V) ∈ exclusion C u r → ∀ i, h i t ≤ τ := by
  classical
  obtain ⟨S, hS, hspan, hyS⟩ := finite_source_tests hc hs hg hB p hy
  have hSne : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa [he] using intrinsicInterior_subset hyS
  letI : Nonempty S := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  let a (i : S) : pure C u := ⟨i, (hS i.property).2⟩
  have hconfirm (i : S) : ∃ h, h ∈ fullZeroConfirmers C u (a i) := by
    obtain ⟨h, hh, hz⟩ := ((exclusion_ball_faces hc hs hg hB).1 (a i)).2.2.2.2.2.2
    exact ⟨h, hh, fun z hzm => (hz ▸ hzm).2⟩
  choose h hh using hconfirm
  have hha (i : S) : h i p = 0 :=
    (hh i).2 p ((exclusion_symmetric p (a i)).mp (hS i.property).1)
  let k := Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction
  have hgap : ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ r : pure C u, ‖(r : V) - y‖ < ε →
        ∀ t : pure C u, (t : V) ∈ exclusion C u r →
        k + 1 ≤ Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction ∨
        δ ≤ sSup (Set.range fun i => positiveSourceDistance p t (h i)) := by
    by_contra! hn
    let v (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have hv (n : ℕ) : 0 < v n := by dsimp [v]; positivity
    have hvlim : Tendsto v atTop (𝓝 0) := by
      simpa only [v] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    have hbad (n : ℕ) : ∃ r : pure C u, ‖(r : V) - y‖ < v n ∧
        ∃ t : pure C u, (t : V) ∈ exclusion C u r ∧
          Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction ≤ k ∧
          sSup (Set.range fun i => positiveSourceDistance p t (h i)) < v n := by
      obtain ⟨r, hr, t, htr, hdim, herr⟩ := hn (v n) (hv n) (v n) (hv n)
      exact ⟨r, hr, t, htr, by omega, herr⟩
    choose rn hrn tn htn hdim herr using hbad
    have hr : Tendsto (fun n => (rn n : V)) atTop (𝓝 y) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hrn n).le) hvlim
    have ht := returned_labels_tendsto hc hs hg hB p hp hy rn tn hr htn
    have hrec (i : S) : ∃ xn : ℕ → pure C u,
        (∀ n, (xn n : V) ∈ exclusion C u (tn n)) ∧
        Tendsto (fun n => (xn n : V)) atTop (𝓝 (i : V)) := by
      have he (n : ℕ) : positiveSourceDistance p (tn n) (h i) < v n :=
        (le_csSup (Set.finite_range _).bddAbove (mem_range_self i)).trans_lt (herr n)
      have hzero (n : ℕ) : (0 : V →ₗ[ℝ] ℝ) ∈ positiveZeros (tn n) := by
        constructor <;> simp
      have hb (n : ℕ) : ∃ b ∈ positiveZeros (tn n), sourceNorm p (b - h i) < v n := by
        obtain ⟨z, ⟨b, hb, rfl⟩, hz⟩ := exists_lt_of_csInf_lt
          (Set.Nonempty.image _ ⟨0, hzero n⟩) (he n)
        exact ⟨b, hb, hz⟩
      choose bn hbn hbound using hb
      have hconv : TendstoUniformly (fun n (x : exclusion C u p) => bn n x)
          (fun x => h i x) atTop := by
        apply Metric.tendstoUniformly_iff.mpr
        intro ε hε
        filter_upwards [hvlim.eventually (gt_mem_nhds hε)] with n hn x
        have hev := source_norm_eval_le hc hs hg hB p (bn n - h i) x.property
        change |bn n x - h i x| ≤ sourceNorm p (bn n - h i) at hev
        rw [Real.dist_eq, abs_sub_comm]
        exact hev.trans_lt ((hbound n).trans hn)
      exact positive_source_pure_recovery hc hs hg hB p hp (a i) (hS i.property).1
        (hh i) tn ht bn hbn hconv
    apply low_dimension_common_ball_impossible hc hs hg hB p S hspan hyS rn tn hr ht
      (fun n => (exclusion_symmetric (rn n) (tn n)).mp (htn n)) hdim
    intro z hz
    obtain ⟨xn, hxn, hxt⟩ := hrec ⟨z, hz⟩
    exact ⟨fun n => (xn n : V), hxn, hxt⟩
  obtain ⟨ε, hε, δ, hδ, hgap⟩ := hgap
  refine ⟨S, a, h, hSne, (fun i => ⟨rfl, (hS i.property).1, hh i⟩), ε, hε, δ, hδ, hgap, ?_⟩
  intro τ hτ
  by_contra! hn
  let v (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hv (n : ℕ) : 0 < v n := by dsimp [v]; positivity
  have hvlim : Tendsto v atTop (𝓝 0) := by
    simpa only [v] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  choose rn hrn tn htn i hi using fun n => hn (v n) (hv n)
  have hr : Tendsto (fun n => (rn n : V)) atTop (𝓝 y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hrn n).le) hvlim
  have ht := returned_labels_tendsto hc hs hg hB p hp hy rn tn hr htn
  have hev : ∀ᶠ n in atTop, ∀ j : S, h j (tn n) < τ := by
    apply Filter.eventually_all.mpr
    intro j
    have hj := (h j).continuous_of_finiteDimensional.tendsto (p : V) |>.comp
      (tendsto_subtype_rng.mp ht)
    rw [hha j] at hj
    exact hj.eventually (gt_mem_nhds hτ)
  obtain ⟨n, hn⟩ := hev.exists
  exact (hi n).not_ge (hn (i n)).le

end D5.S3.Quantum.Foundation.FixedZeroObstruction
