/- GID: D5/S3/Quantum/Foundation/CommonSourceLiftObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/CommonSourceLiftObstruction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Local singleton labels control entire moving original exclusion fibers. -/

import D5.S3.Quantum.Foundation.UniqueConfirmationDensity
import D5.S3.Quantum.Foundation.ExclusionIncidence
import D5.S3.Quantum.Foundation.FixedZeroObstruction
import D5.S3.Quantum.Foundation.CommonPositiveExtension
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Sets.VietorisTopology

/-! The state body, effects, pure labels and norms are the original ones. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.CommonSourceLiftObstruction

open Set Filter Topology TopologicalSpace
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ContinuousFrameSum SingleLabelNormalBody ExclusionIncidence
open UniqueConfirmationDensity WholePairBallConfirmation OriginalFacePolarity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Maximum of a positive original functional on the entire normalized base. -/
def baseMaximum (b : V →ₗ[ℝ] ℝ) : ℝ := sSup (b '' base C u)

/-- Upper displacement of the whole moving exclusion from the fixed source ball. -/
def upperDisplacement (p t : pure C u) : ℝ :=
  sSup ((fun x => Metric.infDist x (exclusion C u p)) '' exclusion C u t)

/-- Restriction to the entire fixed original source ball. -/
def sourceReadout (p : pure C u) (b : V →ₗ[ℝ] ℝ) : C(exclusion C u p, ℝ) :=
  ⟨fun x => b x, b.continuous_of_finiteDimensional.comp continuous_subtype_val⟩

/-- Normalization uses the global maximum on the entire original state body. -/
def normalizePositive (b : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] ℝ :=
  (max 1 (baseMaximum (C := C) (u := u) b))⁻¹ • b

/-- Distance on the entire fixed source ball to restrictions of all original
cone-positive functionals zero at the same return label. The image need not be closed. -/
def sourceDistance
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p t : pure C u) (h : V →ₗ[ℝ] ℝ) : ℝ :=
  let : CompactSpace (exclusion C u p) :=
    isCompact_iff_compactSpace.mp ((exclusion_ball_faces hc hs hg hB).1 p).2.1
  Metric.infDist (sourceReadout p h)
    (sourceReadout p '' CommonPositiveExtension.zeroPositive C u t)

private def baseRestriction : (V →L[ℝ] ℝ) →ₗ[ℝ] C(base C u, ℝ) where
  toFun b := FixedZeroObstruction.stateReadout b.toLinearMap
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

private theorem original_dual_bound
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ A : ℝ, 0 < A ∧ ∀ b : V →ₗ[ℝ] ℝ,
      ‖b.toContinuousLinearMap‖ ≤ A * FixedZeroObstruction.stateNorm hc hs b := by
  let : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  have hi : Function.Injective (baseRestriction (C := C) (u := u)) := by
    apply LinearMap.ker_eq_bot.mp
    refine le_antisymm ?_ bot_le
    intro b hb
    have hz : ∀ z ∈ pure C u, b z = 0 := by
      intro z hz
      exact congrArg (fun f : C(base C u, ℝ) => f ⟨z, pure_mem ⟨z, hz⟩⟩) hb
    have hspan : Submodule.span ℝ (pure C u) ≤ LinearMap.ker b.toLinearMap :=
      Submodule.span_le.mpr hz
    rw [pure_span (base_compact hc hs) hs hg] at hspan
    have hb0 : b = 0 := by
      ext z
      exact LinearMap.congr_fun (LinearMap.ker_eq_top.mp (top_le_iff.mp hspan)) z
    simp [hb0]
  obtain ⟨A, hA, hb⟩ := (baseRestriction (C := C) (u := u)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨A, hA, fun b => ?_⟩
  change ‖b.toContinuousLinearMap‖ ≤ (A : ℝ) *
    ‖baseRestriction (C := C) (u := u) b.toContinuousLinearMap‖
  simpa only [map_zero, dist_zero_right] using
    hb.le_mul_dist b.toContinuousLinearMap 0

private theorem positive_base_norm
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (p : pure C u) (b : V →ₗ[ℝ] ℝ) (hb : ∀ z ∈ C, 0 ≤ b z) :
    FixedZeroObstruction.stateNorm hc hs b = baseMaximum (C := C) (u := u) b := by
  let : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  obtain ⟨x, hx, hm⟩ := (base_compact hc hs).exists_isMaxOn
    ⟨p, pure_mem p⟩ b.continuous_of_finiteDimensional.continuousOn
  have he : baseMaximum (C := C) (u := u) b = b x :=
    (show IsGreatest (b '' base C u) (b x) from
      ⟨Set.mem_image_of_mem b hx, by rintro _ ⟨z, hz, rfl⟩; exact hm hz⟩).csSup_eq
  rw [he]
  change ‖FixedZeroObstruction.stateReadout (C := C) (u := u) b‖ = b x
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (hb x hx.1)).mpr
    intro z
    change |b z| ≤ b x
    rw [abs_of_nonneg (hb z z.property.1)]
    exact hm z.property
  · have h := (FixedZeroObstruction.stateReadout (C := C) (u := u) b).norm_coe_le_norm
      ⟨x, hx⟩
    change ‖b x‖ ≤ _ at h
    simpa [Real.norm_eq_abs, abs_of_nonneg (hb x hx.1)] using h

private theorem upper_displacement_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {t : ℕ → pure C u} (ht : Tendsto t atTop (𝓝 p)) :
    Tendsto (fun n => upperDisplacement p (t n)) atTop (𝓝 0) := by
  have hgD := (exclusion_ball_faces hc hs hg hB).1
  have hnn (q : pure C u) : 0 ≤ upperDisplacement p q := by
    obtain ⟨x, hx⟩ := (hgD q).1.nonempty
    exact Metric.infDist_nonneg.trans (le_csSup
      ((hgD q).2.1.bddAbove_image (Metric.continuous_infDist_pt _).continuousOn)
      (Set.mem_image_of_mem _ hx))
  apply tendsto_order.mpr
  refine ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hnn _), ?_⟩
  intro a ha
  filter_upwards [exclusion_upper_eventually hc hs hg ht (half_pos ha)] with n hn
  have hle : upperDisplacement p (t n) ≤ a / 2 := by
    apply csSup_le (((hgD (t n)).1.nonempty).image _)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hdist⟩ := hn x hx
    exact (Metric.infDist_le_dist_of_mem hz).trans hdist.le
  exact hle.trans_lt (by linarith)

private theorem moving_positive_bound
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p t : pure C u) {A : ℝ} (hA : 0 < A)
    (hdual : ∀ b : V →ₗ[ℝ] ℝ,
      ‖b.toContinuousLinearMap‖ ≤ A * FixedZeroObstruction.stateNorm hc hs b)
    (hsmall : A * upperDisplacement p t < 1)
    (b : V →ₗ[ℝ] ℝ) (hpos : ∀ z ∈ C, 0 ≤ b z) (hzero : b t = 0) :
    baseMaximum (C := C) (u := u) b ≤
      FixedZeroObstruction.faceMaximum p b / (1 - A * upperDisplacement p t) := by
  have geom := (exclusion_ball_faces hc hs hg hB).1
  have hF := (geom p).2.1
  have hFn := (geom p).1.nonempty
  by_cases hb0 : b = 0
  · subst b
    simp [baseMaximum, FixedZeroObstruction.faceMaximum,
      hFn.image_const, (show (base C u).Nonempty from ⟨t, pure_mem t⟩).image_const]
  obtain ⟨x, hx, hbx, hmax⟩ := positive_annihilator_maximum hc hs hg t b hb0 hpos hzero
  have hBmax : baseMaximum (C := C) (u := u) b = b x :=
    (show IsGreatest (b '' base C u) (b x) from
      ⟨Set.mem_image_of_mem b hx.1, by rintro _ ⟨z, hz, rfl⟩; exact hmax z hz⟩).csSup_eq
  obtain ⟨z, hz, hdist⟩ := hF.exists_infDist_eq_dist hFn (x : V)
  have hbz : b z ≤ FixedZeroObstruction.faceMaximum p b :=
    le_csSup (hF.bddAbove_image b.continuous_of_finiteDimensional.continuousOn)
      (Set.mem_image_of_mem b hz)
  have halpha : dist (x : V) z ≤ upperDisplacement p t := by
    rw [← hdist]
    exact le_csSup ((geom t).2.1.bddAbove_image
      (Metric.continuous_infDist_pt _).continuousOn) (Set.mem_image_of_mem _ hx)
  have hdiff : b x - b z ≤ ‖b.toContinuousLinearMap‖ * dist (x : V) z := by
    calc
      b x - b z ≤ |b x - b z| := le_abs_self _
      _ = ‖b.toContinuousLinearMap ((x : V) - z)‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖b.toContinuousLinearMap‖ * ‖(x : V) - z‖ :=
        b.toContinuousLinearMap.le_opNorm _
      _ = _ := by rw [dist_eq_norm]
  have hd := hdual b
  rw [positive_base_norm hc hs p b hpos, hBmax] at hd
  have hmul : ‖b.toContinuousLinearMap‖ * dist (x : V) z ≤
      (A * b x) * upperDisplacement p t :=
    (mul_le_mul_of_nonneg_right hd dist_nonneg).trans
      (mul_le_mul_of_nonneg_left halpha (mul_nonneg hA.le hbx.le))
  rw [hBmax, le_div_iff₀ (by linarith : 0 < 1 - A * upperDisplacement p t)]
  nlinarith

/-- The same original dual constant controls every positive annihilator at every
nearby pure label, with no upper budget on that functional. -/
theorem moving_positive_control
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) :
    ∃ A : ℝ, 0 < A ∧
      (∀ b : V →ₗ[ℝ] ℝ,
        ‖b.toContinuousLinearMap‖ ≤ A * FixedZeroObstruction.stateNorm hc hs b) ∧
      Tendsto (upperDisplacement p) (𝓝 p) (𝓝 0) ∧
      ∀ t : pure C u, A * upperDisplacement p t < 1 →
        ∀ b : V →ₗ[ℝ] ℝ, (∀ z ∈ C, 0 ≤ b z) → b t = 0 →
          baseMaximum (C := C) (u := u) b ≤
            FixedZeroObstruction.faceMaximum p b / (1 - A * upperDisplacement p t) := by
  obtain ⟨A, hA, hdual⟩ := original_dual_bound hc hs hg
  exact ⟨A, hA, hdual, tendsto_nhds_iff_seq_tendsto.mpr
    (fun t ht => upper_displacement_tendsto hc hs hg hB p ht),
    fun t ht b hb hz => moving_positive_bound hc hs hg hB p t hA hdual ht b hb hz⟩

private theorem normalize_positive_properties
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (p : pure C u) (b : V →ₗ[ℝ] ℝ) (hpos : ∀ z ∈ C, 0 ≤ b z) :
    proper C u (normalizePositive (C := C) (u := u) b) ∧
    FixedZeroObstruction.stateNorm hc hs
      (normalizePositive (C := C) (u := u) b - b) =
        max (baseMaximum (C := C) (u := u) b - 1) 0 := by
  let : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  let B := baseMaximum (C := C) (u := u) b
  let D := max 1 B
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB : 0 ≤ B := by
    change 0 ≤ baseMaximum (C := C) (u := u) b
    rw [← positive_base_norm hc hs p b hpos]
    exact norm_nonneg _
  have hbmax (x : V) (hx : x ∈ base C u) : b x ≤ B :=
    le_csSup ((base_compact hc hs).bddAbove_image
      b.continuous_of_finiteDimensional.continuousOn) (Set.mem_image_of_mem b hx)
  refine ⟨cone_bound (base_compact hc hs) hs (fun q => ?_), ?_⟩
  · change 0 ≤ D⁻¹ * b q ∧ D⁻¹ * b q ≤ 1
    refine ⟨mul_nonneg (inv_nonneg.mpr hD.le) (hpos q (pure_mem q).1), ?_⟩
    rw [← div_eq_inv_mul, div_le_one hD]
    exact (hbmax q (pure_mem q)).trans (le_max_right _ _)
  have he : FixedZeroObstruction.stateReadout (C := C) (u := u)
      (normalizePositive (C := C) (u := u) b - b) =
      (D⁻¹ - 1) • FixedZeroObstruction.stateReadout b := by
    ext x
    change D⁻¹ * b x - b x = (D⁻¹ - 1) * b x
    ring
  change ‖FixedZeroObstruction.stateReadout (C := C) (u := u)
    (normalizePositive (C := C) (u := u) b - b)‖ = _
  rw [he, norm_smul, Real.norm_eq_abs,
    show ‖FixedZeroObstruction.stateReadout (C := C) (u := u) b‖ = B from
      positive_base_norm hc hs p b hpos]
  change |D⁻¹ - 1| * B = max (B - 1) 0
  by_cases h : B ≤ 1
  · simp [D, max_eq_left h, max_eq_right (sub_nonpos.mpr h)]
  · have h1 : 1 < B := lt_of_not_ge h
    have hne : B ≠ 0 := (zero_lt_one.trans h1).ne'
    have hi : B⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans h1)).mpr h1.le
    rw [show D = B from max_eq_right h1.le,
      abs_of_nonpos (sub_nonpos.mpr hi), max_eq_left (sub_nonneg.mpr h1.le)]
    field_simp
    ring

/-- Full moving-unit control on unbounded positive annihilators. The limit is
an arbitrary function on all of F; its continuity is derived from uniform convergence. -/
theorem moving_positive_normalization
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (t : ℕ → pure C u) (ht : Tendsto t atTop (𝓝 p))
    (b : ℕ → V →ₗ[ℝ] ℝ) (hpos : ∀ n z, z ∈ C → 0 ≤ b n z)
    (hzero : ∀ n, b n (t n) = 0)
    (ell : exclusion C u p → ℝ) (hell : ∀ x, 0 ≤ ell x ∧ ell x ≤ 1)
    (hu : TendstoUniformly (fun n (x : exclusion C u p) => b n x) ell atTop) :
    (∀ n, proper C u (normalizePositive (C := C) (u := u) (b n)) ∧
      normalizePositive (C := C) (u := u) (b n) (t n) = 0) ∧
    Tendsto (fun n => FixedZeroObstruction.stateNorm hc hs
      (normalizePositive (C := C) (u := u) (b n) - b n)) atTop (𝓝 0) ∧
    TendstoUniformly (fun n (x : exclusion C u p) =>
      normalizePositive (C := C) (u := u) (b n) x) ell atTop ∧
    (sSup (Set.range ell) = 1 →
      Tendsto (fun n => baseMaximum (C := C) (u := u) (b n)) atTop (𝓝 1)) := by
  classical
  have geom := (exclusion_ball_faces hc hs hg hB).1
  let : CompactSpace (exclusion C u p) := isCompact_iff_compactSpace.mp (geom p).2.1
  let : CompactSpace (base C u) := isCompact_iff_compactSpace.mp (base_compact hc hs)
  have hn := fun n => normalize_positive_properties hc hs p (b n) (hpos n)
  let e : C(exclusion C u p, ℝ) := ⟨ell, hu.continuous
    (Frequently.of_forall fun n => (sourceReadout p (b n)).continuous)⟩
  have he : ‖e‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr
    (fun x => by simpa [e, Real.norm_eq_abs, abs_of_nonneg (hell x).1] using (hell x).2)
  have hread : Tendsto (fun n => sourceReadout p (b n)) atTop (𝓝 e) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hu) (ε / 2) (half_pos hε)] with n hn
    rw [dist_eq_norm]
    have hle : ‖sourceReadout p (b n) - e‖ ≤ ε / 2 :=
      (ContinuousMap.norm_le _ (half_pos hε).le).mpr (fun x => by
        simpa [Real.norm_eq_abs, dist_eq_norm, abs_sub_comm, e, sourceReadout] using (hn x).le)
    exact hle.trans_lt (half_lt_self hε)
  let m (n : ℕ) := ‖sourceReadout p (b n)‖
  let B (n : ℕ) := baseMaximum (C := C) (u := u) (b n)
  have hm : Tendsto m atTop (𝓝 ‖e‖) := hread.norm
  have hBnn (n : ℕ) : 0 ≤ B n := by
    change 0 ≤ baseMaximum (C := C) (u := u) (b n)
    rw [← positive_base_norm hc hs p (b n) (hpos n)]
    exact norm_nonneg _
  have hlower (n : ℕ) : m n ≤ B n := by
    apply (ContinuousMap.norm_le _ (hBnn n)).mpr
    intro x
    change |b n x| ≤ B n
    rw [abs_of_nonneg (hpos n x x.property.1.1)]
    exact le_csSup ((base_compact hc hs).bddAbove_image
      (b n).continuous_of_finiteDimensional.continuousOn)
      (Set.mem_image_of_mem _ x.property.1)
  obtain ⟨A, _, _, hlimit, hbound⟩ := moving_positive_control hc hs hg hB p
  have halpha := hlimit.comp ht
  have hden : Tendsto (fun n => 1 - A * upperDisplacement p (t n)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (halpha.const_mul A)
  have hsmall : ∀ᶠ n in atTop, A * upperDisplacement p (t n) < 1 := by
    have ha : Tendsto (fun n => A * upperDisplacement p (t n)) atTop (𝓝 0) := by
      simpa using halpha.const_mul A
    exact ha.eventually (gt_mem_nhds zero_lt_one)
  have hupper : ∀ᶠ n in atTop, B n ≤ m n / (1 - A * upperDisplacement p (t n)) := by
    filter_upwards [hsmall] with n hn
    have hmax : FixedZeroObstruction.faceMaximum p (b n) ≤ m n := by
      apply csSup_le ((geom p).1.nonempty.image _)
      rintro _ ⟨x, hx, rfl⟩
      exact (le_abs_self _).trans ((sourceReadout p (b n)).norm_coe_le_norm ⟨x, hx⟩)
    exact (hbound (t n) hn (b n)
      (hpos n) (hzero n)).trans ((div_le_div_iff_of_pos_right (by linarith)).mpr hmax)
  have hquot : Tendsto (fun n => m n / (1 - A * upperDisplacement p (t n)))
      atTop (𝓝 ‖e‖) := by
    convert hm.div hden one_ne_zero using 1
    rw [div_one]
  have hBt : Tendsto B atTop (𝓝 ‖e‖) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hm
      hquot (Eventually.of_forall hlower) hupper
  have hgap : Tendsto (fun n => FixedZeroObstruction.stateNorm hc hs
      (normalizePositive (C := C) (u := u) (b n) - b n)) atTop (𝓝 0) := by
    have hg := (hBt.sub_const 1).max (tendsto_const_nhds (x := (0 : ℝ)))
    have he0 : max (‖e‖ - 1) 0 = 0 := max_eq_right (sub_nonpos.mpr he)
    simpa only [(hn _).2, he0] using hg
  refine ⟨fun n => ⟨(hn n).1, by simp [normalizePositive, hzero n]⟩, hgap, ?_, ?_⟩
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hu) (ε / 2) (half_pos hε),
      hgap.eventually (gt_mem_nhds (half_pos hε))] with n hn hgapn
    intro x
    have hh := (FixedZeroObstruction.stateReadout (C := C) (u := u)
      (normalizePositive (C := C) (u := u) (b n) - b n)).norm_coe_le_norm
        ⟨x, x.property.1⟩
    have hdist : dist (b n x) (normalizePositive (C := C) (u := u) (b n) x) < ε / 2 := by
      rw [dist_comm, dist_eq_norm]
      exact hh.trans_lt hgapn
    exact (dist_triangle _ (b n x) _).trans_lt (by linarith [hn x])
  · intro hsup
    have hnorm : ‖e‖ = 1 := by
      apply le_antisymm he
      rw [← hsup]
      apply csSup_le (Set.range_nonempty_iff_nonempty.mpr
        ((geom p).1.nonempty.to_subtype))
      rintro _ ⟨x, rfl⟩
      exact (le_abs_self _).trans (e.norm_coe_le_norm x)
    simpa [hnorm] using hBt

/-- A mixed limit in the relative interior of a single-label ball forces every
convergent choice from the entire moving exclusions to limit to that label. -/
private theorem single_label_mixed_upper_limit
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (r : ℕ → pure C u) (hr : Tendsto (fun n => (r n : V)) atTop (𝓝 y))
    {x : V} {xn : ℕ → V} (hxn : ∀ n, xn n ∈ exclusion C u (r n))
    (hx : Tendsto xn atTop (𝓝 x)) : x = (p : V) := by
  classical
  have hall := (exclusion_ball_faces hc hs hg hB).1
  choose e he hz using fun n => (hall (r n)).2.2.2.2.2.2
  let ec (n : ℕ) : V →L[ℝ] ℝ := (e n).toContinuousLinearMap
  obtain ⟨f, hf, φ, hφ, hfe⟩ :=
    (effects_compact hs hg).tendsto_subseq
      (fun n => show ec n ∈ effects C u from (he n).1)
  have heval : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have hfy : f y = 1 := by
    have ht := (heval.tendsto (f, y)).comp
      (hfe.prodMk_nhds (hr.comp hφ.tendsto_atTop))
    have heq : (fun n => (e (φ n)) (r (φ n))) = fun _ : ℕ => (1 : ℝ) :=
      funext fun n => (he (φ n)).2
    change Tendsto (fun n => (e (φ n)) (r (φ n))) atTop (𝓝 (f y)) at ht
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hfx : f x = 0 := by
    have ht := (heval.tendsto (f, x)).comp
      (hfe.prodMk_nhds (hx.comp hφ.tendsto_atTop))
    have heq : (fun n => (e (φ n)) (xn (φ n))) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact (show xn (φ n) ∈ {z | z ∈ base C u ∧ e (φ n) z = 0}
        from hz _ ▸ hxn _).2
    change Tendsto (fun n => (e (φ n)) (xn (φ n))) atTop (𝓝 (f x)) at ht
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hone (z : V) (hzF : z ∈ exclusion C u p) : f z = 1 := by
    have hh := zero_on_exclusion_of_zero_interior hB p (u - f.toLinearMap)
      (fun z hzC => sub_nonneg.mpr (hf z hzC).2) hy
      (by change u y - f y = 0; rw [(intrinsicInterior_subset hy).1.2, hfy]; ring) z hzF
    change u z - f z = 0 at hh
    rw [hzF.1.2] at hh
    linarith
  have hxK : x ∈ base C u := (base_compact hc hs).isClosed.mem_of_tendsto hx
    (Eventually.of_forall fun n => (hxn n).1)
  have hxD (a : pure C u) (ha : (a : V) ∈ exclusion C u p) :
      x ∈ exclusion C u a := ⟨hxK, f.toLinearMap, ⟨hf, hone a ha⟩, hfx⟩
  obtain ⟨a, b, ha, hb, hab⟩ := pure_pair_in_ball hc hs hg hB p
  by_contra hxp
  have heq : exclusion C u a = exclusion C u b :=
    equal_of_two_points hc hs hg hB a b hxp
      ⟨hxD a ha, hxD b hb⟩
      ⟨(exclusion_symmetric p a).mp ha, (exclusion_symmetric p b).mp hb⟩
  exact hab ((single_label_neighbor hc hs hg hB p a hp ha) b heq.symm).symm

/-- Uniform shrinking of each entire original exclusion, without global
injectivity or any common ball dimension. -/
theorem single_label_mixed_shrinking
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (r : ℕ → pure C u) (hr : Tendsto (fun n => (r n : V)) atTop (𝓝 y))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ exclusion C u (r n), ‖x - (p : V)‖ < ε := by
  classical
  by_contra h
  have hb : ∃ᶠ n in atTop, ∃ x ∈ exclusion C u (r n), ε ≤ ‖x - (p : V)‖ := by
    apply (not_eventually.mp h).mono
    intro n hn
    push Not at hn
    exact hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hb
  choose x hx hfar using hbad
  obtain ⟨z, _, ψ, hψ, hxz⟩ :=
    (base_compact hc hs).tendsto_subseq (fun n => (hx n).1)
  have hzp : z = (p : V) := single_label_mixed_upper_limit hc hs hg hB p hp hy
    (fun n => r (φ (ψ n))) (hr.comp (hφ.comp hψ).tendsto_atTop)
    (fun n => hx (ψ n)) hxz
  have hnear : ∀ᶠ n in atTop, dist (x (ψ n)) (p : V) < ε :=
    (Metric.tendsto_nhds.mp (hzp ▸ hxz)) ε hε
  obtain ⟨n, hn⟩ := hnear.exists
  exact (hfar (ψ n)).not_gt (by simpa [dist_eq_norm] using hn)

private theorem local_one_face
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (a : pure C u) (ha : SingleLabel C u a) {h : V →ₗ[ℝ] ℝ}
    (hh : h ∈ FixedZeroObstruction.fullZeroConfirmers C u a) :
    {x | x ∈ base C u ∧ h x = 1} = {(a : V)} := by
  have geom := (exclusion_ball_faces hc hs hg hB).1
  have hpure (v : pure C u) (hv : h v = 1) : v = a := by
    have hsub : exclusion C u a ⊆ exclusion C u v := by
      intro x hx
      exact ⟨hx.1, h, ⟨hh.1.1, hv⟩, hh.2 x hx⟩
    obtain ⟨b⟩ := hB v
    have he : exclusion C u a = exclusion C u v :=
      chart_face_eq b (geom a).2.2.1
        ((geom a).2.2.2.2.1.mono (geom v).2.2.2.2.1.subset hsub) (geom a).1
    exact ha v he.symm
  let L := h.toContinuousLinearMap
  let T := L.toExposed (base C u)
  have hex : IsExposed ℝ (base C u) T := ContinuousLinearMap.toExposed.isExposed
  have hT : T = {x | x ∈ base C u ∧ h x = 1} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, le_antisymm
        (by simpa [hx.1.2] using (hh.1.1 x hx.1.1).2)
        (by
          have hb := hx.2 a (pure_mem a)
          change h a ≤ h x at hb
          simpa only [hh.1.2] using hb)⟩
    · rintro ⟨hx, hx1⟩
      refine ⟨hx, fun z hz => ?_⟩
      change h z ≤ h x
      rw [hx1]
      simpa [hz.2] using (hh.1.1 z hz.1).2
  have hext : T.extremePoints ℝ ⊆ {(a : V)} := by
    intro v hv
    have hvp := hex.isExtreme.extremePoints_subset_extremePoints hv
    exact congrArg Subtype.val (hpure ⟨v, hvp⟩ (hT ▸ hv.1).2)
  have hsub : T ⊆ {(a : V)} := by
    rw [← closure_convexHull_extremePoints (hex.isCompact (base_compact hc hs))
      (hex.convex (base_convex C u))]
    exact closure_minimal (convexHull_min hext (convex_singleton _)) isClosed_singleton
  rw [← hT]
  exact Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr
    (hT.symm ▸ (show (a : V) ∈ {x | x ∈ base C u ∧ h x = 1} from
      ⟨pure_mem a, hh.1.2⟩)))

/-- Unbounded positive approximants, all zero at the same moving label, have
pure maximizers in that same whole return ball converging to the fixed test point. -/
private theorem positive_source_maximizers_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p a : pure C u) (ha : (a : V) ∈ exclusion C u p)
    (haSingle : SingleLabel C u a) (h : V →ₗ[ℝ] ℝ)
    (hh : h ∈ FixedZeroObstruction.fullZeroConfirmers C u a)
    (t : ℕ → pure C u) (ht : Tendsto t atTop (𝓝 p))
    (b : ℕ → V →ₗ[ℝ] ℝ) (hpos : ∀ n z, z ∈ C → 0 ≤ b n z)
    (hzero : ∀ n, b n (t n) = 0)
    (hu : TendstoUniformly (fun n (x : exclusion C u p) => b n x)
      (fun x => h x) atTop) :
    ∃ x : ℕ → pure C u,
      (∀ n, (x n : V) ∈ exclusion C u (t n) ∧
        ∀ z ∈ base C u,
          normalizePositive (C := C) (u := u) (b n) z ≤
            normalizePositive (C := C) (u := u) (b n) (x n)) ∧
      Tendsto (fun n => (x n : V)) atTop (𝓝 (a : V)) := by
  classical
  let f (n : ℕ) := normalizePositive (C := C) (u := u) (b n)
  have hn := moving_positive_normalization hc hs hg hB p t ht b hpos hzero
    (fun x => h x) (fun x => by simpa [x.property.1.2] using hh.1.1 x x.property.1.1) hu
  have hf (n : ℕ) : f n ∈ FixedZeroObstruction.zeroEffects C u (t n) := hn.1 n
  choose x hx hm using fun n =>
    FixedZeroObstruction.zero_effect_maximizer hc hs hg hB (t n) (hf n)
  have hlow : Tendsto (fun n => f n a) atTop (𝓝 1) := by
    simpa [hh.1.2] using hn.2.2.1.tendsto_at ⟨a, ha⟩
  have hmaxlim : Tendsto (fun n => f n (x n)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => hm n a (pure_mem a))
      (fun n => by simpa [(pure_mem (x n)).2] using ((hf n).1 (x n) (pure_mem (x n)).1).2)
  refine ⟨x, fun n => ⟨hx n, hm n⟩, ?_⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨⟨z, e⟩, ⟨_, _⟩, ms, hms, hze⟩ :=
    ((base_compact hc hs).prod (effects_compact hs hg)).tendsto_subseq
      (fun n => show ((x (ns n) : V), (f (ns n)).toContinuousLinearMap) ∈
        base C u ×ˢ effects C u from ⟨pure_mem _, (hf _).1⟩)
  change Tendsto (fun n => ((x (ns (ms n)) : V),
    (f (ns (ms n))).toContinuousLinearMap)) atTop (𝓝 (z, e)) at hze
  have hsub := hns.comp hms.tendsto_atTop
  have hxt : Tendsto (fun n => (x (ns (ms n)) : V)) atTop (𝓝 z) :=
    (continuous_fst.tendsto (z, e)).comp hze
  have het : Tendsto (fun n => (f (ns (ms n))).toContinuousLinearMap)
      atTop (𝓝 e) := (continuous_snd.tendsto (z, e)).comp hze
  have hzF : z ∈ exclusion C u p := exclusion_upper_limit hc hs hg
    (ht.comp hsub) hxt (fun n => hx _)
  have heval : Continuous (fun w : (V →L[ℝ] ℝ) × V => w.1 w.2) := by fun_prop
  have hev : Tendsto (fun n => f (ns (ms n)) (x (ns (ms n)))) atTop (𝓝 (e z)) :=
    (heval.tendsto (e, z)).comp (het.prodMk_nhds hxt)
  have hez : e z = 1 := tendsto_nhds_unique hev (hmaxlim.comp hsub)
  have hread : e z = h z := tendsto_nhds_unique
    ((heval.tendsto (e, z)).comp (het.prodMk_nhds tendsto_const_nhds))
    ((hn.2.2.1.tendsto_at ⟨z, hzF⟩).comp hsub)
  have hza : z = (a : V) := by
    apply Set.mem_singleton_iff.mp
    rw [← local_one_face hc hs hg hB a haSingle hh]
    exact ⟨hzF.1, hread ▸ hez⟩
  exact ⟨ms, hza ▸ hxt⟩

private theorem source_approximation
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p t : pure C u) (h : V →ₗ[ℝ] ℝ) {ε : ℝ}
    (hε : sourceDistance hc hs hg hB p t h < ε) :
    ∃ b : V →ₗ[ℝ] ℝ, (∀ z ∈ C, 0 ≤ b z) ∧ b t = 0 ∧
      ∀ x ∈ exclusion C u p, |b x - h x| < ε := by
  let : CompactSpace (exclusion C u p) :=
    isCompact_iff_compactSpace.mp ((exclusion_ball_faces hc hs hg hB).1 p).2.1
  have hz : (0 : V →ₗ[ℝ] ℝ) ∈ CommonPositiveExtension.zeroPositive C u t := by
    constructor <;> simp
  obtain ⟨_, ⟨b, hb, rfl⟩, hdist⟩ :=
    (Metric.infDist_lt_iff (Set.Nonempty.image (sourceReadout p) ⟨0, hz⟩)).mp hε
  refine ⟨b, hb.1, hb.2, fun x hx => ?_⟩
  have hle := (sourceReadout p b - sourceReadout p h).norm_coe_le_norm ⟨x, hx⟩
  rw [dist_eq_norm, norm_sub_rev] at hdist
  exact hle.trans_lt hdist

/-- A source-distance limit uses the whole positive cone at one common return
label sequence. No minimizer, bounded lift, or pure input sequence is assumed. -/
private theorem source_distance_test_concentration
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p a : pure C u) (ha : (a : V) ∈ exclusion C u p)
    (haSingle : SingleLabel C u a) (h : V →ₗ[ℝ] ℝ)
    (hh : h ∈ FixedZeroObstruction.fullZeroConfirmers C u a)
    (t : ℕ → pure C u) (ht : Tendsto t atTop (𝓝 p))
    (hd : Tendsto (fun n => sourceDistance hc hs hg hB p (t n) h) atTop (𝓝 0)) :
    ∃ x : ℕ → pure C u, (∀ n, (x n : V) ∈ exclusion C u (t n)) ∧
      Tendsto (fun n => (x n : V)) atTop (𝓝 (a : V)) := by
  classical
  let ε (n : ℕ) := sourceDistance hc hs hg hB p (t n) h + 1 / (n + 1 : ℝ)
  have hε (n : ℕ) : sourceDistance hc hs hg hB p (t n) h < ε n := by
    dsimp [ε]
    have hp : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  choose b hb hz herr using fun n => source_approximation hc hs hg hB p (t n) h (hε n)
  have heps : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using hd.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hu : TendstoUniformly (fun n (x : exclusion C u p) => b n x)
      (fun x => h x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro η hη
    filter_upwards [heps.eventually (gt_mem_nhds hη)] with n hn x
    simpa [Real.dist_eq, abs_sub_comm] using (herr n x x.property).trans hn
  obtain ⟨x, hx, hxt⟩ := positive_source_maximizers_tendsto hc hs hg hB p a ha
    haSingle h hh t ht b hb hz hu
  exact ⟨x, fun n => (hx n).1, hxt⟩

private theorem single_label_mixed_neighborhood
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : pure C u, ‖(r : V) - y‖ < δ →
      ∀ x ∈ exclusion C u r, ‖x - (p : V)‖ < ε := by
  classical
  by_contra h
  push Not at h
  choose r hr x hx hfar using fun n : ℕ =>
    h (1 / (n + 1 : ℝ)) (by positivity)
  have hrt : Tendsto (fun n => (r n : V)) atTop (𝓝 y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hr n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨n, hn⟩ := (single_label_mixed_shrinking hc hs hg hB p hp hy r hrt hε).exists
  exact (hfar n).not_gt (hn (x n) (hx n))

private theorem finite_readouts_vanishing {ι : Type*} [Finite ι]
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (h : ι → V →ₗ[ℝ] ℝ) (hz : ∀ i, h i p = 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : pure C u, ‖(r : V) - y‖ < ε →
      ∀ t ∈ exclusion C u r, ∀ i, h i t ≤ τ := by
  have hall : ∀ᶠ x in 𝓝 (p : V), ∀ i, h i x < τ := by
    apply (eventually_all).mpr
    intro i
    have ht := (h i).continuous_of_finiteDimensional.tendsto (p : V)
    rw [hz i] at ht
    exact ht.eventually (gt_mem_nhds hτ)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hall
  obtain ⟨ε, hε, hnear⟩ := single_label_mixed_neighborhood hc hs hg hB p hp hy hρ
  refine ⟨ε, hε, fun r hr t ht i => ?_⟩
  exact (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hnear r hr t ht) i).le

omit [FiniteDimensional ℝ V] in
private theorem intrinsic_interior_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a : E →ᵃ[ℝ] V) (ha : Function.Injective a) (s : Set E) :
    intrinsicInterior ℝ (a '' s) = a '' intrinsicInterior ℝ s := by
  let T : AffineSubspace ℝ V := (⊤ : AffineSubspace ℝ E).map a
  let e : E ≃ᵃ[ℝ] T := (AffineSubspace.topEquiv ℝ E E).symm.trans
    (AffineEquiv.ofBijective (AffineMap.restrict.bijective ha))
  have he : (fun x => T.subtypeₐᵢ (e x)) = a := rfl
  calc
    intrinsicInterior ℝ (a '' s) = intrinsicInterior ℝ (T.subtypeₐᵢ '' (e '' s)) := by
      rw [Set.image_image]; rfl
    _ = T.subtypeₐᵢ '' intrinsicInterior ℝ (e '' s) := T.subtypeₐᵢ.intrinsicInterior_image _
    _ = T.subtypeₐᵢ '' (e '' intrinsicInterior ℝ s) := by rw [e.intrinsicInterior_image]
    _ = a '' intrinsicInterior ℝ s := by rw [Set.image_image]; rfl

private theorem finite_sphere_tests
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] {z : E} (hz : ‖z‖ < 1) :
    ∃ s : Finset E, (s : Set E) ⊆ Metric.sphere 0 1 ∧
      z ∈ interior (convexHull ℝ (s : Set E)) ∧ affineSpan ℝ (s : Set E) = ⊤ := by
  classical
  obtain ⟨b, hb, hball⟩ := exists_mem_interior_convexHull_affineBasis
    (Metric.isOpen_ball.mem_nhds (by simpa using hz : z ∈ Metric.ball (0 : E) 1))
  have hvertex (i) : b i ∈ convexHull ℝ (Metric.sphere (0 : E) 1) := by
    rw [convexHull_sphere_eq_closedBall _ zero_le_one]
    exact Metric.ball_subset_closedBall (hball (subset_convexHull ℝ _ ⟨i, rfl⟩))
  have hs (i) : ∃ s : Finset E, (s : Set E) ⊆ Metric.sphere 0 1 ∧
      b i ∈ convexHull ℝ (s : Set E) := by
    have hi := hvertex i
    rw [convexHull_eq_union_convexHull_finite_subsets] at hi
    simpa only [Set.mem_iUnion, exists_prop] using hi
  choose s hsphere hmem using hs
  let S := Finset.univ.biUnion s
  have hsub (i) : (s i : Set E) ⊆ S := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  have hhull : convexHull ℝ (Set.range b) ⊆ convexHull ℝ (S : Set E) :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact convexHull_mono (hsub i) (hmem i))
      (convex_convexHull ℝ _)
  have hzS := interior_mono hhull hb
  refine ⟨S, ?_, hzS, ?_⟩
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact hsphere i hi
  · exact affineSpan_eq_top_of_nonempty_interior ⟨z, by
      simpa only [(convex_convexHull ℝ (S : Set E)).convexHull_eq] using hzS⟩

/-- The actual finite source tests and their common uniform vanishing are chosen
before every nearby pure input and every return label. -/
private theorem finite_source_tests
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p)) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : Fin m → pure C u, ∃ h : Fin m → V →ₗ[ℝ] ℝ,
      (∀ i, (a i : V) ∈ exclusion C u p ∧
        h i ∈ FixedZeroObstruction.fullZeroConfirmers C u (a i) ∧
        {x | x ∈ base C u ∧ h i x = 1} = {(a i : V)} ∧ h i p = 0) ∧
      affineSpan ℝ (Set.range (fun i => (a i : V))) = affineSpan ℝ (exclusion C u p) ∧
      y ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range (fun i => (a i : V)))) ∧
      ∀ τ : ℝ, 0 < τ → ∃ ε : ℝ, 0 < ε ∧
        ∀ r : pure C u, ‖(r : V) - y‖ < ε →
          ∀ t : pure C u, (t : V) ∈ exclusion C u r → ∀ i, h i t ≤ τ := by
  classical
  obtain ⟨b⟩ := hB p
  let E := EuclideanSpace ℝ (Fin b.dim)
  let : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  rw [MixedExclusionGeometry.chart_intrinsic p b] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨s, hsphere, hzS, hspan⟩ := finite_sphere_tests (by simpa using hz)
  let ι := {z : E // z ∈ s}
  let m := Fintype.card ι
  let e : Fin m ≃ ι := (Fintype.equivFin ι).symm
  have hsnonempty : s.Nonempty := by
    by_contra hh
    simp only [Finset.not_nonempty_iff_eq_empty.mp hh, Finset.coe_empty,
      convexHull_empty, interior_empty, Set.mem_empty_iff_false] at hzS
  have hm : 0 < m := by
    obtain ⟨w, hw⟩ := hsnonempty
    let : Nonempty ι := ⟨⟨w, hw⟩⟩
    exact Fintype.card_pos
  let a (i : Fin m) : pure C u := ⟨b.param (e i),
    ((chart_boundary hc hs hg hB p b).symm ▸
      (show b.param (e i) ∈ b.param '' Metric.sphere 0 1 from
        ⟨e i, hsphere (e i).property, rfl⟩)).2⟩
  have ha (i) : (a i : V) ∈ exclusion C u p :=
    ((chart_boundary hc hs hg hB p b).symm ▸
      (show b.param (e i) ∈ b.param '' Metric.sphere 0 1 from
        ⟨e i, hsphere (e i).property, rfl⟩)).1
  have hrange : Set.range (fun i => (a i : V)) = b.param '' (s : Set E) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, (e i).property, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨e.symm ⟨w, hw⟩, by simp [a]⟩
  have hcommon (i : Fin m) : ∃ h, h ∈ FixedZeroObstruction.fullZeroConfirmers C u (a i) := by
    obtain ⟨h, hh, heq⟩ := ((exclusion_ball_faces hc hs hg hB).1 (a i)).2.2.2.2.2.2
    exact ⟨h, hh, fun x hx => (heq ▸ hx).2⟩
  choose h hh using hcommon
  have hzero (i : Fin m) : h i p = 0 := hh i |>.2 p
    ((exclusion_symmetric p (a i)).mp (ha i))
  refine ⟨m, hm, a, h, fun i => ⟨ha i, hh i,
    local_one_face hc hs hg hB (a i) (single_label_neighbor hc hs hg hB p (a i) hp (ha i))
      (hh i), hzero i⟩, ?_, ?_, ?_⟩
  · rw [hrange, ← b.whole, ← AffineSubspace.map_span, hspan]
    rw [← AffineSubspace.map_span]
    congr 1
    exact (convex_closedBall (0 : E) 1).interior_nonempty_iff_affineSpan_eq_top.mp
      ⟨0, by simp [interior_closedBall]⟩ |>.symm
  · rw [hrange, ← b.param.image_convexHull,
      intrinsic_interior_image b.param b.injective]
    exact ⟨z, interior_subset_intrinsicInterior hzS, hzy⟩
  · intro τ hτ
    obtain ⟨ε, hε, hnear⟩ := finite_readouts_vanishing hc hs hg hB p hp
      (hzy ▸ (MixedExclusionGeometry.chart_intrinsic p b).symm ▸
        (show b.param z ∈ b.param '' Metric.ball 0 1 from ⟨z, hz, rfl⟩)) h hzero hτ
    exact ⟨ε, hε, fun r hr t ht i => hnear r hr t ht i⟩

omit [FiniteDimensional ℝ V] in
theorem ball_affine_span {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →ᵃ[ℝ] V) :
    (affineSpan ℝ (a '' Metric.closedBall (0 : E) 1)).direction = a.linear.range := by
  have hs : affineSpan ℝ (Metric.closedBall (0 : E) 1) = ⊤ := by
    exact affineSpan_eq_top_of_nonempty_interior ⟨0, by
      rw [(convex_closedBall (0 : E) 1).convexHull_eq]
      exact mem_interior_iff_mem_nhds.mpr
        (Metric.closedBall_mem_nhds (0 : E) zero_lt_one)⟩
  rw [← AffineSubspace.map_span, hs, AffineSubspace.map_direction]
  simp

omit [FiniteDimensional ℝ V] in
private theorem chart_dimension (p : pure C u) (a : ExclusionChart C u p) :
    Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction = a.dim := by
  rw [← a.whole, ball_affine_span,
    LinearMap.finrank_range_of_inj (a.param.linear_injective_iff.mpr a.injective)]
  exact finrank_euclideanSpace_fin

private theorem whole_ball_boundary_contradiction
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (t : ℕ → pure C u) (ht : Tendsto t atTop (𝓝 p))
    {d m : ℕ} (hd : 0 < d)
    (maps : ℕ → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] V)
    (hinj : ∀ n, Function.Injective (maps n))
    (hwhole : ∀ n, maps n '' Metric.closedBall 0 1 = exclusion C u (t n))
    (hcap : d ≤ Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction)
    (a : Fin m → V)
    (hspan : affineSpan ℝ (Set.range a) = affineSpan ℝ (exclusion C u p))
    (xs : Fin m → ℕ → V) (hxs : ∀ i n, xs i n ∈ exclusion C u (t n))
    (hxt : ∀ i, Tendsto (xs i) atTop (𝓝 (a i)))
    {y : V} (hy : y ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range a)))
    (r : ℕ → pure C u) (hr : ∀ n, (r n : V) ∈ exclusion C u (t n))
    (hrt : Tendsto (fun n => (r n : V)) atTop (𝓝 y)) : False := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let c (n : ℕ) := maps n 0
  let L (n : ℕ) := (maps n).linear.toContinuousLinearMap
  have heval (n : ℕ) (x : E) : c n + L n x = maps n x := by
    simpa [c, L, add_comm] using (congrFun (maps n).decomp x).symm
  have hball (n : ℕ) : (ballImage (c n) (L n) : Set V) = exclusion C u (t n) := by
    change (fun x => c n + L n x) '' _ = _
    simp_rw [heval]
    exact hwhole n
  obtain ⟨H, hHK, φ, hφ, hH⟩ :=
    (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact
      (base_compact hc hs)).tendsto_subseq
      (fun n => show (ballImage (c n) (L n) : Set V) ⊆ base C u from
        fun x hx => ((hball n) ▸ hx).1)
  obtain ⟨⟨c0, L0⟩, ψ, hψ, hparam, hImage⟩ :=
    parameter_subsequence (c ∘ φ) (L ∘ φ) H hH
  let ns := φ ∘ ψ
  have hns : StrictMono ns := hφ.comp hψ
  let b : E →ᵃ[ℝ] V :=
    (AffineEquiv.constVAdd ℝ V c0).toAffineMap.comp L0.toLinearMap.toAffineMap
  have hbval (x : E) : b x = c0 + L0 x := rfl
  have hbImage : b '' Metric.closedBall (0 : E) 1 = (H : Set V) := by
    change (fun x => c0 + L0 x) '' _ = _
    exact congrArg (fun S : NonemptyCompacts V => (S : Set V)) hImage
  have hfixed (x : E) : Tendsto (fun n => maps (ns n) x) atTop (𝓝 (b x)) := by
    have hc0 : Tendsto (fun n => c (ns n)) atTop (𝓝 c0) :=
      (continuous_fst.tendsto (c0, L0)).comp hparam
    have hL0 : Tendsto (fun n => L (ns n)) atTop (𝓝 L0) :=
      (continuous_snd.tendsto (c0, L0)).comp hparam
    have happ : Continuous (fun z : (E →L[ℝ] V) × E => z.1 z.2) := by fun_prop
    have hv := (happ.tendsto (L0, x)).comp (hL0.prodMk_nhds tendsto_const_nhds)
    simpa only [Function.comp_def, ns, heval, ← hbval] using hc0.add hv
  have hHF : (H : Set V) ⊆ exclusion C u p := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hbImage.symm ▸ hx
    exact exclusion_upper_limit hc hs hg (ht.comp hns.tendsto_atTop) (hfixed v)
      (fun n => (hwhole _).symm ▸ Set.mem_image_of_mem _ hv)
  have haH (i : Fin m) : a i ∈ (H : Set V) := by
    have hz (n : ℕ) : Metric.infDist (xs i (φ n)) (ballImage (c (φ n)) (L (φ n))) = 0 :=
      Metric.infDist_zero_of_mem ((hball _).symm ▸ hxs i _)
    have hv := NonemptyCompacts.lipschitz_infDist.continuous.tendsto (a i, H) |>.comp
      ((hxt i |>.comp hφ.tendsto_atTop).prodMk_nhds hH)
    have hzero : Metric.infDist (a i) (H : Set V) = 0 := tendsto_nhds_unique hv (by
      simpa only [Function.comp_def, hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    exact (H.isCompact.isClosed.mem_iff_infDist_zero H.nonempty).mpr hzero
  have hspanH : affineSpan ℝ (H : Set V) = affineSpan ℝ (exclusion C u p) := by
    apply le_antisymm (affineSpan_mono ℝ hHF)
    rw [← hspan]
    exact affineSpan_mono ℝ (Set.range_subset_iff.mpr haH)
  have hdim : Module.finrank ℝ b.linear.range =
      Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction := by
    rw [← ball_affine_span, hbImage, hspanH]
  have hnull := b.linear.finrank_range_add_finrank_ker
  have hE : Module.finrank ℝ E = d := finrank_euclideanSpace_fin
  have hzker : Module.finrank ℝ b.linear.ker = 0 := by omega
  have hb : Function.Injective b := b.linear_injective_iff.mp
    (LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hzker))
  have hHt : Tendsto (fun n => Metric.hausdorffDist
      (maps (ns n) '' Metric.closedBall (0 : E) 1)
      (b '' Metric.closedBall (0 : E) 1)) atTop (𝓝 0) := by
    have h := tendsto_iff_dist_tendsto_zero.mp (hH.comp hψ.tendsto_atTop)
    simpa only [Function.comp_def, ns, NonemptyCompacts.dist_eq,
      hball, hbImage, hwhole] using h
  have hrbd (n : ℕ) : (r (ns n) : V) ∈ intrinsicFrontier ℝ
      (maps (ns n) '' Metric.closedBall (0 : E) 1) := by
    let chart : ExclusionChart C u (t (ns n)) :=
      ⟨d, hd, maps (ns n), hinj _, hwhole _⟩
    rw [intrinsic_image _ (hinj _), intrinsic_ball]
    exact (chart_boundary hc hs hg hB (t (ns n)) chart) ▸ ⟨hr _, (r _).property⟩
  have hybd := (affine_ball_boundary_limit (fun n => maps (ns n)) b
    (fun n => hinj _) hb hHt).2 (fun n => (r (ns n) : V)) y hrbd
      (hrt.comp hns.tendsto_atTop)
  rw [hbImage] at hybd
  have hconv : Convex ℝ (H : Set V) := by
    rw [← hbImage]
    exact (convex_closedBall (0 : E) 1).affine_image b
  have hch : convexHull ℝ (Set.range a) ⊆ (H : Set V) :=
    convexHull_min (Set.range_subset_iff.mpr haH) hconv
  have hsp : affineSpan ℝ (H : Set V) = affineSpan ℝ (convexHull ℝ (Set.range a)) := by
    rw [affineSpan_convexHull, hspan, hspanH]
  have hyint : y ∈ intrinsicInterior ℝ (H : Set V) := by
    unfold intrinsicInterior at hy ⊢
    rw [hsp]
    exact Set.image_mono (interior_mono (Set.preimage_mono hch)) hy
  rw [← intrinsicClosure_sdiff_intrinsicInterior] at hybd
  exact hybd.2 hyint

/-- Finite common source tests for the entire positive cone: every original
return either increases intrinsic affine dimension or has one fixed positive
source error. All tests precede all inputs and share the same return label. -/
theorem finite_common_source_obstruction
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p)) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : Fin m → pure C u, ∃ h : Fin m → V →ₗ[ℝ] ℝ,
      (∀ i, (a i : V) ∈ exclusion C u p ∧
        h i ∈ FixedZeroObstruction.fullZeroConfirmers C u (a i)) ∧
      (∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
        ∀ r : pure C u, ‖(r : V) - y‖ < ε →
          ∀ t : pure C u, (t : V) ∈ exclusion C u r →
            Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction + 1 ≤
                Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction ∨
              ∃ i, δ ≤ sourceDistance hc hs hg hB p t (h i)) ∧
      (∀ τ : ℝ, 0 < τ → ∃ ε : ℝ, 0 < ε ∧
        ∀ r : pure C u, ‖(r : V) - y‖ < ε →
          ∀ t : pure C u, (t : V) ∈ exclusion C u r → ∀ i, h i t ≤ τ) := by
  classical
  let : CompactSpace (exclusion C u p) :=
    isCompact_iff_compactSpace.mp ((exclusion_ball_faces hc hs hg hB).1 p).2.1
  obtain ⟨m, hm, a, h, hfamily, hspan, hytests, hvanish⟩ :=
    finite_source_tests hc hs hg hB p hp hy
  refine ⟨m, hm, a, h, fun i => ⟨(hfamily i).1, (hfamily i).2.1⟩, ?_, hvanish⟩
  let k := Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction
  by_contra hn
  have hbad (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
      ∃ r : pure C u, ‖(r : V) - y‖ < ε ∧
        ∃ t : pure C u, (t : V) ∈ exclusion C u r ∧
          Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction ≤ k ∧
          ∀ i, sourceDistance hc hs hg hB p t (h i) < δ := by
    by_contra hh
    apply hn
    refine ⟨ε, δ, hε, hδ, fun r hr t ht => ?_⟩
    by_contra hnot
    push Not at hnot
    exact hh ⟨r, hr, t, ht, by dsimp [k]; omega, hnot.2⟩
  choose r hr t ht hdim herr using fun n : ℕ =>
    hbad (1 / (n + 1 : ℝ)) (by positivity) (1 / (n + 1 : ℝ)) (by positivity)
  have hrt : Tendsto (fun n => (r n : V)) atTop (𝓝 y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hr n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htt : Tendsto t atTop (𝓝 p) := by
    apply tendsto_subtype_rng.mpr
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [single_label_mixed_shrinking hc hs hg hB p hp hy r hrt hε] with n hn
    simpa only [dist_eq_norm] using hn (t n) (ht n)
  have hdist (i : Fin m) :
      Tendsto (fun n => sourceDistance hc hs hg hB p (t n) (h i)) atTop (𝓝 0) :=
    squeeze_zero (fun n => Metric.infDist_nonneg) (fun n => (herr n i).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmax (i : Fin m) : ∃ x : ℕ → pure C u,
      (∀ n, (x n : V) ∈ exclusion C u (t n)) ∧
      Tendsto (fun n => (x n : V)) atTop (𝓝 (a i : V)) :=
    source_distance_test_concentration hc hs hg hB p (a i) (hfamily i).1
      (single_label_neighbor hc hs hg hB p (a i) hp (hfamily i).1) (h i)
      (hfamily i).2.1 t htt (hdist i)
  choose x hx hxt using hmax
  let charts (n : ℕ) : ExclusionChart C u (t n) := Classical.choice (hB (t n))
  have hcapped (n : ℕ) : (charts n).dim ≤ k := by
    rw [← chart_dimension (t n) (charts n)]
    exact hdim n
  have hfreq : ∃ᶠ n in atTop, ∃ d : Fin (k + 1), (charts n).dim = d.val :=
    Frequently.of_forall (fun n => ⟨⟨(charts n).dim, by have := hcapped n; omega⟩, rfl⟩)
  obtain ⟨d, hfreq⟩ := frequently_exists.mp hfreq
  obtain ⟨φ, hφ, hφd⟩ := extraction_of_frequently_atTop hfreq
  have hmaps (n : ℕ) : ∃ f : EuclideanSpace ℝ (Fin d.val) →ᵃ[ℝ] V,
      Function.Injective f ∧ f '' Metric.closedBall 0 1 = exclusion C u (t (φ n)) := by
    rw [← hφd n]
    exact ⟨(charts (φ n)).param, (charts (φ n)).injective, (charts (φ n)).whole⟩
  choose maps hinj hwhole using hmaps
  have hd : 0 < d.val := by rw [← hφd 0]; exact (charts (φ 0)).dim_pos
  have hdk : d.val ≤ k := by omega
  exact whole_ball_boundary_contradiction hc hs hg hB p (t ∘ φ)
    (htt.comp hφ.tendsto_atTop) hd maps hinj hwhole hdk
    (fun i => (a i : V)) hspan (fun i n => (x i (φ n) : V))
    (fun i n => hx i (φ n)) (fun i => (hxt i).comp hφ.tendsto_atTop) hytests
    (r ∘ φ) (fun n => (exclusion_symmetric (r (φ n)) (t (φ n))).mp (ht (φ n)))
    (hrt.comp hφ.tendsto_atTop)

end D5.S3.Quantum.Foundation.CommonSourceLiftObstruction
