/- GID: D5/S3/Geometry/Riemannian/ChartComparison
   generality: G
   mirror-B: D5/B/S3/Geometry/Riemannian/ChartComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Geometry.Manifold.Riemannian.Basic]
   utility: none
   digest: Finite intrinsic metric and uniform fixed-basepoint pairwise chart comparison. -/

import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped Bundle Topology ContDiff ENNReal NNReal

noncomputable section

namespace Original172

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [ConnectedSpace M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]

private theorem finite_of_connected {X : Type*} [PseudoEMetricSpace X]
    [PreconnectedSpace X] (x y : X) : edist x y < ⊤ := by
  have hc : IsClopen (Metric.eball x ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hu := hc.eq_univ ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hu]; trivial
  simpa only [Metric.mem_eball, edist_comm] using hy

/- The finite intrinsic metric, obtained from the original topology and original g. -/
@[instance_reducible] def canonicalMetric : MetricSpace M := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  exact EMetricSpace.toMetricSpace (fun x y => (finite_of_connected x y).ne)

theorem canonicalMetric_edist (x y : M) :
    letI : MetricSpace M := canonicalMetric (E := E) (M := M)
    edist x y = riemannianEDist 𝓘(ℝ, E) x y := by
  rfl

local notation "𝕀" => 𝓘(ℝ, E)
local notation "IE" => 𝓘(ℝ, E)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem model_tangent_symm (u w : E) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) u).symm w = w := by
  rfl

private theorem real_tangent_apply (t v : ℝ) :
    NormedSpace.fromTangentSpace (𝕜 := ℝ) t v = v := by
  rfl

private def S (p q : M) : E →L[ℝ] TangentSpace 𝕀 q :=
  (trivializationAt E (TangentSpace 𝕀) p).symmL ℝ q

private def D (p q : M) : TangentSpace 𝕀 q →L[ℝ] E :=
  (trivializationAt E (TangentSpace 𝕀) p).continuousLinearMapAt ℝ q

private theorem DS (p : M) (w : E) : D (E := E) p p (S (E := E) p p w) = w := by
  have hp := FiberBundle.mem_baseSet_trivializationAt' (F := E)
    (E := TangentSpace 𝕀) p
  change ((trivializationAt E (TangentSpace 𝕀) p).continuousLinearMapAt ℝ p)
    (((trivializationAt E (TangentSpace 𝕀) p).symmL ℝ p) w) = w
  simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
    mem_baseSet_trivializationAt]
  convert! (((trivializationAt E (TangentSpace 𝕀) p).continuousLinearEquivAt ℝ p hp).apply_symm_apply w)
  simp [Trivialization.coe_continuousLinearEquivAt_eq _ hp]

/- Relative transport estimates in the original Riemannian fiber norms. -/
set_option backward.isDefEq.respectTransparency false in
private theorem relative_transport (p : M) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ q in 𝓝 p,
      (∀ v : TangentSpace 𝕀 q, ‖S (E := E) p p (D (E := E) p q v)‖ ≤ (1 - ε)⁻¹ * ‖v‖) ∧
      (∀ w : E, ‖S (E := E) p q w‖ ≤ (1 + ε) * ‖S (E := E) p p w‖) := by
  have ha : 0 < 1 - ε := sub_pos.mpr hε1
  have hr : 1 < (1 - ε)⁻¹ := (one_lt_inv₀ ha).mpr (by linarith)
  filter_upwards
    [eventually_norm_symmL_trivializationAt_self_comp_lt E (TangentSpace 𝕀) p hr,
     eventually_norm_symmL_trivializationAt_comp_self_lt E (TangentSpace 𝕀) p
       (show 1 < 1 + ε by linarith)] with q hL hU
  constructor
  · intro v
    exact (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right hL.le (norm_nonneg v))
  · intro w
    have hb := (ContinuousLinearMap.le_opNorm
      ((trivializationAt E (TangentSpace 𝕀) p).symmL ℝ q ∘L
        (trivializationAt E (TangentSpace 𝕀) p).continuousLinearMapAt ℝ p)
      (S (E := E) p p w)).trans
        (mul_le_mul_of_nonneg_right hU.le (norm_nonneg (S (E := E) p p w)))
    change ‖S (E := E) p q (D (E := E) p p (S (E := E) p p w))‖ ≤ (1 + ε) * ‖S (E := E) p p w‖ at hb
    simpa only [DS] using hb

set_option backward.isDefEq.respectTransparency false in
private theorem relative_chart (p : M) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ q in 𝓝 p, q ∈ (extChartAt 𝕀 p).source ∧
      (∀ v : TangentSpace 𝕀 q,
        ‖S (E := E) p p (mfderiv 𝕀 IE (extChartAt 𝕀 p) q v)‖ ≤ (1 - ε)⁻¹ * ‖v‖) ∧
      (∀ w : E,
        ‖mfderivWithin IE 𝕀 (extChartAt 𝕀 p).symm (range 𝕀)
          (extChartAt 𝕀 p q) w‖ ≤ (1 + ε) * ‖S (E := E) p p w‖) := by
  filter_upwards [relative_transport (E := E) p ε hε hε1,
    extChartAt_source_mem_nhds (I := 𝕀) p] with q hq hsource
  have hc : q ∈ (chartAt E p).source := by simpa using hsource
  refine ⟨hsource, ?_, ?_⟩
  · intro v
    have h := hq.1 v
    dsimp [D] at h
    rwa [TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝕀) hc] at h
  · intro w
    have h := hq.2 w
    dsimp [S] at h
    rw [TangentBundle.symmL_trivializationAt (I := 𝕀) hc] at h
    have hi : (extChartAt 𝕀 p).symm (extChartAt 𝕀 p q) = q :=
      (extChartAt 𝕀 p).left_inv hsource
    convert! h using 2 <;> congr

set_option backward.isDefEq.respectTransparency false in
private theorem base_norm (p : M) (w : E) :
    ‖S (E := E) p p w‖ =
      ‖mfderiv IE 𝕀 (extChartAt 𝕀 p).symm (extChartAt 𝕀 p p) w‖ := by
  have hi : (extChartAt 𝕀 p).symm (extChartAt 𝕀 p p) = p :=
    (extChartAt 𝕀 p).left_inv (mem_extChartAt_source p)
  have hn (v : E) :
      ‖(show TangentSpace 𝕀 p from v)‖ =
        ‖(show TangentSpace 𝕀 ((extChartAt 𝕀 p).symm (extChartAt 𝕀 p p)) from v)‖ :=
    congrArg (fun q : M => ‖(show TangentSpace 𝕀 q from v)‖) hi.symm
  dsimp [S]
  rw [TangentBundle.symmL_trivializationAt (I := 𝕀) (mem_chart_source E p)]
  simp only [show range (𝕀 : E → E) = univ by ext; simp, mfderivWithin_univ]
  exact hn _

set_option backward.isDefEq.respectTransparency false in
private theorem forward_endpoint (p : M) {V : Set M} {r : ℝ} (hr : 0 ≤ r)
    (hV : V ⊆ (extChartAt 𝕀 p).source)
    (hD : ∀ q ∈ V, ∀ v : TangentSpace 𝕀 q,
      ‖S (E := E) p p (mfderiv 𝕀 IE (extChartAt 𝕀 p) q v)‖ ≤ r * ‖v‖)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝕀 1 γ (Icc 0 1))
    (hγV : Icc 0 1 ⊆ γ ⁻¹' V) :
    ‖S (E := E) p p (extChartAt 𝕀 p (γ 1) - extChartAt 𝕀 p (γ 0))‖ₑ ≤
      ENNReal.ofReal r * pathELength 𝕀 γ 0 1 := by
  let η := extChartAt 𝕀 p ∘ γ
  let F := S (E := E) p p ∘ η
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact contMDiffOn_extChartAt.comp (I' := 𝕀) hγ
      (fun t ht => by simpa using hV (hγV ht))
  have hF : ContDiffOn ℝ 1 F (Icc 0 1) :=
    (S (E := E) p p).contDiff.comp_contDiffOn hη
  calc
    ‖S (E := E) p p (extChartAt 𝕀 p (γ 1) - extChartAt 𝕀 p (γ 0))‖ₑ
      = ‖F 1 - F 0‖ₑ := by simp [F, η, map_sub]
    _ ≤ ∫⁻ t in Icc 0 1, ‖derivWithin F (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hF zero_le_one
    _ ≤ ∫⁻ t in Icc 0 1,
        ENNReal.ofReal r * ‖mfderivWithin 𝓘(ℝ, ℝ) 𝕀 γ (Icc 0 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hu := uniqueDiffOn_Icc zero_lt_one t ht
      have hηD : mfderivWithin 𝓘(ℝ, ℝ) IE η (Icc 0 1) t =
          (mfderiv 𝕀 IE (extChartAt 𝕀 p) (γ t)) ∘L
            mfderivWithin 𝓘(ℝ, ℝ) 𝕀 γ (Icc 0 1) t := by
        apply mfderiv_comp_mfderivWithin
        · exact mdifferentiableAt_extChartAt (by simpa using hV (hγV ht))
        · exact hγ.mdifferentiableOn one_ne_zero t ht
        · rwa [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      have hFD := ((S (E := E) p p).hasFDerivAt.comp_hasFDerivWithinAt t
        (hη.differentiableOn one_ne_zero t ht).hasFDerivWithinAt).fderivWithin hu
      rw [← fderivWithin_derivWithin, hFD]
      simp only [ContinuousLinearMap.comp_apply]
      have hηD1 : fderivWithin ℝ η (Icc 0 1) t 1 =
          mfderiv 𝕀 IE (extChartAt 𝕀 p) (γ t)
            (mfderivWithin 𝓘(ℝ, ℝ) 𝕀 γ (Icc 0 1) t 1) := by
        have hh := congr($hηD 1)
        simpa only [mfderivWithin_eq_fderivWithin, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, model_tangent_symm, real_tangent_apply] using hh
      rw [hηD1]
      simpa only [ENNReal.ofReal_mul hr, ofReal_norm] using
        ENNReal.ofReal_le_ofReal
          (hD (γ t) (hγV ht) (mfderivWithin 𝓘(ℝ, ℝ) 𝕀 γ (Icc 0 1) t 1))
    _ = ENNReal.ofReal r * pathELength 𝕀 γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

set_option backward.isDefEq.respectTransparency false in
private theorem segment_upper (p : M) {V : Set M} {b R : ℝ} (hb : 0 ≤ b)
    (hInv : ∀ q ∈ V, ∀ w : E,
      ‖mfderivWithin IE 𝕀 (extChartAt 𝕀 p).symm (range 𝕀)
        (extChartAt 𝕀 p q) w‖ ≤ b * ‖S (E := E) p p w‖)
    (hR : ball (extChartAt 𝕀 p p) R ⊆
      (extChartAt 𝕀 p).target ∩ (extChartAt 𝕀 p).symm ⁻¹' V)
    {x y : M} (hx : x ∈ (extChartAt 𝕀 p).source)
    (hy : y ∈ (extChartAt 𝕀 p).source)
    (hxR : extChartAt 𝕀 p x ∈ ball (extChartAt 𝕀 p p) R)
    (hyR : extChartAt 𝕀 p y ∈ ball (extChartAt 𝕀 p p) R) :
    riemannianEDist 𝕀 x y ≤
      ENNReal.ofReal (b * ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖) := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) (extChartAt 𝕀 p x) (extChartAt 𝕀 p y)
  let γ := (extChartAt 𝕀 p).symm ∘ η
  have hη : Icc 0 1 ⊆ η ⁻¹' ((extChartAt 𝕀 p).target ∩
      (extChartAt 𝕀 p).symm ⁻¹' V) := by
    rw [← image_subset_iff]
    apply Subset.trans _ hR
    simpa only [η, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap] using
      (convex_ball (extChartAt 𝕀 p p) R).segment_subset hxR hyR
  have η_smooth : ContMDiffOn 𝓘(ℝ, ℝ) IE 1 η (Icc 0 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝕀 1 γ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm p).comp η_smooth (fun t ht => (hη ht).1)
  have hd : riemannianEDist 𝕀 x y ≤ pathELength 𝕀 γ 0 1 := by
    apply riemannianEDist_le_pathELength hγ _ _ zero_le_one
    · change (extChartAt 𝕀 p).symm (η 0) = x
      have h0 : η 0 = extChartAt 𝕀 p x := by simp [η, ContinuousAffineMap.coe_lineMap_eq]
      rw [h0]
      exact (extChartAt 𝕀 p).left_inv hx
    · change (extChartAt 𝕀 p).symm (η 1) = y
      have h1 : η 1 = extChartAt 𝕀 p y := by simp [η, ContinuousAffineMap.coe_lineMap_eq]
      rw [h1]
      exact (extChartAt 𝕀 p).left_inv hy
  apply hd.trans
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  have hconst : ENNReal.ofReal (b * ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖) =
      ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (b * ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖) := by simp
  rw [hconst]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hcomp : mfderivWithin 𝓘(ℝ, ℝ) 𝕀 γ (Icc 0 1) t =
      (mfderivWithin IE 𝕀 (extChartAt 𝕀 p).symm (range 𝕀) (η t)) ∘L
        (mfderivWithin 𝓘(ℝ, ℝ) IE η (Icc 0 1) t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη ht).1
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · intro t ht
      exact extChartAt_target_subset_range p (hη ht).1
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hline : mfderivWithin 𝓘(ℝ, ℝ) IE η (Icc 0 1) t 1 =
      extChartAt 𝕀 p y - extChartAt 𝕀 p x := by
    rw [mfderivWithin_eq_fderivWithin,
      fderivWithin_eq_fderiv (uniqueDiffOn_Icc zero_lt_one t ht)
        (ContinuousAffineMap.differentiableAt _)]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      model_tangent_symm, real_tangent_apply]
    simp [η]
  have hbound := hInv (γ t) (hη ht).2
    (extChartAt 𝕀 p y - extChartAt 𝕀 p x)
  have hchart : extChartAt 𝕀 p (γ t) = η t :=
    (extChartAt 𝕀 p).right_inv (hη ht).1
  rw [hchart] at hbound
  have hcomp1 : mfderivWithin 𝓘(ℝ, ℝ) 𝕀 γ (Icc 0 1) t 1 =
      mfderivWithin IE 𝕀 (extChartAt 𝕀 p).symm (range 𝕀) (η t)
        (mfderivWithin 𝓘(ℝ, ℝ) IE η (Icc 0 1) t 1) := congr($hcomp 1)
  rw [hcomp1, hline]
  simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hbound

set_option backward.isDefEq.respectTransparency false in
private theorem intrinsic_pairwise (p : M) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ (extChartAt 𝕀 p).source ∧
      ∀ x ∈ U, ∀ y ∈ U,
        ENNReal.ofReal ((1 - ε) * ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖) ≤
          riemannianEDist 𝕀 x y ∧
        riemannianEDist 𝕀 x y ≤
          ENNReal.ofReal ((1 + ε) * ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖) := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have ha : 0 < 1 - ε := sub_pos.mpr hε1
  obtain ⟨V, ⟨hVp, hVo⟩, hV⟩ :=
    (nhds_basis_opens' p).mem_iff.1 (relative_chart (E := E) p ε hε hε1)
  have hVs : V ⊆ (extChartAt 𝕀 p).source := fun q hq => (hV hq).1
  have hVD : ∀ q ∈ V, ∀ v : TangentSpace 𝕀 q,
      ‖S (E := E) p p (mfderiv 𝕀 IE (extChartAt 𝕀 p) q v)‖ ≤ (1 - ε)⁻¹ * ‖v‖ :=
    fun q hq => (hV hq).2.1
  have hVI : ∀ q ∈ V, ∀ w : E,
      ‖mfderivWithin IE 𝕀 (extChartAt 𝕀 p).symm (range 𝕀)
        (extChartAt 𝕀 p q) w‖ ≤ (1 + ε) * ‖S (E := E) p p w‖ :=
    fun q hq => (hV hq).2.2
  obtain ⟨c, hc, hcV⟩ := setOfPred_riemannianEDist_lt_subset_nhds 𝕀 hVp
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have htarget : (extChartAt 𝕀 p).target ∈ 𝓝 (extChartAt 𝕀 p p) := by
    simpa using (extChartAt_target_mem_nhdsWithin (I := 𝕀) p)
  obtain ⟨R, hRpos, hR⟩ := Metric.mem_nhds_iff.1
    (inter_mem htarget ((continuousAt_extChartAt_symm p).preimage_mem_nhds (by simpa using hVp)))
  have hball : ∀ᶠ q in 𝓝 p, extChartAt 𝕀 p q ∈ ball (extChartAt 𝕀 p p) R :=
    (continuousAt_extChartAt p).preimage_mem_nhds (ball_mem_nhds _ hRpos)
  have hnear : ∀ᶠ q in 𝓝 p,
      riemannianEDist 𝕀 p q < ENNReal.ofReal ((c : ℝ) / 4) :=
    eventually_riemannianEDist_lt 𝕀 p (by positivity)
  have hNcont : ContinuousAt
      (fun q : M => ‖S (E := E) p p (extChartAt 𝕀 p q - extChartAt 𝕀 p p)‖) p :=
    ((S (E := E) p p).continuous.continuousAt.comp
      ((continuousAt_extChartAt p).sub continuousAt_const)).norm
  have hsmall : ∀ᶠ q in 𝓝 p,
      ‖S (E := E) p p (extChartAt 𝕀 p q - extChartAt 𝕀 p p)‖ <
        (c : ℝ) / (4 * (1 - ε)) := by
    exact hNcont.eventually (Iio_mem_nhds (by
      simpa using (show 0 < (c : ℝ) / (4 * (1 - ε)) by positivity)))
  obtain ⟨U, ⟨hUp, hUo⟩, hU⟩ := (nhds_basis_opens' p).mem_iff.1
    (inter_mem hVp (hball.and (hnear.and hsmall)))
  refine ⟨U, hUo, mem_of_mem_nhds hUp,
    (fun q hq => hVs (hU hq).1), ?_⟩
  intro x hx y hy
  have hxV := (hU hx).1
  have hyV := (hU hy).1
  have hxR := (hU hx).2.1
  have hyR := (hU hy).2.1
  have hxnear := (hU hx).2.2.1
  have hxsmall := (hU hx).2.2.2
  have hysmall := (hU hy).2.2.2
  constructor
  · by_contra hnot
    have hxy : riemannianEDist 𝕀 x y <
        ENNReal.ofReal ((1 - ε) * ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖) :=
      lt_of_not_ge hnot
    obtain ⟨γ, hγx, hγy, hγsmooth, hγlength, _⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt hxy zero_lt_one
    have hchord : ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖ ≤
        ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p p)‖ +
          ‖S (E := E) p p (extChartAt 𝕀 p x - extChartAt 𝕀 p p)‖ := by
      calc
        _ = ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p p) -
            S (E := E) p p (extChartAt 𝕀 p x - extChartAt 𝕀 p p)‖ := by
          congr 1
          simp only [map_sub]
          abel
        _ ≤ _ := norm_sub_le _ _
    have hB : (1 - ε) * ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖ <
        (c : ℝ) / 2 := by
      have hdiv : (1 - ε) * ((c : ℝ) / (4 * (1 - ε))) = (c : ℝ) / 4 := by
        field_simp [ne_of_gt ha]
        <;> ring
      have hprod := mul_lt_mul_of_pos_left (add_lt_add hysmall hxsmall) ha
      have hmul := mul_le_mul_of_nonneg_left hchord ha.le
      nlinarith only [hprod, hmul, hdiv]
    have hshort : pathELength 𝕀 γ 0 1 < ENNReal.ofReal ((c : ℝ) / 2) :=
      hγlength.trans_le (ENNReal.ofReal_le_ofReal hB.le)
    have hγV : Icc 0 1 ⊆ γ ⁻¹' V := by
      intro t ht
      apply hcV
      have hend : riemannianEDist 𝕀 x (γ t) ≤ pathELength 𝕀 γ 0 t := by
        apply riemannianEDist_le_pathELength _ hγx rfl ht.1
        exact hγsmooth.contMDiffOn.mono (Icc_subset_Icc le_rfl ht.2)
      have hpart : pathELength 𝕀 γ 0 t ≤ pathELength 𝕀 γ 0 1 := by
        gcongr <;> linarith [ht.1, ht.2]
      have hlt : riemannianEDist 𝕀 p (γ t) < ENNReal.ofReal ((c : ℝ) / 4) +
          ENNReal.ofReal ((c : ℝ) / 2) := by
        calc
          _ ≤ riemannianEDist 𝕀 p x + riemannianEDist 𝕀 x (γ t) :=
            riemannianEDist_triangle (I := 𝕀)
          _ ≤ riemannianEDist 𝕀 p x + pathELength 𝕀 γ 0 1 :=
            add_le_add le_rfl (hend.trans hpart)
          _ < _ := ENNReal.add_lt_add hxnear hshort
      have hadd : ENNReal.ofReal ((c : ℝ) / 4) + ENNReal.ofReal ((c : ℝ) / 2) < c := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        simpa only [ENNReal.ofReal_coe_nnreal] using
          (ENNReal.ofReal_lt_ofReal_iff hcR).2
            (show (c : ℝ) / 4 + (c : ℝ) / 2 < c by linarith)
      exact hlt.trans hadd
    have hlen := forward_endpoint (E := E) p (inv_nonneg.mpr ha.le) hVs hVD
      hγsmooth.contMDiffOn hγV
    rw [hγx, hγy] at hlen
    have hbad : ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖ₑ <
        ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖ₑ := by
      calc
        _ ≤ ENNReal.ofReal ((1 - ε)⁻¹) * pathELength 𝕀 γ 0 1 := hlen
        _ < ENNReal.ofReal ((1 - ε)⁻¹) *
            ENNReal.ofReal ((1 - ε) *
              ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖) := by
          gcongr
          all_goals first
            | exact ENNReal.ofReal_ne_top
            | exact ENNReal.ofReal_pos.mpr (inv_pos.mpr ha)
            | exact hγlength
        _ = _ := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
          have heq : (1 - ε)⁻¹ * ((1 - ε) *
              ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖) =
              ‖S (E := E) p p (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖ := by
            field_simp [ne_of_gt ha]
          rw [heq, ofReal_norm]
    exact (lt_irrefl _ hbad)
  · exact segment_upper (E := E) p (by linarith) hVI hR (hVs hxV) (hVs hyV) hxR hyR

/- Exact C1, with dist taken in the metric constructed from the original g. -/
theorem canonical_pairwise_local_comparison (p : M) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    letI : MetricSpace M := canonicalMetric (E := E) (M := M)
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ (extChartAt 𝕀 p).source ∧
      ∀ x ∈ U, ∀ y ∈ U,
        (1 - ε) *
          ‖mfderiv IE 𝕀 (extChartAt 𝕀 p).symm (extChartAt 𝕀 p p)
            (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖ ≤ dist x y ∧
        dist x y ≤ (1 + ε) *
          ‖mfderiv IE 𝕀 (extChartAt 𝕀 p).symm (extChartAt 𝕀 p p)
            (extChartAt 𝕀 p y - extChartAt 𝕀 p x)‖ := by
  obtain ⟨U, hUo, hpU, hUs, hpair⟩ := intrinsic_pairwise (E := E) p ε hε hε1
  letI : MetricSpace M := canonicalMetric (E := E) (M := M)
  refine ⟨U, hUo, hpU, hUs, ?_⟩
  intro x hx y hy
  obtain ⟨hL, hR⟩ := hpair x hx y hy
  rw [← canonicalMetric_edist (E := E) x y, edist_dist] at hL hR
  simp only [← base_norm (E := E) p]
  constructor
  · exact (ENNReal.ofReal_le_ofReal_iff (dist_nonneg)).mp hL
  · exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hR

end Original172
