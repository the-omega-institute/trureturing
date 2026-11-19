/- GID: D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/CommonOldExclusionConfirmation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: One original confirmer controls every mixed input of a fixed old exclusion ball. -/

import D5.S3.Quantum.Foundation.ReciprocalExclusionLimits
import D5.S3.Quantum.Foundation.OriginalWidthContact

/-! Common-effect extrema on entire old exclusion balls. -/
noncomputable section
open Set Filter Topology TopologicalSpace

namespace D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ContinuousFrameSum ExclusionWidthCompactness ReciprocalExclusionLimits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Maximum of the actual dual norms over the entire original effect interval. -/
def effectNormBound (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : ℝ :=
  sSup (norm '' effects C u)

/-- The maximum uses one effect on the entire specified set. -/
def wholeMaximum (G : Set V) (e : V →L[ℝ] ℝ) : ℝ := sSup (e '' G)

/-- The order is minimum over complete confirmers, then maximum over all G. -/
def kappa (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (G : Set V) (a : V) : ℝ :=
  sInf (wholeMaximum G '' confirmingEffects C u a)

private theorem unit_effect (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) :
    u.toContinuousLinearMap ∈ effects C u := by
  intro x hx
  refine ⟨?_, le_rfl⟩
  by_cases hz : x = 0
  · simp [hz]
  · exact (hs x hx hz).le

private theorem confirmers_compact
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : V) :
    IsCompact (confirmingEffects C u a) :=
  (effects_compact hs hg).inter_right (isClosed_eq (by fun_prop) continuous_const)

private theorem confirmers_nonempty
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (a : pure C u) :
    (confirmingEffects C u a).Nonempty := ⟨u.toContinuousLinearMap, unit_effect hs, (pure_mem a).2⟩

private theorem effect_norm_max
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    0 ≤ effectNormBound C u ∧
    (∃ e ∈ effects C u, ‖e‖ = effectNormBound C u) ∧
    ∀ e ∈ effects C u, ‖e‖ ≤ effectNormBound C u := by
  obtain ⟨e, he, hm, hle⟩ := (effects_compact hs hg).exists_sSup_image_eq_and_ge
    ⟨u.toContinuousLinearMap, unit_effect hs⟩ continuous_norm.continuousOn
  refine ⟨?_, ⟨e, he, hm.symm⟩, fun f hf => (hle f hf).trans_eq hm.symm⟩
  change 0 ≤ sSup (norm '' effects C u)
  rw [hm]
  exact norm_nonneg e

private theorem comparison_le {a x : V} (hx : x ∈ base C u)
    {e : V →L[ℝ] ℝ} (he : e ∈ confirmingEffects C u a) :
    comparison C u a x ≤ e x := by
  change sInf {r | ∃ f : V →ₗ[ℝ] ℝ, confirms C u a f ∧ f x = r} ≤ e x
  exact csInf_le ⟨0, by rintro r ⟨f,hf,rfl⟩; exact (hf.1 x hx.1).1⟩
    ⟨e.toLinearMap, ⟨he.1,he.2⟩, rfl⟩

private theorem comparison_nonneg
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : pure C u)
    {x : V} (hx : x ∈ base C u) : 0 ≤ comparison C u a x := by
  obtain ⟨e,he,ht⟩ := comparison_attained hs hg a x
  rw [ht]
  exact (he.1 x hx.1).1

theorem comparison_lipschitz
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : pure C u) :
    LipschitzWith ⟨effectNormBound C u, (effect_norm_max hs hg).1⟩
      (fun x : base C u => comparison C u a x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨e,he,hte⟩ := comparison_attained hs hg a y
  obtain ⟨f,hf,htf⟩ := comparison_attained hs hg a x
  have hM := (effect_norm_max hs hg).2.2
  have hxy : comparison C u a x - comparison C u a y ≤ effectNormBound C u * ‖(x:V)-y‖ := by
    calc
      _ ≤ e x - e y := by rw [hte]; exact sub_le_sub_right (comparison_le x.property he) _
      _ = e ((x:V)-y) := (map_sub e (x:V) (y:V)).symm
      _ ≤ ‖e‖ * ‖(x:V)-y‖ := (le_abs_self _).trans (e.le_opNorm _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hM e he.1) (norm_nonneg _)
  have hyx : comparison C u a y - comparison C u a x ≤ effectNormBound C u * ‖(x:V)-y‖ := by
    calc
      _ ≤ f y - f x := by rw [htf]; exact sub_le_sub_right (comparison_le y.property hf) _
      _ = f ((y:V)-x) := (map_sub f (y:V) (x:V)).symm
      _ ≤ ‖f‖ * ‖(y:V)-x‖ := (le_abs_self _).trans (f.le_opNorm _)
      _ ≤ effectNormBound C u * ‖(y:V)-x‖ :=
        mul_le_mul_of_nonneg_right (hM f hf.1) (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev]
  rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, abs_le]
  change -(effectNormBound C u * ‖(x:V)-(y:V)‖) ≤
    comparison C u a x - comparison C u a y ∧
    comparison C u a x - comparison C u a y ≤ effectNormBound C u * ‖(x:V)-(y:V)‖
  exact ⟨by linarith, hxy⟩

private theorem kappa_attained
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : pure C u)
    {G : Set V} (hG : IsCompact G) (hne : G.Nonempty) :
    ∃ e ∈ confirmingEffects C u a, ∃ x ∈ G,
      kappa C u G a = e x ∧
      wholeMaximum G e = e x ∧
      (∀ y ∈ G, e y ≤ e x) ∧
      ∀ f ∈ confirmingEffects C u a, kappa C u G a ≤ wholeMaximum G f := by
  have hcont : Continuous (wholeMaximum G) :=
    hG.continuous_sSup (show Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) by fun_prop)
  obtain ⟨e,he,hmin,hle⟩ := (confirmers_compact hs hg a).exists_sInf_image_eq_and_le
    (confirmers_nonempty hs a) hcont.continuousOn
  obtain ⟨x,hx,hmax,htop⟩ := hG.exists_sSup_image_eq_and_ge hne e.continuous.continuousOn
  exact ⟨e,he,x,hx,hmin.trans hmax,hmax,htop,fun f hf => hmin.trans_le (hle f hf)⟩

private theorem symmetric_center_mem {G : Set V} {c : V}
    (hne : G.Nonempty) (hconv : Convex ℝ G)
    (hsym : ∀ x ∈ G, (2:ℝ) • c - x ∈ G) : c ∈ G := by
  obtain ⟨x,hx⟩ := hne
  have hm := hconv.midpoint_mem hx (hsym x hx)
  convert hm using 1 <;> simp [midpoint_eq_smul_add] <;> module

private theorem effect_le_two_center {G : Set V} {c : V}
    (hsub : G ⊆ base C u) (hsym : ∀ x ∈ G, (2:ℝ) • c - x ∈ G)
    {e : V →L[ℝ] ℝ} (he : e ∈ effects C u) {x : V} (hx : x ∈ G) :
    e x ≤ 2 * e c := by
  have hz := (he _ (hsub (hsym x hx)).1).1
  change 0 ≤ e ((2:ℝ) • c - x) at hz
  simp only [map_sub, map_smul, smul_eq_mul] at hz
  linarith

private theorem kappa_sandwich
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : pure C u)
    {G : Set V} {c : V} (hG : IsCompact G) (hne : G.Nonempty)
    (hconv : Convex ℝ G) (hsub : G ⊆ base C u)
    (hsym : ∀ x ∈ G, (2:ℝ) • c - x ∈ G) :
    comparison C u a c ≤ kappa C u G a ∧
      kappa C u G a ≤ 2 * comparison C u a c := by
  have hc := symmetric_center_mem hne hconv hsym
  obtain ⟨e,he,x,hx,hk,_,htop,_⟩ := kappa_attained hs hg a hG hne
  constructor
  · exact (comparison_le (hsub hc) he).trans ((htop c hc).trans_eq hk.symm)
  · obtain ⟨f,hf,hfc⟩ := comparison_attained hs hg a c
    obtain ⟨_,_,_,_,_,_,_,hmin⟩ := kappa_attained hs hg a hG hne
    apply (hmin f hf).trans
    apply csSup_le (hne.image f)
    rintro _ ⟨y,hy,rfl⟩
    rw [hfc]
    exact effect_le_two_center hsub hsym hf.1 hy

theorem minimizer_has_zero
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (a : pure C u) {x : V} (hx : x ∈ base C u)
    {e : V →L[ℝ] ℝ} (he : e ∈ confirmingEffects C u a)
    (ht : comparison C u a x = e x) (hlt : e x < 1) :
    ∃ z ∈ base C u, e z = 0 := by
  have hK := base_compact hc hs
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn ⟨a,pure_mem a⟩ e.continuous.continuousOn
  have hm0 : 0 ≤ e z := (he.1 z hz.1).1
  have hm1 : e z < 1 := (hmin hx).trans_lt hlt
  have hez : e z = 0 := by
    by_contra hne
    have hmpos : 0 < e z := lt_of_le_of_ne hm0 (Ne.symm hne)
    let g : V →ₗ[ℝ] ℝ := (1 - e z)⁻¹ • (e.toLinearMap - e z • u)
    have hg : proper C u g := by
      have hp := OriginalWidthContact.normalized_effect hK hs
        (h := e.toLinearMap) hmin
        (fun y hy => by simpa [he.2,hy.2] using (he.1 y hy.1).2)
        (show 0 < e a - e z by rw [he.2]; linarith)
      change proper C u ((e a-e z)⁻¹ • (e.toLinearMap-e z • u)) at hp
      rw [he.2] at hp
      exact hp
    have hga : g a = 1 := by
      change (1-e z)⁻¹ * (e a - e z * u a) = 1
      rw [he.2,(pure_mem a).2,mul_one]
      exact inv_mul_cancel₀ (by linarith)
    have hle := comparison_le hx
      (show g.toContinuousLinearMap ∈ confirmingEffects C u a from ⟨hg,hga⟩)
    rw [ht] at hle
    change e x ≤ (1-e z)⁻¹ * (e x - e z * u x) at hle
    rw [hx.2,mul_one,← div_eq_inv_mul] at hle
    have hbad := (le_div_iff₀ (show 0 < 1-e z by linarith)).mp hle
    nlinarith
  exact ⟨z,hz,hez⟩

private theorem kappa_le_hausdorff
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (a : pure C u) {G : Set V} (hG : IsCompact G) (hne : G.Nonempty) :
    kappa C u G a ≤ effectNormBound C u * Metric.hausdorffDist (exclusion C u a) G := by
  have ha := (exclusion_ball_faces hc hs hg hB).1 a
  obtain ⟨h,hh,hzero⟩ := ha.2.2.2.2.2.2
  let e := h.toContinuousLinearMap
  have he : e ∈ confirmingEffects C u a := ⟨hh.1,hh.2⟩
  obtain ⟨_,_,_,_,_,_,_,hmin⟩ := kappa_attained hs hg a hG hne
  apply (hmin e he).trans
  apply csSup_le (hne.image e)
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨y,hy,hxy⟩ := ha.2.1.exists_infDist_eq_dist ha.1.nonempty x
  have hey : e y = 0 := (hzero ▸ hy).2
  have hdist : dist x y ≤ Metric.hausdorffDist (exclusion C u a) G := by
    rw [← hxy]
    rw [Metric.hausdorffDist_comm]
    exact Metric.infDist_le_hausdorffDist_of_mem hx
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hne ha.1.nonempty hG.isBounded ha.2.1.isBounded)
  calc
    e x = e (x-y) := by rw [map_sub,hey,sub_zero]
    _ ≤ ‖e‖ * ‖x-y‖ := (le_abs_self _).trans (e.le_opNorm _)
    _ ≤ effectNormBound C u * ‖x-y‖ :=
      mul_le_mul_of_nonneg_right ((effect_norm_max hs hg).2.2 e he.1) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hdist)
      (effect_norm_max hs hg).1

/-- A chosen chart of the entire three-ball; no continuity of this choice is asserted. -/
def oldChart (h3 : threeBallExclusions C u) (p : pure C u) :
    EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] V := (h3 p).choose

/-- The old complete ball's affine center. -/
def oldCenter (h3 : threeBallExclusions C u) (p : pure C u) : V := oldChart h3 p 0

private theorem three_implies_balls (h3 : threeBallExclusions C u) : exclusionBalls C u := by
  intro p
  exact ⟨⟨3, by norm_num, oldChart h3 p, (h3 p).choose_spec.1, (h3 p).choose_spec.2⟩⟩

private theorem old_geometry
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (p : pure C u) :
    oldCenter h3 p ∈ exclusion C u p ∧
    (∀ x ∈ exclusion C u p, (2:ℝ) • oldCenter h3 p - x ∈ exclusion C u p) ∧
    ∀ q : pure C u, (q:V) ∈ exclusion C u p →
      ∃ r : pure C u, (r:V) ∈ exclusion C u p ∧
        (q:V) + r = (2:ℝ) • oldCenter h3 p := by
  let f := oldChart h3 p
  have hfi : Function.Injective f := (h3 p).choose_spec.1
  have hfw : f '' Metric.closedBall 0 1 = exclusion C u p := (h3 p).choose_spec.2
  have hreflect (x : EuclideanSpace ℝ (Fin 3)) :
      f (-x) = (2:ℝ) • f 0 - f x := by
    have h1 := congrFun f.decomp x
    have h2 := congrFun f.decomp (-x)
    simp only [Pi.add_apply, map_neg] at h1 h2
    rw [h1,h2]
    module
  refine ⟨hfw ▸ ⟨0,by simp,rfl⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := hfw.symm ▸ hx
    rw [show (2:ℝ) • oldCenter h3 p - f v = f (-v) from (hreflect v).symm]
    exact hfw ▸ ⟨-v,by simpa using hv,rfl⟩
  · intro q hq
    let b : ExclusionChart C u p := ⟨3,by norm_num,f,hfi,hfw⟩
    have hbd := OriginalFacePolarity.chart_boundary hc hs hg (three_implies_balls h3) p b
    obtain ⟨v,hv,hvq⟩ := hbd ▸ (show (q:V) ∈ exclusion C u p ∩ pure C u from ⟨hq,q.property⟩)
    have hr : f (-v) ∈ exclusion C u p ∩ pure C u := hbd.symm ▸
      (show f (-v) ∈ b.param '' Metric.sphere 0 1 from ⟨-v, by simpa using hv,rfl⟩)
    refine ⟨⟨f (-v),hr.2⟩,hr.1,?_⟩
    change (q:V) + f (-v) = _
    rw [hreflect, hvq]
    change (q:V) + ((2:ℝ) • f 0 - q) = (2:ℝ) • f 0
    abel

private theorem singleton_common_effect
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    {p q : pure C u} {an : ℕ → pure C u} (ha : Tendsto an atTop (𝓝 p))
    (hq : (q:V) ∈ exclusion C u p) :
    ∀ᶠ n in atTop, ∃ e ∈ confirmingEffects C u (an n),
      wholeMaximum (exclusion C u p) e ≤ effectNormBound C u *
        (‖(an n:V)-p‖ + Metric.hausdorffDist (exclusion C u (an n)) {(q:V)}) ∧
      e (oldCenter h3 p) ≤ effectNormBound C u / 2 *
        (‖(an n:V)-p‖ + Metric.hausdorffDist (exclusion C u (an n)) {(q:V)}) := by
  have hB := three_implies_balls h3
  have hgeom := (exclusion_ball_faces hc hs hg hB).1
  have hold := old_geometry hc hs hg h3 p
  obtain ⟨r,hr,hqr⟩ := hold.2.2 q hq
  have hTrp : comparison C u r p = 0 := by
    rw [hPR]
    exact (comparison_zero_iff hs hg p (pure_mem r)).mpr hr
  obtain ⟨f,hf,hfp⟩ := comparison_attained hs hg r p
  have hfp0 : f p = 0 := hfp.symm.trans hTrp
  have hbound (n : ℕ) : comparison C u (an n) r ≤ effectNormBound C u * ‖(an n:V)-p‖ := by
    rw [hPR]
    calc
      _ ≤ f (an n) := comparison_le (pure_mem (an n)) hf
      _ = f ((an n:V)-p) := by rw [map_sub,hfp0,sub_zero]
      _ ≤ ‖f‖ * ‖(an n:V)-p‖ := (le_abs_self _).trans (f.le_opNorm _)
      _ ≤ _ := mul_le_mul_of_nonneg_right ((effect_norm_max hs hg).2.2 f hf.1) (norm_nonneg _)
  have hnorm : Tendsto (fun n => ‖(an n:V)-p‖) atTop (𝓝 0) := by
    simpa using ((continuous_subtype_val.tendsto p |>.comp ha).sub (tendsto_const_nhds (x := (p:V)))).norm
  have hsmalllim : Tendsto (fun n => effectNormBound C u * ‖(an n:V)-p‖) atTop (𝓝 0) :=
    by simpa using hnorm.const_mul (effectNormBound C u)
  have hsmall : ∀ᶠ n in atTop, effectNormBound C u * ‖(an n:V)-p‖ < 1 :=
    hsmalllim.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hsmall] with n hn
  obtain ⟨e,he,her⟩ := comparison_attained hs hg (an n) r
  obtain ⟨z,hz,hez⟩ := minimizer_has_zero hc hs (an n) (pure_mem r) he her
    (her ▸ (hbound n).trans_lt hn)
  have hzD : z ∈ exclusion C u (an n) := ⟨hz,e.toLinearMap,⟨he.1,he.2⟩,hez⟩
  have hdist : ‖z-(q:V)‖ ≤ Metric.hausdorffDist (exclusion C u (an n)) {(q:V)} := by
    have hd := Metric.infDist_le_hausdorffDist_of_mem hzD
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hgeom (an n)).1.nonempty (singleton_nonempty (q:V)) (hgeom (an n)).2.1.isBounded (isCompact_singleton.isBounded))
    simpa [Metric.infDist_singleton,dist_eq_norm] using hd
  have heq : e q ≤ effectNormBound C u * Metric.hausdorffDist (exclusion C u (an n)) {(q:V)} := by
    calc
      _ = e ((q:V)-z) := by rw [map_sub,hez,sub_zero]
      _ ≤ ‖e‖ * ‖(q:V)-z‖ := (le_abs_self _).trans (e.le_opNorm _)
      _ ≤ effectNormBound C u * ‖(q:V)-z‖ :=
        mul_le_mul_of_nonneg_right ((effect_norm_max hs hg).2.2 e he.1) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [norm_sub_rev] using hdist)
        (effect_norm_max hs hg).1
  have hecenter : 2 * e (oldCenter h3 p) = e q + e r := by
    have hv := congrArg e hqr
    simpa only [map_add,map_smul,smul_eq_mul] using hv.symm
  have htotal : 2 * e (oldCenter h3 p) ≤ effectNormBound C u *
      (‖(an n:V)-p‖ + Metric.hausdorffDist (exclusion C u (an n)) {(q:V)}) := by
    rw [hecenter]
    have her' := hbound n
    rw [her] at her'
    nlinarith
  refine ⟨e,he,?_,by linarith⟩
  apply (csSup_le ((hgeom p).1.nonempty.image e) ?_).trans htotal
  rintro _ ⟨x,hx,rfl⟩
  exact effect_le_two_center (fun x hx => hx.1) hold.2.1 he.1 hx

private theorem kappa_nonneg
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : pure C u)
    {G : Set V} (hG : IsCompact G) (hne : G.Nonempty) (hsub : G ⊆ base C u) :
    0 ≤ kappa C u G a := by
  obtain ⟨e,he,x,hx,hk,_⟩ := kappa_attained hs hg a hG hne
  rw [hk]
  exact (he.1 x (hsub hx).1).1

private theorem kappa_tendsto_zero
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    {p : pure C u} {an : ℕ → pure C u} (ha : Tendsto an atTop (𝓝 p)) :
    Tendsto (fun n => kappa C u (exclusion C u p) (an n)) atTop (𝓝 0) := by
  have hB := three_implies_balls h3
  have hgB := (exclusion_ball_faces hc hs hg hB).1
  let F : ℕ → NonemptyCompacts V := fun n =>
    ⟨⟨exclusion C u (an n),(hgB (an n)).2.1⟩,(hgB (an n)).1.nonempty⟩
  have hnonneg (n : ℕ) : 0 ≤ kappa C u (exclusion C u p) (an n) :=
    kappa_nonneg hs hg (an n) (hgB p).2.1 (hgB p).1.nonempty (fun x hx => hx.1)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨Q,hQ,ms,hms,hlim⟩ :=
    (NonemptyCompacts.isCompact_subsets_of_isCompact (base_compact hc hs)).tendsto_subseq
      (fun n => (show (F (ns n) : Set V) ⊆ base C u from fun x hx => hx.1))
  have halim : Tendsto (fun n => an (ns (ms n))) atTop (𝓝 p) :=
    (ha.comp hns).comp hms.tendsto_atTop
  refine ⟨ms,?_⟩
  rcases exclusion_limit_dichotomy hc hs hg h3 hPR halim
      (fun n => F (ns (ms n))) Q (fun _ => rfl) hlim with heq | ⟨q,hq,heq⟩
  · have hd : Tendsto (fun n => Metric.hausdorffDist
        (exclusion C u (an (ns (ms n)))) (exclusion C u p)) atTop (𝓝 0) := by
      have ht := tendsto_iff_dist_tendsto_zero.mp hlim
      simpa only [NonemptyCompacts.dist_eq,heq,Function.comp_def,F,NonemptyCompacts.coe_mk,Compacts.coe_mk] using ht
    apply squeeze_zero (fun n => hnonneg (ns (ms n)))
      (fun n => kappa_le_hausdorff hc hs hg hB _ (hgB p).2.1 (hgB p).1.nonempty)
    simpa using hd.const_mul (effectNormBound C u)
  · have hd : Tendsto (fun n => Metric.hausdorffDist
        (exclusion C u (an (ns (ms n)))) {(q:V)}) atTop (𝓝 0) := by
      have ht := tendsto_iff_dist_tendsto_zero.mp hlim
      simpa only [NonemptyCompacts.dist_eq,heq,Function.comp_def,F,NonemptyCompacts.coe_mk,Compacts.coe_mk] using ht
    have hn : Tendsto (fun n => ‖(an (ns (ms n)):V)-p‖) atTop (𝓝 0) := by
      simpa using ((continuous_subtype_val.tendsto p |>.comp halim).sub (tendsto_const_nhds (x := (p:V)))).norm
    have hbound := singleton_common_effect hc hs hg h3 hPR halim hq
    apply squeeze_zero' (Eventually.of_forall fun n => hnonneg (ns (ms n)))
      (hbound.mono ?_)
    · simpa using (hn.add hd).const_mul (effectNormBound C u)
    · intro n ⟨e,he,hm,_⟩
      obtain ⟨_,_,_,_,_,_,_,hmin⟩ := kappa_attained hs hg (an (ns (ms n)))
        (hgB p).2.1 (hgB p).1.nonempty
      exact (hmin e he).trans hm

/-- The actual full-zero confirmer family, represented in the unchanged continuous dual. -/
def fullZeroEffects (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : pure C u) :
    Set (V →L[ℝ] ℝ) := {e | e.toLinearMap ∈ FixedZeroObstruction.fullZeroConfirmers C u p}

private theorem full_zero_face
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (p : pure C u) :
    (fullZeroEffects C u p).Nonempty ∧ IsCompact (fullZeroEffects C u p) ∧
    IsExposed ℝ (confirmingEffects C u p) (fullZeroEffects C u p) ∧
    Convex ℝ (fullZeroEffects C u p) ∧
    fullZeroEffects C u p ≠ confirmingEffects C u p ∧
    fullZeroEffects C u p = {e ∈ confirmingEffects C u p | e (oldCenter h3 p) = 0} ∧
    ∀ e ∈ fullZeroEffects C u p, {x ∈ base C u | e x = 0} = exclusion C u p := by
  have hB := three_implies_balls h3
  have hpgeom := (exclusion_ball_faces hc hs hg hB).1 p
  have hold := old_geometry hc hs hg h3 p
  have hcenter := hold.1.1
  have heq : fullZeroEffects C u p =
      {e ∈ confirmingEffects C u p | e (oldCenter h3 p) = 0} := by
    ext e
    constructor
    · intro he
      exact ⟨⟨he.1.1,he.1.2⟩,he.2 _ hold.1⟩
    · rintro ⟨he,hec⟩
      refine ⟨⟨he.1,he.2⟩,?_⟩
      intro x hx
      change e x = 0
      have hnon : 0 ≤ e x := (he.1 x hx.1.1).1
      have hle := effect_le_two_center (fun x hx => hx.1) hold.2.1 he.1 hx
      rw [hec] at hle
      linarith
  obtain ⟨h,hh,hzero⟩ := hpgeom.2.2.2.2.2.2
  have hne : (fullZeroEffects C u p).Nonempty :=
    ⟨h.toContinuousLinearMap,hh,fun x hx => (hzero ▸ hx).2⟩
  have hcompact : IsCompact (fullZeroEffects C u p) := by
    rw [heq]
    exact (confirmers_compact hs hg p).inter_right
      (isClosed_eq (by fun_prop) continuous_const)
  have hconvF : Convex ℝ (confirmingEffects C u p) := by
    intro e he f hf a b ha hb hab
    constructor
    · intro x hx
      change 0 ≤ a * e x + b * f x ∧ a * e x + b * f x ≤ u x
      have he' := he.1 x hx
      have hf' := hf.1 x hx
      change 0 ≤ e x ∧ e x ≤ u x at he'
      change 0 ≤ f x ∧ f x ≤ u x at hf'
      constructor
      · exact add_nonneg (mul_nonneg ha he'.1) (mul_nonneg hb hf'.1)
      · calc
          _ ≤ a * u x + b * u x := add_le_add
            (mul_le_mul_of_nonneg_left he'.2 ha) (mul_le_mul_of_nonneg_left hf'.2 hb)
          _ = u x := by rw [← add_mul,hab,one_mul]
    · change a * e p + b * f p = 1
      rw [he.2,hf.2]
      linarith
  have hexp : IsExposed ℝ (confirmingEffects C u p) (fullZeroEffects C u p) := by
    intro _
    refine ⟨-(ContinuousLinearMap.apply ℝ ℝ (oldCenter h3 p)),?_⟩
    rw [heq]
    ext e
    constructor
    · rintro ⟨he,hec⟩
      refine ⟨he,fun f hf => ?_⟩
      change - f (oldCenter h3 p) ≤ - e (oldCenter h3 p)
      rw [hec]
      have hfnon : 0 ≤ f (oldCenter h3 p) := (hf.1 _ hcenter.1).1
      linarith
    · rintro ⟨he,hmax⟩
      obtain ⟨f,hf⟩ := hne
      have hfc := ((heq ▸ hf) : f ∈ {e ∈ confirmingEffects C u p | e (oldCenter h3 p) = 0})
      have hh := hmax f hfc.1
      change - f (oldCenter h3 p) ≤ - e (oldCenter h3 p) at hh
      rw [hfc.2] at hh
      exact ⟨he,le_antisymm (by linarith) ((he.1 _ hcenter.1).1)⟩
  refine ⟨hne,hcompact,hexp,hexp.convex hconvF,?_,heq,?_⟩
  · intro hfull
    have hunit : u.toContinuousLinearMap ∈ fullZeroEffects C u p := hfull.symm ▸
      (show u.toContinuousLinearMap ∈ confirmingEffects C u p from
        ⟨unit_effect hs,(pure_mem p).2⟩)
    have hunitc := ((heq ▸ hunit) : u.toContinuousLinearMap ∈
      {e ∈ confirmingEffects C u p | e (oldCenter h3 p) = 0}).2
    change u (oldCenter h3 p) = 0 at hunitc
    linarith [hcenter.2]
  · intro e he
    ext x
    constructor
    · rintro ⟨hx,hez⟩
      exact ⟨hx,e.toLinearMap,he.1,hez⟩
    · intro hx
      exact ⟨hx.1,he.2 x hx⟩

/-- Minimum actual dual distance from an entire confirmer fiber to the old full-zero face. -/
def zeroFiberDistance (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : pure C u) (a : V) : ℝ :=
  sInf ((fun e => Metric.infDist e (fullZeroEffects C u p)) '' confirmingEffects C u a)

private theorem distance_attained
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (p a : pure C u) :
    (∃ e ∈ confirmingEffects C u a,
      zeroFiberDistance C u p a = Metric.infDist e (fullZeroEffects C u p)) ∧
    0 ≤ zeroFiberDistance C u p a ∧
    ∀ e ∈ confirmingEffects C u a,
      zeroFiberDistance C u p a ≤ Metric.infDist e (fullZeroEffects C u p) := by
  obtain ⟨e,he,hmin,hle⟩ := (confirmers_compact hs hg a).exists_sInf_image_eq_and_le
    (confirmers_nonempty hs a) (Metric.continuous_infDist_pt (s := fullZeroEffects C u p)).continuousOn
  refine ⟨⟨e,he,hmin⟩,?_,fun f hf => hmin.trans_le (hle f hf)⟩
  change 0 ≤ sInf ((fun e => Metric.infDist e (fullZeroEffects C u p)) '' confirmingEffects C u a)
  rw [hmin]
  exact Metric.infDist_nonneg

private theorem selected_limit_in_face
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    {p : pure C u} {an : ℕ → pure C u} (ha : Tendsto an atTop (𝓝 p))
    {en : ℕ → V →L[ℝ] ℝ} {e : V →L[ℝ] ℝ}
    (hen : ∀ n, en n ∈ confirmingEffects C u (an n))
    (henc : ∀ n, en n (oldCenter h3 p) ≤ kappa C u (exclusion C u p) (an n))
    (helim : Tendsto en atTop (𝓝 e)) : e ∈ fullZeroEffects C u p := by
  have hE : e ∈ effects C u := (effects_compact hs hg).isClosed.mem_of_tendsto helim
    (Eventually.of_forall fun n => (hen n).1)
  have hax := continuous_subtype_val.tendsto p |>.comp ha
  have hev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have hep : e p = 1 := by
    apply tendsto_nhds_unique ((hev.tendsto (e,(p:V))).comp (helim.prodMk_nhds hax))
    have hone : (fun n => en n (an n)) = fun _ : ℕ => (1:ℝ) := funext fun n => (hen n).2
    change Tendsto (fun n => en n (an n)) atTop (𝓝 1)
    rw [hone]
    exact tendsto_const_nhds
  have hcenter := (old_geometry hc hs hg h3 p).1.1
  have heczero : Tendsto (fun n => en n (oldCenter h3 p)) atTop (𝓝 0) :=
    squeeze_zero (fun n => ((hen n).1 _ hcenter.1).1) henc
      (kappa_tendsto_zero hc hs hg h3 hPR ha)
  have hec : e (oldCenter h3 p) = 0 := tendsto_nhds_unique
    ((show Continuous (fun f : V →L[ℝ] ℝ => f (oldCenter h3 p)) by fun_prop).tendsto e |>.comp helim)
    heczero
  exact (full_zero_face hc hs hg h3 p).2.2.2.2.2.1.symm ▸ ⟨⟨hE,hep⟩,hec⟩

private theorem confirmer_limits
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    {p : pure C u} {an : ℕ → pure C u} (ha : Tendsto an atTop (𝓝 p)) :
    (∀ (F : ℕ → NonemptyCompacts (V →L[ℝ] ℝ)) (A : NonemptyCompacts (V →L[ℝ] ℝ)),
      (∀ n, (F n : Set (V →L[ℝ] ℝ)) = confirmingEffects C u (an n)) →
      Tendsto F atTop (𝓝 A) →
      (A : Set (V →L[ℝ] ℝ)) ⊆ confirmingEffects C u p ∧
        ((A : Set (V →L[ℝ] ℝ)) ∩ fullZeroEffects C u p).Nonempty) ∧
    Tendsto (fun n => zeroFiberDistance C u p (an n)) atTop (𝓝 0) := by
  classical
  have hB := three_implies_balls h3
  have hpgeom := (exclusion_ball_faces hc hs hg hB).1 p
  have hcenter := (old_geometry hc hs hg h3 p).1
  choose en hen xn hxn hk hmax htop hmin using fun n =>
    kappa_attained hs hg (an n) hpgeom.2.1 hpgeom.1.nonempty
  have henc (n : ℕ) : en n (oldCenter h3 p) ≤ kappa C u (exclusion C u p) (an n) :=
    (htop n _ hcenter).trans_eq (hk n).symm
  constructor
  · intro F A hF hlim
    constructor
    · intro f hf
      obtain ⟨fn,hfn,hflim⟩ := FixedZeroObstruction.recover_limit F A hlim hf
      have hfn' (n : ℕ) : fn n ∈ confirmingEffects C u (an n) := hF n ▸ hfn n
      have hfe : f ∈ effects C u := (effects_compact hs hg).isClosed.mem_of_tendsto hflim
        (Eventually.of_forall fun n => (hfn' n).1)
      have hev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
      have hfp : f p = 1 := by
        apply tendsto_nhds_unique ((hev.tendsto (f,(p:V))).comp
          (hflim.prodMk_nhds (continuous_subtype_val.tendsto p |>.comp ha)))
        have hone : (fun n => fn n (an n)) = fun _ : ℕ => (1:ℝ) :=
          funext fun n => (hfn' n).2
        change Tendsto (fun n => fn n (an n)) atTop (𝓝 1)
        rw [hone]
        exact tendsto_const_nhds
      exact ⟨hfe,hfp⟩
    · obtain ⟨e,he,φ,hφ,helim⟩ := (effects_compact hs hg).tendsto_subseq (fun n => (hen n).1)
      have heA : e ∈ A := FixedZeroObstruction.mem_compact_limit
        (fun n => F (φ n)) A (hlim.comp hφ.tendsto_atTop)
        (fun n => by change en (φ n) ∈ (F (φ n) : Set (V →L[ℝ] ℝ)); rw [hF]; exact hen (φ n)) helim
      have heold := selected_limit_in_face hc hs hg h3 hPR (ha.comp hφ.tendsto_atTop)
        (fun n => hen (φ n)) (fun n => henc (φ n)) helim
      exact ⟨e,heA,heold⟩
  · apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨e,he,ms,hms,helim⟩ := (effects_compact hs hg).tendsto_subseq (fun n => (hen (ns n)).1)
    have heold := selected_limit_in_face hc hs hg h3 hPR
      ((ha.comp hns).comp hms.tendsto_atTop)
      (fun n => hen (ns (ms n))) (fun n => henc (ns (ms n))) helim
    refine ⟨ms,?_⟩
    have hd : Tendsto (fun n => Metric.infDist (en (ns (ms n))) (fullZeroEffects C u p))
        atTop (𝓝 0) := by
      simpa only [Metric.infDist_zero_of_mem heold,Function.comp_def] using
        ((Metric.continuous_infDist_pt (s := fullZeroEffects C u p)).tendsto e |>.comp helim)
    exact squeeze_zero (fun n => (distance_attained hs hg p (an (ns (ms n)))).2.1)
      (fun n => (distance_attained hs hg p (an (ns (ms n)))).2.2 _ (hen (ns (ms n)))) hd

private theorem old_center_unique (h3 : threeBallExclusions C u) (p : pure C u)
    {c : V} (hsym : ∀ x ∈ exclusion C u p, (2:ℝ) • c-x ∈ exclusion C u p) :
    c = oldCenter h3 p := by
  let f := oldChart h3 p
  let L := f.linear.toContinuousLinearMap
  have hrepr (x : EuclideanSpace ℝ (Fin 3)) : oldCenter h3 p + L x = f x := by
    simpa [f,L,oldCenter,add_comm] using (congrFun f.decomp x).symm
  have hwhole : (fun x => oldCenter h3 p + L x) '' Metric.closedBall 0 1 = exclusion C u p := by
    simp_rw [hrepr]
    exact (h3 p).choose_spec.2
  have heq : (fun x => oldCenter h3 p + L x) '' Metric.closedBall 0 1 =
      (fun x => ((2:ℝ) • c-oldCenter h3 p) + (-L) x) '' Metric.closedBall 0 1 := by
    apply Subset.antisymm
    · rintro x hx
      have hr := hsym x (hwhole ▸ hx)
      obtain ⟨v,hv,he⟩ := hwhole.symm ▸ hr
      refine ⟨v,hv,?_⟩
      simp only [ContinuousLinearMap.neg_apply]
      have ht : oldCenter h3 p + L v = (2:ℝ) • c-x := he
      have hh := congrArg (fun y : V => (2:ℝ) • c-y) ht
      calc
        _ = (2:ℝ) • c-(oldCenter h3 p+L v) := by abel
        _ = (2:ℝ) • c-((2:ℝ) • c-x) := hh
        _ = x := by abel
    · rintro _ ⟨v,hv,rfl⟩
      have hr := hsym (oldCenter h3 p+L v) (hwhole ▸ ⟨v,hv,rfl⟩)
      rw [hwhole]
      convert hr using 1 <;> simp only [ContinuousLinearMap.neg_apply] <;> module
  have hh := D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq
    (oldCenter h3 p) ((2:ℝ) • c-oldCenter h3 p) L (-L) heq
  have : (2:ℝ) • c = (2:ℝ) • oldCenter h3 p := by
    have h := congrArg (fun y : V => y+oldCenter h3 p) hh
    simpa only [sub_add_cancel,← two_smul ℝ] using h.symm
  exact (smul_right_injective V (by norm_num : (2:ℝ) ≠ 0)) this

/-- The complete common-effect and confirmer-fiber conclusions on the original
finite dimensional cone, with only EB3 and pure-endpoint PR. -/
theorem common_old_exclusion_confirmation
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    (0 ≤ effectNormBound C u ∧
      (∃ e ∈ effects C u, ‖e‖ = effectNormBound C u) ∧
      ∀ e ∈ effects C u, ‖e‖ ≤ effectNormBound C u) ∧
    (∀ a : pure C u, LipschitzWith ⟨effectNormBound C u,(effect_norm_max hs hg).1⟩
      (fun x : base C u => comparison C u a x)) ∧
    (∀ (G : Set V) (c : V), IsCompact G → G.Nonempty → Convex ℝ G → G ⊆ base C u →
      (∀ x ∈ G, (2:ℝ) • c-x ∈ G) → ∀ a : pure C u,
      (∃ e ∈ confirmingEffects C u a, ∃ x ∈ G,
        kappa C u G a = e x ∧ wholeMaximum G e = e x ∧
        (∀ y ∈ G, e y ≤ e x) ∧
        ∀ f ∈ confirmingEffects C u a, kappa C u G a ≤ wholeMaximum G f) ∧
      comparison C u a c ≤ kappa C u G a ∧ kappa C u G a ≤ 2*comparison C u a c) ∧
    (∀ p : pure C u,
      (∀ c : V, (∀ x ∈ exclusion C u p, (2:ℝ) • c-x ∈ exclusion C u p) → c = oldCenter h3 p) ∧
      (fullZeroEffects C u p).Nonempty ∧ IsCompact (fullZeroEffects C u p) ∧
      IsExposed ℝ (confirmingEffects C u p) (fullZeroEffects C u p) ∧
      Convex ℝ (fullZeroEffects C u p) ∧
      fullZeroEffects C u p ≠ confirmingEffects C u p ∧
      fullZeroEffects C u p = {e ∈ confirmingEffects C u p | e (oldCenter h3 p) = 0} ∧
      (∀ e ∈ fullZeroEffects C u p, {x ∈ base C u | e x = 0} = exclusion C u p) ∧
      ∀ an : ℕ → pure C u, Tendsto an atTop (𝓝 p) →
        Tendsto (fun n => kappa C u (exclusion C u p) (an n)) atTop (𝓝 0) ∧
        Tendsto (fun n => comparison C u (an n) (oldCenter h3 p)) atTop (𝓝 0) ∧
        Tendsto (fun n => sSup ((comparison C u (an n)) '' exclusion C u p)) atTop (𝓝 0) ∧
        (∀ n, kappa C u (exclusion C u p) (an n) ≤ effectNormBound C u *
          Metric.hausdorffDist (exclusion C u (an n)) (exclusion C u p)) ∧
        (∀ q : V, Tendsto (fun n => Metric.hausdorffDist (exclusion C u (an n)) {q})
            atTop (𝓝 0) → q ∈ pure C u ∩ exclusion C u p ∧
          ∀ᶠ n in atTop, ∃ e ∈ confirmingEffects C u (an n),
            wholeMaximum (exclusion C u p) e ≤ effectNormBound C u *
              (‖(an n:V)-p‖ + Metric.hausdorffDist (exclusion C u (an n)) {q}) ∧
            e (oldCenter h3 p) ≤ effectNormBound C u / 2 *
              (‖(an n:V)-p‖ + Metric.hausdorffDist (exclusion C u (an n)) {q})) ∧
        (∀ (F : ℕ → NonemptyCompacts (V →L[ℝ] ℝ)) (A : NonemptyCompacts (V →L[ℝ] ℝ)),
          (∀ n, (F n : Set (V →L[ℝ] ℝ)) = confirmingEffects C u (an n)) →
          Tendsto F atTop (𝓝 A) →
          (A : Set (V →L[ℝ] ℝ)) ⊆ confirmingEffects C u p ∧
            ((A : Set (V →L[ℝ] ℝ)) ∩ fullZeroEffects C u p).Nonempty) ∧
        (∀ n, ∃ e ∈ confirmingEffects C u (an n),
          zeroFiberDistance C u p (an n) = Metric.infDist e (fullZeroEffects C u p)) ∧
        Tendsto (fun n => zeroFiberDistance C u p (an n)) atTop (𝓝 0)) := by
  classical
  refine ⟨effect_norm_max hs hg,comparison_lipschitz hs hg,?_,?_⟩
  · intro G c hG hne hconv hsub hsym a
    exact ⟨kappa_attained hs hg a hG hne,kappa_sandwich hs hg a hG hne hconv hsub hsym⟩
  · intro p
    have hface := full_zero_face hc hs hg h3 p
    refine ⟨fun c hsym => old_center_unique h3 p hsym,hface.1,hface.2.1,
      hface.2.2.1,hface.2.2.2.1,hface.2.2.2.2.1,hface.2.2.2.2.2.1,hface.2.2.2.2.2.2,?_⟩
    intro an ha
    have hB := three_implies_balls h3
    have hpgeom := (exclusion_ball_faces hc hs hg hB).1 p
    have hold := old_geometry hc hs hg h3 p
    have hk := kappa_tendsto_zero hc hs hg h3 hPR ha
    have hlim := confirmer_limits hc hs hg h3 hPR ha
    refine ⟨hk,?_,?_,fun n => kappa_le_hausdorff hc hs hg hB _ hpgeom.2.1 hpgeom.1.nonempty,
      ?_,hlim.1,fun n => (distance_attained hs hg p (an n)).1,hlim.2⟩
    · apply squeeze_zero (fun n => comparison_nonneg hs hg (an n) hold.1.1)
        (fun n => (kappa_sandwich hs hg (an n) hpgeom.2.1 hpgeom.1.nonempty
          hpgeom.2.2.1 (fun x hx => hx.1) hold.2.1).1) hk
    · have hbound (n : ℕ) : ∀ x ∈ exclusion C u p,
          0 ≤ comparison C u (an n) x ∧ comparison C u (an n) x ≤ kappa C u (exclusion C u p) (an n) := by
        obtain ⟨e,he,y,hy,hky,_,htop,_⟩ := kappa_attained hs hg (an n) hpgeom.2.1 hpgeom.1.nonempty
        intro x hx
        exact ⟨comparison_nonneg hs hg (an n) hx.1,
          (comparison_le hx.1 he).trans ((htop x hx).trans_eq hky.symm)⟩
      apply squeeze_zero ?_ ?_ hk
      · intro n
        obtain ⟨x,hx⟩ := hpgeom.1.nonempty
        exact (hbound n x hx).1.trans (le_csSup
          ⟨kappa C u (exclusion C u p) (an n),by
            rintro _ ⟨y,hy,rfl⟩; exact (hbound n y hy).2⟩
          (mem_image_of_mem _ hx))
      · intro n
        exact csSup_le (hpgeom.1.nonempty.image _)
          (by rintro _ ⟨x,hx,rfl⟩; exact (hbound n x hx).2)
    · intro q hq
      let F : ℕ → NonemptyCompacts V := fun n =>
        ⟨⟨exclusion C u (an n),((exclusion_ball_faces hc hs hg hB).1 (an n)).2.1⟩,
          ((exclusion_ball_faces hc hs hg hB).1 (an n)).1.nonempty⟩
      have ht : Tendsto F atTop (𝓝 ({q} : NonemptyCompacts V)) :=
        tendsto_iff_dist_tendsto_zero.mpr (by simpa [F,NonemptyCompacts.dist_eq] using hq)
      rcases exclusion_limit_dichotomy hc hs hg h3 hPR ha F {q} (fun _ => rfl) ht with heq | ⟨r,hr,heq⟩
      · have hsingle : (exclusion C u p).Subsingleton := by rw [← heq]; exact subsingleton_singleton
        exact False.elim (hpgeom.1.not_subsingleton hsingle)
      · have hrq : (r:V) = q := by
          have heq' : ({q} : Set V) = {(r:V)} := heq
          have hm : (r:V) ∈ ({q} : Set V) := by rw [heq']; exact mem_singleton (r:V)
          exact hm
        refine ⟨⟨hrq ▸ r.property,hrq ▸ hr⟩,?_⟩
        simpa only [hrq] using singleton_common_effect hc hs hg h3 hPR ha hr

#print axioms common_old_exclusion_confirmation

end D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation
