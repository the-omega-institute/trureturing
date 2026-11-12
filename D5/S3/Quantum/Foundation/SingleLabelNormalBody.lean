/- GID: D5/S3/Quantum/Foundation/SingleLabelNormalBody
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/SingleLabelNormalBody
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole original positive annihilators at a single-label exclusion ball. -/

import D5.S3.Quantum.Foundation.OriginalFacePolarity
import D5.S3.Quantum.Foundation.ContinuousFrameSum

/-! Full original positive annihilator geometry under variable-dimensional exclusion balls. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.SingleLabelNormalBody

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open WholePairBallConfirmation OriginalFacePolarity ContinuousFrameSum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The fiber of the original exclusion map at p contains just p. -/
def SingleLabel (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : pure C u) : Prop :=
  ∀ s : pure C u, exclusion C u s = exclusion C u p → s = p

section Geometry

variable (hc : IsClosed (C : Set V))
  (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)

include hc hs hg hB in
private theorem equal_of_two_points (p q : pure C u) {x y : V}
    (hxy : x ≠ y) (hx : x ∈ exclusion C u p ∩ exclusion C u q)
    (hy : y ∈ exclusion C u p ∩ exclusion C u q) :
    exclusion C u p = exclusion C u q := by
  have all := exclusion_ball_faces hc hs hg hB
  have hconv := (all.1 p).2.2.1.inter (all.1 q).2.2.1
  have hface := (all.1 p).2.2.2.2.1.inter (all.1 q).2.2.2.2.1
  have hn : (exclusion C u p ∩ exclusion C u q).Nontrivial := ⟨x, hx, y, hy, hxy⟩
  obtain ⟨bp⟩ := hB p
  obtain ⟨bq⟩ := hB q
  have hp := chart_face_eq bp hconv
    (hface.mono (all.1 p).2.2.2.2.1.subset inter_subset_left) hn
  have hq := chart_face_eq bq hconv
    (hface.mono (all.1 q).2.2.2.2.1.subset inter_subset_right) hn
  exact hp.symm.trans hq

include hc hs hg hB in
/-- Neighbor single-label propagation uses only EB, including segment balls. -/
theorem single_label_neighbor (p q : pure C u) (hp : SingleLabel C u p)
    (hq : (q : V) ∈ exclusion C u p) : SingleLabel C u q := by
  intro s he
  by_contra hsq
  have hpq : (p : V) ∈ exclusion C u q := (exclusion_symmetric p q).mp hq
  have hsp : (s : V) ∈ exclusion C u p :=
    (exclusion_symmetric s p).mp (he.symm ▸ hpq)
  have hcollapse (r : pure C u) (hr : (r : V) ∈ exclusion C u q) : r = p := by
    apply hp
    apply equal_of_two_points hc hs hg hB r p (Subtype.val_injective.ne (Ne.symm hsq))
    · exact ⟨(exclusion_symmetric q r).mp hr, hq⟩
    · exact ⟨(exclusion_symmetric s r).mp (he.symm ▸ hr), hsp⟩
  obtain ⟨a, b, ha, hb, hab⟩ := pure_pair_in_ball hc hs hg hB q
  exact hab ((hcollapse a ha).trans (hcollapse b hb).symm)

include hc hs hg in
/-- A nonzero positive annihilator reaches its global maximum on D_p itself. -/
theorem positive_annihilator_maximum (p : pure C u) (g : V →ₗ[ℝ] ℝ)
    (hg0 : g ≠ 0) (hpos : ∀ x ∈ C, 0 ≤ g x) (hgp : g p = 0) :
    ∃ s : pure C u, (s : V) ∈ exclusion C u p ∧
      0 < g s ∧ ∀ x ∈ base C u, g x ≤ g s := by
  have hK := base_compact hc hs
  have hsome : ∃ q : pure C u, 0 < g q := by
    by_contra! hn
    have hz (q : pure C u) : g q = 0 := le_antisymm (hn q) (hpos q q.property.1.1)
    have hh : Submodule.span ℝ (pure C u) ≤ LinearMap.ker g :=
      Submodule.span_le.mpr (fun x hx => hz ⟨x, hx⟩)
    rw [pure_span hK hs hg] at hh
    exact hg0 (LinearMap.ker_eq_top.mp (top_le_iff.mp hh))
  obtain ⟨q, hq⟩ := hsome
  let L := g.toContinuousLinearMap
  obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn ⟨q, pure_mem q⟩ L.continuous.continuousOn
  have hex : IsExposed ℝ (base C u) (L.toExposed (base C u)) :=
    ContinuousLinearMap.toExposed.isExposed
  obtain ⟨s, hspure⟩ := (hex.isCompact hK).extremePoints_nonempty ⟨m, hm, hmax⟩
  have hsP : s ∈ pure C u := hex.isExtreme.extremePoints_subset_extremePoints hspure
  have hgs : 0 < g s := hq.trans_le (hspure.1.2 q (pure_mem q))
  let f : V →ₗ[ℝ] ℝ := (g s)⁻¹ • g
  have hf : confirms C u s f := by
    refine ⟨cone_bound hK hs (fun r => ?_), ?_⟩
    · change 0 ≤ (g s)⁻¹ * g r ∧ (g s)⁻¹ * g r ≤ 1
      refine ⟨mul_nonneg (inv_nonneg.mpr hgs.le) (hpos r (pure_mem r).1), ?_⟩
      rw [← div_eq_inv_mul, div_le_one hgs]
      exact hspure.1.2 r (pure_mem r)
    · simp [f, hgs.ne']
  have hpD : (p : V) ∈ exclusion C u s := ⟨pure_mem p, f, hf, by simp [f, hgp]⟩
  exact ⟨⟨s, hsP⟩, (exclusion_symmetric (⟨s, hsP⟩ : pure C u) p).mp hpD,
    hgs, hspure.1.2⟩

end Geometry

/-- The entire original normalized positive annihilator slice, not an effect selection. -/
def normalBody (C : PointedCone ℝ V) (p c : V) : Set (V →L[ℝ] ℝ) :=
  {b | (∀ x ∈ C, 0 ≤ b x) ∧ b p = 0 ∧ b c = 1}

/-- Linear restriction slope in the actual original affine ball chart. -/
def slope {p : V} (a : ExclusionChart C u p) :
    (V →L[ℝ] ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin a.dim) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin a.dim))).symm.toLinearMap.comp
    ({ toFun := fun b => b.comp a.param.linear.toContinuousLinearMap
       map_add' := by intros; ext; simp
       map_smul' := by intro t b; ext z; rfl } :
      (V →L[ℝ] ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin a.dim) →L[ℝ] ℝ))

/-- Image of the whole actual positive annihilator slice. -/
def slopeBody {p : V} (a : ExclusionChart C u p) : Set (EuclideanSpace ℝ (Fin a.dim)) :=
  slope a '' normalBody C p (a.param 0)

private theorem slope_formula {p : V} (a : ExclusionChart C u p)
    (b : V →L[ℝ] ℝ) (z) : b (a.param z) = b (a.param 0) + ⟪slope a b, z⟫ := by
  rw [show ⟪slope a b, z⟫ = b (a.param.linear z) from
    by
      change ⟪(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin a.dim))).symm
        (b.comp a.param.linear.toContinuousLinearMap), z⟫ = _
      exact InnerProductSpace.toDual_symm_apply]
  rw [← map_add]
  congr 1
  simpa [add_comm] using congrFun a.param.decomp z

private theorem slope_norm_le {p : V} (a : ExclusionChart C u p)
    {b : V →L[ℝ] ℝ} (hb : b ∈ normalBody C p (a.param 0)) : ‖slope a b‖ ≤ 1 := by
  apply affine_nonneg_bound
  intro z hz
  rw [← hb.2.2, ← slope_formula]
  exact hb.1 _ (a.whole ▸ mem_image_of_mem a.param (by simpa using hz)).1.1

/-- The whole normalized body is globally bounded by twice the original unit. -/
theorem normal_body_bound (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) (a : ExclusionChart C u p)
    {b : V →L[ℝ] ℝ} (hb : b ∈ normalBody C p (a.param 0)) :
    proper C ((2 : ℝ) • u) b.toLinearMap := by
  have hb0 : b.toLinearMap ≠ 0 := by
    intro he
    have hh := LinearMap.congr_fun he (a.param 0)
    simpa [hb.2.2] using hh
  obtain ⟨s, hsD, _, hmax⟩ := positive_annihilator_maximum hc hs hg p
    b.toLinearMap hb0 hb.1 hb.2.1
  obtain ⟨z, hz, he⟩ := a.whole.symm ▸ hsD
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  have hbs : b s ≤ 2 := by
    rw [← he, slope_formula, hb.2.2]
    have hinner := real_inner_le_norm (slope a b) z
    have hprod : ‖slope a b‖ * ‖z‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_right (slope_norm_le a hb) (norm_nonneg z)).trans (by simpa using hz')
    linarith
  have hupper : ∀ x ∈ C, b x ≤ 2 * u x := by
    intro x hx
    have hh := nonneg_on_cone (f := (2 : ℝ) • u - b.toLinearMap) (base_compact hc hs) hs
      (fun r => by
        change 0 ≤ 2 * u r - b r
        rw [(pure_mem r).2]
        have hh : b r ≤ b s := hmax r (pure_mem r)
        linarith) x hx
    simpa using hh
  exact fun x hx => ⟨hb.1 x hx, hupper x hx⟩

omit [FiniteDimensional ℝ V] in
private theorem normal_body_closed (p c : V) : IsClosed (normalBody C p c) := by
  have he : normalBody C p c =
      (⋂ x : V, ⋂ (_ : x ∈ C), {b : V →L[ℝ] ℝ | 0 ≤ b x}) ∩
      {b | b p = 0} ∩ {b | b c = 1} := by
    ext b
    simp [normalBody, and_assoc]
  rw [he]
  exact ((isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_eq (by fun_prop) continuous_const)

/-- Compactness is for the entire positive annihilator slice in the original dual. -/
theorem normal_body_compact (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) (a : ExclusionChart C u p) :
    IsCompact (normalBody C p (a.param 0)) := by
  have hs2 : ∀ x ∈ C, x ≠ 0 → 0 < ((2 : ℝ) • u) x := by
    intro x hx hne
    change 0 < 2 * u x
    exact mul_pos (by norm_num) (hs x hx hne)
  exact (effects_compact hs2 hg).of_isClosed_subset (normal_body_closed _ _)
    (fun b hb => normal_body_bound hc hs hg p a hb)

omit [FiniteDimensional ℝ V] in
private theorem normal_body_convex (p c : V) : Convex ℝ (normalBody C p c) := by
  intro b hb d hd s t hs ht hst
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · change 0 ≤ s * b x + t * d x
    exact add_nonneg (mul_nonneg hs (hb.1 x hx)) (mul_nonneg ht (hd.1 x hx))
  · change s * b p + t * d p = 0
    rw [hb.2.1, hd.2.1]
    ring
  · change s * b c + t * d c = 1
    simpa [hb.2.2, hd.2.2] using hst

/-- The whole original slope body is compact and convex, and lies in the unit ball. -/
theorem slope_body_geometry (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) (a : ExclusionChart C u p) :
    IsCompact (slopeBody a) ∧ Convex ℝ (slopeBody a) ∧
      slopeBody a ⊆ Metric.closedBall 0 1 := by
  refine ⟨(normal_body_compact hc hs hg p a).image (slope a).continuous_of_finiteDimensional,
    (normal_body_convex _ _).linear_image (slope a), ?_⟩
  rintro v ⟨b, hb, rfl⟩
  simpa using slope_norm_le a hb

private theorem slope_eq_of_formula {p : V} (a : ExclusionChart C u p)
    (b : V →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin a.dim))
    (h : ∀ z, b (a.param z) = b (a.param 0) + ⟪v, z⟫) : slope a b = v := by
  apply ext_inner_right ℝ
  intro z
  linarith [slope_formula a b z, h z]

omit [FiniteDimensional ℝ V] in
private theorem chart_mem {p : V} (a : ExclusionChart C u p)
    {z} (hz : ‖z‖ ≤ 1) : a.param z ∈ exclusion C u p :=
  a.whole ▸ mem_image_of_mem a.param (by simpa using hz)

private def chartPure (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (a : ExclusionChart C u p)
    (n : EuclideanSpace ℝ (Fin a.dim)) (hn : ‖n‖ = 1) : pure C u :=
  ⟨a.param n, ((chart_boundary hc hs hg hB p a).symm ▸
    (show a.param n ∈ a.param '' Metric.sphere 0 1 from
      ⟨n, by simpa using hn, rfl⟩)).2⟩

private theorem slope_body_zero (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (a : ExclusionChart C u p) : (0 : EuclideanSpace ℝ (Fin a.dim)) ∈ slopeBody a := by
  obtain ⟨e, he, hzero⟩ := (exclusion_ball_faces hc hs hg hB).1 p |>.2.2.2.2.2.2
  let b := (u - e).toContinuousLinearMap
  have hconst (z) (hz : ‖z‖ ≤ 1) : b (a.param z) = 1 := by
    have hx := chart_mem a hz
    have hez := (hzero ▸ hx).2
    change u (a.param z) - e (a.param z) = 1
    rw [hx.1.2, hez]
    ring
  have hb : b ∈ normalBody C p (a.param 0) := by
    refine ⟨fun x hx => sub_nonneg.mpr (he.1 x hx).2, ?_, hconst 0 (by simp)⟩
    change u p - e p = 0
    rw [(pure_mem p).2, he.2]
    ring
  have hnorm : ‖slope a b‖ ≤ 0 := affine_nonneg_bound (fun z hz => by
    have h := slope_formula a b z
    rw [hconst z hz, hb.2.2] at h
    linarith)
  exact ⟨b, hb, norm_le_zero_iff.mp hnorm⟩

/-- Every original unit direction has a positive, actual normalized annihilator slope. -/
theorem positive_ray (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p) (a : ExclusionChart C u p)
    (n : EuclideanSpace ℝ (Fin a.dim)) (hn : ‖n‖ = 1) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t • n ∈ slopeBody a := by
  let q := chartPure hc hs hg hB p a n hn
  have hqD : (q : V) ∈ exclusion C u p := chart_mem a hn.le
  have hqsingle := single_label_neighbor hc hs hg hB p q hp hqD
  have all := exclusion_ball_faces hc hs hg hB
  obtain ⟨e, he, hzero⟩ := (all.1 q).2.2.2.2.2.2
  have hep : e p = 0 :=
    ((hzero ▸ (exclusion_symmetric p q).mp hqD) : (p : V) ∈ {x | x ∈ base C u ∧ e x = 0}).2
  let f := (AffineMap.const ℝ (EuclideanSpace ℝ (Fin a.dim)) (1 : ℝ)) -
    e.toAffineMap.comp a.param
  have hfpos (z) (hz : ‖z‖ ≤ 1) : 0 ≤ f z := by
    have hx := chart_mem a hz
    have hu := hx.1.2
    have hb := (he.1 _ hx.1.1).2
    change 0 ≤ 1 - e (a.param z)
    linarith
  have hfn : f (-(-n)) = 0 := by
    change 1 - e (a.param (-(-n))) = 0
    rw [neg_neg]
    change 1 - e q = 0
    rw [he.2]
    ring
  have hformula := affine_zero_antipode f (by simpa using hn : ‖-n‖ = 1) hfpos hfn
  let lam := f (-n) / 2
  have hlam0 : 0 ≤ lam := div_nonneg (hfpos (-n) (by simpa using hn.le)) (by norm_num)
  have hlamhalf : lam ≤ 1 / 2 := by
    have hh := (he.1 _ (chart_mem a (by simpa using hn.le : ‖-n‖ ≤ 1)).1.1).1
    change (1 - e (a.param (-n))) / 2 ≤ 1 / 2
    linarith
  have heformula (z) : e (a.param z) = 1 - lam + lam * ⟪n, z⟫ := by
    have hh := hformula z
    change 1 - e (a.param z) = lam * (1 + ⟪-n, z⟫) at hh
    rw [inner_neg_left] at hh
    linarith
  have hlam : 0 < lam := by
    by_contra hnlam
    have hl0 : lam = 0 := le_antisymm (le_of_not_gt hnlam) hlam0
    have hcollapse (s : pure C u) (hsD : (s : V) ∈ exclusion C u p) : s = q := by
      have hes : e s = 1 := by
        obtain ⟨z, _, hz⟩ := a.whole.symm ▸ hsD
        rw [← hz, heformula, hl0]
        ring
      have hsub : exclusion C u q ⊆ exclusion C u s := by
        intro x hx
        exact ⟨hx.1, e, ⟨he.1, hes⟩, (hzero ▸ hx).2⟩
      obtain ⟨bs⟩ := hB s
      have heq := chart_face_eq bs (all.1 q).2.2.1
        ((all.1 q).2.2.2.2.1.mono (all.1 s).2.2.2.2.1.subset hsub) (all.1 q).1
      exact hqsingle s heq.symm
    obtain ⟨s, t, hsD, htD, hst⟩ := pure_pair_in_ball hc hs hg hB p
    exact hst ((hcollapse s hsD).trans (hcollapse t htD).symm)
  have hden : 0 < 1 - lam := by linarith
  let b : V →L[ℝ] ℝ := (1 - lam)⁻¹ • e.toContinuousLinearMap
  have hb : b ∈ normalBody C p (a.param 0) := by
    refine ⟨fun x hx => mul_nonneg (inv_nonneg.mpr hden.le) (he.1 x hx).1, ?_, ?_⟩
    · change (1 - lam)⁻¹ * e p = 0
      rw [hep, mul_zero]
    · change (1 - lam)⁻¹ * e (a.param 0) = 1
      rw [heformula]
      simp [hden.ne']
  have hbformula (z) : b (a.param z) = b (a.param 0) + ⟪(lam / (1 - lam)) • n, z⟫ := by
    change (1 - lam)⁻¹ * e (a.param z) = b (a.param 0) + _
    rw [heformula, hb.2.2, real_inner_smul_left]
    field_simp
    <;> ring
  have hv := slope_eq_of_formula a b _ hbformula
  refine ⟨lam / (1 - lam), div_pos hlam hden, ?_, b, hb, hv⟩
  exact (div_le_one hden).mpr (by linarith)

/-- A single positive radius works for every original direction; only finitely many
actual coordinate-direction witnesses are selected. -/
theorem slope_body_inradius (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p) (a : ExclusionChart C u p) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧ Metric.closedBall 0 rho ⊆ slopeBody a := by
  classical
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  let dir (j : Fin a.dim × Bool) : EuclideanSpace ℝ (Fin a.dim) :=
    if j.2 then EuclideanSpace.single j.1 1 else -EuclideanSpace.single j.1 1
  have hdir (j) : ‖dir j‖ = 1 := by
    dsimp [dir]
    split_ifs <;> simp [EuclideanSpace.single]
  choose t ht using fun j => positive_ray hc hs hg hB p hp a (dir j) (hdir j)
  obtain ⟨j, _, hj⟩ := (Finset.univ : Finset (Fin a.dim × Bool)).exists_min_image t Finset.univ_nonempty
  let eta := t j
  have heta : 0 < eta := (ht j).1
  have heta1 : eta ≤ 1 := (ht j).2.1
  have hconv := (slope_body_geometry hc hs hg p a).2.1
  have hzero := slope_body_zero hc hs hg hB p a
  have hsmall (k : Fin a.dim × Bool) : eta • dir k ∈ slopeBody a := by
    have hscale : eta / t k ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg heta.le (ht k).1.le, (div_le_one (ht k).1).mpr (hj k (Finset.mem_univ _))⟩
    have hh := hconv.smul_mem_of_zero_mem hzero (ht k).2.2 hscale
    simpa [smul_smul, div_mul_cancel₀ _ (ht k).1.ne'] using hh
  have hd : (0 : ℝ) < a.dim := by exact_mod_cast a.dim_pos
  refine ⟨eta / a.dim, div_pos heta hd, ?_, ?_⟩
  · exact (div_le_one hd).mpr (heta1.trans (by exact_mod_cast a.dim_pos))
  · intro z hz
    have hznorm : ‖z‖ ≤ eta / a.dim := by simpa using hz
    let v (i : Fin a.dim) : EuclideanSpace ℝ (Fin a.dim) :=
      (a.dim : ℝ) • EuclideanSpace.single i (z i)
    have hv (i : Fin a.dim) : v i ∈ slopeBody a := by
      have hcoord : |(a.dim : ℝ) * z i| ≤ eta := by
        rw [abs_mul, abs_of_pos hd]
        have hh : |z i| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z i
        exact (mul_le_mul_of_nonneg_left (hh.trans hznorm) hd.le).trans_eq (by field_simp)
      by_cases hi : 0 ≤ z i
      · have hscale : (a.dim : ℝ) * z i / eta ∈ Icc (0 : ℝ) 1 := by
          refine ⟨div_nonneg (mul_nonneg hd.le hi) heta.le, (div_le_one heta).mpr ?_⟩
          exact (le_abs_self _).trans hcoord
        have hh := hconv.smul_mem_of_zero_mem hzero (hsmall (i, true)) hscale
        convert hh using 1 <;> ext k <;> simp [v, dir, EuclideanSpace.single, smul_smul]
        <;> split_ifs <;> field_simp <;> ring
      · have hscale : -((a.dim : ℝ) * z i) / eta ∈ Icc (0 : ℝ) 1 := by
          refine ⟨div_nonneg (by nlinarith [le_of_not_ge hi]) heta.le, (div_le_one heta).mpr ?_⟩
          exact (neg_le_abs _).trans hcoord
        have hh := hconv.smul_mem_of_zero_mem hzero (hsmall (i, false)) hscale
        convert hh using 1 <;> ext k <;> simp [v, dir, EuclideanSpace.single, smul_smul]
        <;> split_ifs <;> field_simp <;> ring
    have hsum : ∑ i : Fin a.dim, (a.dim : ℝ)⁻¹ • v i ∈ slopeBody a := by
      apply hconv.sum_mem (t := Finset.univ)
        (fun _ _ => inv_nonneg.mpr hd.le) ?_ (fun i _ => hv i)
      simp [hd.ne']
    convert hsum using 1
    ext k
    simp [v, EuclideanSpace.single, Finset.sum_apply, hd.ne']

end D5.S3.Quantum.Foundation.SingleLabelNormalBody
