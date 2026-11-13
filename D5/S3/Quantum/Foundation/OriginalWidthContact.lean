/- GID: D5/S3/Quantum/Foundation/OriginalWidthContact
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalWidthContact
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: A width attaining original effect has one unique joint contact pair. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import Mathlib.Analysis.LocallyConvex.Separation

/-! Joint contacts on the entire original cone base and full effect interval. -/

noncomputable section
open Set
open scoped Pointwise

namespace D5.S3.Quantum.Foundation.OriginalWidthContact

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The whole original effect interval bounds every ordered contrast on F.
Together with an attained contrast M this expresses W(F)=M. -/
def WidthBound (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (F : Set V) (M : ℝ) : Prop :=
  ∀ f : V →ₗ[ℝ] ℝ, proper C u f → ∀ x ∈ F, ∀ y ∈ F, f x - f y ≤ M

private theorem normalized_effect {C : PointedCone ℝ V} {u h : V →ₗ[ℝ] ℝ}
    (hK : IsCompact (base C u)) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {a z : V}
    (hmin : ∀ x ∈ base C u, h a ≤ h x) (hmax : ∀ x ∈ base C u, h x ≤ h z)
    (hs : 0 < h z - h a) :
    proper C u ((h z - h a)⁻¹ • (h - h a • u)) := by
  apply cone_bound hK hu
  intro p
  have hp := pure_mem p
  have hlo := hmin p hp
  have hhi := hmax p hp
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, hp.2, smul_eq_mul, mul_one]
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr hlo)
  · apply (inv_mul_le_iff₀ hs).2
    linarith

private theorem joint_contact_exists {C : PointedCone ℝ V} {u b : V →ₗ[ℝ] ℝ}
    (hK : IsCompact (base C u)) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {F : Set V} (hFK : F ⊆ base C u) {M : ℝ} (hM : 0 < M)
    (hwidth : WidthBound C u F M) (hb : proper C u b)
    {q r : V} (hq : q ∈ F) (hr : r ∈ F) (hbr : b q - b r = M) :
    ∃ x ∈ base C u, ∃ y ∈ base C u,
      b x = 1 ∧ b y = 0 ∧ q - r = M • (x - y) := by
  let d := M⁻¹ • (q - r)
  have hqK := hFK hq
  have hrK := hFK hr
  have hd : d ∈ base C u - base C u := by
    rw [← iInter_halfSpaces_eq ((base_convex C u).sub (base_convex C u))
      (by simpa only [← image2_sub, ← image_prod, Pi.sub_def] using
        ((hK.prod hK).image (continuous_fst.sub continuous_snd)).isClosed)]
    apply mem_iInter.mpr
    intro h
    obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn ⟨q, hqK⟩ h.continuous.continuousOn
    obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨q, hqK⟩ h.continuous.continuousOn
    refine ⟨z - a, sub_mem_sub hz ha, ?_⟩
    have hs : 0 ≤ h z - h a := sub_nonneg.mpr (hmin hz)
    rcases eq_or_lt_of_le hs with hs0 | hspos
    · have hqa : h q = h a := le_antisymm ((hmax hqK).trans (by linarith)) (hmin hqK)
      have hra : h r = h a := le_antisymm ((hmax hrK).trans (by linarith)) (hmin hrK)
      simp [d, map_smul, map_sub, hqa, hra, ← hs0]
    · let f : V →ₗ[ℝ] ℝ := (h z - h a)⁻¹ • (h.toLinearMap - h a • u)
      have hf := normalized_effect hK hu (fun x hx => hmin hx)
        (fun x hx => hmax hx) hspos
      have hw := hwidth f hf q hq r hr
      have hw' : (h z - h a)⁻¹ * (h q - h r) ≤ M := by
        simpa only [f, LinearMap.smul_apply, LinearMap.sub_apply, hqK.2, hrK.2,
          smul_eq_mul, mul_one, ← mul_sub, sub_sub_sub_cancel_right,
          ContinuousLinearMap.coe_coe] using hw
      have hh : h q - h r ≤ (h z - h a) * M := (inv_mul_le_iff₀ hspos).mp hw'
      dsimp only [d]
      rw [map_smul, map_sub, map_sub]
      change M⁻¹ * (h q - h r) ≤ h z - h a
      exact (inv_mul_le_iff₀ hM).mpr (by nlinarith [hh])
  obtain ⟨x, hx, y, hy, hxy⟩ := hd
  change x - y = d at hxy
  have hdiff : q - r = M • (x - y) := by
    rw [hxy]
    simp [d, smul_smul, hM.ne']
  have hbd : b x - b y = 1 := by
    have hh := congrArg b hdiff
    simp only [map_sub, map_smul, smul_eq_mul, hbr] at hh
    nlinarith
  have hbx := hb x hx.1
  have hby := hb y hy.1
  rw [hx.2] at hbx
  rw [hy.2] at hby
  exact ⟨x, hx, y, hy, by linarith, by linarith, hdiff⟩

private theorem top_exposed {C : PointedCone ℝ V} {u f : V →ₗ[ℝ] ℝ}
    (hf : proper C u f) : IsExposed ℝ (base C u) {x ∈ base C u | f x = 1} := by
  rintro ⟨z, hz, hfz⟩
  refine ⟨f.toContinuousLinearMap, Set.ext fun x => ?_⟩
  constructor
  · rintro ⟨hx, hfx⟩
    refine ⟨hx, fun y hy => ?_⟩
    change f y ≤ f x
    rw [hfx]
    simpa only [hy.2] using (hf y hy.1).2
  · rintro ⟨hx, hmax⟩
    have hh := hmax z hz
    change f z ≤ f x at hh
    exact ⟨hx, le_antisymm (by simpa only [hx.2] using (hf x hx.1).2)
      (by simpa only [hfz] using hh)⟩

omit [FiniteDimensional ℝ V] in
private theorem top_convex (C : PointedCone ℝ V) (u f : V →ₗ[ℝ] ℝ) :
    Convex ℝ {x ∈ base C u | f x = 1} :=
  (base_convex C u).inter ((convex_singleton (1 : ℝ)).linear_preimage f)

private theorem top_subsingleton_of_zero_exclusion
    {C : PointedCone ℝ V} {u f : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (hf : proper C u f) (p : pure C u)
    (hz : ∀ z ∈ exclusion C u p, f z = 0) :
    {x ∈ base C u | f x = 1}.Subsingleton := by
  have all := exclusion_ball_faces hc hu hg hB
  have htop := top_exposed hf
  have hcompact := htop.isCompact (base_compact hc hu)
  have hext : {x ∈ base C u | f x = 1}.extremePoints ℝ ⊆ {(p : V)} := by
    intro s hs
    have hsP : s ∈ pure C u := htop.isExtreme.extremePoints_subset_extremePoints hs
    let t : pure C u := ⟨s, hsP⟩
    have hsub : exclusion C u p ⊆ exclusion C u t := by
      intro z hzD
      exact ⟨hzD.1, f, ⟨hf, hs.1.2⟩, hz z hzD⟩
    obtain ⟨bt⟩ := hB t
    have heq := chart_face_eq bt (all.1 p).2.2.1
      ((all.1 p).2.2.2.2.1.mono (all.1 t).2.2.2.2.1.subset hsub) (all.1 p).1
    exact congrArg Subtype.val (hinj heq).symm
  have hsub : {x ∈ base C u | f x = 1} ⊆ {(p : V)} := by
    rw [← closure_convexHull_extremePoints hcompact (top_convex C u f)]
    exact closure_minimal (convexHull_min hext (convex_singleton _)) isClosed_singleton
  exact fun x hx y hy => (hsub hx).trans (hsub hy).symm

private theorem contact_face_subsingleton
    {C : PointedCone ℝ V} {u f : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (hf : proper C u f) {x y : V} (hx : x ∈ base C u) (hy : y ∈ base C u)
    (hfx : f x = 1) (hfy : f y = 0) :
    {z ∈ base C u | f z = 1}.Subsingleton ∨
      {z ∈ base C u | f z = 0}.Subsingleton := by
  have hcomp : proper C u (u - f) := by
    intro z hz
    have hh := hf z hz
    simp only [LinearMap.sub_apply]
    constructor <;> linarith
  have heq : {z ∈ base C u | (u - f) z = 1} = {z ∈ base C u | f z = 0} := by
    ext z
    constructor <;> rintro ⟨hz, he⟩ <;> refine ⟨hz, ?_⟩ <;>
      simpa only [LinearMap.sub_apply, hz.2, sub_eq_self] using he
  have hface := top_exposed hcomp
  rw [heq] at hface
  have hconv := top_convex C u (u - f)
  rw [heq] at hconv
  have hproper : {z ∈ base C u | f z = 0} ≠ base C u := by
    intro he
    have hh : x ∈ {z ∈ base C u | f z = 0} := he.symm ▸ hx
    linarith [hh.2]
  rcases (exclusion_ball_faces hc hu hg hB).2.1 _
      (show {z ∈ base C u | f z = 0}.Nonempty from ⟨y, hy, hfy⟩) hconv
      hface.isExtreme hproper with ⟨p, hp⟩ | ⟨p, hp⟩
  · right
    rw [hp]
    exact subsingleton_singleton
  · left
    apply top_subsingleton_of_zero_exclusion hc hu hg hB hinj hf p
    intro z hz
    exact (show z ∈ {z ∈ base C u | f z = 0} from hp.symm ▸ hz).2

/-- The same actual pair is unique and has strict equal readings for every
original confirming effect vanishing on the whole exclusion face. -/
theorem original_width_contact
    {C : PointedCone ℝ V} {u b : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) {M : ℝ} (hM : 0 < M)
    (hwidth : WidthBound C u (exclusion C u p) M) (hb : proper C u b)
    {q r : V} (hq : q ∈ exclusion C u p) (hr : r ∈ exclusion C u p)
    (hbr : b q - b r = M) :
    ∃ xy : V × V,
      (xy.1 ∈ base C u ∧ xy.2 ∈ base C u ∧ b xy.1 = 1 ∧ b xy.2 = 0 ∧
        q - r = M • (xy.1 - xy.2)) ∧
      (∀ zw : V × V, zw.1 ∈ base C u → zw.2 ∈ base C u →
        b zw.1 = 1 → b zw.2 = 0 → q - r = M • (zw.1 - zw.2) → zw = xy) ∧
      (M < 1 → ∀ e : V →ₗ[ℝ] ℝ, confirms C u p e →
        (∀ z ∈ exclusion C u p, e z = 0) →
        0 < e xy.1 ∧ e xy.1 = e xy.2 ∧ e xy.2 < 1 ∧
          xy.1 ∉ exclusion C u p ∧ xy.2 ∉ exclusion C u p) := by
  obtain ⟨x, hx, y, hy, hbx, hby, hd⟩ :=
    joint_contact_exists (base_compact hc hu) hu (fun _ hz => hz.1) hM hwidth hb hq hr hbr
  refine ⟨(x, y), ⟨hx, hy, hbx, hby, hd⟩, ?_, ?_⟩
  · intro zw hz hw hbz hbw hdiff
    have he : zw.1 - zw.2 = x - y :=
      (smul_right_injective V hM.ne') (hdiff.symm.trans hd)
    rcases contact_face_subsingleton hc hu hg hB hinj hb hx hy hbx hby with ht | ht
    · have hz' : zw.1 = x := ht ⟨hz, hbz⟩ ⟨hx, hbx⟩
      apply Prod.ext hz'
      exact sub_right_inj.mp (hz' ▸ he)
    · have hw' : zw.2 = y := ht ⟨hw, hbw⟩ ⟨hy, hby⟩
      apply Prod.ext _ hw'
      exact sub_left_inj.mp (hw' ▸ he)
  · intro hsmall e he hezero
    have heq : e x = e y := by
      have hh := congrArg e hd
      simp only [map_sub, map_smul, smul_eq_mul, hezero q hq, hezero r hr,
        sub_self] at hh
      nlinarith
    have hlo : 0 < e x := by
      have hn := (he.1 x hx.1).1
      by_contra! hn'
      have hx0 : e x = 0 := le_antisymm hn' hn
      have hy0 : e y = 0 := heq.symm.trans hx0
      have hxD : x ∈ exclusion C u p := ⟨hx, e, he, hx0⟩
      have hyD : y ∈ exclusion C u p := ⟨hy, e, he, hy0⟩
      have hh := hwidth b hb x hxD y hyD
      rw [hbx, hby] at hh
      linarith
    have hhi : e y < 1 := by
      have hn : e y ≤ 1 := by simpa only [hy.2] using (he.1 y hy.1).2
      by_contra! hn'
      have hy1 := le_antisymm hn hn'
      have hx1 := heq.trans hy1
      have ht := top_subsingleton_of_zero_exclusion hc hu hg hB hinj he.1 p hezero
      have hxy := ht ⟨hx, hx1⟩ ⟨hy, hy1⟩
      have hh := congrArg b hxy
      rw [hbx, hby] at hh
      norm_num at hh
    refine ⟨hlo, heq, hhi, ?_, ?_⟩
    · intro hxD
      linarith [hezero x hxD]
    · intro hyD
      linarith [hezero y hyD]

end D5.S3.Quantum.Foundation.OriginalWidthContact
