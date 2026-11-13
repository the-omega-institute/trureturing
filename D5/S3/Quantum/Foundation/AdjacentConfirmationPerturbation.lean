/- GID: D5/S3/Quantum/Foundation/AdjacentConfirmationPerturbation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/AdjacentConfirmationPerturbation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: A specified adjacent-confirmation perturbation strictly increases original ball contrast. -/

import D5.S3.Quantum.Foundation.OriginalWidthContact
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness

/-! Strict contraction of the original global range, with its original-unit normalization. -/

noncomputable section
open Set

namespace D5.S3.Quantum.Foundation.AdjacentConfirmationPerturbation

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalWidthContact ExclusionWidthCompactness

private theorem compact_range_contraction {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {a e : X → ℝ} (ha : Continuous a) (he : Continuous e)
    (ha01 : ∀ x ∈ K, 0 ≤ a x ∧ a x ≤ 1)
    (he01 : ∀ x ∈ K, 0 ≤ e x ∧ e x ≤ 1)
    (hcontact : ∀ x ∈ K, ∀ y ∈ K, a x = 1 → a y = 0 → e x < e y) :
    ∃ t : ℝ, 0 < t ∧ ∀ x ∈ K, ∀ y ∈ K,
      (a x + t * e x) - (a y + t * e y) < 1 := by
  let T : Set (X × X) := {z ∈ K ×ˢ K | e z.2 ≤ e z.1}
  have hT : IsCompact T := (hK.prod hK).inter_right
    (isClosed_le (he.comp continuous_snd) (he.comp continuous_fst))
  obtain ⟨q, hq⟩ := hne
  obtain ⟨z, hz, hmax⟩ := hT.exists_isMaxOn
    (show T.Nonempty from ⟨(q,q), ⟨hq,hq⟩, le_rfl⟩)
    ((ha.comp continuous_fst).sub (ha.comp continuous_snd)).continuousOn
  have hzlt : a z.1 - a z.2 < 1 := by
    have h1 := ha01 z.1 hz.1.1
    have h2 := ha01 z.2 hz.1.2
    by_contra! hn
    have hx : a z.1 = 1 := by linarith
    have hy : a z.2 = 0 := by linarith
    exact (not_lt_of_ge hz.2) (hcontact z.1 hz.1.1 z.2 hz.1.2 hx hy)
  let t := (1 - (a z.1 - a z.2)) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  refine ⟨t, ht, ?_⟩
  intro x hx y hy
  by_cases hxy : e y ≤ e x
  · have ham := hmax (show (x,y) ∈ T from ⟨⟨hx,hy⟩,hxy⟩)
    have hex := he01 x hx
    have hey := he01 y hy
    have hmul : t * (e x - e y) ≤ t :=
      (mul_le_mul_of_nonneg_left (by linarith : e x - e y ≤ 1) ht.le).trans_eq
        (mul_one t)
    dsimp only at ham
    dsimp [t] at hmul ⊢
    nlinarith
  · have hd : t * (e x - e y) < 0 := mul_neg_of_pos_of_neg ht (by linarith)
    have hax := ha01 x hx
    have hay := ha01 y hy
    nlinarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The prescribed perturbation has smaller global range and its normalized original
proper effect has strictly greater contrast on the entire original exclusion ball. -/
theorem adjacent_confirmation_perturbation
    {C : PointedCone ℝ V} {u a e : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p q : pure C u) (hq : (q : V) ∈ exclusion C u p)
    (ha : confirms C u q a) (ha0 : ∀ x ∈ exclusion C u q, a x = 0)
    (he : confirms C u p e) (he0 : ∀ x ∈ exclusion C u p, e x = 0)
    {M : ℝ} (hM : M < 1) (hwidth : WidthBound C u (exclusion C u q) M) :
    ∃ t : ℝ, 0 < t ∧ ∃ lo hi : ℝ,
      (∀ x ∈ base C u, lo ≤ (a + t • e) x ∧ (a + t • e) x ≤ hi) ∧
      (∃ x ∈ base C u, (a + t • e) x = lo) ∧
      (∃ x ∈ base C u, (a + t • e) x = hi) ∧
      0 < hi - lo ∧ hi - lo < 1 ∧
      let b := (hi - lo)⁻¹ • ((a + t • e) - lo • u)
      proper C u b ∧
      oscillation (exclusion C u p) a.toContinuousLinearMap <
        oscillation (exclusion C u p) b.toContinuousLinearMap ∧
      0 < oscillation (exclusion C u p) a.toContinuousLinearMap := by
  have hK := base_compact hc hu
  have hqK := pure_mem q
  have hpK := pure_mem p
  have htop := top_subsingleton_of_zero_exclusion hc hu hg hB hinj ha.1 q ha0
  have hqp := (exclusion_symmetric p q).mp hq
  have hcontact : ∀ x ∈ base C u, ∀ y ∈ base C u,
      a x = 1 → a y = 0 → e x < e y := by
    intro x hx y hy hax hay
    have hxq : x = q := htop ⟨hx,hax⟩ ⟨hqK,ha.2⟩
    have hyD : y ∈ exclusion C u q := ⟨hy,a,ha,hay⟩
    have hw := hwidth e he.1 p hqp y hyD
    rw [he.2] at hw
    rw [hxq, he0 q hq]
    linarith
  obtain ⟨t, ht, hcontract⟩ := compact_range_contraction hK ⟨q,hqK⟩
    a.continuous_of_finiteDimensional e.continuous_of_finiteDimensional
    (fun x hx => by simpa only [hx.2] using ha.1 x hx.1)
    (fun x hx => by simpa only [hx.2] using he.1 x hx.1) hcontact
  let g : V →ₗ[ℝ] ℝ := a + t • e
  obtain ⟨xlo, hxlo, hlo⟩ := hK.exists_isMinOn ⟨q,hqK⟩
    g.continuous_of_finiteDimensional.continuousOn
  obtain ⟨xhi, hxhi, hhi⟩ := hK.exists_isMaxOn ⟨q,hqK⟩
    g.continuous_of_finiteDimensional.continuousOn
  have hgeom := (exclusion_ball_faces hc hu hg hB).1 p
  obtain ⟨r, hr, hrq⟩ : ∃ r ∈ exclusion C u p, r ≠ (q : V) := by
    obtain ⟨x,hx,y,hy,hxy⟩ := hgeom.1
    by_cases hxq : x = q
    · exact ⟨y,hy,by intro h; exact hxy (hxq.trans h.symm)⟩
    · exact ⟨x,hx,hxq⟩
  have har : a r < 1 := by
    have hl : a r ≤ 1 := by simpa only [hr.1.2] using (ha.1 r hr.1.1).2
    exact lt_of_le_of_ne hl (fun h => hrq (htop ⟨hr.1,h⟩ ⟨hqK,ha.2⟩))
  have hgq : g q = 1 := by simp [g, LinearMap.add_apply, LinearMap.smul_apply,
    ha.2, he0 q hq]
  have hgr : g r = a r := by simp [g, LinearMap.add_apply, LinearMap.smul_apply, he0 r hr]
  have hs : 0 < g xhi - g xlo := by
    have h1 := hlo hr.1
    have h2 := hhi hqK
    rw [hgq] at h2
    rw [hgr] at h1
    linarith
  have hslt : g xhi - g xlo < 1 := by
    simpa only [g, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      using hcontract xhi hxhi xlo hxlo
  let b : V →ₗ[ℝ] ℝ := (g xhi - g xlo)⁻¹ • (g - g xlo • u)
  have hb : proper C u b := by
    apply cone_bound hK hu
    intro s
    have hsK := pure_mem s
    have h1 := hlo hsK
    have h2 := hhi hsK
    change 0 ≤ (g xhi - g xlo)⁻¹ * (g s - g xlo * u s) ∧
      (g xhi - g xlo)⁻¹ * (g s - g xlo * u s) ≤ 1
    rw [hsK.2, mul_one]
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr h1)
    · exact (inv_mul_le_iff₀ hs).mpr (by linarith)
  obtain ⟨z,hz,haz⟩ := hgeom.2.1.exists_isMinOn hgeom.1.nonempty
    a.continuous_of_finiteDimensional.continuousOn
  have haq : ∀ x ∈ exclusion C u p, a x ≤ a q := by
    intro x hx
    rw [ha.2]
    simpa only [hx.1.2] using (ha.1 x hx.1.1).2
  have ho : oscillation (exclusion C u p) a.toContinuousLinearMap = 1 - a z := by
    unfold oscillation
    rw [show sSup (a.toContinuousLinearMap '' exclusion C u p) = a q from
      (show IsGreatest (a.toContinuousLinearMap '' exclusion C u p) (a q) from
        ⟨mem_image_of_mem _ hq, by rintro _ ⟨x,hx,rfl⟩; exact haq x hx⟩).csSup_eq]
    rw [show sInf (a.toContinuousLinearMap '' exclusion C u p) = a z from
      (show IsLeast (a.toContinuousLinearMap '' exclusion C u p) (a z) from
        ⟨mem_image_of_mem _ hz, by rintro _ ⟨x,hx,rfl⟩; exact haz hx⟩).csInf_eq]
    rw [ha.2]
  have hop : 0 < oscillation (exclusion C u p) a.toContinuousLinearMap := by
    rw [ho]
    have hh := haz hr
    linarith
  have hbf (x : V) (hx : x ∈ exclusion C u p) :
      b x = (g xhi - g xlo)⁻¹ * (a x - g xlo) := by
    simp [b, g, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      he0 x hx, hx.1.2]
  have hbmax : ∀ x ∈ exclusion C u p, b x ≤ b q := by
    intro x hx
    rw [hbf x hx, hbf q hq]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (haq x hx) _) (inv_nonneg.mpr hs.le)
  have hbmin : ∀ x ∈ exclusion C u p, b z ≤ b x := by
    intro x hx
    rw [hbf z hz, hbf x hx]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (haz hx) _) (inv_nonneg.mpr hs.le)
  have hob : oscillation (exclusion C u p) b.toContinuousLinearMap =
      (g xhi - g xlo)⁻¹ * (1 - a z) := by
    unfold oscillation
    rw [(show IsGreatest (b.toContinuousLinearMap '' exclusion C u p) (b q) from
      ⟨mem_image_of_mem _ hq, by rintro _ ⟨x,hx,rfl⟩; exact hbmax x hx⟩).csSup_eq]
    rw [(show IsLeast (b.toContinuousLinearMap '' exclusion C u p) (b z) from
      ⟨mem_image_of_mem _ hz, by rintro _ ⟨x,hx,rfl⟩; exact hbmin x hx⟩).csInf_eq]
    rw [hbf q hq, hbf z hz, ha.2]
    ring
  refine ⟨t,ht,g xlo,g xhi,?_,⟨xlo,hxlo,rfl⟩,⟨xhi,hxhi,rfl⟩,hs,hslt,hb,?_,hop⟩
  · exact fun x hx => ⟨hlo hx,hhi hx⟩
  · rw [ho,hob]
    have hpos : 0 < 1 - a z := ho ▸ hop
    have hinv : 1 < (g xhi - g xlo)⁻¹ := (one_lt_inv₀ hs).mpr hslt
    nlinarith

end D5.S3.Quantum.Foundation.AdjacentConfirmationPerturbation
