/- GID: D5/S3/Quantum/Foundation/OriginalStateCover
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalStateCover
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original states lie between a pure point and its entire exclusion ball. -/

import D5.S3.Quantum.Foundation.OriginalWidthContact
import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.Normalize

/-! Affine diameters and complete exclusion-ball decompositions on the original carriers. -/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.OriginalStateCover

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces

private theorem support_positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : Set E} (hzero : (0 : E) ∈ interior L) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    {v : E} (hmax : ∀ w ∈ L, f w ≤ f v) : 0 < f v := by
  by_contra! hn
  have hle (w : E) : f w ≤ 0 := by
    have ht : ∀ᶠ t : ℝ in 𝓝 0, t • w ∈ L :=
      (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
        (by simpa using mem_interior_iff_mem_nhds.mp hzero)
    obtain ⟨t, htpos, htw⟩ := ht.exists_gt
    have hh := (hmax _ htw).trans hn
    rw [map_smul, smul_eq_mul] at hh
    exact nonpos_of_mul_nonpos_right hh htpos
  apply hf
  ext w
  change f w = 0
  have hh := hle (-w)
  simp only [map_neg] at hh
  exact le_antisymm (hle w) (by linarith)

/-- A maximal reflected copy of a compact body touches a supporting hyperplane;
the paired point minimizes the same functional on the whole body. -/
theorem centered_affine_diameter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : Set E} (hcompact : IsCompact L) (hconvex : Convex ℝ L)
    (hzero : (0 : E) ∈ interior L) (hnonzero : ∃ z ∈ L, z ≠ 0) :
    ∃ (t : ℝ) (z : E) (f : E →L[ℝ] ℝ),
      0 < t ∧ z ∈ L ∧ (-t) • z ∈ L ∧
      0 < f ((-t) • z) ∧ f z < 0 ∧
      (∀ w ∈ L, f z ≤ f w) ∧ (∀ w ∈ L, f w ≤ f ((-t) • z)) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  let T : Set ℝ := {t | 0 ≤ t ∧ ∀ z ∈ L, (-t) • z ∈ L}
  have hsmall : r / (2 * R) ∈ T := by
    refine ⟨(div_pos hr (by positivity)).le, ?_⟩
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos (div_pos hr (by positivity))]
    calc
      r / (2 * R) * ‖z‖ ≤ r / (2 * R) * R :=
        mul_le_mul_of_nonneg_left (hbound z hz) (by positivity)
      _ = r / 2 := by field_simp
      _ < r := by linarith
  have hclosed : IsClosed T := by
    have hh : IsClosed (Ici 0 ∩ ⋂ z ∈ L, {t : ℝ | (-t) • z ∈ L}) :=
      isClosed_Ici.inter (isClosed_iInter fun z => isClosed_iInter fun _ =>
        hcompact.isClosed.preimage (continuous_neg.smul continuous_const))
    convert hh using 1
    ext t
    simp [T]
  obtain ⟨w, hw, hw0⟩ := hnonzero
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hTbound : T ⊆ Icc 0 (R / ‖w‖) := by
    intro t ht
    refine ⟨ht.1, (le_div_iff₀ hnw).mpr ?_⟩
    have hh := hbound _ (ht.2 w hw)
    simpa only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht.1] using hh
  have hTcompact : IsCompact T := isCompact_Icc.of_isClosed_subset hclosed hTbound
  obtain ⟨t, ht, hmax⟩ := hTcompact.exists_isMaxOn ⟨_, hsmall⟩ continuous_id.continuousOn
  have htpos : 0 < t := (div_pos hr (by positivity)).trans_le (hmax hsmall)
  have hcontact : ∃ z ∈ L, (-t) • z ∉ interior L := by
    by_contra! hall
    have hevent : ∀ᶠ s : ℝ in 𝓝 t, ∀ z ∈ L, (-s) • z ∈ interior L := by
      apply hcompact.eventually_forall_of_forall_eventually
      intro z hz
      have hcont : Continuous (fun a : ℝ × E => (-a.1) • a.2) :=
        (continuous_fst.neg).smul continuous_snd
      exact hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds (hall z hz))
    obtain ⟨s, hst, hs⟩ := hevent.exists_gt
    have hsT : s ∈ T := ⟨htpos.le.trans hst.le,
      fun z hz => interior_subset (hs z hz)⟩
    exact (not_lt_of_ge (hmax hsT)) hst
  obtain ⟨z, hz, hznot⟩ := hcontact
  obtain ⟨f, hf, hsupport⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hconvex hznot ⟨0, hzero⟩
  have hfpos := support_positive hzero f hf hsupport
  have hfz : f z < 0 := by
    have hh : 0 < -t * f z := by simpa only [map_smul, smul_eq_mul] using hfpos
    nlinarith
  refine ⟨t, z, f, htpos, hz, ht.2 z hz, hfpos, hfz, ?_, hsupport⟩
  intro a ha
  have hh := hsupport _ (ht.2 a ha)
  simp only [map_smul, smul_eq_mul] at hh
  nlinarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem interior_diameter
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {x : V} (hx : x ∈ intrinsicInterior ℝ (base C u))
    (hnon : (base C u).Nontrivial) :
    ∃ (a b : V) (s : ℝ) (f : V →ₗ[ℝ] ℝ),
      a ∈ base C u ∧ b ∈ base C u ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      proper C u f ∧ f a = 1 ∧ f b = 0 ∧ x = s • a + (1-s) • b := by
  let K := base C u
  let B := affineSpan ℝ K
  let E := B.direction
  let xB : B := ⟨x, subset_affineSpan ℝ K (intrinsicInterior_subset hx)⟩
  let : Nonempty B := ⟨xB⟩
  let e : E ≃ₜ B := Homeomorph.vaddConst xB
  let F : E →ᵃ[ℝ] V := B.subtype.comp (AffineEquiv.vaddConst ℝ xB).toAffineMap
  have hF (v : E) : F v = (v : V) + x := rfl
  let L : Set E := e ⁻¹' (Subtype.val ⁻¹' K)
  have hcompact : IsCompact L := e.isCompact_preimage.mpr
    (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (base_compact hc hs) (fun y hy => ⟨⟨y, subset_affineSpan ℝ K hy⟩, rfl⟩))
  have hconvex : Convex ℝ L := (base_convex C u).affine_preimage F
  have hzero : (0 : E) ∈ interior L := by
    rw [← e.preimage_interior]
    obtain ⟨b, hb, hbx⟩ := mem_intrinsicInterior.mp hx
    have he : e 0 = b := by apply Subtype.ext; simpa [e, xB] using hbx.symm
    change e 0 ∈ interior (Subtype.val ⁻¹' K : Set B)
    exact he.symm ▸ hb
  have hnonzero : ∃ z ∈ L, z ≠ 0 := by
    obtain ⟨y, hy, hyx⟩ := hnon.exists_ne x
    let yB : B := ⟨y, subset_affineSpan ℝ K hy⟩
    refine ⟨e.symm yB, ?_, ?_⟩
    · change (e (e.symm yB) : V) ∈ K
      simpa using hy
    · intro hz
      have he := congrArg (fun v : E => (e v : V)) hz
      exact hyx (by simpa [e, xB, yB] using he)
  obtain ⟨t,z,h,ht,hz,hv,hpos,hneg,hmin,hmax⟩ :=
    centered_affine_diameter hcompact hconvex hzero hnonzero
  obtain ⟨g, hg⟩ := h.toLinearMap.exists_extend
  have hgv (v : E) : g (v : V) = h v := LinearMap.congr_fun hg v
  have hgF (v : E) : g (F v) = h v + g x := by rw [hF,map_add,hgv]
  let a := F ((-t) • z)
  let b := F z
  have ha : a ∈ K := hv
  have hb : b ∈ K := hz
  have hgmin : ∀ y ∈ K, g b ≤ g y := by
    intro y hy
    let yB : B := ⟨y, subset_affineSpan ℝ K hy⟩
    let v := e.symm yB
    have hvmem : v ∈ L := by change (e (e.symm yB) : V) ∈ K; simpa using hy
    have hFy : F v = y := by change (e (e.symm yB) : V) = y; simp [yB]
    rw [← hFy,hgF,hgF]
    linarith [hmin v hvmem]
  have hgmax : ∀ y ∈ K, g y ≤ g a := by
    intro y hy
    let yB : B := ⟨y, subset_affineSpan ℝ K hy⟩
    let v := e.symm yB
    have hvmem : v ∈ L := by change (e (e.symm yB) : V) ∈ K; simpa using hy
    have hFy : F v = y := by change (e (e.symm yB) : V) = y; simp [yB]
    rw [← hFy,hgF,hgF]
    linarith [hmax v hvmem]
  have hgap : 0 < g a - g b := by dsimp [a,b]; rw [hgF,hgF]; linarith
  let f : V →ₗ[ℝ] ℝ := (g a-g b)⁻¹ • (g-g b • u)
  have hf : proper C u f := OriginalWidthContact.normalized_effect
    (base_compact hc hs) hs hgmin hgmax hgap
  have hfa : f a = 1 := by simp [f,ha.2,hgap.ne']
  have hfb : f b = 0 := by simp [f,hb.2]
  let s := (1+t)⁻¹
  have hspos : 0 < s := inv_pos.mpr (by linarith)
  have hsone : s < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  refine ⟨a,b,s,f,ha,hb,⟨hspos,hsone⟩,hf,hfa,hfb,?_⟩
  have hzsum : s * (-t) + (1-s) = 0 := by dsimp [s]; field_simp; ring
  have he : s • ((-t) • z) + (1-s) • z = 0 := by
    rw [smul_smul,← add_smul,hzsum,zero_smul]
  have hcombo := Convex.combo_affine_apply (f := F) (x := (-t) • z) (y := z)
    (a := s) (b := 1-s) (by ring)
  rw [he] at hcombo
  simpa [a,b,hF] using hcombo

private theorem interior_cover
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    {x : V} (hx : x ∈ intrinsicInterior ℝ (base C u)) (hnon : (base C u).Nontrivial) :
    ∃ (p : pure C u) (y : V) (s : ℝ) (f : V →ₗ[ℝ] ℝ),
      y ∈ exclusion C u p ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      proper C u f ∧ f p = 1 ∧ f y = 0 ∧ x = s • (p : V) + (1-s) • y := by
  obtain ⟨a,b,s,f,ha,hb,hs',hf,hfa,hfb,he⟩ := interior_diameter hc hs hx hnon
  have finish (a b : V) (s : ℝ) (f : V →ₗ[ℝ] ℝ)
      (ha : a ∈ base C u) (hb : b ∈ base C u) (hs' : s ∈ Ioo (0 : ℝ) 1)
      (hf : proper C u f) (hfa : f a = 1) (hfb : f b = 0)
      (he : x = s • a + (1-s) • b)
      (hsub : {z ∈ base C u | f z = 1}.Subsingleton) :
      ∃ (p : pure C u) (y : V) (s : ℝ) (f : V →ₗ[ℝ] ℝ),
        y ∈ exclusion C u p ∧ s ∈ Ioo (0 : ℝ) 1 ∧
        proper C u f ∧ f p = 1 ∧ f y = 0 ∧ x = s • (p : V) + (1-s) • y := by
    have hsingle := hsub.eq_singleton_of_mem (show a ∈ {z ∈ base C u | f z = 1} from ⟨ha,hfa⟩)
    have hap : a ∈ pure C u := isExtreme_singleton.mp
      (hsingle ▸ (OriginalWidthContact.top_exposed hf).isExtreme)
    exact ⟨⟨a,hap⟩,b,s,f,⟨hb,f,⟨hf,hfa⟩,hfb⟩,hs',hf,hfa,hfb,he⟩
  rcases OriginalWidthContact.contact_face_subsingleton hc hs hg hB hinj hf ha hb hfa hfb with htop | hbottom
  · exact finish a b s f ha hb hs' hf hfa hfb he htop
  · have hcomp : proper C u (u-f) := by
      intro z hz
      have hh := hf z hz
      simp only [LinearMap.sub_apply]
      constructor <;> linarith
    have hswap : {z ∈ base C u | (u-f) z = 1} = {z ∈ base C u | f z = 0} := by
      ext z
      constructor <;> rintro ⟨hz,hh⟩ <;> refine ⟨hz,?_⟩ <;>
        simp only [LinearMap.sub_apply,hz.2] at * <;> linarith
    apply finish b a (1-s) (u-f) hb ha ⟨by linarith [hs'.2],by linarith [hs'.1]⟩ hcomp
      (by simp [hb.2,hfb]) (by simp [ha.2,hfa])
      (by convert he using 1; module)
    rwa [hswap]

private theorem radial_decomposition
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (b : ExclusionChart C u p) {y : V} (hy : y ∈ exclusion C u p) :
    ∃ (q r : pure C u) (s : ℝ),
      (q : V) ∈ exclusion C u p ∧ (r : V) ∈ exclusion C u p ∧
      s ∈ Icc (0 : ℝ) 1 ∧ (r : V) = (2 : ℝ) • b.param 0 - (q : V) ∧
      y = s • (q : V) + (1-s) • (r : V) := by
  obtain ⟨v,hv,rfl⟩ := b.whole.symm ▸ hy
  have hvnorm : ‖v‖ ≤ 1 := by simpa using hv
  have hdir : ∃ n : EuclideanSpace ℝ (Fin b.dim), ‖n‖ = 1 ∧ v = ‖v‖ • n := by
    by_cases hz : v = 0
    · let i : Fin b.dim := ⟨0,b.dim_pos⟩
      exact ⟨EuclideanSpace.single i 1,by simp [EuclideanSpace.single],by simp [hz]⟩
    · exact ⟨NormedSpace.normalize v,NormedSpace.norm_normalize hz,
        (NormedSpace.norm_smul_normalize v).symm⟩
  obtain ⟨n,hn,hvn⟩ := hdir
  have hpure (w : EuclideanSpace ℝ (Fin b.dim)) (hw : ‖w‖ = 1) :
      b.param w ∈ exclusion C u p ∩ pure C u := by
    rw [OriginalFacePolarity.chart_boundary hc hs hg hB p b]
    exact ⟨w,by simpa using hw,rfl⟩
  have hq := hpure n hn
  have hr := hpure (-n) (by simpa using hn)
  let s := (1+‖v‖)/2
  have hsn : s ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [s]; positivity,by dsimp [s]; linarith⟩
  have hsum : s • n + (1-s) • (-n) = v := by
    rw [hvn,smul_neg,← sub_eq_add_neg,← sub_smul]
    congr 1
    dsimp [s]
    ring
  have hcombo := Convex.combo_affine_apply (f := b.param) (x := n) (y := -n)
    (a := s) (b := 1-s) (by ring)
  rw [hsum] at hcombo
  have hmid := Convex.combo_affine_apply (f := b.param) (x := n) (y := -n)
    (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num)
  have hzero : (1/2 : ℝ) • n + (1/2 : ℝ) • (-n) = 0 := by simp
  rw [hzero] at hmid
  refine ⟨⟨b.param n,hq.2⟩,⟨b.param (-n),hr.2⟩,s,hq.1,hr.1,hsn,?_,hcombo⟩
  have hh := congrArg (fun z : V => (2 : ℝ) • z) hmid
  simp only [smul_add,smul_smul] at hh
  norm_num at hh
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hh.symm)

/-- Every original state has a pure--whole-exclusion decomposition. Interior
weights are strict, and the same full-domain effect distinguishes its endpoints.
Every chart of that same entire ball supplies pure radial antipodes, including
its center and sphere. No relation between the two antipodes is asserted. -/
theorem original_state_cover [Nontrivial V]
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p)) :
    base C u = ⋃ p : pure C u, convexHull ℝ (insert (p : V) (exclusion C u p)) ∧
    ∀ x ∈ base C u,
      ∃ (p : pure C u) (y : V) (s : ℝ) (f : V →ₗ[ℝ] ℝ),
        y ∈ exclusion C u p ∧ s ∈ Icc (0 : ℝ) 1 ∧
        proper C u f ∧ f p = 1 ∧ f y = 0 ∧
        x = s • (p : V) + (1-s) • y ∧
        (x ∈ intrinsicInterior ℝ (base C u) → s ∈ Ioo (0 : ℝ) 1) ∧
        ∀ b : ExclusionChart C u p,
          ∃ (q r : pure C u) (t : ℝ),
            (q : V) ∈ exclusion C u p ∧ (r : V) ∈ exclusion C u p ∧
            t ∈ Icc (0 : ℝ) 1 ∧ (r : V) = (2 : ℝ) • b.param 0 - (q : V) ∧
            y = t • (q : V) + (1-t) • (r : V) ∧
            x = s • (p : V) + (1-s) • (t • (q : V) + (1-t) • (r : V)) := by
  classical
  have all := exclusion_ball_faces hc hs hg hB
  obtain ⟨p₀⟩ := OriginalFacePolarity.pure_nonempty hc hs hg
  have hnon : (base C u).Nontrivial :=
    (all.1 p₀).1.mono (all.1 p₀).2.2.2.2.1.subset
  have cover (x : V) (hx : x ∈ base C u) :
      ∃ (p : pure C u) (y : V) (s : ℝ) (f : V →ₗ[ℝ] ℝ),
        y ∈ exclusion C u p ∧ s ∈ Icc (0 : ℝ) 1 ∧
        proper C u f ∧ f p = 1 ∧ f y = 0 ∧
        x = s • (p : V) + (1-s) • y ∧
        (x ∈ intrinsicInterior ℝ (base C u) → s ∈ Ioo (0 : ℝ) 1) := by
    by_cases hri : x ∈ intrinsicInterior ℝ (base C u)
    · obtain ⟨p,y,s,f,hy,hs',hf,hfp,hfy,he⟩ := interior_cover hc hs hg hB hinj hri hnon
      exact ⟨p,y,s,f,hy,⟨hs'.1.le,hs'.2.le⟩,hf,hfp,hfy,he,fun _ => hs'⟩
    · by_cases hpure : x ∈ pure C u
      · let p : pure C u := ⟨x,hpure⟩
        obtain ⟨y,hy⟩ := (all.1 p).1.nonempty
        obtain ⟨f,hf,hzero⟩ := (all.1 p).2.2.2.2.2.2
        have hfy : f y = 0 := (hzero ▸ hy).2
        exact ⟨p,y,1,f,hy,⟨by norm_num,le_rfl⟩,hf.1,hf.2,hfy,
          by simp [p],fun h => (hri h).elim⟩
      · have hfront : x ∈ intrinsicFrontier ℝ (base C u) := by
          rw [← closure_sdiff_intrinsicInterior]
          exact ⟨subset_closure hx,hri⟩
        obtain ⟨p,hp⟩ := MixedExclusionGeometry.frontier_covered hc hs hg hfront
        obtain ⟨f,hf,hzero⟩ := (all.1 p).2.2.2.2.2.2
        have hfx : f x = 0 := (hzero ▸ hp).2
        exact ⟨p,x,0,f,hp,⟨le_rfl,by norm_num⟩,hf.1,hf.2,hfx,
          by simp,fun h => (hri h).elim⟩
  constructor
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨p,y,s,f,hy,hs',_,_,_,he,_⟩ := cover x hx
      apply mem_iUnion.mpr
      refine ⟨p,he.symm ▸ ?_⟩
      exact (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (mem_insert _ _))
        (subset_convexHull ℝ _ (mem_insert_of_mem _ hy)) hs'.1
        (sub_nonneg.mpr hs'.2) (by ring)
    · intro x hx
      obtain ⟨p,hp⟩ := mem_iUnion.mp hx
      apply convexHull_min (s := insert (p : V) (exclusion C u p)) ?_ (base_convex C u) hp
      exact insert_subset (pure_mem p) (fun _ hy => hy.1)
  · intro x hx
    obtain ⟨p,y,s,f,hy,hs',hf,hfp,hfy,he,hstrict⟩ := cover x hx
    refine ⟨p,y,s,f,hy,hs',hf,hfp,hfy,he,hstrict,?_⟩
    intro b
    obtain ⟨q,r,t,hq,hr,ht,hanti,hyform⟩ := radial_decomposition hc hs hg hB p b hy
    exact ⟨q,r,t,hq,hr,ht,hanti,hyform,by rwa [← hyform]⟩

end D5.S3.Quantum.Foundation.OriginalStateCover
