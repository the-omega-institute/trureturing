/- GID: D5/S3/Quantum/Foundation/UniqueConfirmationDensity
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/UniqueConfirmationDensity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Joint original state-effect compactness controls limits of exclusion labels. -/

import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import D5.S3.Quantum.Foundation.OriginalWidthContact

/-! All state and effect carriers below are the original full cone carriers.
No closedness of the pure-state set or weak Pair premise is used. -/

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.UniqueConfirmationDensity

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open WholePairBallConfirmation ContinuousFrameSum SingleLabelNormalBody

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Uniqueness concerns the entire original effect fiber, not the exclusion-label fiber. -/
def UniqueConfirmer (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : pure C u) : Prop :=
  ∃ e : V →ₗ[ℝ] ℝ, confirms C u p e ∧
    (∀ z ∈ exclusion C u p, e z = 0) ∧
    ∀ f : V →ₗ[ℝ] ℝ, confirms C u p f →
      (∀ z ∈ exclusion C u p, f z = 0) → f = e

private theorem affine_zero_inside_ball {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →ᵃ[ℝ] ℝ) (hpos : ∀ z, ‖z‖ ≤ 1 → 0 ≤ f z)
    {z : E} (hz : ‖z‖ < 1) (hfz : f z = 0) : ∀ w, f w = 0 := by
  obtain ⟨v, hv⟩ := affine_riesz f
  have hb := affine_nonneg_bound (fun w hw => by rw [← hv]; exact hpos w hw)
  have h0 : 0 ≤ f 0 := hpos 0 (by simp)
  have hi : -⟪v, z⟫ ≤ ‖v‖ * ‖z‖ := by
    have h := real_inner_le_norm (-v) z
    simpa only [inner_neg_left, norm_neg] using h
  have hvan : f 0 = 0 := by
    have he := hv z
    nlinarith [norm_nonneg v, norm_nonneg z, mul_le_mul_of_nonneg_right hb (norm_nonneg z)]
  have hv0 : v = 0 := norm_le_zero_iff.mp (hvan ▸ hb)
  intro w
  rw [hv, hv0, hvan, inner_zero_left, add_zero]

omit [FiniteDimensional ℝ V] in
private theorem zero_on_exclusion_of_zero_interior
    (hB : exclusionBalls C u) (p : pure C u) (f : V →ₗ[ℝ] ℝ)
    (hpos : ∀ z ∈ C, 0 ≤ f z) {x : V}
    (hx : x ∈ intrinsicInterior ℝ (exclusion C u p)) (hfx : f x = 0) :
    ∀ z ∈ exclusion C u p, f z = 0 := by
  obtain ⟨b⟩ := hB p
  rw [MixedExclusionGeometry.chart_intrinsic p b] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hf := affine_zero_inside_ball (f.toAffineMap.comp b.param)
    (fun w hw => hpos _ (b.whole ▸ mem_image_of_mem b.param (by simpa using hw)).1.1)
    (by simpa using hz) hfx
  intro y hy
  obtain ⟨w, _, rfl⟩ := b.whole.symm ▸ hy
  exact hf w

/-- Incidence points converging to the relative interior of D(p) force the full
original pure-label sequence to converge to p, even when P is not closed. -/
theorem original_label_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) {x : V} (hx : x ∈ intrinsicInterior ℝ (exclusion C u p))
    (pn : ℕ → pure C u) (xn : ℕ → V)
    (hxn : ∀ n, xn n ∈ exclusion C u (pn n))
    (hlim : Tendsto xn atTop (𝓝 x)) :
    Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V)) := by
  classical
  have hall := (exclusion_ball_faces hc hs hg hB).1
  choose e he hz using fun n => (hall (pn n)).2.2.2.2.2.2
  let ec (n : ℕ) : V →L[ℝ] ℝ := (e n).toContinuousLinearMap
  let se (n : ℕ) : V × (V →L[ℝ] ℝ) := (pn n, ec n)
  have hmem (n : ℕ) : se n ∈ base C u ×ˢ effects C u := ⟨pure_mem (pn n), (he n).1⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨⟨s, f⟩, ⟨hsK, hf⟩, ms, hms, hsf⟩ :=
    ((base_compact hc hs).prod (effects_compact hs hg)).tendsto_subseq (fun n => hmem (ns n))
  change Tendsto (fun n => ((pn (ns (ms n)) : V), ec (ns (ms n))))
    atTop (𝓝 (s, f)) at hsf
  have hslim : Tendsto (fun n => (pn (ns (ms n)) : V)) atTop (𝓝 s) :=
    (continuous_fst.tendsto (s, f)).comp hsf
  have hflim : Tendsto (fun n => ec (ns (ms n))) atTop (𝓝 f) :=
    (continuous_snd.tendsto (s, f)).comp hsf
  have hxlim : Tendsto (fun n => xn (ns (ms n))) atTop (𝓝 x) :=
    hlim.comp (hns.comp hms.tendsto_atTop)
  have heval : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hfs : f s = 1 := by
    have ht := (heval.tendsto (f, s)).comp (hflim.prodMk_nhds hslim)
    have hh : (fun n => ec (ns (ms n)) (pn (ns (ms n)))) = fun _ : ℕ => (1 : ℝ) := by
      funext n
      exact (he _).2
    change Tendsto (fun n => ec (ns (ms n)) (pn (ns (ms n)))) atTop (𝓝 (f s)) at ht
    rw [hh] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hfx : f x = 0 := by
    have ht := (heval.tendsto (f, x)).comp (hflim.prodMk_nhds hxlim)
    have hh : (fun n => ec (ns (ms n)) (xn (ns (ms n)))) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact (show xn (ns (ms n)) ∈ {z | z ∈ base C u ∧ e (ns (ms n)) z = 0}
        from hz _ ▸ hxn _).2
    change Tendsto (fun n => ec (ns (ms n)) (xn (ns (ms n)))) atTop (𝓝 (f x)) at ht
    rw [hh] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hzero := zero_on_exclusion_of_zero_interior hB p f.toLinearMap
    (fun z hz => (hf z hz).1) hx hfx
  have htop := OriginalWidthContact.top_exposed hf
  have hsingle := OriginalWidthContact.top_subsingleton_of_zero_exclusion
    hc hs hg hB hinj hf p hzero
  have hface : {z ∈ base C u | f z = 1} = {s} :=
    hsingle.eq_singleton_of_mem ⟨hsK, hfs⟩
  have hsP : s ∈ pure C u := isExtreme_singleton.mp (hface ▸ htop.isExtreme)
  let q : pure C u := ⟨s, hsP⟩
  have hsub : exclusion C u p ⊆ exclusion C u q := by
    intro z hzD
    exact ⟨hzD.1, f.toLinearMap, ⟨hf, hfs⟩, hzero z hzD⟩
  obtain ⟨bq⟩ := hB q
  have heq := chart_face_eq bq (hall p).2.2.1
    ((hall p).2.2.2.2.1.mono (hall q).2.2.2.2.1.subset hsub) (hall p).1
  have hsp : s = (p : V) := congrArg Subtype.val (hinj heq).symm
  exact ⟨ms, hsp ▸ hslim⟩

private theorem inner_ball_support_cross {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {z y : E} {r : ℝ} (hr : 0 < r) (hy : dist y z = r)
    (f g : E →ᵃ[ℝ] ℝ)
    (hf : ∀ w ∈ Metric.closedBall z r, 0 ≤ f w)
    (hg : ∀ w ∈ Metric.closedBall z r, 0 ≤ g w)
    (hfy : f y = 0) (hgy : g y = 0) :
    ∀ a b, f a * g b = g a * f b := by
  let n : E := r⁻¹ • (z - y)
  let b : E →ᵃ[ℝ] E := AffineMap.const ℝ E z + r • AffineMap.id ℝ E
  have hbapply (w : E) : b w = z + r • w := rfl
  have hn : ‖n‖ = 1 := by
    rw [show ‖n‖ = |r⁻¹| * ‖z - y‖ by simp [n, norm_smul]]
    rw [abs_of_pos (inv_pos.mpr hr), ← dist_eq_norm, dist_comm, hy, inv_mul_cancel₀ hr.ne']
  have hbn : b (-n) = y := by
    simp only [hbapply, n, smul_neg, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hball {w : E} (hw : ‖w‖ ≤ 1) : b w ∈ Metric.closedBall z r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [hbapply, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hb : Function.Surjective b := by
    intro w
    refine ⟨r⁻¹ • (w - z), ?_⟩
    simp only [hbapply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have formula (k : E →ᵃ[ℝ] ℝ) (hk : ∀ w ∈ Metric.closedBall z r, 0 ≤ k w)
      (hky : k y = 0) : ∀ w, k (b w) = k z * (1 + ⟪n, w⟫) := by
    have hh := affine_zero_antipode (k.comp b) hn (fun w hw => hk _ (hball hw))
      (by simpa only [AffineMap.comp_apply, hbn] using hky)
    have hzero : (k.comp b) n / 2 = k z := by
      have hh0 := hh 0
      change k (b 0) = _ at hh0
      rw [show b 0 = z by simp only [hbapply, smul_zero, add_zero]] at hh0
      simpa only [inner_zero_right, add_zero, mul_one] using hh0.symm
    intro w
    calc
      k (b w) = (k.comp b) n / 2 * (1 + ⟪n, w⟫) := hh w
      _ = k z * (1 + ⟪n, w⟫) := by rw [hzero]
  intro a c
  obtain ⟨a, rfl⟩ := hb a
  obtain ⟨c, rfl⟩ := hb c
  rw [formula f hf hfy a, formula f hf hfy c,
    formula g hg hgy a, formula g hg hgy c]
  ring

private theorem contact_normalized_unique {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hc : IsClosed (C : Set V))
    (a : E →ᵃ[ℝ] V) (hwhole : base C u ⊆ Set.range a)
    {z y : E} {r : ℝ} (hr : 0 < r) (hy : dist y z = r)
    (hball : ∀ w ∈ Metric.closedBall z r, a w ∈ base C u)
    (f g : V →ₗ[ℝ] ℝ) (hf : ∀ v ∈ C, 0 ≤ f v) (hg' : ∀ v ∈ C, 0 ≤ g v)
    (hfy : f (a y) = 0) (hgy : g (a y) = 0)
    {c : V} (hcK : c ∈ base C u) (hfc : f c = 1) (hgc : g c = 1) : f = g := by
  have hcross := inner_ball_support_cross hr hy (f.toAffineMap.comp a) (g.toAffineMap.comp a)
    (fun w hw => hf _ (hball w hw).1) (fun w hw => hg' _ (hball w hw).1) hfy hgy
  obtain ⟨d, hd⟩ := hwhole hcK
  have heq (q : pure C u) : f q = g q := by
    obtain ⟨v, hv⟩ := hwhole (pure_mem q)
    have hh := hcross v d
    change f (a v) * g (a d) = g (a v) * f (a d) at hh
    simpa only [hv, hd, hfc, hgc, mul_one] using hh
  apply LinearMap.ext_on (pure_span (base_compact hc hs) hs hg)
  intro v hv
  exact heq ⟨v, hv⟩

private theorem contact_not_pure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (a : E →ᵃ[ℝ] V) (hwhole : base C u ⊆ Set.range a)
    {z y : E} {r : ℝ} (hr : 0 < r) (hy : dist y z = r)
    (hball : ∀ w ∈ Metric.closedBall z r, a w ∈ base C u) :
    a y ∉ pure C u := by
  intro hyP
  let q : pure C u := ⟨a y, hyP⟩
  obtain ⟨b⟩ := hB q
  have hq : SingleLabel C u q := fun s hs => hinj hs
  obtain ⟨rho, hrho, _, hinner⟩ := slope_body_inradius hc hs hg hB q hq b
  have hsingle : (slopeBody b).Subsingleton := by
    rintro v ⟨f, hf, rfl⟩ w ⟨g, hg', rfl⟩
    have hfg := contact_normalized_unique hs hg hc a hwhole hr hy hball
      f.toLinearMap g.toLinearMap hf.1 hg'.1 hf.2.1 hg'.2.1
      (show b.param 0 ∈ base C u from
        (b.whole ▸ mem_image_of_mem b.param (by simp)).1) hf.2.2 hg'.2.2
    have hfg' : f = g := by
      ext v
      exact LinearMap.congr_fun hfg v
    exact congrArg (slope b) hfg'
  let i : Fin b.dim := ⟨0, b.dim_pos⟩
  let v : EuclideanSpace ℝ (Fin b.dim) := rho • EuclideanSpace.single i 1
  have hv : ‖v‖ = rho := by
    simp [v, norm_smul, Real.norm_eq_abs, abs_of_pos hrho, EuclideanSpace.single]
  have hzmem : (0 : EuclideanSpace ℝ (Fin b.dim)) ∈ slopeBody b :=
    hinner (by simpa using hrho.le)
  have hvmem : v ∈ slopeBody b := hinner (by simpa only [Metric.mem_closedBall,
    dist_zero_right, hv] using (le_rfl : rho ≤ rho))
  have hzero : v = 0 := hsingle hvmem hzmem
  rw [hzero, norm_zero] at hv
  linarith

/-- Every original exclusion-relative interior point is approached by relative
interior points with unique original confirming EFFECT fibers and converging
original pure labels. The relative closure of those labels is the entire P. -/
theorem original_unique_confirmer_density
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p)) :
    (∀ (p : pure C u) (x : V), x ∈ intrinsicInterior ℝ (exclusion C u p) →
      ∃ (pn : ℕ → pure C u) (xn : ℕ → V),
        (∀ n, UniqueConfirmer C u (pn n) ∧
          xn n ∈ intrinsicInterior ℝ (exclusion C u (pn n))) ∧
        Tendsto xn atTop (𝓝 x) ∧ Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V))) ∧
    closure {p : pure C u | UniqueConfirmer C u p} = Set.univ := by
  classical
  have hall := (exclusion_ball_faces hc hs hg hB).1
  have approx (p : pure C u) (x : V)
      (hx : x ∈ intrinsicInterior ℝ (exclusion C u p)) :
      ∃ (pn : ℕ → pure C u) (xn : ℕ → V),
        (∀ n, UniqueConfirmer C u (pn n) ∧
          xn n ∈ intrinsicInterior ℝ (exclusion C u (pn n))) ∧
        Tendsto xn atTop (𝓝 x) ∧ Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V)) := by
    let K := base C u
    let A := affineSpan ℝ K
    let pA : A := ⟨p, subset_affineSpan ℝ K (pure_mem p)⟩
    let : Nonempty A := ⟨pA⟩
    let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ A.direction))
    let l : E ≃ₗ[ℝ] A.direction := LinearEquiv.ofFinrankEq _ _ (by simp [E])
    let e : E ≃ᵃ[ℝ] A := l.toAffineEquiv.trans (AffineEquiv.vaddConst ℝ pA)
    let eh := e.toContinuousAffineEquiv.toHomeomorph
    let a : E →ᵃ[ℝ] V := A.subtype.comp e.toAffineMap
    let S : Set E := a ⁻¹' K
    let KA : Set A := ((↑) : A → V) ⁻¹' K
    have hpre : S = eh ⁻¹' KA := rfl
    have hwhole : K ⊆ Set.range a := by
      intro v hv
      refine ⟨e.symm ⟨v, subset_affineSpan ℝ K hv⟩, ?_⟩
      simp [a]
    have hcompact : IsCompact S := by
      rw [hpre]
      exact eh.isClosedEmbedding.isCompact_preimage
        (A.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage
          (base_compact hc hs))
    have hconv : Convex ℝ S := (base_convex C u).affine_preimage a
    have hnon : (interior S).Nonempty := by
      obtain ⟨v, hv⟩ := Set.Nonempty.intrinsicInterior (base_convex C u) ⟨p, pure_mem p⟩
      obtain ⟨v, hv, _⟩ := mem_intrinsicInterior.mp hv
      rw [hpre, ← eh.preimage_interior]
      refine ⟨e.symm v, ?_⟩
      simpa [eh] using hv
    have hxK : x ∈ K := (intrinsicInterior_subset hx).1
    let xA : A := ⟨x, subset_affineSpan ℝ K hxK⟩
    let x0 : E := e.symm xA
    have hax : a x0 = x := by simp [a, x0, xA]
    have hxfront : x0 ∈ frontier S := by
      have hxf := MixedExclusionGeometry.exclusion_frontier hc hs hg hB p
        (intrinsicInterior_subset hx)
      obtain ⟨v, hv, hvx⟩ := mem_intrinsicFrontier.mp hxf
      have heq : v = xA := Subtype.ext hvx
      rw [hpre, ← eh.preimage_frontier]
      simpa [eh, x0, ← heq] using hv
    have hproper : S ≠ univ := by
      intro heq
      simp [heq] at hxfront
    have hclosure : x0 ∈ closure (interior S) := by
      rw [hconv.closure_interior_eq_closure_of_nonempty_interior hnon,
        hcompact.isClosed.closure_eq]
      exact hcompact.isClosed.frontier_subset hxfront
    obtain ⟨zn, hzn, hzlim⟩ := mem_closure_iff_seq_limit.mp hclosure
    choose yn hyn hyd using fun n =>
      exists_mem_frontier_infDist_compl_eq_dist (interior_subset (hzn n)) hproper
    let rn (n : ℕ) := Metric.infDist (zn n) Sᶜ
    have hrpos (n : ℕ) : 0 < rn n := by
      apply (Metric.infDist_pos_iff_notMem_closure (nonempty_compl.mpr hproper)).mp
      simpa only [closure_compl, mem_compl_iff, not_not] using hzn n
    have hdist (n : ℕ) : dist (yn n) (zn n) = rn n := by
      rw [dist_comm]
      exact (hyd n).symm
    have hball (n : ℕ) : ∀ w ∈ Metric.closedBall (zn n) (rn n), a w ∈ K := by
      intro w hw
      exact hcompact.isClosed.closure_subset
        (Metric.closedBall_infDist_compl_subset_closure (interior_subset (hzn n)) hw)
    have hfront (n : ℕ) : a (yn n) ∈ intrinsicFrontier ℝ K := by
      refine mem_intrinsicFrontier.mpr ⟨e (yn n), ?_, rfl⟩
      have hh := hyn n
      rw [hpre, ← eh.preimage_frontier] at hh
      exact hh
    choose pn hpinc using fun n => MixedExclusionGeometry.frontier_covered hc hs hg (hfront n)
    have hnopure (n : ℕ) : a (yn n) ∉ pure C u :=
      contact_not_pure hc hs hg hB hinj a hwhole (hrpos n) (hdist n) (hball n)
    have hri (n : ℕ) : a (yn n) ∈ intrinsicInterior ℝ (exclusion C u (pn n)) := by
      rw [MixedExclusionGeometry.exclusion_interior hc hs hg hB]
      exact ⟨hpinc n, hnopure n⟩
    choose en hen henz using fun n => (hall (pn n)).2.2.2.2.2.2
    have henzero (n : ℕ) : en n (a (yn n)) = 0 := (henz n ▸ hpinc n).2
    have hray (n : ℕ) :
        {f : V →ₗ[ℝ] ℝ | (∀ v ∈ C, 0 ≤ f v) ∧ f (a (yn n)) = 0} =
          {f | ∃ t : ℝ, 0 ≤ t ∧ f = t • en n} := by
      ext f
      constructor
      · rintro ⟨hf, hfy⟩
        refine ⟨f (pn n), hf _ (pure_mem (pn n)).1, ?_⟩
        have hcross := inner_ball_support_cross (hrpos n) (hdist n)
          (f.toAffineMap.comp a) ((en n).toAffineMap.comp a)
          (fun w hw => hf _ (hball n w hw).1)
          (fun w hw => ((hen n).1 _ (hball n w hw).1).1) hfy (henzero n)
        obtain ⟨d, hd⟩ := hwhole (pure_mem (pn n))
        apply LinearMap.ext_on (pure_span (base_compact hc hs) hs hg)
        intro q hq
        obtain ⟨v, hv⟩ := hwhole (pure_mem (⟨q, hq⟩ : pure C u))
        have hh := hcross v d
        change f (a v) * en n (a d) = en n (a v) * f (a d) at hh
        simpa only [hv, hd, (hen n).2, mul_one, one_mul, LinearMap.smul_apply,
          smul_eq_mul, mul_comm] using hh
      · rintro ⟨t, ht, rfl⟩
        refine ⟨fun v hv => mul_nonneg ht (((hen n).1 v hv).1), ?_⟩
        simp only [LinearMap.smul_apply, smul_eq_mul, henzero n, mul_zero]
    have hpzero (n : ℕ) : UniqueConfirmer C u (pn n) := by
      refine ⟨en n, hen n, fun v hv => (henz n ▸ hv).2, ?_⟩
      intro f hf hfzero
      obtain ⟨t, _, hft⟩ := (Set.ext_iff.mp (hray n) f).mp
        ⟨fun v hv => (hf.1 v hv).1, hfzero _ (hpinc n)⟩
      have ht : t = 1 := by
        have hh := LinearMap.congr_fun hft (pn n)
        simpa only [LinearMap.smul_apply, smul_eq_mul, (hen n).2, hf.2, mul_one] using hh.symm
      simpa only [ht, one_smul] using hft
    have hnear (n : ℕ) : dist (yn n) x0 ≤ 2 * dist (zn n) x0 := by
      have hxc : x0 ∈ closure Sᶜ := by
        rw [closure_compl]
        exact hxfront.2
      have hrle : rn n ≤ dist (zn n) x0 := by
        dsimp only [rn]
        rw [← Metric.infDist_closure]
        exact Metric.infDist_le_dist_of_mem hxc
      have ht := dist_triangle (yn n) (zn n) x0
      rw [hdist n] at ht
      linarith
    have hylim : Tendsto yn atTop (𝓝 x0) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      have hzdist : Tendsto (fun n => dist (zn n) x0) atTop (𝓝 0) := by
        have hh : Tendsto (fun n => dist (zn n) x0) atTop (𝓝 (dist x0 x0)) :=
          hzlim.dist tendsto_const_nhds
        simpa only [dist_self] using hh
      exact squeeze_zero (fun _ => dist_nonneg) hnear
        (by simpa only [mul_zero] using tendsto_const_nhds.mul hzdist)
    have hxlim : Tendsto (fun n => a (yn n)) atTop (𝓝 x) := by
      simpa only [Function.comp_def, hax] using
        (a.continuous_of_finiteDimensional.tendsto x0).comp hylim
    exact ⟨pn, fun n => a (yn n), fun n => ⟨hpzero n, hri n⟩, hxlim,
      original_label_tendsto hc hs hg hB hinj p hx pn _ hpinc hxlim⟩
  refine ⟨approx, Set.eq_univ_of_forall ?_⟩
  intro p
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (hall p).2.2.1 (hall p).1.nonempty
  obtain ⟨pn, xn, hpn, _, hlim⟩ := approx p x hx
  exact mem_closure_of_tendsto (tendsto_subtype_rng.mpr hlim)
    (Eventually.of_forall (fun n => (hpn n).1))

end D5.S3.Quantum.Foundation.UniqueConfirmationDensity
