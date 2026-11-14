/- GID: D5/S3/Quantum/Foundation/ContinuousFrameSum
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ContinuousFrameSum
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Topology.Maps.Proper.Basic]
   utility: none
   digest: Original joint frames force compact pure carriers and continuous frame sums. -/

import D5.S3.Quantum.Foundation.OrthogonalJointCompletion
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Convex.Intrinsic

/-! Compact whole-domain frames and their original pure carrier. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.ContinuousFrameSum

open CircuitBalancedConfirmation FacetZeroGluing WholePairBallConfirmation
open ExclusionBallFaces OrthogonalJointCompletion

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The entire original proper interval, represented by continuous maps.
In finite dimension every original linear effect has this representation. -/
def effects (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Set (V →L[ℝ] ℝ) :=
  {f | proper C u f.toLinearMap}

omit [FiniteDimensional ℝ V] in
private theorem effects_closed (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) :
    IsClosed (effects C u) := by
  have he : effects C u = ⋂ x : V, ⋂ (_ : x ∈ C),
      {f : V →L[ℝ] ℝ | 0 ≤ f x ∧ f x ≤ u x} := by
    ext f
    simp [effects, proper]
  rw [he]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    (isClosed_le (f := fun _ : V →L[ℝ] ℝ => (0 : ℝ)) continuous_const
      (g := fun f => f x) (by fun_prop)).inter
      (isClosed_le (f := fun f : V →L[ℝ] ℝ => f x) (by fun_prop) continuous_const)

theorem effects_compact {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) : IsCompact (effects C u) := by
  have hint : (interior (C : Set V)).Nonempty := by
    apply C.convex.interior_nonempty_iff_affineSpan_eq_top.mpr
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ C.zero_mem), hg]
    rfl
  obtain ⟨v, hv⟩ := hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hv)
  have huv : 0 ≤ u v := by
    by_cases hz : v = 0
    · simp [hz]
    · exact (hs v (interior_subset hv) hz).le
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδe : δ < ε := by dsimp [δ]; linarith
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨effects_closed C u, isBounded_iff_forall_norm_le.mpr ⟨u v / δ, ?_⟩⟩
  intro f hf
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg huv hδ.le)
  intro x hx
  have hmem (y : V) (hy : ‖y‖ = 1) : v + δ • y ∈ C := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [norm_smul, abs_of_pos hδ, hy] using hδe
  have hp := (hf (v + δ • x) (hmem x hx)).1
  have hm := (hf (v + δ • -x) (hmem (-x) (by simpa using hx))).1
  have hvf := (hf v (interior_subset hv)).2
  simp only [map_add, map_smul, map_neg, smul_eq_mul] at hp hm
  change 0 ≤ f v + δ * f x at hp
  change 0 ≤ f v + δ * -f x at hm
  change f v ≤ u v at hvf
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · rw [← neg_div]
    exact (div_le_iff₀ hδ).mpr (by nlinarith)
  · exact (le_div_iff₀ hδ).mpr (by nlinarith)

theorem exclusion_injective [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) {p q : pure C u}
    (he : exclusion C u p = exclusion C u q) : p = q := by
  have hall := whole_joint_completion hc hs hg hB hW
  obtain ⟨r, s, ht⟩ := hall.2.1 p
  obtain ⟨t, hrt, _⟩ := hall.1 r s ht.2.2.2.2.1
  have hpr : (p : V) ∈ exclusion C u r :=
    (exclusion_symmetric p r).mp ⟨pure_mem r, ht.2.2.1⟩
  have hps : (p : V) ∈ exclusion C u s :=
    (exclusion_symmetric p s).mp ⟨pure_mem s, ht.2.2.2.1⟩
  have hqr : (q : V) ∈ exclusion C u r :=
    (exclusion_symmetric q r).mp (he ▸ ⟨pure_mem r, ht.2.2.1⟩)
  have hqs : (q : V) ∈ exclusion C u s :=
    (exclusion_symmetric q s).mp (he ▸ ⟨pure_mem s, ht.2.2.2.1⟩)
  apply Subtype.ext
  have hp : (p : V) = t := by
    have hh : (p : V) ∈ exclusion C u r ∩ exclusion C u s := ⟨hpr,hps⟩
    simpa [hrt.1] using hh
  have hq : (q : V) = t := by
    have hh : (q : V) ∈ exclusion C u r ∩ exclusion C u s := ⟨hqr,hqs⟩
    simpa [hrt.1] using hh
  exact hp.trans hq.symm

/-- Frames allow arbitrary states initially. Purity of their vertices is a theorem. -/
def frames (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) :
    Set ((Fin 3 → V) × (Fin 3 → (V →L[ℝ] ℝ))) :=
  {T : ((Fin 3 → V) × (Fin 3 → (V →L[ℝ] ℝ))) | (∀ i, T.1 i ∈ base C u) ∧ (∀ i, T.2 i ∈ effects C u) ∧
    (∀ i j, T.2 i (T.1 j) = if i = j then 1 else 0) ∧
    ∑ i, (T.2 i).toLinearMap = u}

private theorem frames_compact {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) : IsCompact (frames C u) := by
  let S := (univ.pi (fun _ : Fin 3 => base C u)).prod
    (univ.pi (fun _ : Fin 3 => effects C u))
  have hS : IsCompact S := (isCompact_univ_pi fun _ => base_compact hc hs).prod
    (isCompact_univ_pi fun _ => effects_compact hs hg)
  have hF : IsClosed (frames C u) := by
    have hK : IsClosed (base C u) := (base_compact hc hs).isClosed
    have he : frames C u =
        {T : ((Fin 3 → V) × (Fin 3 → (V →L[ℝ] ℝ))) | ∀ i, T.1 i ∈ base C u} ∩ {T : ((Fin 3 → V) × (Fin 3 → (V →L[ℝ] ℝ))) | ∀ i, T.2 i ∈ effects C u} ∩
        {T : ((Fin 3 → V) × (Fin 3 → (V →L[ℝ] ℝ))) | ∀ i j, T.2 i (T.1 j) = if i = j then 1 else 0} ∩
        {T : ((Fin 3 → V) × (Fin 3 → (V →L[ℝ] ℝ))) | ∀ v : V, ∑ i, T.2 i v = u v} := by
      ext T
      simp only [frames, mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨h1,h2,h3,h4⟩
        refine ⟨⟨⟨h1,h2⟩,h3⟩,fun v => ?_⟩
        simpa using LinearMap.congr_fun h4 v
      · rintro ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩
        exact ⟨h1,h2,h3,LinearMap.ext h4⟩
    rw [he]
    simp only [ofPred_forall]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · exact isClosed_iInter fun i => hK.preimage (by fun_prop)
    · exact isClosed_iInter fun i => (effects_closed C u).preimage (by fun_prop)
    · exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_iInter fun v => isClosed_eq (by fun_prop) continuous_const
  exact hS.of_isClosed_subset hF (by
    intro T hT
    exact ⟨fun i _ => hT.1 i, fun i _ => hT.2.1 i⟩)

private theorem frame_vertex_pure [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) {T} (hT : T ∈ frames C u) : T.1 0 ∈ pure C u := by
  have hK := base_compact hc hs
  obtain ⟨geom, _, _⟩ := exclusion_ball_faces hc hs hg hB
  let a := T.2 0
  let F := a.toExposed (base C u)
  have hex : IsExposed ℝ (base C u) F := ContinuousLinearMap.toExposed.isExposed
  have hone (x : V) : x ∈ F ↔ x ∈ base C u ∧ a x = 1 := by
    constructor
    · rintro ⟨hx, hm⟩
      refine ⟨hx, le_antisymm ?_ ?_⟩
      · simpa [hx.2] using (hT.2.1 0 x hx.1).2
      · have he := hT.2.2.1 0 0
        simpa [a, he] using hm (T.1 0) (hT.1 0)
    · rintro ⟨hx, hax⟩
      refine ⟨hx, fun y hy => ?_⟩
      rw [hax]
      simpa [hy.2] using (hT.2.1 0 y hy.1).2
  have hxF : T.1 0 ∈ F := (hone _).mpr ⟨hT.1 0, by simpa [a] using hT.2.2.1 0 0⟩
  have hFc := hex.isCompact hK
  obtain ⟨p, hp⟩ := hFc.extremePoints_nonempty ⟨_, hxF⟩
  have hpP : p ∈ pure C u := hex.isExtreme.extremePoints_subset_extremePoints hp
  have hsame : F.extremePoints ℝ ⊆ {p} := by
    intro q hq
    have hqP : q ∈ pure C u := hex.isExtreme.extremePoints_subset_extremePoints hq
    let p' : pure C u := ⟨p, hpP⟩
    let q' : pure C u := ⟨q, hqP⟩
    have hy (s : V) (hsF : s ∈ F) : T.1 1 ∈ exclusion C u s :=
      ⟨hT.1 1, a.toLinearMap, ⟨hT.2.1 0, (hone s).mp hsF |>.2⟩,
        by simpa [a] using hT.2.2.1 0 1⟩
    have hz (s : V) (hsF : s ∈ F) : T.1 2 ∈ exclusion C u s :=
      ⟨hT.1 2, a.toLinearMap, ⟨hT.2.1 0, (hone s).mp hsF |>.2⟩,
        by simpa [a] using hT.2.2.1 0 2⟩
    have hne : T.1 1 ≠ T.1 2 := by
      intro he
      have h1 := hT.2.2.1 1 1
      have h2 := hT.2.2.1 1 2
      rw [he] at h1
      norm_num at h1 h2
      linarith
    have hn : (exclusion C u p' ∩ exclusion C u q').Nontrivial :=
      ⟨T.1 1, ⟨hy p hp.1, hy q hq.1⟩, T.1 2, ⟨hz p hp.1, hz q hq.1⟩, hne⟩
    obtain ⟨bp⟩ := hB p'
    have he := chart_face_eq bp ((geom p').2.2.1.inter (geom q').2.2.1)
      (((geom p').2.2.2.2.1.inter (geom q').2.2.2.2.1).mono
        (geom p').2.2.2.2.1.subset inter_subset_left) hn
    obtain ⟨bq⟩ := hB q'
    have he' := chart_face_eq bq ((geom p').2.2.1.inter (geom q').2.2.1)
      (((geom p').2.2.2.2.1.inter (geom q').2.2.2.2.1).mono
        (geom q').2.2.2.2.1.subset inter_subset_right) hn
    have hpq := exclusion_injective hc hs hg hB hW (he.symm.trans he')
    exact (congrArg Subtype.val hpq).symm
  have hsub : F ⊆ {p} := by
    rw [← closure_convexHull_extremePoints hFc (hex.convex (base_convex C u))]
    exact closure_minimal (convexHull_min hsame (convex_singleton p)) isClosed_singleton
  have he := hsub hxF
  rw [Set.mem_singleton_iff] at he
  exact he ▸ hpP

private theorem pure_frame [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (p : V) (hp : p ∈ pure C u) :
    ∃ T ∈ frames C u, (∀ i, T.1 i ∈ pure C u) ∧ T.1 0 = p := by
  let p' : pure C u := ⟨p, hp⟩
  obtain ⟨q,r,ht⟩ := (whole_joint_completion hc hs hg hB hW).2.1 p'
  obtain ⟨geom,_,_⟩ := exclusion_ball_faces hc hs hg hB
  obtain ⟨a,ha,haz⟩ := (geom p').2.2.2.2.2.2
  obtain ⟨b,hb,hbz⟩ := (geom q).2.2.2.2.2.2
  have haA : common C u p' a := ⟨ha,fun x hx => (haz ▸ hx).2⟩
  have hbA : common C u q b := ⟨hb,fun x hx => (hbz ▸ hx).2⟩
  obtain ⟨hd,hap,haq,har,hbp,hbq,hbr,hdp,hdq,hdr,hsum⟩ := ht.2.2.2.2.2 a b haA hbA
  let T := (![p,q,r], ![a.toContinuousLinearMap,b.toContinuousLinearMap,
    (u-a-b).toContinuousLinearMap])
  refine ⟨T, ?_, ?_, rfl⟩
  · refine ⟨?_,?_,?_,?_⟩
    · intro i
      fin_cases i
      · exact pure_mem p'
      · exact pure_mem q
      · exact pure_mem r
    · intro i
      fin_cases i
      · exact ha.1
      · exact hb.1
      · exact hd.1.1
    · intro i j
      dsimp [p'] at hap hbp hdp
      fin_cases i <;> fin_cases j <;>
        simp [T,hap,haq,har,hbp,hbq,hbr,hp.1.2,(pure_mem q).2,(pure_mem r).2]
    · simpa [T,Fin.sum_univ_succ] using hsum
  · intro i
    fin_cases i
    · exact hp
    · exact q.property
    · exact r.property

/-- Compactness is derived from original W and joint completion; it is not an input. -/
theorem original_pure_compact [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) : IsCompact (pure C u) := by
  have he : pure C u = (fun T => T.1 0) '' frames C u := by
    apply Subset.antisymm
    · intro p hp
      obtain ⟨T,hT,_,he⟩ := pure_frame hc hs hg hB hW p hp
      exact ⟨T,hT,he⟩
    · rintro _ ⟨T,hT,rfl⟩
      exact frame_vertex_pure hc hs hg hB hW hT
  rw [he]
  exact (frames_compact hc hs hg).image (by fun_prop)

/-- The center of any chosen chart of each complete original exclusion ball. -/
def center {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hB : exclusionBalls C u) (p : pure C u) : V := (hB p).some.param 0

/-- The original point plus twice its exclusion-ball center. -/
def sumVector {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hB : exclusionBalls C u) (p : pure C u) : V := (p : V) + (2 : ℝ) • center hB p

/-- The original common-center condition, on all original pure points. -/
def commonCenter {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hB : exclusionBalls C u) : Prop := ∀ p q : pure C u, sumVector hB p = sumVector hB q

private theorem exclusion_pair_chart {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (b : ExclusionChart C u p) :
    ∃ x y : V, Nonempty (BallChart C u x y) ∧ pairBase C u x y = exclusion C u p := by
  obtain ⟨geom,_,_⟩ := exclusion_ball_faces hc hs hg hB
  obtain ⟨x,hx,y,hy,hxy⟩ := (geom p).1
  obtain ⟨F,hF⟩ := base_face_lift hs (geom p).2.2.1 (geom p).2.2.2.2.1
  have hsub : pairBase C u x y ⊆ exclusion C u p := by
    intro z hz
    rw [← hF]
    exact ⟨hz.2 F ((hF.symm ▸ hx).1) ((hF.symm ▸ hy).1),hz.1.2⟩
  have hx' : x ∈ pairBase C u x y := ⟨hx.1,fun _ hx _ => hx⟩
  have hy' : y ∈ pairBase C u x y := ⟨hy.1,fun _ _ hy => hy⟩
  have he := chart_face_eq b (pair_convex C u x y)
    ((pair_extreme C u x y).mono (geom p).2.2.2.2.1.subset hsub)
    ⟨x,hx',y,hy',hxy⟩
  exact ⟨x,y,⟨⟨b.dim,b.dim_pos,b.param,b.injective,b.whole.trans he.symm⟩⟩,he⟩

private theorem exclusion_coordinates {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p q : pure C u) (b : ExclusionChart C u p) (hq : (q : V) ∈ exclusion C u p) :
    ∃ n, ‖n‖ = 1 ∧ b.param n = q := by
  obtain ⟨n,hn,he⟩ := b.whole.symm ▸ hq
  obtain ⟨x,y,⟨b'⟩,hpair⟩ := exclusion_pair_chart hc hs hg hB p b
  let b'' : BallChart C u x y :=
    ⟨b.dim,b.dim_pos,b.param,b.injective,b.whole.trans hpair.symm⟩
  exact ⟨n,chart_pure_norm b'' (by simpa using hn) (by rw [he]; exact q.property),he⟩

private theorem orthogonal_center_sum {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p q r : pure C u) (hq : (q : V) ∈ exclusion C u p)
    (hr : (r : V) ∈ exclusion C u p) (hqr : excludes C u q r) :
    (q : V) + r = (2 : ℝ) • center hB p := by
  let b := (hB p).some
  obtain ⟨n,hn,hnq⟩ := exclusion_coordinates hc hs hg hB p q b hq
  obtain ⟨m,hm,hmr⟩ := exclusion_coordinates hc hs hg hB p r b hr
  obtain ⟨f,hf,hfr⟩ := hqr
  have mem (s) (hs : ‖s‖ ≤ 1) : b.param s ∈ base C u := by
    have hh : b.param s ∈ exclusion C u p := b.whole ▸ ⟨s,by simpa using hs,rfl⟩
    exact hh.1
  let g := (u-f).toAffineMap.comp b.param
  have hnon : ∀ s, ‖s‖ ≤ 1 → 0 ≤ g s := by
    intro s hs
    exact sub_nonneg.mpr (hf.1 _ (mem s hs).1).2
  have hz : g (-(-n)) = 0 := by simp [g,hnq,hf.2,(pure_mem q).2]
  have hform := affine_zero_antipode g (by simpa using hn : ‖-n‖ = 1) hnon hz
  have hgm : g m = 1 := by simp [g,hmr,hfr,(pure_mem r).2]
  have hcap : g (-n) ≤ 1 := by
    change u (b.param (-n)) - f (b.param (-n)) ≤ 1
    rw [(mem (-n) (by simpa using hn.le)).2]
    linarith [(hf.1 _ (mem (-n) (by simpa using hn.le)).1).1]
  have hcoeff : 0 ≤ g (-n) := hnon _ (by simpa using hn.le)
  have hinner : ⟪-n,m⟫ ≤ 1 := by simpa [hn,hm] using real_inner_le_norm (-n) m
  have hformula := hform m
  rw [hgm] at hformula
  have hprod := mul_nonneg hcoeff (sub_nonneg.mpr hinner)
  have hcoef1 : g (-n) = 1 := le_antisymm hcap (by nlinarith)
  have heq : ⟪-n,m⟫ = 1 := by rw [hcoef1] at hformula; linarith
  have hnm : -n = m := (inner_eq_one_iff_of_norm_eq_one (by simpa using hn) hm).mp heq
  have hmid : b.param 0 = (1/2 : ℝ) • (b.param n + b.param (-n)) := by
    simpa [midpoint_eq_smul_add] using b.param.map_midpoint n (-n)
  have : (1/2 : ℝ) • ((q : V) + r) = center hB p := by
    rw [hnm,hnq,hmr] at hmid
    exact hmid.symm
  calc
    (q : V) + r = (2 : ℝ) • ((1/2 : ℝ) • ((q : V) + r)) := by simp [smul_smul]
    _ = (2 : ℝ) • center hB p := congrArg _ this

private theorem joint_sum [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p q r : pure C u) (ht : jointThird C u p q r) :
    (p : V) + q + r = sumVector hB p ∧ sumVector hB p = sumVector hB q := by
  have hpq : (q : V) ∈ exclusion C u p := ⟨pure_mem q,ht.2.2.1⟩
  have hpr : (r : V) ∈ exclusion C u p := ⟨pure_mem r,ht.2.2.2.1⟩
  have hqp := (exclusion_symmetric p q).mp hpq
  have hqr : (r : V) ∈ exclusion C u q := ⟨pure_mem r,ht.2.2.2.2.1⟩
  have hs1 := orthogonal_center_sum hc hs hg hB p q r hpq hpr ht.2.2.2.2.1
  have hs2 := orthogonal_center_sum hc hs hg hB q p r hqp hqr ht.2.2.2.1
  dsimp [sumVector]
  constructor
  · rw [← hs1]; abel
  · rw [← hs1,← hs2]; abel

private theorem original_orthogonality_closed
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    IsClosed {s : pure C u × pure C u | excludes C u s.1 s.2} := by
  let E := effects C u
  letI : CompactSpace E := isCompact_iff_compactSpace.mp (effects_compact hs hg)
  let S : Set ((pure C u × pure C u) × E) :=
    {z | z.2.1 z.1.1 = 1 ∧ z.2.1 z.1.2 = 0}
  have hS : IsClosed S := (isClosed_eq (by fun_prop) continuous_const).inter
    (isClosed_eq (by fun_prop) continuous_const)
  have he : {s : pure C u × pure C u | excludes C u s.1 s.2} = Prod.fst '' S := by
    ext s
    constructor
    · rintro ⟨f,hf,hz⟩
      exact ⟨(s,⟨f.toContinuousLinearMap,hf.1⟩),⟨hf.2,hz⟩,rfl⟩
    · rintro ⟨⟨s,f⟩,hf,rfl⟩
      exact ⟨f.1.toLinearMap,⟨f.2,hf.1⟩,hf.2⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hS

/-- All original edges have the same frame sum. Continuity is obtained from the
actual compact original frame carrier, without a compactness hypothesis on P. -/
theorem original_continuous_frame_sum [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    :
    (weakPair C u →
    IsClosed {s : pure C u × pure C u | excludes C u s.1 s.2} ∧
    Continuous (sumVector hB) ∧
    (∀ p q : pure C u, excludes C u p q → sumVector hB p = sumVector hB q) ∧
    (commonCenter hB ↔ ∃ U : V, ∀ p : pure C u, sumVector hB p = U) ) ∧
    (pairProper C u → commonCenter hB) := by
  have hweak (hW : weakPair C u) :
    IsClosed {s : pure C u × pure C u | excludes C u s.1 s.2} ∧
    Continuous (sumVector hB) ∧
    (∀ p q : pure C u, excludes C u p q → sumVector hB p = sumVector hB q) ∧
    (commonCenter hB ↔ ∃ U : V, ∀ p : pure C u, sumVector hB p = U) := by
    have hP := original_pure_compact hc hs hg hB hW
    have hedge : ∀ p q : pure C u, excludes C u p q →
        sumVector hB p = sumVector hB q := by
      intro p q hpq
      obtain ⟨r,ht,_⟩ := (whole_joint_completion hc hs hg hB hW).1 p q hpq
      exact (joint_sum hc hs hg hB p q r ht).2
    have hnon : (pure C u).Nonempty := by
      by_contra hn
      have hh := pure_span (base_compact hc hs) hs hg
      rw [Set.not_nonempty_iff_eq_empty.mp hn,Submodule.span_empty] at hh
      exact bot_ne_top hh
    refine ⟨original_orthogonality_closed hs hg,?_,hedge,?_⟩
    · let S := frames C u ∩ {T | ∀ i, T.1 i ∈ pure C u}
      have hS : IsCompact S := (frames_compact hc hs hg).inter_right (by
        simp only [ofPred_forall]
        exact isClosed_iInter fun i => hP.isClosed.preimage (by fun_prop))
      letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
      let π : S → pure C u := fun T => ⟨T.1.1 0,T.2.2 0⟩
      have hπ : Continuous π := by fun_prop
      have hsurj : Function.Surjective π := by
        intro p
        obtain ⟨T,hT,hpure,he⟩ := pure_frame hc hs hg hB hW p p.property
        exact ⟨⟨T,hT,hpure⟩,Subtype.ext he⟩
      apply (hπ.isClosedMap.isQuotientMap hπ hsurj).continuous_iff.mpr
      have hsum : (sumVector hB) ∘ π = fun T : S => ∑ i, T.1.1 i := by
        funext T
        let p : pure C u := ⟨T.1.1 0,T.2.2 0⟩
        let q : pure C u := ⟨T.1.1 1,T.2.2 1⟩
        let r : pure C u := ⟨T.1.1 2,T.2.2 2⟩
        have hpq : excludes C u p q :=
          ⟨(T.1.2 0).toLinearMap,⟨T.2.1.2.1 0,by simpa using T.2.1.2.2.1 0 0⟩,
            by simpa using T.2.1.2.2.1 0 1⟩
        have hpr : (r : V) ∈ exclusion C u p :=
          ⟨T.2.1.1 2,(T.1.2 0).toLinearMap,
            ⟨T.2.1.2.1 0,by simpa using T.2.1.2.2.1 0 0⟩,
            by simpa using T.2.1.2.2.1 0 2⟩
        have hqr : (r : V) ∈ exclusion C u q :=
          ⟨T.2.1.1 2,(T.1.2 1).toLinearMap,
            ⟨T.2.1.2.1 1,by simpa using T.2.1.2.2.1 1 1⟩,
            by simpa using T.2.1.2.2.1 1 2⟩
        obtain ⟨s,ht,_⟩ := (whole_joint_completion hc hs hg hB hW).1 p q hpq
        have hrs : r = s := by
          apply Subtype.ext
          have hh : (r : V) ∈ exclusion C u p ∩ exclusion C u q := ⟨hpr,hqr⟩
          simpa [ht.1] using hh
        have he := (joint_sum hc hs hg hB p q s ht).1.symm
        rw [← hrs] at he
        simpa [Function.comp_def,π,p,q,r,Fin.sum_univ_succ,add_assoc] using he
      rw [hsum]
      fun_prop
    · constructor
      · intro h
        obtain ⟨p,hp⟩ := hnon
        exact ⟨sumVector hB ⟨p,hp⟩,fun q => h q ⟨p,hp⟩⟩
      · rintro ⟨U,hU⟩ p q
        exact (hU p).trans (hU q).symm
  refine ⟨hweak,?_⟩
  intro hPair
  have hW : weakPair C u := by
    intro p q hpq
    apply hPair p q
    intro he
    subst q
    obtain ⟨f,hf,hzero⟩ := hpq
    linarith [hf.2]
  have hedge := (hweak hW).2.2.1
  intro p q
  by_cases he : p = q
  · rw [he]
  obtain ⟨s,hpq⟩ := (exclusion_ball_faces hc hs hg hB).2.2 hPair |>.1 p q he
  have hp : (p : V) ∈ exclusion C u s := hpq ▸ ⟨pure_mem p,fun _ hp _ => hp⟩
  have hq : (q : V) ∈ exclusion C u s := hpq ▸ ⟨pure_mem q,fun _ _ hq => hq⟩
  exact (hedge s p hp.2).symm.trans (hedge s q hq.2)


/-- EB and the original common-center equation alone imply weakPair and a
relative interior common barycenter. No weakPair premise is used here. -/
theorem common_center_interior [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hG : commonCenter hB) :
    weakPair C u ∧ ∃ U : V,
      (∀ p : pure C u, sumVector hB p = U) ∧
      (1/3 : ℝ) • U ∈ intrinsicInterior ℝ (base C u) ∧ U ∈ interior (C : Set V) := by
  obtain ⟨geom,_,_⟩ := exclusion_ball_faces hc hs hg hB
  have hcenter (p : pure C u) : center hB p ∈ exclusion C u p := by
    exact (hB p).some.whole ▸ ⟨0,by simp,rfl⟩
  have hP : (pure C u).Nonempty := by
    by_contra hn
    have hh := pure_span (base_compact hc hs) hs hg
    rw [Set.not_nonempty_iff_eq_empty.mp hn,Submodule.span_empty] at hh
    exact bot_ne_top hh
  obtain ⟨p₀,hp₀⟩ := hP
  let U := sumVector hB ⟨p₀,hp₀⟩
  have hU (p : pure C u) : sumVector hB p = U := hG p ⟨p₀,hp₀⟩
  let w := (1/3 : ℝ) • U
  have hw : w ∈ base C u := by
    rw [show w = (1/3 : ℝ) • p₀ + (2/3 : ℝ) • center hB ⟨p₀,hp₀⟩ by
      dsimp [w,U,sumVector]; module]
    exact (base_convex C u) hp₀.1 (hcenter ⟨p₀,hp₀⟩).1
      (by norm_num) (by norm_num) (by norm_num)
  have hint : (interior (C : Set V)).Nonempty := by
    apply C.convex.interior_nonempty_iff_affineSpan_eq_top.mpr
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ C.zero_mem), hg]
    rfl
  have hwi : w ∈ interior (C : Set V) := by
    by_contra hn
    obtain ⟨f,hf,hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point C.convex hn hint
    have h0 : 0 ≤ f w := by simpa using hmax 0 C.zero_mem
    have h2 := hmax ((2 : ℝ) • w) (C.smul_mem (by norm_num) hw.1)
    have hfw : f w = 0 := by simp only [map_smul,smul_eq_mul] at h2; linarith
    have hfU : f U = 0 := by
      have hh : f w = (1/3 : ℝ) * f U := by simp [w]
      linarith
    have hzero (p : pure C u) : f p = 0 := by
      have hfp := hmax p (pure_mem p).1
      have hfc := hmax (center hB p) (hcenter p).1.1
      have he := congrArg f (hU p)
      simp only [sumVector,map_add,map_smul,smul_eq_mul,hfU] at he
      rw [hfw] at hfp hfc
      linarith
    have hker : Submodule.span ℝ (pure C u) ≤ LinearMap.ker f.toLinearMap :=
      Submodule.span_le.mpr (fun x hx => hzero ⟨x,hx⟩)
    rw [pure_span (base_compact hc hs) hs hg] at hker
    apply hf
    have he := LinearMap.ker_eq_top.mp (top_le_iff.mp hker)
    ext x
    exact LinearMap.congr_fun he x
  have hri : w ∈ intrinsicInterior ℝ (base C u) := by
    let A : AffineSubspace ℝ V := ({(1 : ℝ)} : AffineSubspace ℝ ℝ).comap u.toAffineMap
    have hKA : affineSpan ℝ (base C u) ≤ A := affineSpan_le.mpr (by
      intro x hx
      simpa [A] using hx.2)
    have hunit (x : affineSpan ℝ (base C u)) : u x = 1 := by
      have hh := hKA x.property
      simpa [A] using hh
    let x : affineSpan ℝ (base C u) := ⟨w,subset_affineSpan ℝ _ hw⟩
    refine ⟨x,?_,rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    have hn : {z : affineSpan ℝ (base C u) | (z : V) ∈ C} ∈ nhds x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp hwi)
    exact Filter.mem_of_superset hn (fun z hz => ⟨hz,hunit z⟩)
  have hUi : U ∈ interior (C : Set V) := by
    have ho : IsOpen ((fun z : V => (3 : ℝ) • z) '' interior (C : Set V)) :=
      isOpenMap_smul₀ (by norm_num : (3 : ℝ) ≠ 0) _ isOpen_interior
    have hsub : (fun z : V => (3 : ℝ) • z) '' interior (C : Set V) ⊆ C := by
      rintro _ ⟨z,hz,rfl⟩
      exact C.smul_mem (by norm_num) (interior_subset hz)
    have hh := interior_maximal hsub ho (show (3 : ℝ) • w ∈
      (fun z : V => (3 : ℝ) • z) '' interior (C : Set V) from ⟨w,hwi,rfl⟩)
    simpa [w,smul_smul] using hh
  refine ⟨?_,U,hU,hri,hUi⟩
  intro p q hpq
  let b := (hB p).some
  obtain ⟨n,hn,hnq⟩ := exclusion_coordinates hc hs hg hB p q b ⟨pure_mem q,hpq⟩
  have hnpure : b.param (-n) ∈ pure C u := by
    have : Nonempty (Fin b.dim) := ⟨⟨0,b.dim_pos⟩⟩
    have hsphere : -n ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) 1).extremePoints ℝ := by
      rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
      simpa using hn
    have hh := affine_extreme_image (Metric.closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) 1)
      (convex_closedBall 0 1) b.param (fun _ _ _ _ he => b.injective he) hsphere
    rw [b.whole] at hh
    exact (geom p).2.2.2.2.1.extremePoints_subset_extremePoints hh
  let r : pure C u := ⟨b.param (-n),hnpure⟩
  have hrp : (r : V) ∈ exclusion C u p :=
    b.whole ▸ ⟨-n,by simpa using hn.le,rfl⟩
  obtain ⟨a,ha,haz⟩ := (geom q).2.2.2.2.2.2
  have hac : a (center hB q) = 0 := (haz ▸ hcenter q).2
  have haU : a U = 1 := by
    have he := congrArg a (hU q)
    simpa [sumVector,ha.2,hac] using he.symm
  have hap : a p = 0 := (haz ▸ (exclusion_symmetric p q).mp ⟨pure_mem q,hpq⟩).2
  have hsum : (p : V) + q + r = U := by
    have hh : b.param 0 = (1/2 : ℝ) • (b.param n + b.param (-n)) := by
      simpa [midpoint_eq_smul_add] using b.param.map_midpoint n (-n)
    have he := hU p
    dsimp [sumVector,center] at he
    rw [hh,hnq] at he
    simpa [r,b,smul_smul,smul_add,add_assoc] using he
  have har : a r = 0 := by
    have he := congrArg a hsum
    simp only [map_add,ha.2,hap,haU] at he
    linarith
  have hrq : (r : V) ∈ exclusion C u q := ⟨pure_mem r,a,ha,har⟩
  have hpr := (exclusion_symmetric p r).mp hrp
  have hqr := (exclusion_symmetric q r).mp hrq
  obtain ⟨F,hF⟩ := base_face_lift hs (geom r).2.2.1 (geom r).2.2.2.2.1
  have hsub : pairBase C u p q ⊆ exclusion C u r := by
    intro z hz
    rw [← hF]
    exact ⟨hz.2 F ((hF.symm ▸ hpr).1) ((hF.symm ▸ hqr).1),hz.1.2⟩
  intro he
  exact (geom r).2.2.2.2.2.1 (Subset.antisymm (fun x hx => (geom r).2.2.2.2.1.subset hx)
    (he ▸ hsub))

#print axioms original_pure_compact
#print axioms original_continuous_frame_sum
#print axioms common_center_interior

end D5.S3.Quantum.Foundation.ContinuousFrameSum
