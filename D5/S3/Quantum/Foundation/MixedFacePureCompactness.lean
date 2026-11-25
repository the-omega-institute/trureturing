/- GID: D5/S3/Quantum/Foundation/MixedFacePureCompactness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/MixedFacePureCompactness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Proper pure-pair faces and maximal mixed faces close the original pure locus. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import D5.S3.Quantum.Foundation.HitSectionGeneration

/-! Proper pure-pair faces and maximal mixed faces give compactness of the pure locus. -/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.MixedFacePureCompactness

open CircuitBalancedConfirmation WholePairBallConfirmation FacetZeroGluing
  ExclusionBallFaces HitSectionGeneration

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem pair_unit_support
    (hu : ∀ y ∈ C, y ≠ 0 → 0 < u y)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hpair : pairProper C u) (p q : pure C u) (hpq : p ≠ q) :
    ∃ e : V →L[ℝ] ℝ, ‖e‖ = 1 ∧ (∀ y ∈ C, 0 ≤ e y) ∧ e p = 0 ∧ e q = 0 := by
  obtain ⟨F, hF⟩ := base_face_lift hu (pair_convex C u p q) (pair_extreme C u p q)
  have hproper : F.toPointedCone ≠ C := fun h =>
    hpair p q hpq (hF.symm.trans (congrArg (fun D => base D u) h))
  have hpF : (p : V) ∈ base F.toPointedCone u := by
    rw [hF]
    exact ⟨p.property.1, fun _ hp _ => hp⟩
  have hqF : (q : V) ∈ base F.toPointedCone u := by
    rw [hF]
    exact ⟨q.property.1, fun _ _ hq => hq⟩
  obtain ⟨g, hg0, hpos, hzero⟩ := proper_cone_face_support hg F hproper
  let L := g.toContinuousLinearMap
  have hL : L ≠ 0 := fun h => hg0 (congrArg (fun e : V →L[ℝ] ℝ => e.toLinearMap) h)
  have hnorm : ‖L‖ ≠ 0 := norm_ne_zero_iff.mpr hL
  refine ⟨‖L‖⁻¹ • L, by simp [norm_smul, hnorm], ?_, ?_, ?_⟩
  · intro y hy
    change 0 ≤ ‖L‖⁻¹ * g y
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg L)) (hpos y hy)
  · change ‖L‖⁻¹ * g p = 0
    rw [hzero p hpF.1, mul_zero]
  · change ‖L‖⁻¹ * g q = 0
    rw [hzero q hqF.1, mul_zero]

private theorem limit_pair_support
    (hu : ∀ y ∈ C, y ≠ 0 → 0 < u y)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hpair : pairProper C u)
    {p : ℕ → V} {x : V} (hp : ∀ n, p n ∈ pure C u)
    (hpx : Tendsto p atTop (𝓝 x)) (q : pure C u) (hxq : x ≠ (q : V)) :
    ∃ e : V →L[ℝ] ℝ, ‖e‖ = 1 ∧ (∀ y ∈ C, 0 ≤ e y) ∧ e x = 0 ∧ e q = 0 := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hpx.eventually_ne hxq)
  have hpq (n : ℕ) : (⟨p (n + N), hp (n + N)⟩ : pure C u) ≠ q :=
    fun h => hN (n + N) (by omega) (congrArg Subtype.val h)
  choose e heNorm hePos heP heQ using fun n =>
    pair_unit_support hu hg hpair ⟨p (n + N), hp (n + N)⟩ q (hpq n)
  obtain ⟨f, hf, φ, hφ, hlim⟩ := (isCompact_sphere (0 : V →L[ℝ] ℝ) 1).tendsto_subseq
    (x := e) (fun n => by simpa using heNorm n)
  have htail : Tendsto (fun n => p (n + N)) atTop (𝓝 x) :=
    (tendsto_add_atTop_iff_nat N).mpr hpx
  have heval : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have eval_limit {y : ℕ → V} {z : V} (hy : Tendsto y atTop (𝓝 z)) :
      Tendsto (fun n => e (φ n) (y n)) atTop (𝓝 (f z)) :=
    (heval.tendsto (f, z)).comp (hlim.prodMk_nhds hy)
  refine ⟨f, by simpa using hf, ?_, ?_, ?_⟩
  · intro y hy
    exact (isClosed_Ici : IsClosed (Ici (0 : ℝ))).mem_of_tendsto
      (eval_limit (y := fun _ => y) tendsto_const_nhds)
      (Eventually.of_forall fun n => hePos (φ n) y hy)
  · refine tendsto_nhds_unique (eval_limit (htail.comp hφ.tendsto_atTop)) ?_
    simpa only [Function.comp_apply, heP] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · refine tendsto_nhds_unique (eval_limit (y := fun _ => (q : V)) tendsto_const_nhds) ?_
    simpa only [heQ] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Distinct pure pairs generate proper faces. If every proper actual face
containing a mixed point is maximal among the proper actual faces, the whole
original pure locus is closed and compact. -/
theorem pure_closed_compact_of_mixed_face_coatoms
    (hc : IsClosed (C : Set V)) (hu : ∀ y ∈ C, y ≠ 0 → 0 < u y)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hpair : pairProper C u)
    (hcoatom : ∀ F : Set V, Convex ℝ F → IsExtreme ℝ (base C u) F →
      F ≠ base C u → (∃ x ∈ F, x ∉ pure C u) →
      ∀ G : Set V, Convex ℝ G → IsExtreme ℝ (base C u) G →
        F ⊆ G → G ≠ base C u → G = F) :
    IsClosed (pure C u) ∧ IsCompact (pure C u) := by
  classical
  have hK := base_compact hc hu
  have hclosed : IsClosed (pure C u) := by
    apply isSeqClosed_iff_isClosed.mp
    intro p x hp hpx
    have hx : x ∈ base C u := hK.isClosed.mem_of_tendsto hpx
      (Eventually.of_forall fun n => (hp n).1)
    by_contra hxp
    let F := principalFace C x
    let B := base F.toPointedCone u
    have hxB : x ∈ B := ⟨mem_principalFace x hx.1, hx.2⟩
    have hBface : IsExtreme ℝ (base C u) B := face_base_extreme F
    have hzeroFace (q : pure C u) :
        ∃ G : Set V, Convex ℝ G ∧ IsExtreme ℝ (base C u) G ∧
          G ≠ base C u ∧ B ⊆ G ∧ (q : V) ∈ G := by
      have hxq : x ≠ (q : V) := fun h => hxp (h.symm ▸ q.property)
      obtain ⟨e, heNorm, hePos, hex, heq⟩ := limit_pair_support hu hg hpair hp hpx q hxq
      let G : Set V := {y | y ∈ base C u ∧ e y = 0}
      have hGexp : IsExposed ℝ (base C u) G := by
        intro _
        refine ⟨-e, ?_⟩
        ext y
        constructor
        · rintro ⟨hy, hey⟩
          refine ⟨hy, fun z hz => ?_⟩
          change -e z ≤ -e y
          rw [hey, neg_zero]
          exact neg_nonpos.mpr (hePos z hz.1)
        · rintro ⟨hy, hmax⟩
          have hle := hmax x hx
          change -e x ≤ -e y at hle
          rw [hex, neg_zero] at hle
          exact ⟨hy, le_antisymm (neg_nonneg.mp hle) (hePos y hy.1)⟩
      refine ⟨G, hGexp.convex (base_convex C u), hGexp.isExtreme, ?_, ?_,
        ⟨q.property.1, heq⟩⟩
      · intro hG
        have hs : Submodule.span ℝ (pure C u) ≤ LinearMap.ker e.toLinearMap :=
          Submodule.span_le.mpr fun y hy => (show y ∈ G from hG.symm ▸ hy.1).2
        rw [pure_span hK hu hg] at hs
        have he0 : e.toLinearMap = 0 := LinearMap.ker_eq_top.mp (top_le_iff.mp hs)
        have he : e = 0 := by
          ext y
          exact LinearMap.congr_fun he0 y
        simpa [he] using heNorm
      · intro y hy
        obtain ⟨_, _, _, ht⟩ := hy.1
        have hnonneg := hePos _ ht
        rw [map_sub, map_smul, hex, smul_zero, zero_sub] at hnonneg
        have hyK := hBface.subset hy
        exact ⟨hyK, le_antisymm (neg_nonneg.mp hnonneg) (hePos y hyK.1)⟩
    have hBproper : B ≠ base C u := by
      obtain ⟨G, _, hGface, hGproper, hBG, _⟩ := hzeroFace ⟨p 0, hp 0⟩
      intro hB
      rw [hB] at hBG
      exact hGproper (Subset.antisymm hGface.subset hBG)
    have houtside : ∃ q : pure C u, (q : V) ∉ B := by
      by_contra! h
      have hsub : pure C u ⊆ (F : Set V) := fun y hy => (h ⟨y, hy⟩).1
      have hcl := closure_minimal (convexHull_min hsub F.toPointedCone.convex) (face_closed hc F)
      rw [show closure (convexHull ℝ (pure C u)) = base C u from
        closure_convexHull_extremePoints hK (base_convex C u)] at hcl
      exact hBproper (Subset.antisymm hBface.subset (fun y hy => ⟨hcl hy, hy.2⟩))
    obtain ⟨q, hq⟩ := houtside
    obtain ⟨G, hGconv, hGface, hGproper, hBG, hqG⟩ := hzeroFace q
    have hGB := hcoatom B (base_convex F.toPointedCone u) hBface hBproper ⟨x, hxB, hxp⟩
      G hGconv hGface hBG hGproper
    exact hq (hGB ▸ hqG)
  exact ⟨hclosed, hK.of_isClosed_subset hclosed extremePoints_subset⟩

end D5.S3.Quantum.Foundation.MixedFacePureCompactness
