/- GID: D5/S3/Quantum/Foundation/ExclusionBallFaces
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionBallFaces
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Entire exclusion balls expose and exhaust the original proper faces. -/

import D5.S3.Quantum.Foundation.FacetZeroGluing
import D5.S3.Quantum.Foundation.WholePairBallConfirmation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! Original full-effect exclusions and all convex faces of the normalized cone base. -/

noncomputable section
open Set

namespace D5.S3.Quantum.Foundation.ExclusionBallFaces

open CircuitBalancedConfirmation WeightedRelationConfirmation FacetZeroGluing
open WholePairBallConfirmation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A ball parametrizes the entire original exclusion set; no facial property is a field. -/
structure ExclusionChart (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V) where
  dim : ℕ
  dim_pos : 0 < dim
  param : EuclideanSpace ℝ (Fin dim) →ᵃ[ℝ] V
  injective : Function.Injective param
  whole : param '' Metric.closedBall 0 1 = exclusion C u p

/-- Every full mixed-state exclusion is a nondegenerate finite Euclidean ball. -/
def exclusionBalls (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p : pure C u, Nonempty (ExclusionChart C u p)

/-- Every distinct original pure pair generates a proper whole minimal face. -/
def pairProper (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p q : pure C u, p ≠ q → pairBase C u p q ≠ base C u

private theorem face_eq_of_interior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S F : Set E} (hF : IsExtreme ℝ S F)
    {x : E} (hx : x ∈ interior S) (hxF : x ∈ F) : F = S := by
  apply Subset.antisymm hF.subset
  intro y hy
  have hcont : Continuous (fun t : ℝ => AffineMap.lineMap y x t) :=
    AffineMap.lineMap_continuous
  obtain ⟨t, ht, hz⟩ := hcont.tendsto' 1 x (AffineMap.lineMap_apply_one y x) |>.eventually_mem
    (mem_interior_iff_mem_nhds.mp hx) |>.exists_gt
  apply hF.left_mem_of_mem_openSegment hy hz hxF
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := ℝ) y x]
  rw [← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht⟩, AffineMap.lineMap_apply_one y x⟩

private theorem proper_cone_face_support {C : PointedCone ℝ V}
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (F : C.Face)
    (hproper : F.toPointedCone ≠ C) :
    ∃ g : V →ₗ[ℝ] ℝ, g ≠ 0 ∧ (∀ x ∈ C, 0 ≤ g x) ∧ ∀ x ∈ F, g x = 0 := by
  have hint : (interior (C : Set V)).Nonempty := by
    apply C.convex.interior_nonempty_iff_affineSpan_eq_top.mpr
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ C.zero_mem), hgen]
    rfl
  have hdis : Disjoint (interior (C : Set V)) (F : Set V) := by
    rw [Set.disjoint_left]
    intro x hx hxF
    have he := face_eq_of_interior F.isFaceOf.isExtreme hx hxF
    exact hproper (SetLike.coe_injective he)
  obtain ⟨f, a, hf, hC, hF⟩ := geometric_hahn_banach_of_nonempty_interior
    C.convex F.toPointedCone.convex hdis hint ⟨0, F.toPointedCone.zero_mem⟩
  have ha : 0 ≤ a := by simpa using hC 0 C.zero_mem
  have ha' : a ≤ 0 := by simpa using hF 0 F.toPointedCone.zero_mem
  have ha0 : a = 0 := le_antisymm ha' ha
  refine ⟨-f.toLinearMap, ?_, ?_, ?_⟩
  · intro he
    apply hf
    ext x
    have hh := LinearMap.congr_fun he x
    simpa using hh
  · intro x hx
    have hh := hC x hx
    simpa [ha0] using hh
  · intro x hx
    have hle := hC x (F.isFaceOf.le hx)
    have hge := hF x hx
    simp only [ha0] at hle hge
    change -(f x) = 0
    linarith

theorem positive_support_confirmer {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    {g : V →ₗ[ℝ] ℝ} (hg : g ≠ 0) (hpos : ∀ x ∈ C, 0 ≤ g x) :
    ∃ (p : pure C u) (f : V →ₗ[ℝ] ℝ), confirms C u p f ∧
      ∀ x, g x = 0 → f x = 0 := by
  have hK := base_compact hclosed hstrict
  have hsome : ∃ q : pure C u, 0 < g q := by
    by_contra! hn
    have hz (q : pure C u) : g q = 0 := le_antisymm (hn q) (hpos q q.property.1.1)
    have hs : Submodule.span ℝ (pure C u) ≤ LinearMap.ker g :=
      Submodule.span_le.mpr (fun x hx => hz ⟨x, hx⟩)
    rw [pure_span hK hstrict hgen] at hs
    exact hg (LinearMap.ker_eq_top.mp (top_le_iff.mp hs))
  obtain ⟨q, hq⟩ := hsome
  let L := g.toContinuousLinearMap
  obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn ⟨q, pure_mem q⟩ L.continuous.continuousOn
  have hex : IsExposed ℝ (base C u) (L.toExposed (base C u)) :=
    ContinuousLinearMap.toExposed.isExposed
  obtain ⟨p, hp⟩ := (hex.isCompact hK).extremePoints_nonempty
    ⟨m, hm, hmax⟩
  have hpure : p ∈ pure C u := hex.isExtreme.extremePoints_subset_extremePoints hp
  have hgp : 0 < g p := hq.trans_le (hp.1.2 q (pure_mem q))
  let f := (g p)⁻¹ • g
  refine ⟨⟨p, hpure⟩, f, ⟨cone_bound hK hstrict ?_, ?_⟩, ?_⟩
  · intro r
    change 0 ≤ (g p)⁻¹ * g r ∧ (g p)⁻¹ * g r ≤ 1
    refine ⟨mul_nonneg (inv_nonneg.mpr hgp.le) (hpos r (pure_mem r).1), ?_⟩
    have hr : g r ≤ g p := hp.1.2 r (pure_mem r)
    calc
      (g p)⁻¹ * g r = g r / g p := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ 1 := (div_le_one hgp).mpr hr
  · simp [f, hgp.ne']
  · intro x hx
    simp [f, hx]

private theorem proper_base_face_in_exclusion {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) {F : Set V}
    (hconv : Convex ℝ F) (hface : IsExtreme ℝ (base C u) F)
    (hproper : F ≠ base C u) : ∃ p : pure C u, F ⊆ exclusion C u p := by
  obtain ⟨G, hG⟩ := base_face_lift hstrict hconv hface
  have hGproper : G.toPointedCone ≠ C := by
    intro he
    exact hproper (hG.symm.trans (congrArg (fun D => base D u) he))
  obtain ⟨g, hg, hpos, hzero⟩ := proper_cone_face_support hgen G hGproper
  obtain ⟨p, f, hf, hz⟩ := positive_support_confirmer hclosed hstrict hgen hg hpos
  refine ⟨p, fun x hx => ⟨hface.subset hx, f, hf, hz x ?_⟩⟩
  exact hzero x (show x ∈ G from (hG.symm ▸ hx : x ∈ base G.toPointedCone u).1)

private theorem ball_face_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [StrictConvexSpace ℝ E] {F : Set E} (hconv : Convex ℝ F)
    (hface : IsExtreme ℝ (Metric.closedBall (0 : E) 1) F) (hnon : F.Nontrivial) :
    F = Metric.closedBall (0 : E) 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnon
  have hzF := hconv hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hzint := (strictConvex_closedBall ℝ (0 : E) 1) (hface.subset hx)
    (hface.subset hy) hxy (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  exact face_eq_of_interior hface hzint hzF

omit [FiniteDimensional ℝ V] in
theorem chart_face_eq {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p : V}
    (b : ExclusionChart C u p) {F : Set V} (hconv : Convex ℝ F)
    (hface : IsExtreme ℝ (exclusion C u p) F) (hnon : F.Nontrivial) :
    F = exclusion C u p := by
  let S := b.param ⁻¹' F
  have hSsub : S ⊆ Metric.closedBall 0 1 := by
    intro x hx
    exact b.injective.mem_set_image.mp (b.whole.symm ▸ hface.subset hx)
  have hSface : IsExtreme ℝ (Metric.closedBall 0 1) S := by
    refine ⟨hSsub, ?_⟩
    intro x hx y hy z hz hseg
    apply hface.left_mem_of_mem_openSegment
      (b.whole ▸ mem_image_of_mem b.param hx) (b.whole ▸ mem_image_of_mem b.param hy) hz
    rw [← image_openSegment ℝ b.param]
    exact mem_image_of_mem b.param hseg
  have hSnon : S.Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnon
    obtain ⟨a, _, ha⟩ := b.whole.symm ▸ hface.subset hx
    obtain ⟨c, _, hc⟩ := b.whole.symm ▸ hface.subset hy
    refine ⟨a, (show b.param a ∈ F from ha.symm ▸ hx), c,
      (show b.param c ∈ F from hc.symm ▸ hy), ?_⟩
    intro he
    exact hxy (ha.symm.trans ((congrArg b.param he).trans hc))
  have hSeq := ball_face_eq (hconv.affine_preimage b.param) hSface hSnon
  apply Subset.antisymm hface.subset
  intro x hx
  obtain ⟨a, ha, rfl⟩ := b.whole.symm ▸ hx
  have : a ∈ S := by rw [show S = _ from hSeq]; exact ha
  exact this

omit [FiniteDimensional ℝ V] in
private theorem ball_exclusion_convex {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hB : exclusionBalls C u) (p : pure C u) : Convex ℝ (exclusion C u p) := by
  obtain ⟨b⟩ := hB p
  rw [← b.whole]
  exact (convex_closedBall _ _).affine_image b.param

omit [FiniteDimensional ℝ V] in
private theorem ball_zero_gluing {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hB : exclusionBalls C u) : zeroGluing C u := by
  intro p x y hx hy hfx hfy
  have hh := ball_exclusion_convex hB p ⟨hx, hfx⟩ ⟨hy, hfy⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simpa only [← smul_add] using hh.2

omit [FiniteDimensional ℝ V] in
private theorem chart_nontrivial {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p : V}
    (b : ExclusionChart C u p) : (exclusion C u p).Nontrivial := by
  let i : Fin b.dim := ⟨0, b.dim_pos⟩
  let n : EuclideanSpace ℝ (Fin b.dim) := EuclideanSpace.single i 1
  have hn : ‖n‖ = 1 := by simp [n, EuclideanSpace.single]
  refine ⟨b.param 0, b.whole ▸ mem_image_of_mem b.param (by simp),
    b.param n, b.whole ▸ mem_image_of_mem b.param (by simpa using hn.le), ?_⟩
  intro he
  have hh := b.injective he
  have : ‖n‖ = 0 := by rw [← hh]; simp
  linarith

private theorem exclusion_exposed {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (p : pure C u) {f : V →ₗ[ℝ] ℝ} (hf : confirms C u p f)
    (hzero : exclusion C u p = {x | x ∈ base C u ∧ f x = 0}) :
    IsExposed ℝ (base C u) (exclusion C u p) := by
  intro hne
  obtain ⟨z, hz⟩ := hne
  rw [hzero] at hz
  refine ⟨-f.toContinuousLinearMap, ?_⟩
  rw [hzero]
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    refine ⟨hx, fun y hy => ?_⟩
    change -f y ≤ -f x
    rw [hfx]
    simpa using neg_nonpos.mpr (hf.1 y hy.1).1
  · rintro ⟨hx, hmax⟩
    have hh := hmax z hz.1
    change -f z ≤ -f x at hh
    rw [hz.2] at hh
    exact ⟨hx, by linarith [(hf.1 x hx.1).1]⟩

omit [FiniteDimensional ℝ V] in
theorem pair_convex (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p q : V) :
    Convex ℝ (pairBase C u p q) := by
  intro x hx y hy a b ha hb hab
  refine ⟨base_convex C u hx.1 hy.1 ha hb hab, fun F hp hq => ?_⟩
  exact F.toPointedCone.convex (hx.2 F hp hq) (hy.2 F hp hq) ha hb hab

/-- Whole exclusion balls expose and exhaust all original proper convex faces.
Faces are not assumed closed. Pair properness then gives whole pair balls. -/
theorem exclusion_ball_faces {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    (∀ p : pure C u,
      (exclusion C u p).Nontrivial ∧ IsCompact (exclusion C u p) ∧
      Convex ℝ (exclusion C u p) ∧ IsExposed ℝ (base C u) (exclusion C u p) ∧
      IsExtreme ℝ (base C u) (exclusion C u p) ∧ exclusion C u p ≠ base C u ∧
      ∃ f, confirms C u p f ∧ exclusion C u p = {x | x ∈ base C u ∧ f x = 0}) ∧
    (∀ F : Set V, F.Nonempty → Convex ℝ F → IsExtreme ℝ (base C u) F →
      F ≠ base C u →
      (∃ p : pure C u, F = {(p : V)}) ∨ ∃ p : pure C u, F = exclusion C u p) ∧
    (pairProper C u →
      (∀ p q : pure C u, p ≠ q → ∃ r : pure C u,
        pairBase C u p q = exclusion C u r) ∧ wholePairBalls C u) := by
  have hgeom (p : pure C u) :
      (exclusion C u p).Nontrivial ∧ IsCompact (exclusion C u p) ∧
      Convex ℝ (exclusion C u p) ∧ IsExposed ℝ (base C u) (exclusion C u p) ∧
      IsExtreme ℝ (base C u) (exclusion C u p) ∧ exclusion C u p ≠ base C u ∧
      ∃ f, confirms C u p f ∧ exclusion C u p = {x | x ∈ base C u ∧ f x = 0} := by
    obtain ⟨b⟩ := hB p
    have hnon := chart_nontrivial b
    obtain ⟨f, hf, hzero⟩ := zero_gluing_common_effect (ball_zero_gluing hB) p hnon.nonempty
    have hex := exclusion_exposed p hf hzero
    refine ⟨hnon, ?_, ball_exclusion_convex hB p, hex, hex.isExtreme, ?_, f, hf, hzero⟩
    · rw [← b.whole]
      exact (isCompact_closedBall _ _).image b.param.continuous_of_finiteDimensional
    · intro he
      have hpD : (p : V) ∈ exclusion C u p := he.symm ▸ pure_mem p
      obtain ⟨g, hg, hgp⟩ := hpD.2
      linarith [hg.2]
  have hclass (F : Set V) (hne : F.Nonempty) (hconv : Convex ℝ F)
      (hface : IsExtreme ℝ (base C u) F) (hproper : F ≠ base C u) :
      (∃ p : pure C u, F = {(p : V)}) ∨ ∃ p : pure C u, F = exclusion C u p := by
    obtain ⟨x, hx⟩ := hne
    rcases Set.eq_singleton_or_nontrivial hx with he | hn
    · left
      have hp : x ∈ pure C u := by
        apply isExtreme_singleton.mp
        simpa [he] using hface
      exact ⟨⟨x, hp⟩, he⟩
    · obtain ⟨p, hsub⟩ := proper_base_face_in_exclusion hclosed hstrict hgen hconv hface hproper
      obtain ⟨b⟩ := hB p
      right
      exact ⟨p, chart_face_eq b hconv (hface.mono (hgeom p).2.2.2.2.1.subset hsub) hn⟩
  refine ⟨hgeom, hclass, fun hPair => ?_⟩
  have hpairs (p q : pure C u) (hpq : p ≠ q) :
      ∃ r : pure C u, pairBase C u p q = exclusion C u r := by
    have hp : (p : V) ∈ pairBase C u p q := ⟨pure_mem p, fun _ hp _ => hp⟩
    have hq : (q : V) ∈ pairBase C u p q := ⟨pure_mem q, fun _ _ hq => hq⟩
    rcases hclass _ ⟨p, hp⟩ (pair_convex C u p q) (pair_extreme C u p q)
      (hPair p q hpq) with ⟨r, he⟩ | h
    · rw [he] at hp hq
      exact (hpq (Subtype.ext (hp.trans hq.symm))).elim
    · exact h
  refine ⟨hpairs, fun p q hpq => ?_⟩
  obtain ⟨r, hr⟩ := hpairs p q hpq
  obtain ⟨b⟩ := hB r
  exact ⟨{ dim := b.dim
           dim_pos := b.dim_pos
           param := b.param
           injective := b.injective
           whole := b.whole.trans hr.symm }⟩

end D5.S3.Quantum.Foundation.ExclusionBallFaces
