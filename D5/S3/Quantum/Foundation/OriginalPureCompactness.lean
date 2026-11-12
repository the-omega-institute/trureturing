/- GID: D5/S3/Quantum/Foundation/OriginalPureCompactness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalPureCompactness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original joint separation makes the entire pure locus compact. -/

import D5.S3.Quantum.Foundation.OrthogonalJointCompletion
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Compactness from the entire original effect interval and joint completion. -/

noncomputable section
open Set

namespace D5.S3.Quantum.Foundation.OriginalPureCompactness

open CircuitBalancedConfirmation FacetZeroGluing WholePairBallConfirmation
open ExclusionBallFaces OrthogonalJointCompletion

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem effects_compact {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    IsCompact {f : V →L[ℝ] ℝ | proper C u f.toLinearMap} := by
  have hcl : IsClosed {f : V →L[ℝ] ℝ | proper C u f.toLinearMap} := by
    have he : {f : V →L[ℝ] ℝ | proper C u f.toLinearMap} =
        ⋂ (x : V) (_ : x ∈ C), {f : V →L[ℝ] ℝ | 0 ≤ f x ∧ f x ≤ u x} := by
      ext f
      simp [proper]
    rw [he]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    have hlo : IsClosed {f : V →L[ℝ] ℝ | (0 : ℝ) ≤ f x} :=
      isClosed_le continuous_const (by fun_prop)
    have hhi : IsClosed {f : V →L[ℝ] ℝ | f x ≤ u x} :=
      isClosed_le (by fun_prop) continuous_const
    exact hlo.inter hhi
  have hspan := pure_span (base_compact hc hs) hs hg
  let b := Module.Basis.ofSpan hspan.ge
  let := FiniteDimensional.fintypeBasisIndex b
  obtain ⟨M, _, hbound⟩ := b.exists_opNorm_le (F := ℝ)
  refine Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hcl, isBounded_iff_forall_norm_le.mpr ⟨M, ?_⟩⟩
  intro f hf
  have hle : ‖f‖ ≤ M * 1 := by
    apply hbound (show (0 : ℝ) ≤ 1 by norm_num)
    intro i
    have hp := Module.Basis.ofSpan_subset hspan.ge (mem_range_self i)
    have hi := hf (b i) hp.1.1
    change 0 ≤ f (b i) ∧ f (b i) ≤ u (b i) at hi
    rw [Real.norm_eq_abs, abs_of_nonneg hi.1]
    have hui : u (b i) = 1 := hp.1.2
    exact hi.2.trans_eq hui
  simpa using hle

private theorem exclusion_injective [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) : Function.Injective (fun p : pure C u => exclusion C u p) := by
  intro p q he
  change exclusion C u p = exclusion C u q at he
  have hj := whole_joint_completion hc hs hg hB hW
  obtain ⟨r, s, hprs⟩ := hj.2.1 p
  obtain ⟨t, ht, _⟩ := hj.1 r s hprs.2.2.2.2.1
  have hpr : (r : V) ∈ exclusion C u p := ⟨pure_mem r, hprs.2.2.1⟩
  have hps : (s : V) ∈ exclusion C u p := ⟨pure_mem s, hprs.2.2.2.1⟩
  have hpin : (p : V) ∈ exclusion C u r ∩ exclusion C u s :=
    ⟨(exclusion_symmetric p r).mp hpr, (exclusion_symmetric p s).mp hps⟩
  have hqin : (q : V) ∈ exclusion C u r ∩ exclusion C u s :=
    ⟨(exclusion_symmetric q r).mp (he ▸ hpr),
      (exclusion_symmetric q s).mp (he ▸ hps)⟩
  apply Subtype.ext
  have hp : (p : V) = t := by simpa [ht.1] using hpin
  have hq : (q : V) = t := by simpa [ht.1] using hqin
  exact hp.trans hq.symm

private theorem equal_exclusions_of_two_points
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p q : pure C u) {y z : V} (hy : y ∈ exclusion C u p ∩ exclusion C u q)
    (hz : z ∈ exclusion C u p ∩ exclusion C u q) (hne : y ≠ z) :
    exclusion C u p = exclusion C u q := by
  obtain ⟨geom, _, _⟩ := exclusion_ball_faces hc hs hg hB
  have hn : (exclusion C u p ∩ exclusion C u q).Nontrivial := ⟨y, hy, z, hz, hne⟩
  have hconv := (geom p).2.2.1.inter (geom q).2.2.1
  have hface := (geom p).2.2.2.2.1.inter (geom q).2.2.2.2.1
  obtain ⟨bp⟩ := hB p
  obtain ⟨bq⟩ := hB q
  have hp := chart_face_eq bp hconv
    (hface.mono (geom p).2.2.2.2.1.subset inter_subset_left) hn
  have hq := chart_face_eq bq hconv
    (hface.mono (geom q).2.2.2.2.1.subset inter_subset_right) hn
  exact hp.symm.trans hq

private theorem separated_zeros_force_pure [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) {x y z : V}
    (hx : x ∈ base C u) (hy : y ∈ base C u) (hz : z ∈ base C u)
    (a b : V →L[ℝ] ℝ) (ha : proper C u a.toLinearMap)
    (hax : a x = 1) (hay : a y = 0) (haz : a z = 0)
    (hby : b y = 1) (hbz : b z = 0) : x ∈ pure C u := by
  let F : Set V := {s | s ∈ base C u ∧ a s = 1}
  have hxF : x ∈ F := ⟨hx, hax⟩
  have hconv : Convex ℝ F := by
    intro s hs' t ht r k hr hk hrk
    refine ⟨base_convex C u hs'.1 ht.1 hr hk hrk, ?_⟩
    simp only [map_add, map_smul, hs'.2, ht.2, smul_eq_mul, mul_one]
    exact hrk
  have hex : IsExposed ℝ (base C u) F := by
    intro _
    refine ⟨a, ?_⟩
    ext s
    constructor
    · rintro ⟨hs', has⟩
      refine ⟨hs', fun t ht => ?_⟩
      change a t ≤ a s
      rw [has]
      simpa [ht.2] using (ha t ht.1).2
    · rintro ⟨hs', hmax⟩
      refine ⟨hs', le_antisymm ?_ ?_⟩
      · simpa [hs'.2] using (ha s hs'.1).2
      · simpa [hax] using hmax x hx
  have hproper : F ≠ base C u := by
    intro he
    have hyF : y ∈ F := he.symm ▸ hy
    linarith [hyF.2]
  obtain ⟨geom, classify, _⟩ := exclusion_ball_faces hc hs hg hB
  rcases classify F ⟨x, hxF⟩ hconv hex.isExtreme hproper with ⟨p, hp⟩ | ⟨p, hp⟩
  · have he : x = p := by simpa [hp] using hxF
    exact he ▸ p.property
  · obtain ⟨chart⟩ := hB p
    let i : Fin chart.dim := ⟨0, chart.dim_pos⟩
    let n : EuclideanSpace ℝ (Fin chart.dim) := EuclideanSpace.single i 1
    have hn : ‖n‖ = 1 := by simp [n, EuclideanSpace.single]
    have pure_sphere (v : EuclideanSpace ℝ (Fin chart.dim)) (hv : ‖v‖ = 1) :
        chart.param v ∈ pure C u := by
      let : Nonempty (Fin chart.dim) := ⟨i⟩
      have hvext : v ∈ (Metric.closedBall 0 1).extremePoints ℝ := by
        rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
        simpa using hv
      have hi' := affine_extreme_image (Metric.closedBall (0 : EuclideanSpace ℝ (Fin chart.dim)) 1)
        (convex_closedBall 0 1) chart.param (fun _ _ _ _ h => chart.injective h) hvext
      rw [chart.whole] at hi'
      exact (geom p).2.2.2.2.1.extremePoints_subset_extremePoints hi'
    let s : pure C u := ⟨chart.param n, pure_sphere n hn⟩
    let t : pure C u := ⟨chart.param (-n), pure_sphere (-n) (by simpa using hn)⟩
    have memF (v : EuclideanSpace ℝ (Fin chart.dim)) (hv : ‖v‖ = 1) : chart.param v ∈ F := by
      rw [hp, ← chart.whole]
      exact mem_image_of_mem _ (by simpa using hv.le)
    have has : a s = 1 := (memF n hn).2
    have hat : a t = 1 := (memF (-n) (by simpa using hn)).2
    have hst : s ≠ t := by
      intro he
      have hnt : n = -n := chart.injective (congrArg Subtype.val he)
      have hn0 : n = 0 := by
        have hsum : n + n = 0 := (congrArg (fun v => n + v) hnt).trans (add_neg_cancel n)
        have : (2 : ℝ) • n = 0 := by simpa only [two_smul] using hsum
        exact (smul_eq_zero.mp this).resolve_left (by norm_num)
      simp [hn0] at hn
    have hyz : y ≠ z := by intro he; rw [he, hbz] at hby; norm_num at hby
    have he := equal_exclusions_of_two_points hc hs hg hB s t
      ⟨⟨hy, a.toLinearMap, ⟨ha, has⟩, hay⟩, ⟨hy, a.toLinearMap, ⟨ha, hat⟩, hay⟩⟩
      ⟨⟨hz, a.toLinearMap, ⟨ha, has⟩, haz⟩, ⟨hz, a.toLinearMap, ⟨ha, hat⟩, haz⟩⟩ hyz
    exact (hst (exclusion_injective hc hs hg hB hW he)).elim

/-- The entire original pure locus is compact under EB and weak orthogonal Pair.
No closedness, finite pure menu, reciprocal metric or global Pair is assumed. -/
theorem whole_pure_compact [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) : IsCompact (pure C u) := by
  let E : Set (V →L[ℝ] ℝ) := {f | proper C u f.toLinearMap}
  let T := base C u ×ˢ base C u ×ˢ base C u ×ˢ E ×ˢ E
  let A : Set (V × V × V × (V →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) :=
    {t | t.2.2.2.1 t.1 = 1 ∧ t.2.2.2.1 t.2.1 = 0 ∧
      t.2.2.2.1 t.2.2.1 = 0 ∧ t.2.2.2.2 t.2.1 = 1 ∧ t.2.2.2.2 t.2.2.1 = 0}
  have hT : IsCompact T := (base_compact hc hs).prod ((base_compact hc hs).prod
    ((base_compact hc hs).prod ((effects_compact hc hs hg).prod (effects_compact hc hs hg))))
  have hA : IsClosed A := by
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const))))
  have he : Prod.fst '' (T ∩ A) = pure C u := by
    ext x
    constructor
    · rintro ⟨⟨x, y, z, a, b⟩, ⟨⟨hx, hy, hz, ha, _⟩, hax, hay, haz, hby, hbz⟩, rfl⟩
      exact separated_zeros_force_pure hc hs hg hB hW hx hy hz a b ha hax hay haz hby hbz
    · intro hx
      let p : pure C u := ⟨x, hx⟩
      obtain ⟨q, r, hr⟩ := (whole_joint_completion hc hs hg hB hW).2.1 p
      obtain ⟨geom, _, _⟩ := exclusion_ball_faces hc hs hg hB
      obtain ⟨a, ha, hazero⟩ := (geom p).2.2.2.2.2.2
      obtain ⟨b, hb, hbzero⟩ := (geom q).2.2.2.2.2.2
      have haq : a q = 0 := (hazero ▸ (show (q : V) ∈ exclusion C u p from
        ⟨pure_mem q, hr.2.2.1⟩)).2
      have har : a r = 0 := (hazero ▸ (show (r : V) ∈ exclusion C u p from
        ⟨pure_mem r, hr.2.2.2.1⟩)).2
      have hbr : b r = 0 := (hbzero ▸ (show (r : V) ∈ exclusion C u q from
        ⟨pure_mem r, hr.2.2.2.2.1⟩)).2
      exact ⟨(x, q, r, a.toContinuousLinearMap, b.toContinuousLinearMap),
        ⟨⟨hx.1, pure_mem q, pure_mem r, ha.1, hb.1⟩, ha.2, haq, har, hb.2, hbr⟩, rfl⟩
  rw [← he]
  exact (hT.inter_right hA).image continuous_fst

#print axioms whole_pure_compact

end D5.S3.Quantum.Foundation.OriginalPureCompactness
