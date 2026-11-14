/- GID: D5/S3/Quantum/Foundation/BinaryCenterNoncollapse
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/BinaryCenterNoncollapse
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Binary original compatibility bounds center variation on each fixed sphere. -/

import D5.S3.Quantum.Foundation.BinaryCenterGeometry
import D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation
import D5.S3.Quantum.Foundation.CommonSourceLiftObstruction

/-! Quantitative variation and attained distance on each fixed original sphere. -/

noncomputable section
open Set Metric Filter Topology
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.BinaryCenterNoncollapse

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity SingleLabelNormalBody ContinuousFrameSum BinaryCenterGeometry
open ReciprocalExclusionLimits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

variable (hc : IsClosed (C : Set V))
  (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)

/-- Chord compatibility determines an affine extension in the chart's own
Euclidean carrier. Coordinate reflections give its linear coefficients. -/
private theorem sphere_chord_extension {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → V)
    (h : ∀ x y z w, ‖x‖ = 1 → ‖y‖ = 1 → ‖z‖ = 1 → ‖w‖ = 1 →
      ∀ t v : ℝ, t ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
      t • x + (1-t) • y = v • z + (1-v) • w →
      t • f x + (1-t) • f y = v • f z + (1-v) • f w) :
    ∃ g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] V,
      ∀ x, ‖x‖ = 1 → g x = f x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let i₀ : Fin n := ⟨0, hn⟩
  let o : V := (1/2 : ℝ) • (f (e i₀) + f (-e i₀))
  let d (i : Fin n) := f (e i) - f (-e i)
  let flip (s : Finset (Fin n)) (x : E) : E :=
    WithLp.toLp 2 (fun i => if i ∈ s then -x i else x i)
  have fnorm (s : Finset (Fin n)) (x : E) : ‖flip s x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [flip]
    split_ifs <;> ring
  have anti (x : E) (hx : ‖x‖ = 1) : f x + f (-x) = (2 : ℝ) • o := by
    have hh := h x (-x) (e i₀) (-e i₀) hx (by simpa using hx)
      (e.norm_eq_one i₀) (by simpa using e.norm_eq_one i₀)
      (1/2) (1/2) (by norm_num) (by norm_num) (by module)
    have hh' := congrArg (fun z : V => (2 : ℝ) • z) hh
    calc
      f x + f (-x) = f (e i₀) + f (-e i₀) := by convert hh' using 1 <;> module
      _ = _ := by dsimp [o]; module
  have step (x : E) (hx : ‖x‖ = 1) (i : Fin n) :
      f x - f (flip {i} x) = x i • d i := by
    let y := flip {i} x
    have hy : ‖y‖ = 1 := (fnorm _ _).trans hx
    have hcoord : |x i| ≤ 1 := by
      calc
        |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖x‖ := PiLp.norm_apply_le x i
        _ = 1 := hx
    let v : ℝ := (1 + x i) / 2
    have hv : v ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨hl, hr⟩ := abs_le.mp hcoord
      dsimp [v]
      constructor <;> linarith
    have chord : (1/2 : ℝ) • x + (1-1/2 : ℝ) • (-y) =
        v • e i + (1-v) • (-e i) := by
      ext j
      change (1/2 : ℝ) * x j + (1-1/2) * (-(y j)) =
        v * (e i) j + (1-v) * (-((e i) j))
      dsimp [y, flip, v, e]
      simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply,
        Finset.mem_singleton, PiLp.toLp_apply]
      by_cases hij : j = i
      · subst j
        simp
        ring
      · simp [hij]
        ring
    have hh := h x (-y) (e i) (-e i) hx (by simpa using hy)
      (e.norm_eq_one i) (by simpa using e.norm_eq_one i)
      (1/2) v (by norm_num) hv chord
    have hh' := congrArg (fun z : V => (2 : ℝ) • z) hh
    have hh'' : f x + f (-y) = (2*v) • f (e i) + (2*(1-v)) • f (-e i) := by
      convert hh' using 1 <;> module
    calc
      f x - f y = (f x + f (-y)) - (f y + f (-y)) := by abel
      _ = (2*v) • f (e i) + (2*(1-v)) • f (-e i) - (2 : ℝ) • o := by
        rw [hh'', anti y hy]
      _ = (2*v) • f (e i) + (2*(1-v)) • f (-e i) - (f (e i) + f (-e i)) := by
        rw [anti (e i) (e.norm_eq_one i)]
      _ = x i • d i := by dsimp [v, d]; module
  have telescoping (s : Finset (Fin n)) (x : E) (hx : ‖x‖ = 1) :
      f x - f (flip s x) = ∑ i ∈ s, x i • d i := by
    induction s using Finset.induction_on with
    | empty =>
      have he : flip ∅ x = x := by ext i; simp [flip]
      simp [he]
    | @insert i s his ih =>
      have he : flip (insert i s) x = flip {i} (flip s x) := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [flip, his]
        · simp [flip, hji]
      have hi : (flip s x) i = x i := by simp [flip, his]
      rw [he, Finset.sum_insert his]
      calc
        f x - f (flip {i} (flip s x)) =
            (f x - f (flip s x)) + (f (flip s x) - f (flip {i} (flip s x))) := by abel
        _ = (∑ j ∈ s, x j • d j) + x i • d i := by rw [ih, step _ ((fnorm _ _).trans hx) i, hi]
        _ = _ := by abel
  let L : E →ₗ[ℝ] V := e.toBasis.constr ℝ (fun i => (1/2 : ℝ) • d i)
  refine ⟨L.toAffineMap + AffineMap.const ℝ E o, ?_⟩
  intro x hx
  have he : flip Finset.univ x = -x := by ext i; simp [flip]
  have ht := telescoping Finset.univ x hx
  rw [he] at ht
  have hL : L x = (1/2 : ℝ) • (∑ i, x i • d i) := by
    dsimp only [L]
    rw [Module.Basis.constr_apply_fintype]
    change (∑ i, x i • ((1/2 : ℝ) • d i)) = _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    module
  change L x + o = f x
  rw [hL, ← ht]
  have ha := anti x hx
  have hh : (1/2 : ℝ) • (f x + f (-x)) = o := by rw [ha]; module
  rw [← hh]
  module

include hc hs hg hB in
/-- Every whole original ball has a unique chart-affine center graph. Its
entire closed ball maps into the original base. Uniqueness is on the chart
carrier, equivalently the affine span of the source ball. -/
theorem whole_ball_center_affine (hBC : binaryCompatible hB)
    (p : pure C u) (b : ExclusionChart C u p) :
    ∃! g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
      (∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx)) ∧
      g '' Metric.closedBall 0 1 ⊆ base C u := by
  classical
  let E := EuclideanSpace ℝ (Fin b.dim)
  let f (x : E) : V := if hx : ‖x‖ = 1 then
    center hB (chartPure hc hs hg hB p b x hx) else 0
  obtain ⟨g, hgs⟩ := sphere_chord_extension b.dim_pos f (by
    intro x y z w hx hy hz hw t v ht hv he
    have he' : t • (chartPure hc hs hg hB p b x hx : V) +
        (1-t) • (chartPure hc hs hg hB p b y hy : V) =
        v • (chartPure hc hs hg hB p b z hz : V) +
        (1-v) • (chartPure hc hs hg hB p b w hw : V) := by
      change t • b.param x + (1-t) • b.param y = v • b.param z + (1-v) • b.param w
      rw [← Convex.combo_affine_apply (by ring), ← Convex.combo_affine_apply (by ring), he]
    simpa only [f, dite_eq_left hx, dite_eq_left hy, dite_eq_left hz, dite_eq_left hw] using
      hBC (chartPure hc hs hg hB p b x hx) (chartPure hc hs hg hB p b y hy)
        (chartPure hc hs hg hB p b z hz) (chartPure hc hs hg hB p b w hw) t v ht hv he')
  have hboundary (x : E) (hx : ‖x‖ = 1) :
      g x = center hB (chartPure hc hs hg hB p b x hx) := by
    simpa [f, hx] using hgs x hx
  letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  have hball : convexHull ℝ (Metric.sphere (0 : E) 1) = Metric.closedBall 0 1 :=
    convexHull_sphere_eq_closedBall 0 zero_le_one
  have hspan : affineSpan ℝ (Metric.sphere (0 : E) 1) = ⊤ := by
    rw [← affineSpan_convexHull, hball]
    apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
    exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds (0 : E) zero_lt_one)⟩
  refine ⟨g, ⟨hboundary, ?_⟩, ?_⟩
  · rw [← hball, g.image_convexHull]
    apply convexHull_min _ (base_convex C u)
    rintro _ ⟨x, hx, rfl⟩
    rw [hboundary x (by simpa using hx)]
    exact (chart_mem (hB _).some (by simp)).1
  · intro k hk
    apply AffineMap.ext_on hspan
    intro x hx
    exact (hk.1 x (by simpa using hx)).trans (hboundary x (by simpa using hx)).symm

include hc hs hg hB in
private theorem balls_eq_of_center_eq (p q : pure C u)
    (he : center hB p = center hB q) : exclusion C u p = exclusion C u q := by
  have all := (exclusion_ball_faces hc hs hg hB).1
  let F := exclusion C u p ∩ exclusion C u q
  have hm := (MixedExclusionGeometry.centerSection hc hs hg hB p).property
  have hp : center hB p ∈ F :=
    ⟨chart_mem (hB p).some (by simp), he.symm ▸ chart_mem (hB q).some (by simp)⟩
  have hface : IsExtreme ℝ (base C u) F :=
    (all p).2.2.2.2.1.inter (all q).2.2.2.2.1
  have hn : F.Nontrivial := by
    by_contra hn
    have hsingle := (Set.not_nontrivial_iff.mp hn).eq_singleton_of_mem hp
    exact hm.1 (isExtreme_singleton.mp (hsingle ▸ hface))
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  exact equal_of_two_points hc hs hg hB p q hxy hx hy

include hc hs hg hB in
private theorem center_graph_branches (p : pure C u) (b : ExclusionChart C u p)
    (g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V)
    (hb : ∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx)) :
    (SingleLabel C u p → Function.Injective g ∧ Module.finrank ℝ g.linear.range = b.dim) ∧
    (¬ SingleLabel C u p → ∃ c : V, ∀ x, g x = c) := by
  classical
  let E := EuclideanSpace ℝ (Fin b.dim)
  have spanSphere : affineSpan ℝ (Metric.sphere (0 : E) 1) = ⊤ := by
    letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
    rw [← affineSpan_convexHull, convexHull_sphere_eq_closedBall 0 zero_le_one]
    apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
    exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds (0 : E) zero_lt_one)⟩
  constructor
  · intro hp
    have hlin : Function.Injective g.linear := by
      apply (injective_iff_map_eq_zero g.linear).mpr
      intro z hz
      by_contra hzne
      let k : E := ‖z‖⁻¹ • z
      have hk : ‖k‖ = 1 := by simp [k, norm_smul, norm_ne_zero_iff.mpr hzne]
      have hl : g.linear k = 0 := by simp [k, hz]
      have he : g k = g (-k) := by
        rw [show g k = g.linear k + g 0 from congrFun g.decomp k,
          show g (-k) = g.linear (-k) + g 0 from congrFun g.decomp (-k), map_neg, hl]
        simp
      let r := chartPure hc hs hg hB p b k hk
      let s := chartPure hc hs hg hB p b (-k) (by simpa using hk)
      have hec : center hB r = center hB s := by rw [← hb, ← hb]; exact he
      have her : exclusion C u r = exclusion C u s := balls_eq_of_center_eq hc hs hg hB r s hec
      have hrp : (r : V) ∈ exclusion C u p := chart_mem b (by simpa using hk.le)
      have hrs : r = s := (single_label_neighbor hc hs hg hB p r hp hrp s her.symm).symm
      have hks : k = -k := b.injective (congrArg Subtype.val hrs)
      have hk0 : k = 0 := by
        have hh : (2 : ℝ) • k = 0 := by
          calc
            (2 : ℝ) • k = k + k := two_smul ℝ k
            _ = k + (-k) := congrArg (fun v : E => k + v) hks
            _ = 0 := add_neg_cancel k
        exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
      rw [hk0, norm_zero] at hk
      norm_num at hk
    have hgi := g.linear_injective_iff.mp hlin
    exact ⟨hgi, (LinearMap.finrank_range_of_inj hlin).trans finrank_euclideanSpace_fin⟩
  · intro hp
    obtain ⟨s, hns⟩ := not_forall.mp hp
    obtain ⟨hsp, hne⟩ := not_imp.mp hns
    obtain ⟨q, r, hq, hr, hqr⟩ := pure_pair_in_ball hc hs hg hB p
    have hf := repeated_partner_fibers hc hs hg hB p s q (Ne.symm hne) hsp hq
    have hgconst : g = AffineMap.const ℝ E (center hB q) := by
      apply AffineMap.ext_on spanSphere
      intro x hx
      have hnx : ‖x‖ = 1 := by simpa using hx
      rw [hb x hnx]
      exact center_eq_of_exclusion_eq hB _ q ((hf.1 _).mpr (chart_mem b hnx.le))
    exact ⟨center hB q, fun x => by rw [hgconst]; rfl⟩

include hc hs hg hB in
/-- The actual BC graph exists on every whole original ball and has only
the constant repeated-fiber branch or the injective full-chart-rank branch. -/
theorem whole_ball_center_graph (hBC : binaryCompatible hB)
    (p : pure C u) (b : ExclusionChart C u p) :
    ∃ g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
      (∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx)) ∧
      g '' Metric.closedBall 0 1 ⊆ base C u ∧
      (∀ k : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
        (∀ x (hx : ‖x‖ = 1), k x = center hB (chartPure hc hs hg hB p b x hx)) → k = g) ∧
      (SingleLabel C u p → Function.Injective g ∧ Module.finrank ℝ g.linear.range = b.dim) ∧
      (¬ SingleLabel C u p → ∃ c : V, ∀ x, g x = c) := by
  obtain ⟨g, hgraph, huniq⟩ := whole_ball_center_affine hc hs hg hB hBC p b
  have hb := center_graph_branches hc hs hg hB p b g hgraph.1
  refine ⟨g, hgraph.1, hgraph.2, ?_, hb.1, hb.2⟩
  intro k hk
  have hsphere : affineSpan ℝ (Metric.sphere (0 : EuclideanSpace ℝ (Fin b.dim)) 1) = ⊤ := by
    letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
    rw [← affineSpan_convexHull, convexHull_sphere_eq_closedBall 0 zero_le_one]
    apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
    exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
  exact AffineMap.ext_on hsphere (fun x hx =>
    (hk x (by simpa using hx)).trans (hgraph.1 x (by simpa using hx)).symm)

include hc hs hg hB in
private theorem center_graph_interior (p : pure C u) (b : ExclusionChart C u p)
    (g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V)
    (hb : ∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx))
    (hK : g '' Metric.closedBall 0 1 ⊆ base C u) (hi : Function.Injective g)
    {z : EuclideanSpace ℝ (Fin b.dim)} (hz : ‖z‖ < 1) :
    g z ∈ intrinsicInterior ℝ (base C u) := by
  by_contra hn
  have hfro : g z ∈ intrinsicFrontier ℝ (base C u) := by
    rw [← closure_sdiff_intrinsicInterior]
    exact ⟨subset_closure (hK ⟨z, by simpa using hz.le, rfl⟩), hn⟩
  obtain ⟨r, hr⟩ := MixedExclusionGeometry.frontier_covered hc hs hg hfro
  have all := (exclusion_ball_faces hc hs hg hB).1
  obtain ⟨f, hf, hzero⟩ := (all r).2.2.2.2.2.2
  have hvan := UniqueConfirmationDensity.affine_zero_inside_ball (f.toAffineMap.comp g)
    (fun w hw => (hf.1 (g w) (hK ⟨w, by simpa using hw, rfl⟩).1).1)
    hz (show f (g z) = 0 from (hzero ▸ hr).2)
  have hsame (x : EuclideanSpace ℝ (Fin b.dim)) (hx : ‖x‖ = 1) :
      g x = center hB r := by
    let q := chartPure hc hs hg hB p b x hx
    have hcq : center hB q ∈ intrinsicInterior ℝ (exclusion C u q) := by
      rw [MixedExclusionGeometry.chart_intrinsic q (hB q).some]
      exact ⟨0, by simp, rfl⟩
    have hfc : f (center hB q) = 0 := by rw [← hb x hx]; exact hvan x
    have hsub : exclusion C u q ⊆ exclusion C u r := by
      intro y hy
      rw [hzero]
      exact ⟨hy.1, UniqueConfirmationDensity.zero_on_exclusion_of_zero_interior hB q f
        (fun v hv => (hf.1 v hv).1) hcq hfc y hy⟩
    have he : exclusion C u q = exclusion C u r :=
      chart_face_eq (hB r).some (all q).2.2.1
        ((all q).2.2.2.2.1.mono (all r).2.2.2.2.1.subset hsub) (all q).1
    exact (hb x hx).trans (center_eq_of_exclusion_eq hB q r he)
  let e := EuclideanSpace.basisFun (Fin b.dim) ℝ ⟨0, b.dim_pos⟩
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin b.dim) ℝ).norm_eq_one _
  have heq : e = -e := hi ((hsame e he).trans (hsame (-e) (by simpa using he)).symm)
  have h2 : (2 : ℝ) • e = 0 := by
    calc
      (2 : ℝ) • e = e + e := two_smul ℝ e
      _ = e + (-e) := congrArg (fun v => e + v) heq
      _ = 0 := add_neg_cancel e
  have he0 : e = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [he0, norm_zero] at he
  norm_num at he

include hc hs hg hB in
private theorem center_graph_transverse (p : pure C u) (b : ExclusionChart C u p)
    (g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V)
    (hb : ∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx))
    (hi : Function.Injective g)
    (hsec : g '' Metric.closedBall 0 1 = base C u ∩ Set.range g)
    (x : EuclideanSpace ℝ (Fin b.dim)) (hx : ‖x‖ = 1) :
    Disjoint g.linear.range
      (hB (chartPure hc hs hg hB p b x hx)).some.param.linear.range := by
  letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  let q := chartPure hc hs hg hB p b x hx
  let a := (hB q).some
  let E := g '' Metric.closedBall 0 1
  have hcq : center hB q = g x := (hb x hx).symm
  have hext : center hB q ∈ E.extremePoints ℝ := by
    rw [hcq]
    apply affine_extreme_image _ (convex_closedBall _ _) g hi.injOn
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    simpa using hx
  apply Submodule.disjoint_def.mpr
  rintro z ⟨w, hw⟩ ⟨v, hv⟩
  let ε : ℝ := (‖v‖ + 1)⁻¹
  have hε : 0 < ε := inv_pos.mpr (by positivity)
  have hsmall : ‖ε • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    dsimp [ε]
    exact (inv_mul_le_one₀ (by positivity : 0 < ‖v‖+1)).mpr (by linarith)
  have hparam (t : ℝ) : a.param (t • v) = center hB q + t • z := by
    rw [show a.param (t • v) = a.param.linear (t • v) + a.param 0 from
      congrFun a.param.decomp (t • v), map_smul, hv]
    exact add_comm _ _
  have hinK (t : ℝ) (ht : ‖t • v‖ ≤ 1) : center hB q + t • z ∈ base C u :=
    (hparam t) ▸ (chart_mem a ht).1
  have hinRange (t : ℝ) : center hB q + t • z ∈ Set.range g := by
    refine ⟨t • w + x, ?_⟩
    rw [show g (t • w + x) = g.linear (t • w) + g x from g.map_vadd x (t • w),
      map_smul, hw, ← hcq, add_comm]
  have hp : center hB q + ε • z ∈ E := by
    dsimp only [E]
    rw [hsec]
    exact ⟨hinK ε hsmall, hinRange ε⟩
  have hm : center hB q + (-ε) • z ∈ E := by
    dsimp only [E]
    rw [hsec]
    exact ⟨hinK (-ε) (by simpa using hsmall), hinRange (-ε)⟩
  have hmid : center hB q ∈ openSegment ℝ
      (center hB q + ε • z) (center hB q + (-ε) • z) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have he := hext.2 hp hm hmid
  have hz : ε • z = 0 := by
    apply add_left_cancel (a := center hB q)
    simpa using he
  exact (smul_eq_zero.mp hz).resolve_left hε.ne'

include hc hs hg hB in
/-- A singleton-label original ball has an entire interior center image and
an exact section of the original base by its image affine carrier. -/
theorem whole_ball_center_section (hBC : binaryCompatible hB)
    (p : pure C u) (hp : SingleLabel C u p) (b : ExclusionChart C u p) :
    ∃ g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
      (∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx)) ∧
      Function.Injective g ∧ Module.finrank ℝ g.linear.range = b.dim ∧
      (∀ x, ‖x‖ < 1 → g x ∈ intrinsicInterior ℝ (base C u)) ∧
      g '' Metric.closedBall 0 1 = base C u ∩ Set.range g ∧
      (∀ x (hx : ‖x‖ = 1), Disjoint g.linear.range
        (hB (chartPure hc hs hg hB p b x hx)).some.param.linear.range) := by
  obtain ⟨g, hb, hK, hu, hi, hr⟩ := whole_ball_center_graph hc hs hg hB hBC p b
  have hgi := (hi hp).1
  have hint (x : EuclideanSpace ℝ (Fin b.dim)) (hx : ‖x‖ < 1) :=
    center_graph_interior hc hs hg hB p b g hb hK hgi hx
  have hsection : g '' Metric.closedBall 0 1 = base C u ∩ Set.range g := by
    apply Subset.antisymm
    · rintro y hy
      exact ⟨hK hy, by obtain ⟨x, hx, rfl⟩ := hy; exact ⟨x, rfl⟩⟩
    · rintro y ⟨hy, z, rfl⟩
      have hn : ‖z‖ ≤ 1 := by
        by_contra hn
        have hz : 1 < ‖z‖ := lt_of_not_ge hn
        have hz0 : 0 < ‖z‖ := lt_trans zero_lt_one hz
        let w := ‖z‖⁻¹ • z
        have hw : ‖w‖ = 1 := by simp [w, norm_smul, hz0.ne']
        have hseg : g w ∈ openSegment ℝ (g 0) (g z) := by
          refine ⟨1 - ‖z‖⁻¹, ‖z‖⁻¹, ?_, inv_pos.mpr hz0, by ring, ?_⟩
          · exact sub_pos.mpr ((inv_lt_one₀ hz0).mpr hz)
          · rw [← Convex.combo_affine_apply (by ring)]
            congr 1
            simp [w]
        have hri := (base_convex C u).openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
          (hint 0 (by simp : ‖(0 : EuclideanSpace ℝ (Fin b.dim))‖ < 1))
          (subset_intrinsicClosure hy) hseg
        have hbd : g w ∈ intrinsicFrontier ℝ (base C u) := by
          rw [hb w hw]
          exact MixedExclusionGeometry.exclusion_frontier hc hs hg hB _ (chart_mem (hB _).some (by simp))
        rw [← closure_sdiff_intrinsicInterior] at hbd
        exact hbd.2 hri
      exact ⟨z, by simpa using hn, rfl⟩
  exact ⟨g, hb, hgi, (hi hp).2, hint, hsection,
    center_graph_transverse hc hs hg hB p b g hb hgi hsection⟩

theorem affine_ball_frontier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (g : E →ᵃ[ℝ] V) (hi : Function.Injective g) :
    intrinsicFrontier ℝ (g '' Metric.closedBall 0 1) = g '' Metric.sphere 0 1 := by
  have htop : affineSpan ℝ (Metric.closedBall (0 : E) 1) = ⊤ :=
    (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
      ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds (0 : E) zero_lt_one)⟩
  have hint : intrinsicInterior ℝ (Metric.closedBall (0 : E) 1) = Metric.ball 0 1 := by
    let A := affineSpan ℝ (Metric.closedBall (0 : E) 1)
    let e := AffineIsometryEquiv.ofTop A htop
    have he : (e : A → E) = ((↑) : A → E) := by
      funext x
      exact AffineIsometryEquiv.ofTop_apply htop x
    change ((↑) : A → E) '' interior (((↑) : A → E) ⁻¹' Metric.closedBall 0 1) = _
    rw [← he]
    change e.toHomeomorph '' interior (e.toHomeomorph ⁻¹' Metric.closedBall 0 1) = _
    rw [e.toHomeomorph.image_interior]
    change interior ((e : A → E) '' ((e : A → E) ⁻¹' Metric.closedBall 0 1)) = _
    rw [Set.image_preimage_eq _ e.surjective, interior_closedBall]
    norm_num
  have hc : IsClosed (g '' Metric.closedBall (0 : E) 1) :=
    ((isCompact_closedBall _ _).image g.continuous_of_finiteDimensional).isClosed
  rw [← closure_sdiff_intrinsicInterior, hc.closure_eq,
    CommonSourceLiftObstruction.intrinsic_interior_image g hi, hint,
    ← Set.image_sdiff hi, Metric.closedBall_sdiff_ball]

include hc hs hg in
/-- The complete singleton center-section geometry in the original EB3 model.
The dimension bound and existence are on the same original normalized base. -/
theorem original_center_sections [Nontrivial V] (h3 : threeBallExclusions C u)
    (hBC : binaryCompatible (CommonOldExclusionConfirmation.three_implies_balls h3)) :
    6 ≤ Module.finrank ℝ (affineSpan ℝ (base C u)).direction ∧
    (∃ p : pure C u, SingleLabel C u p) ∧
    ∀ p : pure C u, SingleLabel C u p →
      ∃ b : ExclusionChart C u p, b.dim = 3 ∧
      ∃ g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
        (∀ x (hx : ‖x‖ = 1), g x = center
          (CommonOldExclusionConfirmation.three_implies_balls h3)
          (chartPure hc hs hg (CommonOldExclusionConfirmation.three_implies_balls h3) p b x hx)) ∧
        Function.Injective g ∧ Module.finrank ℝ g.linear.range = 3 ∧
        (∀ x, ‖x‖ < 1 → g x ∈ intrinsicInterior ℝ (base C u)) ∧
        g '' Metric.closedBall 0 1 =
          base C u ∩ (affineSpan ℝ (g '' Metric.closedBall 0 1) : Set V) ∧
        intrinsicFrontier ℝ (g '' Metric.closedBall 0 1) = g '' Metric.sphere 0 1 ∧
        g '' Metric.sphere 0 1 ⊆ intrinsicFrontier ℝ (base C u) ∧
        (∀ x (hx : ‖x‖ = 1), Disjoint g.linear.range
          ((CommonOldExclusionConfirmation.three_implies_balls h3)
            (chartPure hc hs hg (CommonOldExclusionConfirmation.three_implies_balls h3) p b x hx)).some.param.linear.range) := by
  let B := CommonOldExclusionConfirmation.three_implies_balls h3
  let chart (p : pure C u) : ExclusionChart C u p :=
    ⟨3, by norm_num, CommonOldExclusionConfirmation.oldChart h3 p,
      (h3 p).choose_spec.1, (h3 p).choose_spec.2⟩
  obtain ⟨p₀, hp₀⟩ := ActualExclusionBoundary.original_singleton_label_exists hc hs hg B
  have hdim : 6 ≤ Module.finrank ℝ (affineSpan ℝ (base C u)).direction := by
    obtain ⟨q, r, hq, hr, hqr⟩ := pure_pair_in_ball hc hs hg B p₀
    have hnat := native_dimension hc hs hg B p₀ hp₀ (chart p₀) q hq (chart q)
    have hnonzero : (p₀ : V) ≠ 0 := by
      intro he
      have hunit := (pure_mem p₀).2
      rw [he, map_zero] at hunit
      norm_num at hunit
    have hbase := normalized_face_dimension C u hs ⟨p₀, (pure_mem p₀).1, hnonzero⟩
    rw [hg, finrank_top] at hbase
    dsimp [chart] at hnat
    omega
  refine ⟨hdim, ⟨p₀, hp₀⟩, ?_⟩
  intro p hp
  let b := chart p
  obtain ⟨g, hb, hi, hrank, hint, hsection, htrans⟩ :=
    whole_ball_center_section hc hs hg B hBC p hp b
  have hspan : (affineSpan ℝ (g '' Metric.closedBall 0 1) : Set V) = Set.range g := by
    have hs : affineSpan ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) 1) = ⊤ :=
      (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
        ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
    rw [← AffineSubspace.map_span, hs]
    ext y
    simp
  refine ⟨b, rfl, g, hb, hi, hrank, hint, ?_, ?_, ?_, htrans⟩
  · rw [hspan]
    exact hsection
  · exact affine_ball_frontier g hi
  · rintro _ ⟨x, hx, rfl⟩
    rw [hb x (by simpa using hx)]
    exact MixedExclusionGeometry.exclusion_frontier hc hs hg B _
      (chart_mem (B _).some (by simp))

include hc hs hg hB in
/-- On each actual chart sphere, BC alone gives a quantitative Lipschitz
bound for the original centers. No global center-continuity assumption is used. -/
theorem sphere_center_lipschitz (hBC : binaryCompatible hB)
    (p : pure C u) (b : ExclusionChart C u p) :
    LipschitzWith ⟨Metric.diam (base C u) / 2, by positivity⟩
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin b.dim)) 1 =>
        center hB (chartPure hc hs hg hB p b x (by simpa using x.property))) := by
  let E := EuclideanSpace ℝ (Fin b.dim)
  let label (z : E) (hz : ‖z‖ = 1) := chartPure hc hs hg hB p b z hz
  have memK (r : pure C u) : center hB r ∈ base C u :=
    (chart_mem (hB r).some (by simp)).1
  have mapCombo (x y : E) (t : ℝ) :
      b.param (t • x + (1-t) • y) = t • b.param x + (1-t) • b.param y :=
    Convex.combo_affine_apply (by ring)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : ‖(x : E)‖ = 1 := by simpa using x.property
  have hy : ‖(y : E)‖ = 1 := by simpa using y.property
  by_cases hxy : (x : E) = y
  · have he : x = y := Subtype.ext hxy
    subst y
    simp
  let d : ℝ := ‖(x : E) - y‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hd2 : d ≤ 2 := by
    calc
      d ≤ ‖(x : E)‖ + ‖(y : E)‖ := norm_sub_le _ _
      _ = 2 := by rw [hx, hy]; norm_num
  let k : E := d⁻¹ • ((x : E) - y)
  have hk : ‖k‖ = 1 := by
    simp [k, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le), d, hd.ne']
  have hdk : d • k = (x : E) - y := by simp [k, smul_smul, hd.ne']
  let v : ℝ := (2+d)/4
  have hv : v ∈ Icc (0 : ℝ) 1 := by dsimp [v]; constructor <;> linarith
  let a := label x hx
  let c := label y hy
  let nc := label (-(y : E)) (by simpa using hy)
  let z := label k hk
  let nz := label (-k) (by simpa using hk)
  have orig : (1/2 : ℝ) • (a : V) + (1-1/2 : ℝ) • (nc : V) =
      v • (z : V) + (1-v) • (nz : V) := by
    change (1/2 : ℝ) • b.param x + (1-1/2 : ℝ) • b.param (-(y : E)) =
      v • b.param k + (1-v) • b.param (-k)
    rw [← mapCombo, ← mapCombo]
    congr 1
    calc
      (1/2 : ℝ) • (x : E) + (1-1/2 : ℝ) • (-(y : E)) =
          (1/2 : ℝ) • ((x : E) - y) := by module
      _ = (d/2) • k := by rw [← hdk]; module
      _ = v • k + (1-v) • (-k) := by dsimp [v]; module
  have origAnti : (1/2 : ℝ) • (c : V) + (1-1/2 : ℝ) • (nc : V) =
      (1/2 : ℝ) • (z : V) + (1-1/2 : ℝ) • (nz : V) := by
    change (1/2 : ℝ) • b.param y + (1-1/2 : ℝ) • b.param (-(y : E)) =
      (1/2 : ℝ) • b.param k + (1-1/2 : ℝ) • b.param (-k)
    rw [← mapCombo, ← mapCombo]
    congr 1
    module
  have bc := hBC a nc z nz (1/2) v (by norm_num) hv orig
  have ba := hBC c nc z nz (1/2) (1/2) (by norm_num) (by norm_num) origAnti
  have hsum : center hB a + center hB nc =
      (2*v) • center hB z + (2*(1-v)) • center hB nz := by
    have h := congrArg (fun w : V => (2 : ℝ) • w) bc
    convert h using 1 <;> module
  have hanti : center hB c + center hB nc = center hB z + center hB nz := by
    have h := congrArg (fun w : V => (2 : ℝ) • w) ba
    convert h using 1 <;> module
  have hdiff : center hB a - center hB c =
      (d/2) • (center hB z - center hB nz) := by
    calc
      center hB a - center hB c =
          (center hB a + center hB nc) - (center hB c + center hB nc) := by abel
      _ = (2*v) • center hB z + (2*(1-v)) • center hB nz -
          (center hB z + center hB nz) := by rw [hsum, hanti]
      _ = _ := by dsimp [v]; module
  have hbound : ‖center hB z - center hB nz‖ ≤ Metric.diam (base C u) := by
    simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem'
      (base_compact hc hs).isBounded.ediam_ne_top (memK z) (memK nz)
  change dist (center hB a) (center hB c) ≤ (Metric.diam (base C u) / 2) * dist x y
  rw [dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg (div_nonneg hd.le (by norm_num))]
  calc
    d/2 * ‖center hB z - center hB nz‖ ≤ d/2 * Metric.diam (base C u) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (Metric.diam (base C u) / 2) * dist x y := by
      rw [Subtype.dist_eq, dist_eq_norm]
      dsimp [d]
      ring

include hc hs hg in
/-- The fixed-sphere minimum is attained and strictly positive. Its own
constant bounds every whole exclusion with label on that sphere, and a
diameter-zero sequence eventually avoids that fixed sphere. -/
theorem fixed_sphere_noncollapse (h3 : threeBallExclusions C u)
    (hBC : binaryCompatible (CommonOldExclusionConfirmation.three_implies_balls h3))
    (p : pure C u) :
    ∃ δ : ℝ, 0 < δ ∧
      (∃ q₀ : pure C u, (q₀ : V) ∈ exclusion C u p ∧
        δ = 2 * ‖(p : V) - center (CommonOldExclusionConfirmation.three_implies_balls h3) q₀‖ ∧
        ∀ q : pure C u, (q : V) ∈ exclusion C u p →
          δ ≤ 2 * ‖(p : V) - center (CommonOldExclusionConfirmation.three_implies_balls h3) q‖) ∧
      (∀ q : pure C u, (q : V) ∈ exclusion C u p → δ ≤ Metric.diam (exclusion C u q)) ∧
      ∀ an : ℕ → pure C u,
        Tendsto (fun n => Metric.diam (exclusion C u (an n))) atTop (𝓝 0) →
        ∀ᶠ n in atTop, (an n : V) ∉ exclusion C u p := by
  classical
  let B := CommonOldExclusionConfirmation.three_implies_balls h3
  let b := (B p).some
  let E := EuclideanSpace ℝ (Fin b.dim)
  let S := Metric.sphere (0 : E) 1
  let label (x : S) := chartPure hc hs hg B p b x (by simpa using x.property)
  let f (x : S) := ‖(p : V) - center B (label x)‖
  have hcont : Continuous f :=
    (continuous_const.sub (sphere_center_lipschitz hc hs hg B hBC p b).continuous).norm
  have : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  obtain ⟨z, hz⟩ := exists_norm_eq E zero_le_one
  have hSne : (Set.univ : Set S).Nonempty := ⟨⟨z, by simpa [S] using hz⟩, mem_univ _⟩
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  obtain ⟨x₀, _, hmin⟩ := isCompact_univ.exists_isMinOn hSne hcont.continuousOn
  have hpos : 0 < f x₀ := by
    apply norm_pos_iff.mpr
    intro hzero
    have he : (p : V) = center B (label x₀) := sub_eq_zero.mp hzero
    have hm := (MixedExclusionGeometry.centerSection hc hs hg B (label x₀)).property.1
    apply hm
    change center B (label x₀) ∈ pure C u
    rw [← he]
    exact p.property
  let δ := 2 * f x₀
  have hδ : 0 < δ := mul_pos (by norm_num) hpos
  have onSphere (q : pure C u) (hq : (q : V) ∈ exclusion C u p) :
      ∃ x : S, label x = q := by
    have hh : (q : V) ∈ exclusion C u p ∩ pure C u := ⟨hq, q.property⟩
    rw [chart_boundary hc hs hg B p b] at hh
    obtain ⟨x, hx, hxe⟩ := hh
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hminq (q : pure C u) (hq : (q : V) ∈ exclusion C u p) :
      δ ≤ 2 * ‖(p : V) - center B q‖ := by
    obtain ⟨x, rfl⟩ := onSphere q hq
    exact mul_le_mul_of_nonneg_left (hmin (mem_univ x)) (by norm_num)
  have oldCenter_eq (q : pure C u) : CommonOldExclusionConfirmation.oldCenter h3 q = center B q := by
    let g := CommonOldExclusionConfirmation.oldChart h3 q
    have gd (x) : g x = g 0 + g.linear.toContinuousLinearMap x := by
      simpa [add_comm] using congrFun g.decomp x
    have bd (x) : (B q).some.param x = (B q).some.param 0 +
        (B q).some.param.linear.toContinuousLinearMap x := by
      simpa [add_comm] using congrFun (B q).some.param.decomp x
    apply D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq
      (g 0) ((B q).some.param 0) g.linear.toContinuousLinearMap
      (B q).some.param.linear.toContinuousLinearMap
    have whole : g '' closedBall 0 1 =
        (B q).some.param '' closedBall 0 1 :=
      (h3 q).choose_spec.2.trans (B q).some.whole.symm
    rw [show (fun x => g 0 + g.linear.toContinuousLinearMap x) = g from
      funext (fun x => (gd x).symm)]
    rw [show (fun x => (B q).some.param 0 +
        (B q).some.param.linear.toContinuousLinearMap x) = (B q).some.param from
      funext (fun x => (bd x).symm)]
    exact whole
  have bound (q : pure C u) (hq : (q : V) ∈ exclusion C u p) :
      δ ≤ Metric.diam (exclusion C u q) := by
    have hp := (exclusion_symmetric p q).mp hq
    have hr := (CommonOldExclusionConfirmation.old_geometry hc hs hg h3 q).2.1 p hp
    rw [oldCenter_eq] at hr
    have hdiam := Metric.dist_le_diam_of_mem'
      ((exclusion_ball_faces hc hs hg B).1 q).2.1.isBounded.ediam_ne_top hp hr
    have he : dist (p : V) ((2 : ℝ) • center B q - p) =
        2 * ‖(p : V) - center B q‖ := by
      rw [dist_eq_norm, show (p : V) - ((2 : ℝ) • center B q - p) =
        (2 : ℝ) • ((p : V) - center B q) by module, norm_smul]
      norm_num
    exact (hminq q hq).trans (he ▸ hdiam)
  refine ⟨δ, hδ, ⟨label x₀, chart_mem b (by simpa using (le_of_eq (Metric.mem_sphere_zero_iff_norm.mp x₀.property))), rfl, hminq⟩,
    bound, ?_⟩
  intro an han
  have hsmall : ∀ᶠ n in atTop, Metric.diam (exclusion C u (an n)) < δ :=
    han.eventually (gt_mem_nhds hδ)
  exact hsmall.mono (fun n hn hnp => (not_lt_of_ge (bound (an n) hnp)) hn)

end D5.S3.Quantum.Foundation.BinaryCenterNoncollapse
