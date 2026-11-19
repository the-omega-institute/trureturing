/- GID: D5/S3/Quantum/Foundation/BinaryCenterGraph
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/BinaryCenterGraph
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Affine center graphs on whole original exclusion balls. -/

import D5.S3.Quantum.Foundation.BinaryCenterNoncollapse

/-! A whole exclusion ball has a unique affine graph of the original centers. -/

noncomputable section
open Set Metric Filter Topology
open scoped BigOperators RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.BinaryCenterGeometry

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity SingleLabelNormalBody ContinuousFrameSum ReciprocalExclusionLimits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

variable (hc : IsClosed (C : Set V))
  (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)

/-- Choice-independent equality of the existing original centers. -/
private theorem center_eq_of_exclusion_eq (p q : pure C u)
    (he : exclusion C u p = exclusion C u q) : center hB p = center hB q := by
  have decomp (r : pure C u) (x) :
      (hB r).some.param x = (hB r).some.param 0 +
        (hB r).some.param.linear.toContinuousLinearMap x := by
    simpa [add_comm] using congrFun (hB r).some.param.decomp x
  apply D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq
    (center hB p) (center hB q) (hB p).some.param.linear.toContinuousLinearMap
    (hB q).some.param.linear.toContinuousLinearMap
  simpa only [ContinuousFrameSum.center, ← decomp] using
    (hB p).some.whole.trans (he.trans (hB q).some.whole.symm)

private theorem affineSpan_unitSphere {n : ℕ} (hn : 0 < n) :
    affineSpan ℝ (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = ⊤ := by
  let E := EuclideanSpace ℝ (Fin n)
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← affineSpan_convexHull, convexHull_sphere_eq_closedBall 0 zero_le_one]
  apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
  exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds (0 : E) zero_lt_one)⟩

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
  have hspan := affineSpan_unitSphere b.dim_pos
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
  have spanSphere := affineSpan_unitSphere b.dim_pos
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
    obtain ⟨q, _, hq, _, _⟩ := pure_pair_in_ball hc hs hg hB p
    have partner (r : pure C u) (hr : (r : V) ∈ exclusion C u p) :
        exclusion C u r = exclusion C u q := by
      apply equal_of_two_points hc hs hg hB r q (Subtype.val_injective.ne (Ne.symm hne))
      · exact ⟨(exclusion_symmetric p r).mp hr, (exclusion_symmetric p q).mp hq⟩
      · exact ⟨(exclusion_symmetric s r).mp (hsp.symm ▸ hr),
          (exclusion_symmetric s q).mp (hsp.symm ▸ hq)⟩
    have hgconst : g = AffineMap.const ℝ E (center hB q) := by
      apply AffineMap.ext_on spanSphere
      intro x hx
      have hnx : ‖x‖ = 1 := by simpa using hx
      rw [hb x hnx]
      exact center_eq_of_exclusion_eq hB _ q (partner _ (chart_mem b hnx.le))
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
  have hsphere := affineSpan_unitSphere b.dim_pos
  exact AffineMap.ext_on hsphere (fun x hx =>
    (hk x (by simpa using hx)).trans (hgraph.1 x (by simpa using hx)).symm)

end D5.S3.Quantum.Foundation.BinaryCenterGeometry
