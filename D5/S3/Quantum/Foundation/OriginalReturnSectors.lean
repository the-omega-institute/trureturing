/- GID: D5/S3/Quantum/Foundation/OriginalReturnSectors
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalReturnSectors
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole original return faces near an arbitrary interior source. -/

import D5.S3.Quantum.Foundation.OriginalReturnSectors.Contacts
import D5.S3.Quantum.Foundation.OriginalReturnSectors.LinearGeometry

noncomputable section

namespace D5.S3.Quantum.Foundation.OriginalReturnSectors

open Set Filter Topology
open scoped RealInnerProductSpace
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity ContinuousFrameSum SingleLabelNormalBody WholePairBallConfirmation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Q133.7 with the actual attained maximum over the entire original return.
The constants precede both pure points; neither label injectivity nor purity
of any limiting label is required. -/
theorem whole_return_leakage (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r t : pure C u,
      dist (r : V) y < ε → (t : V) ∈ exclusion C u r → leakage C u p t < δ := by
  obtain ⟨ε, hε, h⟩ := whole_return_near_source hc hs hg hB p hy hδ
  refine ⟨ε, hε, fun r t hr ht => ?_⟩
  have hD := (exclusion_ball_faces hc hs hg hB).1 t
  exact (hD.2.1.sSup_lt_iff_of_continuous hD.1.nonempty
    (Metric.continuous_infDist_pt _).continuousOn δ).mpr (h r t hr ht)

/-- Actual source contacts exist for every relative-interior point and every
whole injective source chart, including segment balls and the chart center.
Strictly positive barycentric coordinates express interior of their simplex. -/
theorem source_contact_simplex (p : pure C u) (a : ExclusionChart C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p)) :
    ∃ (ξ : EuclideanSpace ℝ (Fin a.dim))
      (b : AffineBasis (Fin (a.dim + 1)) ℝ (EuclideanSpace ℝ (Fin a.dim))),
      a.param ξ = y ∧ ‖ξ‖ < 1 ∧ (∀ i, ‖b i‖ = 1) ∧
      (∀ i, 0 < b.coord i ξ) ∧ AffineIndependent ℝ (fun i => a.param (b i)) ∧
      Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction = a.dim ∧
      LinearMap.range a.param.linear ≤ LinearMap.ker u := by
  rw [MixedExclusionGeometry.chart_intrinsic p a] at hy
  obtain ⟨ξ, hξ, rfl⟩ := hy
  have hξ' : ‖ξ‖ < 1 := by simpa using hξ
  obtain ⟨b, hb, hpos⟩ := sphere_affine_basis a.dim_pos hξ'
  refine ⟨ξ, b, rfl, hξ', hb, hpos, b.ind.map' a.param a.injective,
    chart_dimension a,?_⟩
  rintro _ ⟨z,rfl⟩
  exact chart_unit_linear a z

/-- A single sector is valid for every original positive annihilator after
all constants have been chosen, without a bound on its global maximum. -/
theorem uniform_return_sectors (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (a : ExclusionChart C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (_hb : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ) :
    ∃ ε θ H : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < H ∧
      ∀ r t : pure C u, dist (r:V) y < ε → (t:V) ∈ exclusion C u r →
        Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction ≤ a.dim →
        ∃ i : Fin (a.dim+1), ∀ f : V →L[ℝ] ℝ,
          f ≠ 0 → (∀ x ∈ C, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
          ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
          ‖slope a f‖ ≤ H * baseMaximum C u f * leakage C u p t := by
  classical
  obtain ⟨δ,hδ,hstable⟩ := common_flat_reconstruction b (by simp) hpos
    (sourceInverse a) (fun i => a.param (b i)) (fun i => sourceInverse_apply a _)
    y (by rw [← hξ,sourceInverse_apply])
  obtain ⟨θ,H,hθ,hH,hcontact⟩ := sector_contact_family hc hs hg hB p a b hδ
  obtain ⟨ε₀,hε₀,hleak⟩ := whole_return_leakage hc hs hg hB p hy
    (show 0 < δ/4 by positivity)
  refine ⟨min ε₀ δ,θ,H,lt_min hε₀ hδ,hθ,hH,fun r t hr ht hdim => ?_⟩
  by_contra! hn
  have hα : leakage C u p t < δ/4 := hleak r t (hr.trans_le (min_le_left _ _)) ht
  obtain ⟨x,hx⟩ := hcontact t hα hn
  have hrD : (r:V) ∈ exclusion C u t := (exclusion_symmetric r t).mp ht
  obtain ⟨hind,w,hw,hsum,hrec⟩ := hstable (fun i => (x i:V)) r
    (affineSpan ℝ (exclusion C u t)) (fun i => (hx i).2) (hr.trans_le (min_le_right _ _))
    (fun i => subset_affineSpan ℝ _ (hx i).1) (subset_affineSpan ℝ _ hrD)
    (by simpa using hdim)
  have : Nontrivial (Fin (a.dim+1)) :=
    Fin.nontrivial_iff_two_le.mpr (Nat.succ_le_succ a.dim_pos)
  exact not_positive_simplex_extreme (fun i => (x i:V)) hind r
    (fun i => pure_mem (x i)) w hw hsum hrec

private theorem chart_operator_bound
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {p : V} (a : ExclusionChart C u p) :
    ‖a.param.linear.toContinuousLinearMap‖ ≤ Metric.diam (base C u)/2 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro z hz
  have hd := Metric.dist_le_diam_of_mem (base_compact hc hs).isBounded
    (chart_mem a hz.le).1 (chart_mem a (by simpa using hz.le : ‖-z‖ ≤ 1)).1
  have he : a.param z - a.param (-z) = (2:ℝ) • a.param.linear z := by
    rw [← vsub_eq_sub,← a.param.linear_apply_vsub,vsub_eq_sub]
    have hh : z - -z = (2:ℝ) • z := by module
    rw [hh,map_smul]
  rw [dist_eq_norm,he,norm_smul] at hd
  norm_num at hd
  change ‖a.param.linear z‖ ≤ _
  linarith

private theorem base_radius_positive
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (p : pure C u) (a : ExclusionChart C u p) : 0 < Metric.diam (base C u)/2 := by
  let z : EuclideanSpace ℝ (Fin a.dim) := EuclideanSpace.single ⟨0,a.dim_pos⟩ 1
  have hz : ‖z‖ = 1 := by simp [z]
  have hzne : z ≠ -z := by
    intro he
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin a.dim) => v ⟨0,a.dim_pos⟩) he
    norm_num [z] at hh
  have hne : a.param z ≠ a.param (-z) := a.injective.ne hzne
  have hh := Metric.dist_le_diam_of_mem (base_compact hc hs).isBounded
    (chart_mem a hz.le).1 (chart_mem a (by simpa using hz.le : ‖-z‖ ≤ 1)).1
  have hpos := (dist_pos.mpr hne).trans_le hh
  positivity

private theorem actual_parameter_unit
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (r t : pure C u) (ht : (t:V) ∈ exclusion C u r)
    (a : ExclusionChart C u t) (z : EuclideanSpace ℝ (Fin a.dim))
    (hz : a.param z = r) : ‖z‖ = 1 := by
  have hr : (r:V) ∈ exclusion C u t ∩ pure C u :=
    ⟨(exclusion_symmetric r t).mp ht,r.property⟩
  rw [chart_boundary hc hs hg hB t a] at hr
  obtain ⟨w,hw,he⟩ := hr
  have hzw := a.injective (hz.trans he.symm)
  rw [hzw]
  simpa using hw

private theorem actual_leakage_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (r t : ℕ → pure C u) (hr : Tendsto (fun n => (r n:V)) atTop (𝓝 y))
    (ht : ∀ n, (t n:V) ∈ exclusion C u (r n)) :
    Tendsto (fun n => leakage C u p (t n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨ε,hε,h⟩ := whole_return_leakage hc hs hg hB p hy hδ
  filter_upwards [Metric.tendsto_nhds.mp hr ε hε] with n hn
  have hα0 : 0 ≤ leakage C u p (t n) := by
    obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 (t n)).1.nonempty
    exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p (t n) hx)
  simpa [Real.dist_eq,abs_of_nonneg hα0] using h (r n) (t n) hn (ht n)

section EuclideanReturns
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {C₁ : PointedCone ℝ E} {u₁ : E →ₗ[ℝ] ℝ}

/-- Orthogonal affine projection onto the direction of the whole source face. -/
def sourceProjection (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) : E →ᵃ[ℝ] E :=
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  U.starProjection.toLinearMap.toAffineMap.comp
    ((AffineMap.id ℝ E) - AffineMap.const ℝ E (a.param 0)) +
      AffineMap.const ℝ E (a.param 0)

private theorem sourceProjection_linear (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) :
    (sourceProjection p a).linear =
      (affineSpan ℝ (exclusion C₁ u₁ p)).direction.starProjection.toLinearMap := by
  simp [sourceProjection]

private theorem sourceProjection_fix (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {z : E} (hz : z ∈ affineSpan ℝ (exclusion C₁ u₁ p)) : sourceProjection p a z = z := by
  have hc : a.param 0 ∈ affineSpan ℝ (exclusion C₁ u₁ p) :=
    subset_affineSpan ℝ _ (chart_mem a (by simp : ‖(0 : EuclideanSpace ℝ (Fin a.dim))‖ ≤ 1))
  have hd := (affineSpan ℝ (exclusion C₁ u₁ p)).vsub_mem_direction hz hc
  change z-a.param 0 ∈ (affineSpan ℝ (exclusion C₁ u₁ p)).direction at hd
  change (affineSpan ℝ (exclusion C₁ u₁ p)).direction.starProjection (z-a.param 0) + a.param 0 = z
  rw [Submodule.starProjection_eq_self_iff.mpr hd,sub_add_cancel]

private theorem sourceProjection_dist (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {z : E} (hz : z ∈ affineSpan ℝ (exclusion C₁ u₁ p)) (x : E) :
    dist (sourceProjection p a x) z ≤ dist x z := by
  calc
    _ = dist (sourceProjection p a x) (sourceProjection p a z) := by rw [sourceProjection_fix p a hz]
    _ = ‖(affineSpan ℝ (exclusion C₁ u₁ p)).direction.starProjection (x-z)‖ := by
      rw [dist_eq_norm,← vsub_eq_sub,← (sourceProjection p a).linear_apply_vsub,sourceProjection_linear]
      rfl
    _ ≤ dist x z := by simpa [dist_eq_norm] using (affineSpan ℝ (exclusion C₁ u₁ p)).direction.norm_starProjection_apply_le (x-z)

omit [FiniteDimensional ℝ E] in
private theorem chart_inverse_reconstruct (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {z : E} (hz : z ∈ affineSpan ℝ (exclusion C₁ u₁ p)) : a.param (sourceInverse a z) = z := by
  have hspan : affineSpan ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin a.dim)) 1) = ⊤ :=
    (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
      ⟨0,mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
  rw [← a.whole,← AffineSubspace.map_span,hspan] at hz
  obtain ⟨q,_,rfl⟩ := hz
  rw [sourceInverse_apply]

private theorem sourceProjection_mem (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) (z : E) :
    sourceProjection p a z ∈ affineSpan ℝ (exclusion C₁ u₁ p) := by
  have hc := subset_affineSpan ℝ (exclusion C₁ u₁ p) (chart_mem a (by simp : ‖(0 : EuclideanSpace ℝ (Fin a.dim))‖ ≤ 1))
  apply (affineSpan ℝ (exclusion C₁ u₁ p)).vadd_mem_of_mem_direction
    (v := (affineSpan ℝ (exclusion C₁ u₁ p)).direction.starProjection (z-a.param 0))
    (Submodule.starProjection_apply_mem _ _) hc

private theorem projected_simplex_ball (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (hunit : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ) :
    ∃ δ β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ x : Fin (a.dim+1) → E,
      (∀ i, dist (x i) (a.param (b i)) < δ) →
      Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
        convexHull ℝ (range (fun i => sourceProjection p a (x i))) := by
  obtain ⟨δ₀,β₀,hδ₀,hβ₀,hball⟩ := fixed_simplex_ball b hpos
  obtain ⟨K,hK⟩ := (sourceInverse a).lipschitzWith_of_finiteDimensional
  let D := (K:ℝ)+1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨δ₀/D,β₀/D,div_pos hδ₀ hD,div_pos hβ₀ hD,fun x hx z hz => ?_⟩
  have hproj (i) : dist (sourceInverse a (sourceProjection p a (x i))) (b i) < δ₀ := by
    rw [← sourceInverse_apply a (b i)]
    calc
      _ ≤ (K:ℝ)*dist (sourceProjection p a (x i)) (a.param (b i)) := hK.dist_le_mul _ _
      _ ≤ (K:ℝ)*dist (x i) (a.param (b i)) := mul_le_mul_of_nonneg_left
        (sourceProjection_dist p a (subset_affineSpan ℝ _ (chart_mem a (hunit i).le)) _) K.coe_nonneg
      _ ≤ D*dist (x i) (a.param (b i)) := by dsimp [D]; nlinarith [dist_nonneg (x:=x i) (y:=a.param (b i))]
      _ < D*(δ₀/D) := mul_lt_mul_of_pos_left (hx i) hD
      _ = δ₀ := mul_div_cancel₀ _ hD.ne'
  have hz' : sourceInverse a z ∈ Metric.closedBall ξ β₀ := by
    rw [Metric.mem_closedBall,← sourceInverse_apply a ξ,hξ]
    calc
      _ ≤ (K:ℝ)*dist z y := hK.dist_le_mul _ _
      _ ≤ D*dist z y := by dsimp [D]; nlinarith [dist_nonneg (x:=z) (y:=y)]
      _ ≤ D*(β₀/D) := mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hz.1) hD.le
      _ = β₀ := mul_div_cancel₀ _ hD.ne'
  have hzm := (hball (fun i => sourceInverse a (sourceProjection p a (x i))) hproj).2 hz'
  have him := mem_image_of_mem a.param hzm
  rw [a.param.image_convexHull] at him
  have hrange : a.param '' range (fun i => sourceInverse a (sourceProjection p a (x i))) =
      range (fun i => sourceProjection p a (x i)) := by
    rw [← range_comp]
    congr 1
    ext i
    exact chart_inverse_reconstruct p a (sourceProjection_mem p a (x i))
  rw [hrange,chart_inverse_reconstruct p a hz.2] at him
  exact him

/-- The actual return linear chart followed by the orthogonal source projection,
with its codomain restricted to the source direction. -/
def projectedLinear (p : pure C₁ u₁) {t : E}
    (c : ExclusionChart C₁ u₁ t) :
    EuclideanSpace ℝ (Fin c.dim) →L[ℝ] (affineSpan ℝ (exclusion C₁ u₁ p)).direction :=
  (affineSpan ℝ (exclusion C₁ u₁ p)).direction.orthogonalProjectionOnto.comp
    c.param.linear.toContinuousLinearMap

private theorem projectedLinear_formula (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {t : E} (c : ExclusionChart C₁ u₁ t) (z : EuclideanSpace ℝ (Fin c.dim)) :
    sourceProjection p a (c.param z) =
      (projectedLinear p c z:E) + sourceProjection p a (c.param 0) := by
  have h := (sourceProjection p a).linear_apply_vsub (c.param z) (c.param 0)
  rw [sourceProjection_linear] at h
  have hc : c.param z -ᵥ c.param 0 = c.param.linear z := by
    rw [← c.param.linear_apply_vsub,vsub_eq_sub,sub_zero]
  rw [hc] at h
  change (projectedLinear p c z:E) = sourceProjection p a (c.param z) - sourceProjection p a (c.param 0) at h
  exact (eq_sub_iff_add_eq.mp h).symm

private theorem actual_projected_margin
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (hy : y ∈ affineSpan ℝ (exclusion C₁ u₁ p))
    {β : ℝ} (_hβ : 0 < β) (hβR : β < Metric.diam (base C₁ u₁)/2)
    (r t : pure C₁ u₁) (ht : (t:E) ∈ exclusion C₁ u₁ r)
    (c : ExclusionChart C₁ u₁ t) (z : EuclideanSpace ℝ (Fin c.dim)) (hz : c.param z = r)
    (hnear : dist (r:E) y < β)
    (hball : Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
      sourceProjection p a '' exclusion C₁ u₁ t) :
    1-(1-(β-dist (r:E) y)/(Metric.diam (base C₁ u₁)/2))^2 ≤
      ‖(projectedLinear p c).ker.starProjection z‖^2 := by
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let A := projectedLinear p c
  let R := Metric.diam (base C₁ u₁)/2
  let ρ := β-dist (r:E) y
  have hR : 0 < R := base_radius_positive hc hs p a
  have hρ : 0 < ρ := sub_pos.mpr hnear
  have hρR : ρ ≤ R := by dsimp [ρ,R]; linarith [dist_nonneg (x:=(r:E)) (y:=y)]
  have hA : ‖A‖ ≤ R := by
    apply A.opNorm_le_bound hR.le
    intro v
    change ‖U.starProjection (c.param.linear v)‖ ≤ _
    exact (U.norm_starProjection_apply_le (c.param.linear v)).trans
      ((c.param.linear.toContinuousLinearMap.le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (chart_operator_bound hc hs c) (norm_nonneg v)))
  have heval : sourceProjection p a (r:E) = (A z:E) + sourceProjection p a (c.param 0) := by
    rw [← hz]; exact projectedLinear_formula p a c z
  have hballA : Metric.closedBall (A z) ρ ⊆ A '' Metric.closedBall 0 1 := by
    intro v hv
    let q : E := (v:E) + sourceProjection p a (c.param 0)
    have hqF : q ∈ affineSpan ℝ (exclusion C₁ u₁ p) :=
      (affineSpan ℝ (exclusion C₁ u₁ p)).vadd_mem_of_mem_direction
        v.property (sourceProjection_mem p a (c.param 0))
    have hqdist : dist q y ≤ β := by
      have hqr : dist q (sourceProjection p a (r:E)) ≤ ρ := by
        rw [heval]
        simpa only [q,dist_add_right,Subtype.dist_eq] using (Metric.mem_closedBall.mp hv)
      have hh := dist_triangle q (sourceProjection p a (r:E)) y
      have hp := sourceProjection_dist p a hy (r:E)
      dsimp [ρ] at hqr
      linarith
    obtain ⟨w,hw,he⟩ := hball ⟨Metric.mem_closedBall.mpr hqdist,hqF⟩
    obtain ⟨v₀,hv₀,rfl⟩ := c.whole.symm ▸ hw
    refine ⟨v₀,hv₀,?_⟩
    apply Subtype.val_injective
    have hh := projectedLinear_formula p a c v₀
    rw [he] at hh
    exact add_right_cancel hh.symm
  exact (kernel_margin A hR hρ hρR hA
    (actual_parameter_unit hc hs hg hB r t ht c z hz) hballA).2

private theorem normal_leakage
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p t : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) {x : E}
    (hx : x ∈ exclusion C₁ u₁ t) :
    ‖(affineSpan ℝ (exclusion C₁ u₁ p)).directionᗮ.starProjection (x-a.param 0)‖ ≤
      leakage C₁ u₁ p t := by
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let Q := Uᗮ.starProjection
  obtain ⟨q,hq,hqdist⟩ := ((exclusion_ball_faces hc hs hg hB).1 p).2.1.exists_infDist_eq_dist
    ((exclusion_ball_faces hc hs hg hB).1 p).1.nonempty x
  have hcF := subset_affineSpan ℝ (exclusion C₁ u₁ p)
    (chart_mem a (by simp : ‖(0 : EuclideanSpace ℝ (Fin a.dim))‖ ≤ 1))
  have hqU := (affineSpan ℝ (exclusion C₁ u₁ p)).vsub_mem_direction (subset_affineSpan ℝ _ hq) hcF
  change q-a.param 0 ∈ U at hqU
  have hq0 : Q (q-a.param 0) = 0 := U.starProjection_orthogonal_apply_eq_zero hqU
  have he : Q (x-a.param 0) = Q (x-q)+Q (q-a.param 0) := by rw [← map_add]; congr 1; abel
  change ‖Q (x-a.param 0)‖ ≤ _
  rw [he,hq0,add_zero]
  exact (Uᗮ.norm_starProjection_apply_le (x-q)).trans
    (by rw [← dist_eq_norm,← hqdist]; exact leakage_point_le hc hs hg hB p t hx)

private theorem normal_operator_bound
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p t : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) (c : ExclusionChart C₁ u₁ t) :
    ‖(affineSpan ℝ (exclusion C₁ u₁ p)).directionᗮ.starProjection.comp
      c.param.linear.toContinuousLinearMap‖ ≤ leakage C₁ u₁ p t := by
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let Q := Uᗮ.starProjection
  have hα : 0 ≤ leakage C₁ u₁ p t := by
    obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 t).1.nonempty
    exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p t hx)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hα
  intro v hv
  have hp := normal_leakage hc hs hg hB p t a (chart_mem c hv.le)
  have hm := normal_leakage hc hs hg hB p t a (chart_mem c (by simpa using hv.le : ‖-v‖ ≤ 1))
  have hd : Q (c.param v-a.param 0)-Q (c.param (-v)-a.param 0) =
      (2:ℝ) • Q (c.param.linear v) := by
    rw [← map_sub]
    have he : c.param v-a.param 0-(c.param (-v)-a.param 0) = c.param v-c.param (-v) := by abel
    rw [he,← vsub_eq_sub,← c.param.linear_apply_vsub,vsub_eq_sub]
    have he : v- -v = (2:ℝ) • v := by module
    rw [he,map_smul,map_smul]
  have hh := norm_sub_le (Q (c.param v-a.param 0)) (Q (c.param (-v)-a.param 0))
  rw [hd,norm_smul] at hh
  norm_num at hh
  simp only [map_sub] at hp hm
  change ‖Q (c.param.linear v)‖ ≤ _
  linarith

private theorem projected_ball_dual_bound
    (p t : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) (c : ExclusionChart C₁ u₁ t)
    {y : E} (hy : y ∈ affineSpan ℝ (exclusion C₁ u₁ p)) {β : ℝ} (hβ : 0 < β)
    (hball : Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
      sourceProjection p a '' exclusion C₁ u₁ t) :
    ∀ h ∈ (affineSpan ℝ (exclusion C₁ u₁ p)).direction,
      β*‖h‖ ≤ ‖c.param.linear.toContinuousLinearMap.adjoint h‖ := by
  intro h hh
  by_cases hz : h = 0
  · simp [hz]
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let e := ‖h‖⁻¹ • h
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hz
  have he : ‖e‖ = 1 := by simp [e,norm_smul,hn.ne']
  have heU : e ∈ U := U.smul_mem _ hh
  have hpF : β • e+y ∈ affineSpan ℝ (exclusion C₁ u₁ p) :=
    (affineSpan ℝ (exclusion C₁ u₁ p)).vadd_mem_of_mem_direction (U.smul_mem _ heU) hy
  have hmF : (-β) • e+y ∈ affineSpan ℝ (exclusion C₁ u₁ p) :=
    (affineSpan ℝ (exclusion C₁ u₁ p)).vadd_mem_of_mem_direction (U.smul_mem _ heU) hy
  have hpB : β • e+y ∈ Metric.closedBall y β := by simp [Metric.mem_closedBall,dist_eq_norm,norm_smul,he,abs_of_pos hβ]
  have hmB : (-β) • e+y ∈ Metric.closedBall y β := by simp [Metric.mem_closedBall,dist_eq_norm,norm_smul,he,abs_of_pos hβ]
  obtain ⟨xp,hxp,hxpπ⟩ := hball ⟨hpB,hpF⟩
  obtain ⟨xm,hxm,hxmπ⟩ := hball ⟨hmB,hmF⟩
  obtain ⟨vp,hvp,rfl⟩ := c.whole.symm ▸ hxp
  obtain ⟨vm,hvm,rfl⟩ := c.whole.symm ▸ hxm
  have hvp1 : ‖vp‖ ≤ 1 := by simpa using hvp
  have hvm1 : ‖vm‖ ≤ 1 := by simpa using hvm
  have hd : U.starProjection (c.param.linear (vp-vm)) = (2*β) • e := by
    have h := (sourceProjection p a).linear_apply_vsub (c.param vp) (c.param vm)
    rw [sourceProjection_linear,hxpπ,hxmπ] at h
    rw [← c.param.linear_apply_vsub,vsub_eq_sub] at h
    change U.starProjection (c.param.linear (vp-vm)) = _ at h
    change U.starProjection (c.param.linear (vp-vm)) = β • e+y-((-β) • e+y) at h
    rw [h]
    module
  have hhP : U.starProjection h = h := Submodule.starProjection_eq_self_iff.mpr hh
  have heinner : ⟪h,e⟫ = ‖h‖ := by
    simp only [e,inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  have hvdiff : ‖vp-vm‖ ≤ 2 := (norm_sub_le vp vm).trans (by linarith)
  have hcs := real_inner_le_norm (c.param.linear.toContinuousLinearMap.adjoint h) (vp-vm)
  have heq : ⟪c.param.linear.toContinuousLinearMap.adjoint h,vp-vm⟫ = 2*β*‖h‖ := by
    calc
      _ = ⟪h,c.param.linear (vp-vm)⟫ := ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = ⟪U.starProjection h,c.param.linear (vp-vm)⟫ := by rw [hhP]
      _ = ⟪h,U.starProjection (c.param.linear (vp-vm))⟫ := U.inner_starProjection_left_eq_right _ _
      _ = _ := by rw [hd,inner_smul_right,heinner]
  rw [heq] at hcs
  have hh2 := mul_le_mul_of_nonneg_left hvdiff (norm_nonneg (c.param.linear.toContinuousLinearMap.adjoint h))
  linarith

private theorem actual_singular_bounds
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p t : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) (c : ExclusionChart C₁ u₁ t)
    {y : E} (hy : y ∈ affineSpan ℝ (exclusion C₁ u₁ p)) {β : ℝ} (hβ : 0 < β)
    (hd : a.dim+1 ≤ c.dim)
    (hball : Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
      sourceProjection p a '' exclusion C₁ u₁ t)
    {z : EuclideanSpace ℝ (Fin c.dim)} (hz : ‖z‖ = 1) :
    β ≤ c.param.linear.singularValues (a.dim-1) ∧
    c.param.linear.singularValues a.dim ≤ leakage C₁ u₁ p t ∧
    ‖(projectedLinear p c).ker.starProjection z‖ ≤
      ‖(singularTail c.param.linear.toContinuousLinearMap a.dim).starProjection z‖+
        leakage C₁ u₁ p t/β := by
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let L := c.param.linear.toContinuousLinearMap
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin c.dim)) = c.dim := by simp
  have hα : 0 ≤ leakage C₁ u₁ p t := by
    obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 t).1.nonempty
    exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p t hx)
  have herr (x) : ‖Uᗮ.starProjection (L x)‖ ≤ leakage C₁ u₁ p t*‖x‖ :=
    ((Uᗮ.starProjection.comp L).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (normal_operator_bound hc hs hg hB p t a c) (norm_nonneg x))
  have hkept := kept_of_dual_coercive L U (chart_dimension a) a.dim_pos
    (by rw [hdim]; omega) hβ (projected_ball_dual_bound p t a c hy hβ hball)
  have hthin := thin_of_projected_error L U (chart_dimension a)
    (by rw [hdim]; omega) hα herr
  refine ⟨hkept,hthin,?_⟩
  rw [singularTail_eq]
  apply projection_mass_transfer _ _ (div_nonneg hα hβ.le) _ hz
  intro v hv
  have hAv : U.starProjection (L v) = 0 := by
    have hh := hv
    change projectedLinear p c v = 0 at hh
    exact congrArg (fun w : U => (w:E)) hh
  have he := U.starProjection_add_starProjection_orthogonal (L v)
  rw [hAv,zero_add] at he
  have hLv : ‖L v‖ ≤ leakage C₁ u₁ p t*‖v‖ := by simpa only [he] using herr v
  have hlead := leading_projection_bound L a.dim_pos (by rw [hdim]; omega) v
  have hh := mul_le_mul_of_nonneg_right hkept (norm_nonneg ((leading L a.dim).starProjection v))
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hβ).mpr (by nlinarith)

private theorem tail_mass_from_margin {R β e q w α : ℝ}
    (hR : 0 < R) (hβ : 0 < β) (hβR : β < R) (he : 0 ≤ e) (heβ : e < β/2)
    (hq : 0 ≤ q) (hw : 0 ≤ w) (_hw1 : w ≤ 1) (_hα : 0 ≤ α)
    (hmargin : 1-(1-(β-e)/R)^2 ≤ q^2)
    (htransfer : q ≤ w+α/β)
    (hsmall : α/β < Real.sqrt (1-(1-β/(2*R))^2)/2) :
    (1-(1-β/(2*R))^2)/4 ≤ w^2 := by
  let γ := 1-(1-β/(2*R))^2
  have hm : 0 < β/(2*R) := div_pos hβ (by positivity)
  have hm1 : β/(2*R) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hγ : 0 < γ := by dsimp [γ]; nlinarith
  have hratio : β/(2*R) ≤ (β-e)/R := by
    rw [le_div_iff₀ hR]
    field_simp
    nlinarith
  have hratio1 : (β-e)/R ≤ 1 := (div_le_one hR).mpr (by linarith)
  have hγq : γ ≤ q^2 := by dsimp [γ]; nlinarith
  have hs := Real.sq_sqrt hγ.le
  have hs0 := Real.sqrt_nonneg γ
  have hsq : Real.sqrt γ ≤ q := by nlinarith
  have htail : Real.sqrt γ/2 ≤ w := by dsimp [γ] at hsq hs0 ⊢; linarith
  nlinarith

/-- Fixed original sectors force dimension escape and an actual projected
inner ball for every sequence satisfying the additional common-sector condition.
The singular estimates and tail transfer are supplied by the spectral lemmas. -/
private theorem projected_return_geometry
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (hy : y ∈ intrinsicInterior ℝ (exclusion C₁ u₁ p))
    (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (hb : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ) :
    ∃ ε θ H β : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < H ∧ 0 < β ∧
      β < Metric.diam (base C₁ u₁)/2 ∧
      (∀ r t : pure C₁ u₁, dist (r:E) y < ε → (t:E) ∈ exclusion C₁ u₁ r →
        Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ t)).direction ≤ a.dim →
        ∃ i : Fin (a.dim+1), ∀ f : E →L[ℝ] ℝ,
          f ≠ 0 → (∀ x ∈ C₁, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
          ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
          ‖slope a f‖ ≤ H*baseMaximum C₁ u₁ f*leakage C₁ u₁ p t) ∧
      ∀ (r t : ℕ → pure C₁ u₁), Tendsto (fun n => (r n:E)) atTop (𝓝 y) →
        (∀ n, (t n:E) ∈ exclusion C₁ u₁ (r n)) →
        (∀ᶠ n in atTop, sectorViolation a b (t n) θ H) →
        ∀ (c : ∀ n, ExclusionChart C₁ u₁ (t n))
          (z : ∀ n, EuclideanSpace ℝ (Fin (c n).dim)),
          (∀ n, (c n).param (z n) = r n) →
          Tendsto (fun n => leakage C₁ u₁ p (t n)) atTop (𝓝 0) ∧
          (∀ n, ‖z n‖ = 1 ∧ 0 < (c n).dim ∧
            (c n).dim ≤ Module.finrank ℝ (LinearMap.ker u₁) ∧
            ‖(c n).param.linear.toContinuousLinearMap‖ ≤ Metric.diam (base C₁ u₁)/2) ∧
          ∀ᶠ n in atTop, a.dim+1 ≤ (c n).dim ∧
            Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
              sourceProjection p a '' exclusion C₁ u₁ (t n) ∧
            1-(1-(β-dist (r n:E) y)/(Metric.diam (base C₁ u₁)/2))^2 ≤
              ‖(projectedLinear p (c n)).ker.starProjection (z n)‖^2 := by
  classical
  obtain ⟨ε₀,θ₀,H₀,hε₀,hθ₀,hH₀,hsector⟩ := uniform_return_sectors hc hs hg hB p a hy ξ hξ b hb hpos
  obtain ⟨δ,β₀,hδ,hβ₀,hball⟩ := projected_simplex_ball p a ξ hξ b hb hpos
  obtain ⟨θ₁,H₁,hθ₁,hH₁,hcontact⟩ := sector_contact_family hc hs hg hB p a b hδ
  obtain ⟨ε₁,hε₁,hleak⟩ := whole_return_leakage hc hs hg hB p hy (by positivity : 0 < δ/4)
  let θ := min θ₀ θ₁
  let H := max H₀ H₁
  let β := min β₀ (Metric.diam (base C₁ u₁)/4)
  have hR := base_radius_positive hc hs p a
  have hβ : 0 < β := lt_min hβ₀ (by linarith)
  have hβR : β < Metric.diam (base C₁ u₁)/2 := (min_le_right _ _).trans_lt (by linarith)
  have hα0 (t : pure C₁ u₁) : 0 ≤ leakage C₁ u₁ p t := by
    obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 t).1.nonempty
    exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p t hx)
  have hM0 (t : pure C₁ u₁) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
      (hp : ∀ x ∈ C₁, 0 ≤ f x) (ht : f t = 0) : 0 ≤ baseMaximum C₁ u₁ f := by
    obtain ⟨A,_,h⟩ := uniform_dual_bound hc hs hg
    exact (h t f hf hp ht).1.le
  have hsector' : ∀ r t : pure C₁ u₁, dist (r:E) y < min ε₀ ε₁ →
      (t:E) ∈ exclusion C₁ u₁ r →
      Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ t)).direction ≤ a.dim →
      ∃ i : Fin (a.dim+1), ∀ f : E →L[ℝ] ℝ,
        f ≠ 0 → (∀ x ∈ C₁, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
        ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
        ‖slope a f‖ ≤ H*baseMaximum C₁ u₁ f*leakage C₁ u₁ p t := by
    intro r t hr ht hd
    obtain ⟨i,hi⟩ := hsector r t (hr.trans_le (min_le_left _ _)) ht hd
    refine ⟨i,fun f hf hp hft hfg hdir => ?_⟩
    exact (hi f hf hp hft hfg (hdir.trans_le (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (hM0 t f hf hp hft)) (hα0 t))
  refine ⟨min ε₀ ε₁,θ,H,β,lt_min hε₀ hε₁,lt_min hθ₀ hθ₁,
    hH₀.trans_le (le_max_left _ _),hβ,hβR,hsector',fun r t hr ht hfail c z hz => ?_⟩
  refine ⟨actual_leakage_tendsto hc hs hg hB p hy r t hr ht,
    fun n => ⟨actual_parameter_unit hc hs hg hB (r n) (t n) (ht n) (c n) (z n) (hz n),
      (c n).dim_pos,chart_dimension_bound (c n),chart_operator_bound hc hs (c n)⟩,?_⟩
  filter_upwards [hfail,Metric.tendsto_nhds.mp hr (min (min ε₀ ε₁) β)
    (lt_min (lt_min hε₀ hε₁) hβ)] with n hn hnear₀
  have hnear := hnear₀.trans_le (min_le_left _ _)
  have hnearβ := hnear₀.trans_le (min_le_right _ _)
  have hfail₁ : sectorViolation a b (t n) θ₁ H₁ := by
    intro i
    obtain ⟨f,hf,hp,hft,hfg,hdir,hbig⟩ := hn i
    refine ⟨f,hf,hp,hft,hfg,hdir.trans_le (min_le_right _ _),?_⟩
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (hM0 (t n) f hf hp hft)) (hα0 (t n))).trans_lt hbig
  have hdim : a.dim+1 ≤ (c n).dim := by
    by_contra! hd
    have hd' : Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ (t n))).direction ≤ a.dim := by
      rw [chart_dimension (c n)]; omega
    obtain ⟨i,hi⟩ := hsector' (r n) (t n) hnear (ht n) hd'
    obtain ⟨f,hf,hp,hft,hfg,hdir,hbig⟩ := hn i
    exact hbig.not_ge (hi f hf hp hft hfg hdir)
  have hreturnball : Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
      sourceProjection p a '' exclusion C₁ u₁ (t n) := by
    obtain ⟨x,hx⟩ := hcontact (t n) (hleak (r n) (t n) (hnear.trans_le (min_le_right _ _)) (ht n)) hfail₁
    have hinside : convexHull ℝ (range (fun i => sourceProjection p a (x i:E))) ⊆
        sourceProjection p a '' exclusion C₁ u₁ (t n) :=
      convexHull_min (by rintro _ ⟨i,rfl⟩; exact mem_image_of_mem _ (hx i).1)
        (((exclusion_ball_faces hc hs hg hB).1 (t n)).2.2.1.affine_image (sourceProjection p a))
    intro q hq
    apply hinside
    apply hball (fun i => (x i:E)) (fun i => (hx i).2)
    exact ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hq.1,hq.2⟩
  exact ⟨hdim,hreturnball,actual_projected_margin hc hs hg hB p a
    (subset_affineSpan ℝ _ (intrinsicInterior_subset hy)) hβ hβR
    (r n) (t n) (ht n) (c n) (z n) (hz n) hnearβ hreturnball⟩

/-- Complete original common-sector return conclusion, with fixed kept singular value
and positive mass in the ordered right singular tail. -/
theorem original_return_geometry
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (hy : y ∈ intrinsicInterior ℝ (exclusion C₁ u₁ p))
    (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (hb : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ) :
    ∃ ε θ H β η : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < H ∧ 0 < β ∧ 0 < η ∧
      β < Metric.diam (base C₁ u₁)/2 ∧
      (∀ r t : pure C₁ u₁, dist (r:E) y < ε → (t:E) ∈ exclusion C₁ u₁ r →
        Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ t)).direction ≤ a.dim →
        ∃ i : Fin (a.dim+1), ∀ f : E →L[ℝ] ℝ,
          f ≠ 0 → (∀ x ∈ C₁, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
          ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
          ‖slope a f‖ ≤ H*baseMaximum C₁ u₁ f*leakage C₁ u₁ p t) ∧
      ∀ (r t : ℕ → pure C₁ u₁), Tendsto (fun n => (r n:E)) atTop (𝓝 y) →
        (∀ n, (t n:E) ∈ exclusion C₁ u₁ (r n)) →
        (∀ᶠ n in atTop, sectorViolation a b (t n) θ H) →
        ∀ (c : ∀ n, ExclusionChart C₁ u₁ (t n))
          (z : ∀ n, EuclideanSpace ℝ (Fin (c n).dim)),
          (∀ n, (c n).param (z n) = r n) →
          Tendsto (fun n => leakage C₁ u₁ p (t n)) atTop (𝓝 0) ∧
          (∀ n, ‖z n‖ = 1 ∧ 0 < (c n).dim ∧
            (c n).dim ≤ Module.finrank ℝ (LinearMap.ker u₁) ∧
            ‖(c n).param.linear.toContinuousLinearMap‖ ≤ Metric.diam (base C₁ u₁)/2) ∧
          (∀ᶠ n in atTop, a.dim+1 ≤ (c n).dim ∧
            Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
              sourceProjection p a '' exclusion C₁ u₁ (t n) ∧
            1-(1-(β-dist (r n:E) y)/(Metric.diam (base C₁ u₁)/2))^2 ≤
              ‖(projectedLinear p (c n)).ker.starProjection (z n)‖^2 ∧
            β ≤ (c n).param.linear.singularValues (a.dim-1) ∧
            (c n).param.linear.singularValues a.dim ≤ leakage C₁ u₁ p (t n)) ∧
          β ≤ liminf (fun n => (c n).param.linear.singularValues (a.dim-1)) atTop ∧
          η ≤ liminf (fun n => ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖^2) atTop := by
  classical
  obtain ⟨ε,θ,H,β,hε,hθ,hH,hβ,hβR,hsector,hgeometry⟩ :=
    projected_return_geometry hc hs hg hB p a hy ξ hξ b hb hpos
  let R := Metric.diam (base C₁ u₁)/2
  let γ := 1-(1-β/(2*R))^2
  have hR : 0 < R := base_radius_positive hc hs p a
  have hm : 0 < β/(2*R) := div_pos hβ (by positivity)
  have hm1 : β/(2*R) < 1 := (div_lt_one (by positivity)).mpr (by dsimp [R]; linarith)
  have hγ : 0 < γ := by dsimp [γ]; nlinarith
  refine ⟨ε,θ,H,β,γ/4,hε,hθ,hH,hβ,by positivity,hβR,hsector,?_⟩
  intro r t hr ht hfail c z hz
  obtain ⟨hleak,hunit,hgeom⟩ := hgeometry r t hr ht hfail c z hz
  have hspec : ∀ᶠ n in atTop,
      β ≤ (c n).param.linear.singularValues (a.dim-1) ∧
      (c n).param.linear.singularValues a.dim ≤ leakage C₁ u₁ p (t n) ∧
      ‖(projectedLinear p (c n)).ker.starProjection (z n)‖ ≤
        ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖+
          leakage C₁ u₁ p (t n)/β := by
    filter_upwards [hgeom] with n hn
    exact actual_singular_bounds hc hs hg hB p (t n) a (c n)
      (subset_affineSpan ℝ _ (intrinsicInterior_subset hy)) hβ hn.1 hn.2.1 (hunit n).1
  have hnorm (n) : ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖ ≤ 1 :=
    ((singularTail (c n).param.linear.toContinuousLinearMap a.dim).norm_starProjection_apply_le (z n)).trans_eq (hunit n).1
  have hmass : ∀ᶠ n in atTop,
      γ/4 ≤ ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖^2 := by
    have hsmall : ∀ᶠ n in atTop, leakage C₁ u₁ p (t n)/β < Real.sqrt γ/2 :=
      (tendsto_order.mp (hleak.div_const β)).2 _ (by simp only [zero_div]; positivity)
    filter_upwards [hgeom,hspec,Metric.tendsto_nhds.mp hr (β/2) (by positivity),hsmall]
      with n hn hspectral hnear hsmall
    have hα : 0 ≤ leakage C₁ u₁ p (t n) := by
      obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 (t n)).1.nonempty
      exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p (t n) hx)
    exact tail_mass_from_margin hR hβ hβR dist_nonneg hnear (norm_nonneg _) (norm_nonneg _)
      (hnorm n) hα hn.2.2 hspectral.2.2 hsmall
  refine ⟨hleak,hunit,?_,?_,?_⟩
  · filter_upwards [hgeom,hspec] with n hn hspectral
    exact ⟨hn.1,hn.2.1,hn.2.2,hspectral.1,hspectral.2.1⟩
  · apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n =>
      (singular_le_norm (c n).param.linear.toContinuousLinearMap (a.dim-1)).trans (hunit n).2.2.2))
    exact hspec.mono fun _ hn => hn.1
  · apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n =>
      show ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖^2 ≤ 1 from by
        nlinarith [hnorm n,norm_nonneg ((singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n))]))
    exact hmass

end EuclideanReturns

end D5.S3.Quantum.Foundation.OriginalReturnSectors
