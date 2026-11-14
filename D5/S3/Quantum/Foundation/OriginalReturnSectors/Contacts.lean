/- GID: D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalReturnSectors/Contacts
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole original return leakage and stable source-contact geometry. -/

import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import D5.S3.Quantum.Foundation.UniqueConfirmationDensity
import D5.S3.Quantum.Foundation.CommonSourceLiftObstruction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.Normed.Affine.Convex


noncomputable section

namespace D5.S3.Quantum.Foundation.OriginalReturnSectors

open Set Filter Topology
open scoped RealInnerProductSpace
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity ContinuousFrameSum SingleLabelNormalBody WholePairBallConfirmation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The maximum distance from the entire return face to the fixed source face. -/
def leakage (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p t : V) : ℝ :=
  sSup ((fun x => Metric.infDist x (exclusion C u p)) '' exclusion C u t)

private theorem zero_face_eq (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y t : V}
    (hy : y ∈ intrinsicInterior ℝ (exclusion C u p)) (ht : t ∈ base C u)
    (e : V →L[ℝ] ℝ) (he : e ∈ effects C u) (hey : e y = 0) (het : e t = 1) :
    {x | x ∈ base C u ∧ e x = 0} = exclusion C u p := by
  let G := {x | x ∈ base C u ∧ e x = 0}
  have all := exclusion_ball_faces hc hs hg hB
  have hFG : exclusion C u p ⊆ G := fun x hx =>
    ⟨hx.1, UniqueConfirmationDensity.zero_on_exclusion_of_zero_interior hB p
      e.toLinearMap (fun z hz => (he z hz).1) hy hey x hx⟩
  have hGconv : Convex ℝ G := by
    intro x hx z hz a b ha hb hab
    refine ⟨base_convex C u hx.1 hz.1 ha hb hab, ?_⟩
    simp [map_add, map_smul, hx.2, hz.2]
  have hGexp : IsExposed ℝ (base C u) G := by
    intro _
    refine ⟨-e, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      exact ⟨hx, fun z hz => by simpa [hx0] using (he z hz.1).1⟩
    · rintro ⟨hx, hmax⟩
      have hh := hmax y ((intrinsicInterior_subset hy).1)
      change -e y ≤ -e x at hh
      rw [hey] at hh
      exact ⟨hx, le_antisymm (by simpa only [neg_zero, neg_nonneg] using hh)
        (he x hx.1).1⟩
  have hproper : G ≠ base C u := by
    intro heq
    have hh : t ∈ G := heq.symm ▸ ht
    linarith [hh.2]
  rcases all.2.1 G ⟨y, hFG (intrinsicInterior_subset hy)⟩ hGconv hGexp.isExtreme
      hproper with ⟨q, hq⟩ | ⟨q, hq⟩
  · exact ((all.1 p).1.not_subsingleton (fun x hx z hz => by
      have hxq := hq ▸ hFG hx
      have hzq := hq ▸ hFG hz
      exact hxq.trans hzq.symm)).elim
  · obtain ⟨b⟩ := hB q
    have hsub : exclusion C u p ⊆ exclusion C u q := hq ▸ hFG
    have hface := (all.1 p).2.2.2.2.1.mono (all.1 q).2.2.2.2.1.subset hsub
    exact hq.trans (chart_face_eq b (all.1 p).2.2.1 hface (all.1 p).1).symm

/-- Every whole actual return lies uniformly close to F as its returned pure
point approaches any relative-interior point of F. The label limit may be mixed. -/
theorem whole_return_near_source (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r t : pure C u,
      dist (r : V) y < ε → (t : V) ∈ exclusion C u r →
      ∀ x ∈ exclusion C u t, Metric.infDist x (exclusion C u p) < δ := by
  classical
  by_contra! hn
  have hb (n : ℕ) := hn (1 / ((n : ℝ) + 1)) (by positivity)
  choose r t hr ht x hx hfar using hb
  let e (n : ℕ) : V →L[ℝ] ℝ :=
    (((exclusion_ball_faces hc hs hg hB).1 (t n)).2.2.2.2.2.2.choose).toContinuousLinearMap
  have he (n : ℕ) : confirms C u (t n) (e n).toLinearMap :=
    ((exclusion_ball_faces hc hs hg hB).1 (t n)).2.2.2.2.2.2.choose_spec.1
  have hezero (n : ℕ) (z : V) (hz : z ∈ exclusion C u (t n)) : e n z = 0 := by
    have hh := ((exclusion_ball_faces hc hs hg hB).1 (t n)).2.2.2.2.2.2.choose_spec.2
    exact (hh ▸ hz).2
  have hrconv : Tendsto (fun n => (r n : V)) atTop (𝓝 y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (show ‖(r n : V) - y‖ < 1 / ((n : ℝ) + 1) from
        by simpa [dist_eq_norm] using hr n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hK := base_compact hc hs
  obtain ⟨z, hz, φ, hφ, hlim⟩ := (hK.prod (hK.prod (effects_compact hs hg))).tendsto_subseq
    (fun n => show ((t n : V), x n, e n) ∈
      base C u ×ˢ (base C u ×ˢ effects C u) from
      ⟨pure_mem (t n), (hx n).1, (he n).1⟩)
  have htl := hlim.fst_nhds
  have hxl := hlim.snd_nhds.fst_nhds
  have hel := hlim.snd_nhds.snd_nhds
  have hrl := hrconv.comp hφ.tendsto_atTop
  have hev : Continuous (fun v : (V →L[ℝ] ℝ) × V => v.1 v.2) := by fun_prop
  have hey : z.2.2 y = 0 := by
    apply tendsto_nhds_unique ((hev.tendsto _).comp (hel.prodMk_nhds hrl))
    convert tendsto_const_nhds (x := (0 : ℝ)) using 1
    ext n
    exact hezero (φ n) _ ((exclusion_symmetric (r (φ n)) (t (φ n))).mp (ht (φ n)))
  have hex : z.2.2 z.2.1 = 0 := by
    apply tendsto_nhds_unique ((hev.tendsto _).comp (hel.prodMk_nhds hxl))
    convert tendsto_const_nhds (x := (0 : ℝ)) using 1
    ext n
    exact hezero (φ n) _ (hx (φ n))
  have het : z.2.2 z.1 = 1 := by
    apply tendsto_nhds_unique ((hev.tendsto _).comp (hel.prodMk_nhds htl))
    convert tendsto_const_nhds (x := (1 : ℝ)) using 1
    ext n
    exact (he (φ n)).2
  have hxF : z.2.1 ∈ exclusion C u p :=
    zero_face_eq hc hs hg hB p hy hz.1 z.2.2 hz.2.2 hey het ▸ ⟨hz.2.1, hex⟩
  have hnear := Metric.tendsto_nhds.mp hxl δ hδ
  obtain ⟨n, hn⟩ := hnear.exists
  exact (hfar (φ n)).not_gt ((Metric.infDist_le_dist_of_mem hxF).trans_lt hn)

private theorem radial_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ξ v : E} (hξ : ‖ξ‖ < 1) (hv : v ≠ ξ) :
    ∃ s : ℝ, 0 < s ∧ ‖ξ + s • (v - ξ)‖ = 1 := by
  have hd : 0 < ‖v - ξ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
  let T := (2 + ‖ξ‖) / ‖v - ξ‖
  have hT : 0 < T := by dsimp [T]; positivity
  have hlarge : 1 ≤ ‖ξ + T • (v - ξ)‖ := by
    have hh := norm_sub_le (ξ + T • (v - ξ)) ξ
    have he : ξ + T • (v - ξ) - ξ = T • (v - ξ) := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hT] at hh
    have hmul : T * ‖v - ξ‖ = 2 + ‖ξ‖ := div_mul_cancel₀ _ hd.ne'
    linarith
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc hT.le
    (show ContinuousOn (fun s : ℝ => ‖ξ + s • (v - ξ)‖) (Icc 0 T) by fun_prop)
    (show (1 : ℝ) ∈ Icc ‖ξ + (0 : ℝ) • (v - ξ)‖ ‖ξ + T • (v - ξ)‖ from
      ⟨by simpa using hξ.le, hlarge⟩)
  refine ⟨s, lt_of_le_of_ne hs.1 ?_, he⟩
  intro hz
  have : ‖ξ‖ = 1 := by simpa [← hz] using he
  linarith

theorem sphere_affine_basis {d : ℕ} (hd : 0 < d)
    {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ < 1) :
    ∃ b : AffineBasis (Fin (d + 1)) ℝ (EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖b i‖ = 1) ∧ ∀ i, 0 < b.coord i ξ := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  obtain ⟨b, hb, _⟩ := exists_mem_interior_convexHull_affineBasis
    (s := Metric.ball (0 : E) 1) (Metric.isOpen_ball.mem_nhds (by simpa using hξ))
  have hcoord : ∀ i, 0 < b.coord i ξ := by
    simpa only [b.interior_convexHull, mem_ofPred_eq] using hb
  have : Nontrivial (Fin (Module.finrank ℝ E + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (by simpa [E] using Nat.succ_le_succ hd)
  have hne (i) : b i ≠ ξ := by
    obtain ⟨j, hj⟩ := exists_ne i
    intro he
    have hh := hcoord j
    rw [← he, b.coord_apply_ne hj] at hh
    exact lt_irrefl _ hh
  choose t ht hunit using fun i => radial_sphere hξ (hne i)
  let q := fun i => ξ + t i • (b i - ξ)
  let S := ∑ i, b.coord i ξ / t i
  have hS : 0 < S := Finset.sum_pos (fun i _ => div_pos (hcoord i) (ht i))
    Finset.univ_nonempty
  let w := fun i => (b.coord i ξ / t i) / S
  have hwpos (i) : 0 < w i := div_pos (div_pos (hcoord i) (ht i)) hS
  have hwsum : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self hS.ne'
  have hcomb : ∑ i, w i • q i = ξ := by
    simp only [q, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul,
      hwsum, one_smul]
    have hwt (i) : w i * t i = S⁻¹ * b.coord i ξ := by
      dsimp [w]
      field_simp [(ht i).ne', hS.ne']
    simp_rw [hwt, mul_smul, ← Finset.smul_sum, smul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [b.linear_combination_coord_eq_self, b.sum_coord_apply_eq_one, one_smul,
      sub_self, smul_zero, add_zero]
  have hξspan : ξ ∈ affineSpan ℝ (range q) := by
    rw [← hcomb, ← Finset.univ.affineCombination_eq_linear_combination _ _ hwsum]
    exact affineCombination_mem_affineSpan hwsum q
  have hspan : affineSpan ℝ (range q) = ⊤ := by
    apply top_unique
    rw [← b.tot]
    apply affineSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    have hq := subset_affineSpan ℝ (range q) (mem_range_self i)
    have hh := AffineMap.lineMap_mem ((t i)⁻¹) hξspan hq
    convert hh using 1;
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, q,
        add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ht i).ne', one_smul,
        sub_add_cancel]
    rfl
  have hind : AffineIndependent ℝ q := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ q (Fintype.card_fin _)).mpr
    rw [← direction_affineSpan, hspan, AffineSubspace.direction_top, finrank_top]
  let c : AffineBasis _ ℝ E := ⟨q, hind, hspan⟩
  have hccoord (i) : c.coord i ξ = w i := by
    rw [← hcomb, ← Finset.univ.affineCombination_eq_linear_combination _ _ hwsum]
    exact c.coord_apply_combination_of_mem (Finset.mem_univ i) hwsum
  have he : Module.finrank ℝ E = d := by simp [E]
  refine ⟨c.reindex (finCongr (congrArg (fun n => n + 1) he)), ?_, ?_⟩
  · intro i
    exact hunit _
  · intro i
    rw [AffineBasis.coord_reindex, hccoord]
    exact hwpos _


section SimplexStability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

private def interpLinear (b : AffineBasis ι ℝ E) (x : ι → E) : E →L[ℝ] E :=
  ∑ i, (b.coord i).linear.toContinuousLinearMap.smulRight (x i)

private def interpConst (b : AffineBasis ι ℝ E) (x : ι → E) : E :=
  ∑ i, b.coord i 0 • x i

private theorem interp_formula (b : AffineBasis ι ℝ E) (x : ι → E) (z : E) :
    ∑ i, b.coord i z • x i = interpLinear b x z + interpConst b x := by
  have h (i) : b.coord i z = (b.coord i).linear z + b.coord i 0 := by
    simpa using (b.coord i).map_vadd (0 : E) z
  simp only [h, add_smul, Finset.sum_add_distrib, interpLinear, interpConst,
    sum_apply, ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap']

private theorem interp_self (b : AffineBasis ι ℝ E) :
    interpLinear b b = 1 ∧ interpConst b b = 0 := by
  have hc : interpConst b b = 0 := b.linear_combination_coord_eq_self 0
  refine ⟨?_, hc⟩
  ext z
  have hh := interp_formula b b z
  rw [b.linear_combination_coord_eq_self, hc, add_zero] at hh
  exact hh.symm

private theorem interpLinear_continuous (b : AffineBasis ι ℝ E) :
    Continuous (interpLinear b) := by
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.smulRightₗ (T := ℝ)
    (b.coord i).linear.toContinuousLinearMap : E →ₗ[ℝ] (E →L[ℝ] E)).continuous_of_finiteDimensional).comp
      (continuous_apply i)

omit [FiniteDimensional ℝ E] in
private theorem interpConst_continuous (b : AffineBasis ι ℝ E) :
    Continuous (interpConst b) := by
  unfold interpConst
  fun_prop

private theorem simplex_reconstruction (b : AffineBasis ι ℝ E) {y : E}
    (hy : ∀ i, 0 < b.coord i y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι → E) (z : E),
      (∀ i, dist (x i) (b i) < δ) → dist z y < δ →
      AffineIndependent ℝ x ∧ ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        ∑ i, w i • x i = z := by
  classical
  let L := interpLinear b
  let c := interpConst b
  have hL := interpLinear_continuous b
  have hc := interpConst_continuous b
  have hLb : L b = 1 := (interp_self b).1
  have hcb : c b = 0 := (interp_self b).2
  let h := fun p : (ι → E) × E => Ring.inverse (L p.1) (p.2 - c p.1)
  have hcont : ContinuousAt h (b, y) := by
    have hinv : ContinuousAt Ring.inverse (L b) := by
      simpa only [hLb, Units.val_one] using
        (NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ))
    have hi : ContinuousAt (fun p : (ι → E) × E => Ring.inverse (L p.1)) (b,y) := by
      have hi' : ContinuousAt Ring.inverse ((fun p : (ι → E) × E => L p.1) (b,y)) := hinv
      exact ContinuousAt.comp (f := fun p : (ι → E) × E => L p.1) (x := (b,y)) hi'
        ((hL.comp continuous_fst).continuousAt)
    exact hi.clm_apply ((continuous_snd.sub (hc.comp continuous_fst)).continuousAt)
  have hby : h (b,y) = y := by simp [h, hLb, hcb]
  have hevent : ∀ᶠ p : (ι → E) × E in 𝓝 (b,y),
      IsUnit (L p.1) ∧ (∀ i, 0 < b.coord i (h p)) ∧ AffineIndependent ℝ p.1 := by
    have hunit : ∀ᶠ p : (ι → E) × E in 𝓝 (b,y), IsUnit (L p.1) := by
      apply (Units.isOpen.preimage (hL.comp continuous_fst)).mem_nhds
      change IsUnit (L b)
      rw [hLb]
      exact isUnit_one
    apply hunit.and
    apply Filter.Eventually.and ?_ ?_
    · apply (eventually_all.mpr fun i => ?_)
      have ht := ((b.coord i).continuous_of_finiteDimensional.continuousAt.comp hcont)
      exact ht.eventually (lt_mem_nhds (by simpa only [Function.comp_apply, hby] using hy i))
    · exact (isOpen_setOfPred_affineIndependent.preimage continuous_fst).mem_nhds b.ind
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ,hδ, fun x z hx hz => ?_⟩
  have hp : dist (x,z) (b,y) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(dist_pi_lt_iff hδ).mpr hx,hz⟩
  obtain ⟨hunit, hpos, hind⟩ := hball hp
  refine ⟨hind, fun i => b.coord i (h (x,z)), hpos, b.sum_coord_apply_eq_one _, ?_⟩
  rw [interp_formula]
  change L x (Ring.inverse (L x) (z - c x)) + c x = z
  have hh := congrArg (fun f : E →L[ℝ] E => f (z-c x)) (Ring.mul_inverse_cancel (L x) hunit)
  change L x (Ring.inverse (L x) (z-c x)) = z-c x at hh
  rw [hh, sub_add_cancel]


theorem fixed_simplex_ball (b : AffineBasis ι ℝ E) {y : E}
    (hy : ∀ i, 0 < b.coord i y) :
    ∃ δ β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ x : ι → E,
      (∀ i, dist (x i) (b i) < δ) → AffineIndependent ℝ x ∧
        Metric.closedBall y β ⊆ convexHull ℝ (range x) := by
  obtain ⟨δ,hδ,h⟩ := simplex_reconstruction b hy
  refine ⟨δ,δ/2,hδ,by positivity,fun x hx => ?_⟩
  have hind := (h x y hx (by simpa using hδ)).1
  refine ⟨hind,fun z hz => ?_⟩
  have hz' : dist z y < δ := (Metric.mem_closedBall.mp hz).trans_lt (by linarith)
  obtain ⟨w,hw,hsum,hrec⟩ := (h x z hx hz').2
  rw [← hrec, ← Finset.univ.affineCombination_eq_linear_combination _ _ hsum]
  exact affineCombination_mem_convexHull (fun i _ => (hw i).le) hsum

theorem common_flat_reconstruction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (b : AffineBasis ι ℝ E) (hcard : Fintype.card ι = Module.finrank ℝ E + 1)
    {y : E} (hy : ∀ i, 0 < b.coord i y)
    (f : V →ᵃ[ℝ] E) (q : ι → V) (hq : ∀ i, f (q i) = b i)
    (r₀ : V) (hr₀ : f r₀ = y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : ι → V) (r : V) (W : AffineSubspace ℝ V),
      (∀ i, dist (x i) (q i) < ε) → dist r r₀ < ε →
      (∀ i, x i ∈ W) → r ∈ W → Module.finrank ℝ W.direction ≤ Module.finrank ℝ E →
      AffineIndependent ℝ x ∧ ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • x i = r := by
  classical
  obtain ⟨δ,hδ,h⟩ := simplex_reconstruction b hy
  obtain ⟨K,hK⟩ := f.lipschitzWith_of_finiteDimensional
  let ε := δ / ((K:ℝ)+1)
  have hK1 : 0 < (K:ℝ)+1 := by positivity
  have hε : 0 < ε := div_pos hδ hK1
  have hnear {v w : V} (hv : dist v w < ε) : dist (f v) (f w) < δ := by
    calc
      _ ≤ (K:ℝ)*dist v w := hK.dist_le_mul _ _
      _ ≤ ((K:ℝ)+1)*dist v w := by nlinarith [dist_nonneg (x:=v) (y:=w)]
      _ < ((K:ℝ)+1)*ε := mul_lt_mul_of_pos_left hv hK1
      _ = δ := mul_div_cancel₀ _ hK1.ne'
  refine ⟨ε,hε,fun x r W hx hr hxW hrW hdim => ?_⟩
  have hx' : ∀ i, dist (f (x i)) (b i) < δ := fun i => hq i ▸ hnear (hx i)
  have hr' : dist (f r) y < δ := hr₀ ▸ hnear hr
  obtain ⟨hind,w,hw,hsum,hrec⟩ := h (fun i => f (x i)) (f r) hx' hr'
  have hxi : AffineIndependent ℝ x := AffineIndependent.of_comp f hind
  have hle : affineSpan ℝ (range x) ≤ W := affineSpan_le.mpr (by rintro _ ⟨i,rfl⟩; exact hxW i)
  have hdimX : Module.finrank ℝ (affineSpan ℝ (range x)).direction = Module.finrank ℝ E := by
    rw [direction_affineSpan]
    exact hxi.finrank_vectorSpan hcard
  have hdimW : Module.finrank ℝ W.direction = Module.finrank ℝ E :=
    le_antisymm hdim (hdimX ▸ Submodule.finrank_mono (AffineSubspace.direction_le hle))
  have heq := hxi.affineSpan_eq_of_le_of_card_eq_finrank_add_one hle (hdimW ▸ hcard)
  have hrspan : r ∈ affineSpan ℝ (range x) := heq.symm ▸ hrW
  obtain ⟨v,hv,hvr⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hrspan
  have hfv : Finset.univ.affineCombination ℝ (fun i => f (x i)) v = f r := by
    change Finset.univ.affineCombination ℝ (f ∘ x) v = f r
    rw [← Finset.univ.map_affineCombination x v hv f, ← hvr]
  have hfw : Finset.univ.affineCombination ℝ (fun i => f (x i)) w = f r := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hsum]
    exact hrec
  have hwv : w = v := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ
    (fun i => f (x i))).mp hind w v hsum hv (hfw.trans hfv.symm)
  refine ⟨hxi,w,hw,hsum,?_⟩
  rw [hwv,← Finset.univ.affineCombination_eq_linear_combination _ _ hv,← hvr]


end SimplexStability

omit [FiniteDimensional ℝ V] in
private theorem chart_direction {p : V} (a : ExclusionChart C u p) :
    (affineSpan ℝ (exclusion C u p)).direction = LinearMap.range a.param.linear := by
  rw [← a.whole]
  exact CommonSourceLiftObstruction.ball_affine_span a.param
omit [FiniteDimensional ℝ V] in
theorem chart_dimension {p : V} (a : ExclusionChart C u p) :
    Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction = a.dim := by
  rw [chart_direction,LinearMap.finrank_range_of_inj (a.param.linear_injective_iff.mpr a.injective)]
  simp
theorem chart_dimension_bound {p : V} (a : ExclusionChart C u p) :
    a.dim ≤ Module.finrank ℝ (LinearMap.ker u) := by
  rw [← chart_dimension a,chart_direction]
  apply Submodule.finrank_mono
  rintro _ ⟨z,rfl⟩
  exact chart_unit_linear a z

def sourceInverse {p : V} (a : ExclusionChart C u p) :
    V →ᵃ[ℝ] EuclideanSpace ℝ (Fin a.dim) :=
  a.param.linear.leftInverse.toAffineMap.comp
    ((AffineMap.id ℝ V) - AffineMap.const ℝ V (a.param 0))
omit [FiniteDimensional ℝ V] in
theorem sourceInverse_apply {p : V} (a : ExclusionChart C u p)
    (z : EuclideanSpace ℝ (Fin a.dim)) : sourceInverse a (a.param z) = z := by
  change a.param.linear.leftInverse (a.param z - a.param 0) = z
  change a.param.linear.leftInverse (a.param z -ᵥ a.param 0) = z
  rw [← a.param.linear_apply_vsub, vsub_eq_sub,sub_zero]
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (a.param.linear_injective_iff.mpr a.injective)) z
omit [FiniteDimensional ℝ V] in
theorem not_positive_simplex_extreme {ι : Type*} [Fintype ι] [Nontrivial ι]
    (x : ι → V) (hind : AffineIndependent ℝ x) (r : pure C u)
    (hx : ∀ i, x i ∈ base C u) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i,w i = 1) (hrec : ∑ i,w i • x i = (r:V)) : False := by
  classical
  have hrh : (r:V) ∈ convexHull ℝ (range x) := by
    rw [← hrec,← Finset.univ.affineCombination_eq_linear_combination _ _ hsum]
    exact affineCombination_mem_convexHull (fun i _ => (hw i).le) hsum
  have hhull : convexHull ℝ (range x) ⊆ base C u :=
    convexHull_min (by rintro _ ⟨i,rfl⟩; exact hx i) (base_convex C u)
  obtain ⟨i,hi⟩ := extremePoints_convexHull_subset
    (inter_extremePoints_subset_extremePoints_of_subset hhull ⟨hrh,r.property⟩)
  have hcomb : Finset.univ.affineCombination ℝ x w =
      Finset.univ.affineCombination ℝ x (Pi.single i 1) := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hsum,hrec,
      Finset.univ.affineCombination_piSingle ℝ x (Finset.mem_univ i),hi]
  have hwone : w = Pi.single i 1 :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ x).mp hind w
      (Pi.single i 1) hsum (by simp) hcomb
  obtain ⟨j,hji⟩ := exists_ne i
  have hh := hw j
  rw [hwone,Pi.single_eq_of_ne hji] at hh
  exact lt_irrefl _ hh

/-- The actual maximum of an original normal on the entire normalized base. -/
def baseMaximum (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (b : V →L[ℝ] ℝ) : ℝ :=
  sSup (b '' base C u)
private theorem maximum_at (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (t : pure C u)
    (b : V →L[ℝ] ℝ) (hm : ∀ x ∈ base C u, b x ≤ b t) : baseMaximum C u b = b t := by
  exact (show IsGreatest (b '' base C u) (b t) from
    ⟨mem_image_of_mem b (pure_mem t), by rintro _ ⟨x,hx,rfl⟩; exact hm x hx⟩).csSup_eq
theorem uniform_dual_bound (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ A : ℝ, 0 < A ∧ ∀ (t : pure C u) (b : V →L[ℝ] ℝ),
      b ≠ 0 → (∀ x ∈ C, 0 ≤ b x) → b t = 0 →
      0 < baseMaximum C u b ∧ ‖b‖ ≤ A * baseMaximum C u b := by
  obtain ⟨A,hA,hdual⟩ := CommonSourceLiftObstruction.original_dual_bound hc hs hg
  refine ⟨A,hA,fun t b hb hp ht => ?_⟩
  have hb' : b.toLinearMap ≠ 0 := by intro he; exact hb ((by ext z; exact LinearMap.congr_fun he z))
  obtain ⟨s,hsD,hbs,hmax⟩ := positive_annihilator_maximum hc hs hg t b.toLinearMap hb' hp ht
  change 0 < b s at hbs
  change ∀ x ∈ base C u, b x ≤ b s at hmax
  have hM := maximum_at hc hs s b hmax
  refine ⟨hM.symm ▸ hbs,?_⟩
  have hbcont : b.toLinearMap.toContinuousLinearMap = b := by ext x; rfl
  simpa only [CommonSourceLiftObstruction.positive_base_norm hc hs t b.toLinearMap hp,
    hbcont, CommonSourceLiftObstruction.baseMaximum, baseMaximum, ContinuousLinearMap.coe_coe]
    using hdual b.toLinearMap

private theorem contact_estimate
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p t : pure C u) (a : ExclusionChart C u p) (b : V →L[ℝ] ℝ)
    (hb : b ≠ 0) (hp : ∀ x ∈ C, 0 ≤ b x) (ht : b t = 0)
    {A α : ℝ} (hA : ‖b‖ ≤ A * baseMaximum C u b)
    (hα : ∀ x ∈ exclusion C u t, Metric.infDist x (exclusion C u p) ≤ α)
    (hg0 : slope a b ≠ 0) (v : EuclideanSpace ℝ (Fin a.dim)) :
    ∃ x : pure C u, (x : V) ∈ exclusion C u t ∧
      ‖(x : V) - a.param v‖ ≤ α + ‖a.param.linear.toContinuousLinearMap‖ *
        (Real.sqrt (2*A*baseMaximum C u b*α/‖slope a b‖) +
          ‖‖slope a b‖⁻¹ • slope a b - v‖) := by
  have hb' : b.toLinearMap ≠ 0 := by intro he; exact hb ((by ext z; exact LinearMap.congr_fun he z))
  obtain ⟨x,hx,hbx,hmax⟩ := positive_annihilator_maximum hc hs hg t b.toLinearMap hb' hp ht
  change 0 < b x at hbx
  change ∀ z ∈ base C u, b z ≤ b x at hmax
  have hM : baseMaximum C u b = b x := maximum_at hc hs x b hmax
  obtain ⟨z,hz,hzdist⟩ := ((exclusion_ball_faces hc hs hg hB).1 p).2.1.exists_infDist_eq_dist
    ((exclusion_ball_faces hc hs hg hB).1 p).1.nonempty (x:V)
  have hxz : ‖(x:V)-z‖ ≤ α := by rw [← dist_eq_norm,← hzdist]; exact hα x hx
  obtain ⟨q,hq,rfl⟩ := a.whole.symm ▸ hz
  have hq1 : ‖q‖ ≤ 1 := by simpa using hq
  let s := ‖slope a b‖
  let w := s⁻¹ • slope a b
  have hspos : 0 < s := norm_pos_iff.mpr hg0
  have hw : ‖w‖ = 1 := by simp [w,s,norm_smul,hspos.ne']
  have hsw : s • w = slope a b := by simp [w,smul_smul,hspos.ne']
  have htop : b (a.param 0) + s ≤ b x := by
    have hh := hmax (a.param w) (chart_mem a hw.le).1
    rw [slope_formula,← hsw,real_inner_smul_left,real_inner_self_eq_norm_sq,hw] at hh
    simpa using hh
  have hgap : s * (1-⟪w,q⟫) ≤ A*baseMaximum C u b*α := by
    have hh := b.le_opNorm ((x:V)-a.param q)
    have hn : b ((x:V)-a.param q) ≤ ‖b ((x:V)-a.param q)‖ := le_abs_self _
    have hbq := slope_formula a b q
    rw [← hsw,real_inner_smul_left] at hbq
    rw [map_sub] at hn hh
    have hα0 : 0 ≤ α := (norm_nonneg _).trans hxz
    have hh2 := mul_le_mul hA hxz (norm_nonneg _) (le_trans (norm_nonneg _) hA)
    nlinarith
  have hnormsq : ‖q-w‖^2 ≤ 2*(1-⟪w,q⟫) := by
    rw [norm_sub_sq_real,hw,real_inner_comm]
    nlinarith [sq_nonneg ‖q‖,mul_self_le_mul_self (norm_nonneg q) hq1]
  have hsq : ‖q-w‖^2 ≤ 2*A*baseMaximum C u b*α/s := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hnormsq hspos.le]
  have hsqrt : ‖q-w‖ ≤ Real.sqrt (2*A*baseMaximum C u b*α/s) :=
    (Real.le_sqrt (norm_nonneg _) (le_trans (sq_nonneg _) hsq)).mpr hsq
  refine ⟨x,hx,?_⟩
  have hpardiff : a.param q - a.param v = a.param.linear (q-v) := by
    simpa using (a.param.linear_apply_vsub q v).symm
  calc
    _ ≤ ‖(x:V)-a.param q‖ + ‖a.param q-a.param v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ α + ‖a.param.linear.toContinuousLinearMap‖ * ‖q-v‖ := by
      rw [hpardiff]; exact add_le_add hxz (a.param.linear.toContinuousLinearMap.le_opNorm _)
    _ ≤ _ := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sub_le_norm_sub_add_norm_sub q w v).trans (add_le_add_left hsqrt _)

theorem leakage_point_le (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p t : pure C u) {x : V} (hx : x ∈ exclusion C u t) :
    Metric.infDist x (exclusion C u p) ≤ leakage C u p t := by
  exact le_csSup (((exclusion_ball_faces hc hs hg hB).1 t).2.1.bddAbove_image
    (Metric.continuous_infDist_pt _).continuousOn) (mem_image_of_mem _ hx)

/-- All source directions fail at the same actual return label. This is an
extra condition on original positive normals, with no effect-budget bound. -/
def sectorViolation {p : V} (a : ExclusionChart C u p)
    (v : Fin (a.dim+1) → EuclideanSpace ℝ (Fin a.dim)) (t : V) (θ H : ℝ) : Prop :=
  ∀ i, ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ (∀ x ∈ C, 0 ≤ f x) ∧ f t = 0 ∧
    slope a f ≠ 0 ∧ ‖‖slope a f‖⁻¹ • slope a f - v i‖ < θ ∧
    H * baseMaximum C u f * leakage C u p t < ‖slope a f‖

theorem sector_contact_family (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (a : ExclusionChart C u p)
    (b : Fin (a.dim+1) → EuclideanSpace ℝ (Fin a.dim)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ H : ℝ, 0 < θ ∧ 0 < H ∧ ∀ t : pure C u,
      leakage C u p t < δ/4 → sectorViolation a b t θ H →
      ∃ x : Fin (a.dim+1) → pure C u, ∀ i,
        (x i:V) ∈ exclusion C u t ∧ dist (x i:V) (a.param (b i)) < δ := by
  classical
  obtain ⟨A,hA,hdual⟩ := uniform_dual_bound hc hs hg
  let T := ‖a.param.linear.toContinuousLinearMap‖
  let θ := δ / (4*(T+1))
  let H := 2*A/θ^2
  have hT : 0 ≤ T := norm_nonneg _
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨θ,H,hθ,hH,fun t hα hn => ?_⟩
  choose f hf0 hfpos hft hfg hfdir hfbig using hn
  have hcontacts (i : Fin (a.dim+1)) : ∃ x : pure C u,
      (x:V) ∈ exclusion C u t ∧ dist (x:V) (a.param (b i)) < δ := by
    obtain ⟨hM,hbound⟩ := hdual t (f i) (hf0 i) (hfpos i) (hft i)
    obtain ⟨x,hx,he⟩ := contact_estimate hc hs hg hB p t a (f i) (hf0 i)
      (hfpos i) (hft i) hbound (fun x hx => leakage_point_le hc hs hg hB p t hx)
      (hfg i) (b i)
    have hspos : 0 < ‖slope a (f i)‖ := norm_pos_iff.mpr (hfg i)
    have hratio : 2*A*baseMaximum C u (f i)*leakage C u p t/‖slope a (f i)‖ ≤ θ^2 := by
      apply (div_le_iff₀ hspos).mpr
      have hh := mul_le_mul_of_nonneg_right (hfbig i).le (sq_nonneg θ)
      have hHθ : H*θ^2 = 2*A := div_mul_cancel₀ _ (pow_ne_zero 2 hθ.ne')
      calc
        _ = (H*θ^2)*baseMaximum C u (f i)*leakage C u p t := by rw [hHθ]
        _ = H*baseMaximum C u (f i)*leakage C u p t*θ^2 := by ring
        _ ≤ _ := by simpa only [mul_comm] using hh
    have hsqrt : Real.sqrt (2*A*baseMaximum C u (f i)*leakage C u p t/‖slope a (f i)‖) ≤ θ :=
      (Real.sqrt_le_iff).mpr ⟨hθ.le,hratio⟩
    have hsmall : T*(θ+θ) < δ/2 := by
      have heq : (4*(T+1))*θ = δ := mul_div_cancel₀ _ (by positivity)
      nlinarith
    refine ⟨x,hx,?_⟩
    rw [dist_eq_norm]
    calc
      _ ≤ _ := he
      _ ≤ leakage C u p t + T*(θ+θ) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left
          (add_le_add hsqrt (hfdir i).le) hT) _
      _ < δ := by linarith
  choose x hx hxdist using hcontacts
  exact ⟨x,fun i => ⟨hx i,hxdist i⟩⟩

end D5.S3.Quantum.Foundation.OriginalReturnSectors
