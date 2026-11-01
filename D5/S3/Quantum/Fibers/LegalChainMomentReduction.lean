/- GID: D5/S3/Quantum/Fibers/LegalChainMomentReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/LegalChainMomentReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual smooth positive symplectic reduction and exact legal-chain dimensions. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
import D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount

/-! Smooth local lifts, actual tangent reduction, source forms and legal layer dimensions. -/

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentLayers
open D5.S1.Words.AdmissibleWords.AdmissibleCount (adm_iff_no_adjacent_true)
open D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Combinatorics.Graph.LegalWordDegree
open D5.S3.Combinatorics.Graph.LegalWords.SupportSizeCount
open scoped BigOperators

abbrev Words (n : ℕ) := D5.S3.Combinatorics.Graph.LegalWords.EdgeCount.Legal n
abbrev Layer (n k : ℕ) := {I : Pattern n // I.val.card = k}
instance (n k : ℕ) : Fintype (Layer n k) := Fintype.ofFinite _

/-- Characteristic Boolean words identify the actual path subsets without changing support. -/
def patternWordEquiv (n : ℕ) : Pattern n ≃ Words n where
  toFun I := ⟨fun i => decide (i ∈ I.val), by
    apply (adm_iff_no_adjacent_true n _).mpr
    intro i j hij
    by_cases hi : i ∈ I.val
    · right
      have hj : j ∉ I.val := fun hj => I.property i hi j hj hij
      simp [hj]
    · left; simp [hi]⟩
  invFun w := ⟨Finset.univ.filter (fun i => w.val i = true), by
    intro i hi j hj hij
    have h := (adm_iff_no_adjacent_true n w.val).mp w.property i j hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rcases h with h | h <;> simp_all⟩
  left_inv I := by apply Subtype.ext; ext i; simp
  right_inv w := by apply Subtype.ext; funext i; simp

private theorem word_occupation {n : ℕ} (I : Pattern n) :
    occupationCount (patternWordEquiv n I).val = I.val.card := by
  classical
  have he : (Finset.univ.filter (fun i => i ∈ I.val)) = I.val := by ext i; simp
  rw [occupationCount, ← he, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I.val <;> simp [patternWordEquiv, hi]

/-- The maximum legal size is inherited from the existing sharp occupation bound. -/
private theorem layer_bound {n : ℕ} (I : Pattern n) : I.val.card ≤ (n + 1) / 2 := by
  have h := (flippable_bound_and_equality n (patternWordEquiv n I)).1
  rw [word_occupation] at h
  omega

private def layerWordEquiv (n k : ℕ) :
    Layer n k ≃ {w : Words n // occupationCount w.val = k} :=
  (patternWordEquiv n).subtypeEquiv (fun I => by rw [word_occupation])

/-- The actual legal layer count follows by direct use of the frozen support-size theorem. -/
private theorem layer_card {n k : ℕ} (hnk : k ≤ n) :
    Fintype.card (Layer n k) = (n - k + 1).choose k := by
  classical
  rw [Fintype.card_congr (layerWordEquiv n k), Fintype.card_subtype]
  change D5.S3.Combinatorics.Graph.LegalWords.EdgeCount.supportCount n k = _
  rw [support_count_eq_choose]
  congr 1
  omega

private def highLayerEquiv (n q : ℕ) :
    High n q ≃ Σ k : ↥(Finset.Ioc q ((n + 1) / 2)), Layer n k.val where
  toFun I := ⟨⟨I.val.val.card, Finset.mem_Ioc.mpr ⟨I.property, layer_bound I.val⟩⟩,
    I.val, rfl⟩
  invFun z := ⟨z.2.val, by rw [z.2.property]; exact (Finset.mem_Ioc.mp z.1.property).1⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨k, hk⟩, ⟨I, hI⟩⟩
    change I.val.card = k at hI
    subst k
    rfl

/-- Exact high-order counts for all natural q, including an empty high layer. -/
private theorem high_card {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    Fintype.card (High n q) =
      ∑ k ∈ Finset.Ioc q ((n + 1) / 2), (n - k + 1).choose k := by
  classical
  rw [Fintype.card_congr (highLayerEquiv n q), Fintype.card_sigma]
  have hc : ∀ k : ↥(Finset.Ioc q ((n + 1) / 2)),
      Fintype.card (Layer n k.val) = (n - k.val + 1).choose k.val := by
    intro k
    apply layer_card
    have hk := (Finset.mem_Ioc.mp k.property).2
    omega
  simp_rw [hc]
  exact Finset.sum_coe_sort (Finset.Ioc q ((n + 1) / 2))
    (fun k => (n - k + 1).choose k)

end D5.S3.Quantum.Fibers.LegalChainMomentLayers

end

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentSmooth
open D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open D5.S3.Quantum.Fibers.LegalChainMomentTopology
open scoped Manifold Topology ContDiff

section LiftCharts
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
  (f : E →+ T) (hf : IsLocalHomeomorph f)
include hf

private theorem transition_translation (e e' : OpenPartialHomeomorph T E)
    (he : (e.symm : E → T) = f) (he' : (e'.symm : E → T) = f)
    (x : E) (hx : x ∈ (e.symm.trans e').source) :
    (e.symm.trans e' : E → E) =ᶠ[𝓝 x]
      (fun y => y + ((e.symm.trans e') x - x)) := by
  let t := e.symm.trans e'
  have hcx : ContinuousAt t x := t.continuousOn.continuousAt (t.open_source.mem_nhds hx)
  have hdelta : ContinuousAt (fun y => t y - y) x := hcx.sub continuousAt_id
  obtain ⟨e0, hxU, he0⟩ := hf (t x - x)
  have hnear : ∀ᶠ y in 𝓝 x, t y - y ∈ e0.source :=
    hdelta (e0.open_source.mem_nhds hxU)
  have hinj : e0.source.InjOn f := he0 ▸ e0.injOn
  have hsrc : ∀ᶠ y in 𝓝 x, y ∈ t.source := t.open_source.mem_nhds hx
  have hperiod : ∀ y ∈ t.source, f (t y - y) = 0 := by
    intro y hy
    rw [map_sub]
    have hy' : e.symm y ∈ e'.source := hy.2
    have hyf : f (e' (e.symm y)) = e.symm y := by
      rw [← he']
      exact e'.left_inv hy'
    change f (e' (e.symm y)) - f y = 0
    rw [hyf, he]
    exact sub_self _
  filter_upwards [hnear, hsrc] with y hyU hys
  have hd : t y - y = t x - x := hinj hyU hxU ((hperiod y hys).trans (hperiod x hx).symm)
  change t y = y + (t x - x)
  rw [← hd]
  abel

private theorem transition_smooth (e e' : OpenPartialHomeomorph T E)
    (he : (e.symm : E → T) = f) (he' : (e'.symm : E → T) = f) :
    ContDiffOn ℝ ∞ (e.symm.trans e') (e.symm.trans e').source := by
  intro x hx
  exact ((contDiff_id.add contDiff_const).contDiffAt.congr_of_eventuallyEq
    (transition_translation f hf e e' he he' x hx)).contDiffWithinAt

private theorem projection_translation (e : OpenPartialHomeomorph T E)
    (he : (e.symm : E → T) = f) (x : E) (hx : f x ∈ e.source) :
    (fun y => e (f y)) =ᶠ[𝓝 x] (fun y => y + (e (f x) - x)) := by
  have hc : ContinuousAt (fun y => e (f y)) x :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hx)).comp hf.continuous.continuousAt
  have hdelta := hc.sub continuousAt_id
  obtain ⟨e0, hxU, he0⟩ := hf (e (f x) - x)
  have hnear : ∀ᶠ y in 𝓝 x, e (f y) - y ∈ e0.source :=
    hdelta (e0.open_source.mem_nhds hxU)
  have hsrc : ∀ᶠ y in 𝓝 x, f y ∈ e.source :=
    hf.continuous.continuousAt (e.open_source.mem_nhds hx)
  have hinj : e0.source.InjOn f := he0 ▸ e0.injOn
  have hperiod : ∀ y, f y ∈ e.source → f (e (f y) - y) = 0 := by
    intro y hy
    rw [map_sub]
    have hyf : f (e (f y)) = f y := by
      calc
        f (e (f y)) = e.symm (e (f y)) := congrFun he.symm _
        _ = f y := e.left_inv hy
    rw [hyf, sub_self]
  filter_upwards [hnear, hsrc] with y hyU hys
  have hd := hinj hyU hxU ((hperiod y hys).trans (hperiod x hx).symm)
  rw [show e (f x) - x = e (f y) - y from hd.symm]
  abel

private theorem projection_derivative (e : OpenPartialHomeomorph T E)
    (he : (e.symm : E → T) = f) (x : E) (hx : f x ∈ e.source) :
    HasFDerivAt (fun y => e (f y)) (ContinuousLinearMap.id ℝ E) x :=
  ((hasFDerivAt_id x).add_const (e (f x) - x)).congr_of_eventuallyEq
    (projection_translation f hf e he x hx)

/-- The atlas consists of genuine local inverses of a surjective period projection. -/
private def liftChartedSpace (hs : Function.Surjective f) : ChartedSpace E T where
  atlas := Set.range hf.localInverseAt
  chartAt x := hf.localInverseAt (Function.surjInv hs x)
  mem_chart_source x := by
    have h := hf.apply_self_mem_localInverseAt_source (x := Function.surjInv hs x)
    simpa only [Function.surjInv_eq hs] using h
  chart_mem_atlas x := ⟨_, rfl⟩

private theorem lift_manifold (hs : Function.Surjective f) :
    letI := liftChartedSpace f hf hs
    IsManifold 𝓘(ℝ, E) ∞ T := by
  letI := liftChartedSpace f hf hs
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id, Set.inter_univ, Set.preimage_id] using
    transition_smooth f hf (hf.localInverseAt a) (hf.localInverseAt b)
      (hf.localInverseAt_symm a) (hf.localInverseAt_symm b)

end LiftCharts

/-- The actual period projection is additive, without a rescaled or finite covering lattice. -/
def angleProjection (n q : ℕ) : (High n q → ℝ) →+ (High n q → AddCircle (2 * Real.pi)) where
  toFun := angleCover n q
  map_zero' := by funext T; simp [angleCover]
  map_add' x y := by funext T; simp [angleCover]

private theorem angle_surjective (n q : ℕ) : Function.Surjective (angleProjection n q) := by
  intro phi
  have h : ∀ T, ∃ a : ℝ, (a : AddCircle (2 * Real.pi)) = phi T :=
    fun T => QuotientAddGroup.mk_surjective (phi T)
  choose a ha using h
  exact ⟨a, funext ha⟩

instance torusCharted (n q : ℕ) :
    ChartedSpace (High n q → ℝ) (High n q → AddCircle (2 * Real.pi)) :=
  liftChartedSpace (angleProjection n q) (legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.2.2.2.2 (angle_surjective n q)

instance torusSmooth (n q : ℕ) :
    IsManifold 𝓘(ℝ, High n q → ℝ) ∞ (High n q → AddCircle (2 * Real.pi)) :=
  lift_manifold (angleProjection n q) (legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.2.2.2.2 (angle_surjective n q)

/-- In every real-lift chart the actual phase-period projection has identity derivative. -/
private theorem angle_chart_hasFDerivAt {n q : ℕ}
    (e : OpenPartialHomeomorph (High n q → AddCircle (2 * Real.pi)) (High n q → ℝ))
    (he : e ∈ atlas (High n q → ℝ) (High n q → AddCircle (2 * Real.pi)))
    (theta : High n q → ℝ) (h : angleCover n q theta ∈ e.source) :
    HasFDerivAt (fun t => e (angleCover n q t))
      (ContinuousLinearMap.id ℝ (High n q → ℝ)) theta := by
  obtain ⟨a, rfl⟩ := he
  exact projection_derivative (angleProjection n q) (legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.2.2.2.2 _
    ((legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.2.2.2.2.localInverseAt_symm a) theta h

section Transport
variable {E K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace K] [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace K M]

@[instance_reducible]
private def transportedCharts (h : M ≃ₜ N) : ChartedSpace K N where
  atlas := Set.range (fun a : M => h.symm.toOpenPartialHomeomorph.trans (chartAt K a))
  chartAt x := h.symm.toOpenPartialHomeomorph.trans (chartAt K (h.symm x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨_, rfl⟩

private theorem transported_smooth {I : ModelWithCorners ℝ E K}
    [IsManifold I ∞ M] (h : M ≃ₜ N) :
    letI := transportedCharts (K := K) h
    IsManifold I ∞ N := by
  letI := transportedCharts (K := K) h
  haveI : HasGroupoid N (contDiffGroupoid ∞ I) := by
    constructor
    rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
    have htrans :
        (h.symm.toOpenPartialHomeomorph.trans (chartAt K a)).symm.trans
          (h.symm.toOpenPartialHomeomorph.trans (chartAt K b)) =
        (chartAt K a).symm.trans (chartAt K b) := by
      ext x <;> simp [OpenPartialHomeomorph.trans_source]
    rw [htrans]
    exact (contDiffGroupoid ∞ I).compatible (chart_mem_atlas K a) (chart_mem_atlas K b)
  exact IsManifold.mk' I ∞ N

end Transport

instance probabilityDomainNonempty {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    Nonempty (positiveDomain q p0) := by
  obtain ⟨x, hx⟩ := ((legal_chain_coordinate_laws n q).2.2.2.2.1 p0).1
  exact ⟨⟨x, hx⟩⟩

instance probabilityCharted {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    ChartedSpace (High n q → ℝ) (positiveDomain q p0) :=
  (((legal_chain_coordinate_laws n q).2.2.2.2.1 p0).2.1).isOpenEmbedding_subtypeVal.singletonChartedSpace

instance probabilitySmooth {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    IsManifold 𝓘(ℝ, High n q → ℝ) ∞ (positiveDomain q p0) :=
  (((legal_chain_coordinate_laws n q).2.2.2.2.1 p0).2.1).isOpenEmbedding_subtypeVal.isManifold_singleton

/-- The actual orbit quotient has the smooth structure determined by its proved inverse charts. -/
instance reductionCharted {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    ChartedSpace (ModelProd (High n q → ℝ) (High n q → ℝ))
      (Quotient (reductionSetoid q p0)) :=
  transportedCharts (K := ModelProd (High n q → ℝ) (High n q → ℝ))
    (reductionHomeomorph q p0).symm

/-- This is a smooth manifold for every nonempty positive fibre, including the point fibre. -/
instance reductionSmooth {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    IsManifold (𝓘(ℝ, High n q → ℝ).prod 𝓘(ℝ, High n q → ℝ)) ∞
      (Quotient (reductionSetoid q p0)) :=
  transported_smooth (I := 𝓘(ℝ, High n q → ℝ).prod 𝓘(ℝ, High n q → ℝ))
    (reductionHomeomorph q p0).symm

/-- The quotient charts use the actual high moments and local lifts of the actual relation phases. -/
private theorem reduction_chart_coordinates {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z y : Quotient (reductionSetoid q p0)) :
    chartAt (ModelProd (High n q → ℝ) (High n q → ℝ)) z y =
      ((reductionHomeomorph q p0 y).1.val,
        chartAt (High n q → ℝ) (reductionHomeomorph q p0 z).2
          (reductionHomeomorph q p0 y).2) := by
  rfl

end D5.S3.Quantum.Fibers.LegalChainMomentSmooth

end

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentReduction
open D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open D5.S3.Quantum.Fibers.LegalChainMomentGeometry
open D5.S3.Quantum.Fibers.LegalChainMomentLayers
open D5.S3.Quantum.Fibers.LegalChainMomentSmooth
open scoped BigOperators ContDiff Topology Manifold

abbrev H (n q : ℕ) := High n q → ℝ
abbrev E (n q : ℕ) := H n q × H n q

/-- Zero extension of the high real moment or phase coordinates. -/
def highLinear (n q : ℕ) : H n q →ₗ[ℝ] V n :=
  { highEmbedding n q ℝ with
    map_smul' := by intro c x; ext I; simp [highEmbedding] }

/-- A real lift of the actual inverse quotient coordinates in the original variables. -/
def representativeLift {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) (z : E n q) :
    V n × V n :=
  (probabilities (fillMoments q p0 z.1), originalPhases (highEmbedding n q ℝ z.2))

/-- The linear part of that affine lift. -/
def liftLinear (n q : ℕ) : E n q →ₗ[ℝ] V n × V n :=
  (((momentLinearEquiv n).symm.toLinearMap.comp (highLinear n q)).comp
    (LinearMap.fst ℝ (H n q) (H n q))).prod
    (((phaseLinearEquiv n).symm.toLinearMap.comp (highLinear n q)).comp
      (LinearMap.snd ℝ (H n q) (H n q)))

private theorem lift_affine {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) (z : E n q) :
    representativeLift q p0 z = representativeLift q p0 0 + liftLinear n q z := by
  have hfill : fillMoments q p0 z.1 =
      fillMoments q p0 0 + highEmbedding n q ℝ z.1 := by
    ext I
    simp only [fillMoments, highEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Pi.add_apply, Pi.zero_apply]
    by_cases hi : I.val.card ≤ q
    · simp [hi, not_lt.mpr hi]
    · simp [hi, not_le.mp hi]
  apply Prod.ext
  · change probabilities (fillMoments q p0 z.1) =
      probabilities (fillMoments q p0 0) + probabilities (highEmbedding n q ℝ z.1)
    rw [hfill]
    exact (momentEquiv n ℝ).symm.map_add _ _
  · change originalPhases (highEmbedding n q ℝ z.2) =
      originalPhases (highEmbedding n q ℝ 0) + originalPhases (highEmbedding n q ℝ z.2)
    have hz : originalPhases (highEmbedding n q ℝ 0) = (0 : V n) := by
      change (phaseEquiv n ℝ).symm ((highEmbedding n q ℝ) 0) = 0
      rw [map_zero, map_zero]
    rw [hz, zero_add]

/-- The tangent lift is the actual derivative, rather than a supplied rank premise. -/
private theorem representative_lift_hasFDerivAt {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : E n q) :
    HasFDerivAt (representativeLift q p0) (liftLinear n q).toContinuousLinearMap z := by
  have h := ((liftLinear n q).toContinuousLinearMap.hasFDerivAt (x := z)).const_add
    (representativeLift q p0 0)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (lift_affine q p0))

/-- Tangents to the full fixed-low-moment equations, including normalization. -/
def fixedTangent (n q : ℕ) : Submodule ℝ (V n × V n) where
  carrier := {d | ∀ T : Low n q, moments d.1 T.val = 0}
  zero_mem' := by intro T; exact congrFun (map_zero (momentLinearEquiv n)) T.val
  add_mem' := by
    intro d e hd he T
    change momentLinearEquiv n (d.1 + e.1) T.val = 0
    rw [map_add]
    change moments d.1 T.val + moments e.1 T.val = 0
    rw [hd T, he T, zero_add]
  smul_mem' := by
    intro c d hd T
    change momentLinearEquiv n (c • d.1) T.val = 0
    rw [map_smul]; change c * moments d.1 T.val = 0; rw [hd T, mul_zero]

/-- Differentiate the actual high moments and relation phases. -/
def tangentCoordinates (n q : ℕ) : fixedTangent n q →ₗ[ℝ] E n q where
  toFun d := ((fun T => moments d.val.1 T.val), (fun T => phases d.val.2 T.val))
  map_add' d e := by
    apply Prod.ext <;> ext T
    · exact congrFun ((momentLinearEquiv n).map_add d.val.1 e.val.1) T.val
    · exact congrFun ((phaseLinearEquiv n).map_add d.val.2 e.val.2) T.val
  map_smul' c d := by
    apply Prod.ext <;> ext T
    · exact congrFun ((momentLinearEquiv n).map_smul c d.val.1) T.val
    · exact congrFun ((phaseLinearEquiv n).map_smul c d.val.2) T.val

private theorem lift_moments (n q : ℕ) (d : E n q) :
    moments (liftLinear n q d).1 = highEmbedding n q ℝ d.1 :=
  (momentEquiv n ℝ).apply_symm_apply _

private theorem lift_phases (n q : ℕ) (d : E n q) :
    phases (liftLinear n q d).2 = highEmbedding n q ℝ d.2 :=
  (phaseEquiv n ℝ).apply_symm_apply _

private theorem lift_fixed (n q : ℕ) (d : E n q) : liftLinear n q d ∈ fixedTangent n q := by
  intro T
  rw [lift_moments]
  simp [highEmbedding, not_lt.mpr T.property]

private theorem coordinates_lift (n q : ℕ) (d : E n q) :
    tangentCoordinates n q ⟨liftLinear n q d, lift_fixed n q d⟩ = d := by
  apply Prod.ext <;> ext T
  · change moments (liftLinear n q d).1 T.val = d.1 T
    rw [lift_moments]; simp [highEmbedding, T.property]
  · change phases (liftLinear n q d).2 T.val = d.2 T
    rw [lift_phases]; simp [highEmbedding, T.property]

/-- The actual infinitesimal low-phase orbits, at fixed probability. -/
def verticalTangent (n q : ℕ) : Submodule ℝ (fixedTangent n q) where
  carrier := {d | d.val.1 = 0 ∧ ∃ t, d.val.2 = actionHom n q ℝ t}
  zero_mem' := ⟨rfl, 0, by simp⟩
  add_mem' := by
    rintro d e ⟨hd, t, ht⟩ ⟨he, u, hu⟩
    exact ⟨by change d.val.1 + e.val.1 = 0; rw [hd, he, zero_add],
      t + u, by change d.val.2 + e.val.2 = _; rw [ht, hu, map_add]⟩
  smul_mem' := by
    rintro c d ⟨hd, t, ht⟩
    refine ⟨by change c • d.val.1 = 0; rw [hd, smul_zero], c • t, ?_⟩
    change c • d.val.2 = actionHom n q ℝ (c • t)
    rw [ht]
    apply (phaseLinearEquiv n).injective
    rw [map_smul]
    change c • phaseEquiv n ℝ ((phaseEquiv n ℝ).symm _) =
      phaseEquiv n ℝ ((phaseEquiv n ℝ).symm _)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    ext I
    simp [lowEmbedding]

private theorem vertical_eq_kernel (n q : ℕ) :
    verticalTangent n q = (tangentCoordinates n q).ker := by
  ext d
  change (d.val.1 = 0 ∧ ∃ t, d.val.2 = actionHom n q ℝ t) ↔
    tangentCoordinates n q d = 0
  constructor
  · rintro ⟨hp, t, ht⟩
    apply Prod.ext <;> ext T
    · change moments d.val.1 T.val = 0; rw [hp]; exact congrFun (map_zero (momentEquiv n ℝ)) _
    · change phases d.val.2 T.val = 0
      rw [ht]
      change phaseEquiv n ℝ ((phaseEquiv n ℝ).symm _) T.val = 0
      rw [AddEquiv.apply_symm_apply]
      simp [lowEmbedding, not_le.mpr T.property]
  · intro h
    have hlow : ∀ T : Low n q, moments d.val.1 T.val = 0 := d.property
    have hhigh : ∀ T : High n q, moments d.val.1 T.val = 0 :=
      fun T => congrFun (congrArg Prod.fst h) T
    have hp : d.val.1 = 0 := by
      apply (momentEquiv n ℝ).injective
      rw [map_zero]
      ext I
      by_cases hi : I.val.card ≤ q
      · exact hlow ⟨I, hi⟩
      · exact hhigh ⟨I, not_le.mp hi⟩
    refine ⟨hp, ?_⟩
    have hphase : highPhases (q := q) (0 : V n) = highPhases d.val.2 := by
      ext T
      have he := congrFun (congrArg Prod.snd h) T
      change phaseEquiv n ℝ 0 T.val = _
      rw [map_zero]
      exact he.symm
    obtain ⟨t, ht⟩ := ((legal_chain_coordinate_laws n q).2.2.2.1 ℝ (0 : V n) d.val.2).mpr hphase
    exact ⟨t, by simpa only [zero_add, (legal_chain_coordinate_laws n q).2.2.1 ℝ] using ht⟩

/-- The tangent quotient by the actual low-phase velocities is exactly the high-coordinate space. -/
def reducedTangentEquiv (n q : ℕ) :
    (fixedTangent n q ⧸ verticalTangent n q) ≃ₗ[ℝ] E n q := by
  rw [vertical_eq_kernel]
  exact (tangentCoordinates n q).quotKerEquivOfSurjective
    (fun d => ⟨⟨liftLinear n q d, lift_fixed n q d⟩, coordinates_lift n q d⟩)

/-- The canonical high-coordinate alternating pairing. -/
def reducedForm (n q : ℕ) (d e : E n q) : ℝ :=
  ∑ T, (d.2 T * e.1 T - e.2 T * d.1 T)

private theorem sum_high (n q : ℕ) (f : Pattern n → ℝ)
    (hf : ∀ T, T.val.card ≤ q → f T = 0) :
    ∑ I, f I = ∑ T : High n q, f T.val := by
  classical
  have hsum := Finset.sum_subtype (F := inferInstanceAs (Fintype (High n q)))
    (Finset.univ.filter (fun I : Pattern n => q < I.val.card))
    (by simp : ∀ I : Pattern n, I ∈ Finset.univ.filter (fun I => q < I.val.card) ↔
      q < I.val.card) f
  rw [← hsum]
  exact (Finset.sum_subset (Finset.filter_subset _ _) (by
    intro I _ hi
    apply hf
    simpa using hi)).symm

/-- The source form on every fixed-moment tangent factors through exactly the high velocities. -/
private theorem fixed_source_form (n q : ℕ) (d e : fixedTangent n q) :
    sourceTwoForm n d.val e.val =
      reducedForm n q (tangentCoordinates n q d) (tangentCoordinates n q e) := by
  rw [(legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.1]
  rw [sum_high n q _ (by
    intro T hT
    rw [d.property ⟨T, hT⟩, e.property ⟨T, hT⟩, mul_zero, mul_zero, sub_self])]
  rfl

private theorem fixed_normalized (n q : ℕ) (d : fixedTangent n q) :
    ∑ I, d.val.1 I = 0 := by
  have h := d.property ⟨emptyPattern n, by simp [emptyPattern]⟩
  simpa [moments, act, incidence, emptyPattern] using h

/-- The actual projective expression has the same value for all tangent representatives. -/
private theorem fixed_projective_form (n q : ℕ) (x : V n × V n)
    (hx : ∀ I, 0 < x.1 I) (d e : fixedTangent n q) :
    projectiveTwoForm n x d.val e.val =
      reducedForm n q (tangentCoordinates n q d) (tangentCoordinates n q e) := by
  rw [(legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.2.1 x d.val e.val hx
    (fixed_normalized n q d) (fixed_normalized n q e), fixed_source_form]

/-- Restricting the actual source form to the differentiated inverse chart gives the high pairs. -/
theorem reduced_form_pullback (n q : ℕ) (d e : E n q) :
    sourceTwoForm n (liftLinear n q d) (liftLinear n q e) = reducedForm n q d e := by
  rw [(legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.1, lift_moments, lift_moments, lift_phases, lift_phases]
  rw [sum_high n q _ (by intro T hT; simp [highEmbedding, not_lt.mpr hT])]
  apply Finset.sum_congr rfl
  intro T _
  simp [reducedForm, highEmbedding, T.property]

/-- Nondegeneracy includes the zero-dimensional case, since no surviving tangent is omitted. -/
private theorem reduced_form_nondegenerate (n q : ℕ) (d : E n q)
    (h : ∀ e, reducedForm n q d e = 0) : d = 0 := by
  classical
  apply Prod.ext <;> ext T
  · have ht := h (0, Pi.single T 1)
    simpa [reducedForm, Pi.single_apply, mul_ite, ite_mul] using ht
  · have ht := h (Pi.single T 1, 0)
    simpa [reducedForm, Pi.single_apply, mul_ite, ite_mul] using ht

/-- The radical of the restricted source form is precisely the actual infinitesimal phase action. -/
private theorem source_form_radical (n q : ℕ) (d : fixedTangent n q) :
    (∀ e : fixedTangent n q, sourceTwoForm n d.val e.val = 0) ↔
      d ∈ verticalTangent n q := by
  rw [vertical_eq_kernel]
  change _ ↔ tangentCoordinates n q d = 0
  constructor
  · intro h
    apply reduced_form_nondegenerate
    intro e
    have he := h ⟨liftLinear n q e, lift_fixed n q e⟩
    rw [fixed_source_form, coordinates_lift] at he
    exact he
  · intro h e
    rw [fixed_source_form, h]
    simp [reducedForm]

/-- The dimension is computed from the derived legal-layer cardinalities. -/
private theorem reduced_tangent_dimension {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    Module.finrank ℝ (fixedTangent n q ⧸ verticalTangent n q) =
      2 * ∑ k ∈ Finset.Ioc q ((n + 1) / 2), (n - k + 1).choose k := by
  rw [(reducedTangentEquiv n q).finrank_eq, Module.finrank_prod, Module.finrank_pi]
  rw [high_card hn]
  omega

end D5.S3.Quantum.Fibers.LegalChainMomentReduction

end

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentAtlas
open D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open D5.S3.Quantum.Fibers.LegalChainMomentTopology
open D5.S3.Quantum.Fibers.LegalChainMomentGeometry
open D5.S3.Quantum.Fibers.LegalChainMomentLayers
open D5.S3.Quantum.Fibers.LegalChainMomentSmooth
open D5.S3.Quantum.Fibers.LegalChainMomentReduction
open scoped Topology ContDiff Manifold BigOperators

/-- The local coordinate expression of the real covering of the actual quotient. -/
def liftedChart {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) (u : E n q) : E n q :=
  (u.1, chartAt (High n q → ℝ) (reductionHomeomorph q p0 z).2 (angleCover n q u.2))

/-- This expression is the actual quotient chart on every admissible real lift. -/
private theorem lifted_chart_eq {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0))
    (u : positiveDomain q p0 × H n q) :
    chartAt (ModelProd (H n q) (H n q)) z (quotientCover q p0 u) =
      liftedChart q p0 z (u.1.val, u.2) := by
  rw [reduction_chart_coordinates]
  simp only [quotientCover, Homeomorph.apply_symm_apply, liftedChart]

/-- Every genuine local lift chart has identity differential over its whole source. -/
private theorem lifted_chart_hasFDerivAt_in_source {n : ℕ} (q : ℕ)
    (p0 : PositiveProbability n) (z : Quotient (reductionSetoid q p0))
    (u : positiveDomain q p0 × H n q)
    (hmem : angleCover n q u.2 ∈ (chartAt (H n q) (reductionHomeomorph q p0 z).2).source) :
    HasFDerivAt (liftedChart q p0 z) (ContinuousLinearMap.id ℝ (E n q))
      (u.1.val, u.2) := by
  have hangle := angle_chart_hasFDerivAt _ (chart_mem_atlas _ _) u.2 hmem
  have hsnd := hangle.comp (u.1.val, u.2)
    (ContinuousLinearMap.snd ℝ (H n q) (H n q)).hasFDerivAt
  have hfst := (ContinuousLinearMap.fst ℝ (H n q) (H n q)).hasFDerivAt
    (x := (u.1.val, u.2))
  convert! hfst.prodMk hsnd using 1

/-- Differentiating a genuine quotient chart after any real lift gives identity. -/
private theorem lifted_chart_hasFDerivAt {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) (u : positiveDomain q p0 × H n q)
    (hu : quotientCover q p0 u = z) :
    HasFDerivAt (liftedChart q p0 z) (ContinuousLinearMap.id ℝ (E n q)) (u.1.val, u.2) := by
  have hphase : angleCover n q u.2 = (reductionHomeomorph q p0 z).2 := by
    simpa only [quotientCover, Homeomorph.apply_symm_apply] using
      congrArg (fun w => (reductionHomeomorph q p0 w).2) hu
  have hmem : angleCover n q u.2 ∈
      (chartAt (H n q) (reductionHomeomorph q p0 z).2).source := by
    rw [hphase]
    exact mem_chart_source _ _
  exact lifted_chart_hasFDerivAt_in_source q p0 z u hmem

/-- High relation-phase velocities computed from the original phase variables. -/
def highPhaseLinear (n q : ℕ) : V n →ₗ[ℝ] H n q where
  toFun := highPhases
  map_add' x y := by ext T; exact congrFun ((phaseLinearEquiv n).map_add x y) T.val
  map_smul' c x := by ext T; exact congrFun ((phaseLinearEquiv n).map_smul c x) T.val

/-- The actual orbit projection represented using arbitrary original real phases. -/
def originalPhaseProjection {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (x : positiveDomain q p0) (theta : V n) : Quotient (reductionSetoid q p0) :=
  Quotient.mk _ ((probabilityFibreEquiv q p0).symm x,
    fun I => (theta I : AddCircle (2 * Real.pi)))

private theorem high_phases_period {n q : ℕ} (theta : V n) :
    highPhases (q := q) (fun I => (theta I : AddCircle (2 * Real.pi))) =
      angleCover n q (highPhases theta) := by
  ext T
  change (∑ I, (signedIncidence n).transpose T.val I •
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * Real.pi))) (theta I)) =
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * Real.pi)))
      (∑ I, (signedIncidence n).transpose T.val I • theta I)
  rw [map_sum]
  simp only [map_zsmul]

/-- The quotient projection uses exactly the high transformed phases of the original state. -/
private theorem original_projection_eq_cover {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (x : positiveDomain q p0) (theta : V n) :
    originalPhaseProjection q p0 x theta = quotientCover q p0 (x, highPhases theta) := by
  apply (reductionHomeomorph q p0).injective
  change (probabilityFibreEquiv q p0 ((probabilityFibreEquiv q p0).symm x), _) = _
  simp only [Equiv.apply_symm_apply, quotientCover, Homeomorph.apply_symm_apply,
    high_phases_period]

/-- An ambient real expression for a quotient chart after the actual projection. -/
def projectedChart {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) (v : H n q × V n) : E n q :=
  liftedChart q p0 z (v.1, highPhases v.2)

/-- Its derivative drops precisely the low phase velocities and keeps all high moment velocities. -/
private theorem projected_chart_hasFDerivAt {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (x : positiveDomain q p0) (theta : V n) :
    HasFDerivAt (projectedChart q p0 (originalPhaseProjection q p0 x theta))
      ((LinearMap.fst ℝ (H n q) (V n)).prod
        ((highPhaseLinear n q).comp (LinearMap.snd ℝ (H n q) (V n)))).toContinuousLinearMap
      (x.val, theta) := by
  let L : (H n q × V n) →ₗ[ℝ] E n q :=
    (LinearMap.fst ℝ (H n q) (V n)).prod
      ((highPhaseLinear n q).comp (LinearMap.snd ℝ (H n q) (V n)))
  have h := lifted_chart_hasFDerivAt q p0 _ (x, highPhases theta)
    (original_projection_eq_cover q p0 x theta).symm
  convert! h.comp (x.val, theta)
    (L.toContinuousLinearMap.hasFDerivAt (x := (x.val, theta))) using 1

/-- The chart expression above agrees with the original orbit projection on its positive domain. -/
private theorem projected_chart_eq {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) (x : positiveDomain q p0) (theta : V n) :
    chartAt (ModelProd (H n q) (H n q)) z (originalPhaseProjection q p0 x theta) =
      projectedChart q p0 z (x.val, theta) := by
  rw [original_projection_eq_cover, lifted_chart_eq]
  rfl

/-- The actual smooth quotient has the dimension supplied by its proved local tangent coordinates. -/
private theorem quotient_manifold_dimension {n : ℕ} (hn : 1 ≤ n) (q : ℕ)
    (p0 : PositiveProbability n) (z : Quotient (reductionSetoid q p0)) :
    Module.finrank ℝ (TangentSpace
      (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) z) =
      2 * ∑ k ∈ Finset.Ioc q ((n + 1) / 2), (n - k + 1).choose k := by
  change Module.finrank ℝ (E n q) = _
  exact (reducedTangentEquiv n q).finrank_eq.symm.trans (reduced_tangent_dimension hn q)

end D5.S3.Quantum.Fibers.LegalChainMomentAtlas

end

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentReduction
open D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open D5.S3.Quantum.Fibers.LegalChainMomentTopology
open D5.S3.Quantum.Fibers.LegalChainMomentGeometry
open D5.S3.Quantum.Fibers.LegalChainMomentLayers
open D5.S3.Quantum.Fibers.LegalChainMomentSmooth
open D5.S3.Quantum.Fibers.LegalChainMomentAtlas
open scoped BigOperators Topology ContDiff Manifold

private theorem normalized_polar {n : ℕ} (p : PositiveProbability n) (theta : V n) :
    ∑ I, Complex.normSq (polarMap n (p.val, theta) I) = 1 := by
  have h : ∀ I, Complex.normSq (polarMap n (p.val, theta) I) = p.val I := by
    intro I
    rw [polarMap, Complex.normSq_mul, Complex.normSq_ofReal]
    have hexp : Complex.normSq (Complex.exp (-Complex.I * (theta I : ℂ))) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
      simp
    rw [hexp, mul_one, Real.mul_self_sqrt (p.property.1 I).le]
  simp_rw [h]
  exact p.property.2

/-- The bilinear form obtained by the actual differentiated inverse and the source form. -/
def sourceReducedBilin (n q : ℕ) : LinearMap.BilinForm ℝ (E n q) :=
  LinearMap.mk₂ ℝ (fun d e => sourceTwoForm n (liftLinear n q d) (liftLinear n q e))
    (by
      intro d d' e
      simp only [reduced_form_pullback, reducedForm, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T _
      ring)
    (by
      intro c d e
      simp only [reduced_form_pullback, reducedForm, Prod.smul_fst, Prod.smul_snd,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring)
    (by
      intro d e e'
      simp only [reduced_form_pullback, reducedForm, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T _
      ring)
    (by
      intro c d e
      simp only [reduced_form_pullback, reducedForm, Prod.smul_fst, Prod.smul_snd,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring)

/-- The actual source two-form as a continuous alternating map. -/
def sourceAlternating (n : ℕ) : (V n × V n) [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := sourceTwoForm n (v 0) (v 1)
  map_update_add' := by
    intro inst v i x y
    fin_cases i
    all_goals
      simp only [sourceTwoForm, Function.update_apply]
      norm_num
      simp only [mul_add, add_mul, Finset.sum_add_distrib]
      ring
  map_update_smul' := by
    intro inst v i c x
    fin_cases i
    all_goals
      simp only [sourceTwoForm, Function.update_apply]
      norm_num
      simp_rw [mul_assoc, mul_left_comm _ c, ← Finset.mul_sum]
      ring
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [sourceTwoForm]
  cont := by
    change Continuous (fun v : Fin 2 → V n × V n =>
      ∑ I, ((v 0).2 I * (v 1).1 I - (v 1).2 I * (v 0).1 I))
    fun_prop

/-- The literal pullback along the differentiated real inverse coordinates. -/
def liftedSourceTwoForm {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (u : E n q) : E n q [⋀^Fin 2]→L[ℝ] ℝ :=
  (sourceAlternating n).compContinuousLinearMap (fderiv ℝ (representativeLift q p0) u)

private theorem lifted_source_closed {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (u : E n q) : extDeriv (liftedSourceTwoForm q p0) u = 0 := by
  have hf : liftedSourceTwoForm q p0 = fun _ : E n q =>
      (sourceAlternating n).compContinuousLinearMap (liftLinear n q).toContinuousLinearMap := by
    funext x
    exact congrArg ((sourceAlternating n).compContinuousLinearMap)
      (representative_lift_hasFDerivAt q p0 x).fderiv
  rw [hf]
  simp only [extDeriv, fderiv_const_apply, ContinuousAlternatingMap.alternatizeUncurryFin,
    map_zero]

private theorem lifted_source_values {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (u : E n q) (v : Fin 2 → E n q) :
    liftedSourceTwoForm q p0 u v = reducedForm n q (v 0) (v 1) := by
  change sourceTwoForm n (fderiv ℝ (representativeLift q p0) u (v 0))
    (fderiv ℝ (representativeLift q p0) u (v 1)) = _
  rw [(representative_lift_hasFDerivAt q p0 u).fderiv]
  exact reduced_form_pullback n q (v 0) (v 1)

/-- The descended source form on the actual quotient tangent spaces. -/
def quotientTwoForm {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) :
    LinearMap.BilinForm ℝ (TangentSpace (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) z) :=
  sourceReducedBilin n q

private theorem quotient_form_coordinates {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) (d e : E n q) :
    quotientTwoForm q p0 z d e = reducedForm n q d e :=
  reduced_form_pullback n q d e

private theorem quotient_form_source {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) (p : ProbabilityFibre q p0) (theta : V n)
    (d e : fixedTangent n q) :
    quotientTwoForm q p0 z (tangentCoordinates n q d) (tangentCoordinates n q e) =
      projectiveTwoForm n (p.val.val, theta) d.val e.val := by
  rw [quotient_form_coordinates, fixed_projective_form n q _ p.val.property.1]

private theorem quotient_form_alternating {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) (d : E n q) : quotientTwoForm q p0 z d d = 0 := by
  rw [quotient_form_coordinates]
  simp [reducedForm]

private theorem quotient_form_nondegenerate {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : Quotient (reductionSetoid q p0)) (d : E n q)
    (h : ∀ e, quotientTwoForm q p0 z d e = 0) : d = 0 :=
  reduced_form_nondegenerate n q d (fun e => by simpa only [quotient_form_coordinates] using h e)

private theorem quotient_form_smooth {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (d e : E n q) :
    ContMDiff (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) 𝓘(ℝ, ℝ) ∞
      (fun z : Quotient (reductionSetoid q p0) => quotientTwoForm q p0 z d e) :=
  contMDiff_const

/-- Complete actual moment and phase coordinates on every positive fixed-moment quotient. -/
theorem complete_legal_chain_coordinates {n : ℕ} (hn : 1 ≤ n) (q : ℕ)
    (p0 : PositiveProbability n) :
    ∃ h : Quotient (reductionSetoid q p0) ≃ₜ
        positiveDomain q p0 × (High n q → AddCircle (2 * Real.pi)),
      (∀ a : Representative q p0,
        h (Quotient.mk _ a) = (probabilityFibreEquiv q p0 a.1, highPhases a.2)) ∧
      signedIncidence n * incidence n = 1 ∧ incidence n * signedIncidence n = 1 ∧
      (∀ theta : Pattern n → AddCircle (2 * Real.pi),
        originalPhases (phases theta) = theta ∧ phases (originalPhases theta) = theta) ∧
      (positiveDomain q p0).Nonempty ∧ IsOpen (positiveDomain q p0) ∧
      Convex ℝ (positiveDomain q p0) ∧
      IsManifold (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) ∞ (Quotient (reductionSetoid q p0)) ∧
      (∀ (x y : positiveDomain q p0 × H n q),
        quotientCover q p0 x = quotientCover q p0 y ↔ x.1 = y.1 ∧
          ∃ k : High n q → ℤ, ∀ T, x.2 T - y.2 T = 2 * Real.pi * (k T : ℝ)) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n) (d : V n × V n),
        amplitudeOneForm n (p.val.val, theta) d =
          ∑ T, moments p.val.val T * phases d.2 T) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n) (d e : fixedTangent n q),
        projectiveTwoForm n (p.val.val, theta) d.val e.val =
          reducedForm n q (tangentCoordinates n q d) (tangentCoordinates n q e)) ∧
      (∀ d : fixedTangent n q,
        (∀ e : fixedTangent n q, sourceTwoForm n d.val e.val = 0) ↔
          d ∈ verticalTangent n q) ∧
      (∀ d : E n q, (∀ e, reducedForm n q d e = 0) → d = 0) ∧
      (∀ (x : positiveDomain q p0) (theta : V n),
        ∃ f : H n q × V n → E n q,
          (∀ (y : positiveDomain q p0) (eta : V n),
            chartAt (ModelProd (H n q) (H n q)) (originalPhaseProjection q p0 x theta)
              (originalPhaseProjection q p0 y eta) = f (y.val, eta)) ∧
          HasFDerivAt f
            ((LinearMap.fst ℝ (H n q) (V n)).prod
              ((highPhaseLinear n q).comp (LinearMap.snd ℝ (H n q) (V n)))).toContinuousLinearMap
            (x.val, theta)) ∧
      (∀ (z : E n q), HasFDerivAt (representativeLift q p0)
        (liftLinear n q).toContinuousLinearMap z) ∧
      (∀ (d e : E n q), sourceTwoForm n (liftLinear n q d) (liftLinear n q e) =
        reducedForm n q d e) ∧
      (∀ k : ℕ, k ≤ (n + 1) / 2 →
        Fintype.card (Layer n k) = (n - k + 1).choose k) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n),
        ∑ I, Complex.normSq (polarMap n (p.val.val, theta) I) = 1) ∧
      (∀ z : Quotient (reductionSetoid q p0),
        (∀ d : E n q, quotientTwoForm q p0 z d d = 0) ∧
        (∀ d : E n q, (∀ e, quotientTwoForm q p0 z d e = 0) → d = 0) ∧
        (∀ (p : ProbabilityFibre q p0) (theta : V n) (d e : fixedTangent n q),
          quotientTwoForm q p0 z (tangentCoordinates n q d) (tangentCoordinates n q e) =
            projectiveTwoForm n (p.val.val, theta) d.val e.val)) ∧
      (∀ d e : E n q,
        ContMDiff (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) 𝓘(ℝ, ℝ) ∞
          (fun z : Quotient (reductionSetoid q p0) => quotientTwoForm q p0 z d e)) ∧
      (∀ (z : Quotient (reductionSetoid q p0)) (u : positiveDomain q p0 × H n q),
        angleCover n q u.2 ∈ (chartAt (H n q) (reductionHomeomorph q p0 z).2).source →
        HasFDerivAt (liftedChart q p0 z) (ContinuousLinearMap.id ℝ (E n q))
          (u.1.val, u.2)) ∧
      (∀ (p : ProbabilityFibre q p0) (theta : V n),
        polarMap n (p.val.val, theta) =
          polarTorusMap n p.val.val (fun I => (theta I : Real.Angle)) ∧
        HasFDerivAt (polarMap n) (polarDerivative n (p.val.val, theta))
          (p.val.val, theta)) ∧
      (∀ (u : E n q) (v : Fin 2 → E n q),
        liftedSourceTwoForm q p0 u v = reducedForm n q (v 0) (v 1)) ∧
      (∀ u : E n q, extDeriv (liftedSourceTwoForm q p0) u = 0) ∧
      Fintype.card (Pattern n) = Nat.fib (n + 2) ∧
      (∀ b : Low n q → ℝ, (∀ T, moments p0.val T.val = b T) →
        {p : PositiveProbability n | ∀ T : Low n q, moments p.val T.val = b T} =
          {p : PositiveProbability n | ∀ T : Low n q,
            moments p.val T.val = moments p0.val T.val}) ∧
      (∀ z : Quotient (reductionSetoid q p0),
        Module.finrank ℝ (TangentSpace (𝓘(ℝ, H n q).prod 𝓘(ℝ, H n q)) z) =
          2 * ∑ k ∈ Finset.Ioc q ((n + 1) / 2), (n - k + 1).choose k) := by
  refine ⟨reductionHomeomorph q p0, (fun _ => rfl), (legal_chain_coordinate_laws n q).1,
    (legal_chain_coordinate_laws n q).2.1, ?_, ((legal_chain_coordinate_laws n q).2.2.2.2.1 p0).1,
    ((legal_chain_coordinate_laws n q).2.2.2.2.1 p0).2.1, ((legal_chain_coordinate_laws n q).2.2.2.2.1 p0).2.2, inferInstance,
    (legal_chain_coordinate_laws n q).2.2.2.2.2.1 p0, ?_, ?_, source_form_radical n q,
    reduced_form_nondegenerate n q, ?_, representative_lift_hasFDerivAt q p0,
    reduced_form_pullback n q, ?_, ?_, ?_, quotient_form_smooth q p0,
    lifted_chart_hasFDerivAt_in_source q p0, ?_,
    lifted_source_values q p0, lifted_source_closed q p0, ?_, ?_,
    quotient_manifold_dimension hn q p0⟩
  · intro theta
    exact ⟨(phaseEquiv n _).symm_apply_apply theta, (phaseEquiv n _).apply_symm_apply theta⟩
  · intro p theta d
    exact (legal_chain_coordinate_laws n q).2.2.2.2.2.2.1 _ d p.val.property.1
  · intro p theta d e
    exact fixed_projective_form n q _ p.val.property.1 d e
  · intro x theta
    exact ⟨projectedChart q p0 (originalPhaseProjection q p0 x theta),
      projected_chart_eq q p0 _, projected_chart_hasFDerivAt q p0 x theta⟩
  · intro k hk
    exact layer_card (by omega)
  · intro p theta
    exact normalized_polar p.val theta
  · intro z
    exact ⟨quotient_form_alternating q p0 z, quotient_form_nondegenerate q p0 z,
      quotient_form_source q p0 z⟩
  · intro p theta
    exact ⟨(legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.2.2.2.1 p.val.val theta,
      (legal_chain_coordinate_laws n q).2.2.2.2.2.2.2.2.2.1 _ p.val.property.1⟩

  · exact (Fintype.card_congr (patternWordEquiv n)).trans
      (D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib n)
  · intro b hb
    ext p
    constructor
    · intro hp T
      rw [hb T]
      exact hp T
    · intro hp T
      rw [← hb T]
      exact hp T

end D5.S3.Quantum.Fibers.LegalChainMomentReduction
end
