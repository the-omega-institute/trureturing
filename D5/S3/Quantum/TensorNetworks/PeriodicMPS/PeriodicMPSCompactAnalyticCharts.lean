/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSCompactAnalyticCharts
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSCompactAnalyticCharts
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSLocalObservationGraph]
   utility: none
   digest: Regular compact fibers in codimension one admit finite common analytic charts. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSAnalyticBranchSeparation
import D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactFiber
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSLocalObservationGraph
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! A common tangent projection and compactness give a finite description of
the ambiguity locus near any regular fiber into a target of codimension one. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactAnalyticCharts

open Set Function Filter Topology PeriodicMPSCompactFiber PeriodicMPSLocalObservationGraph
  PeriodicMPSAnalyticBranchSeparation
open scoped Topology

noncomputable section

section OpenSubsets

variable {S A B : Type*} [TopologicalSpace S] [TopologicalSpace A] [TopologicalSpace B]

/-- A subtype of a subtype, using the original ambient condition on both levels. -/
def interSubtypeHomeomorph (U V : Set S) :
    {x : U // x.val ∈ V} ≃ₜ (U ∩ V : Set S) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def chartIntoAmbient {U : Set A} {V : Set B} (hV : IsOpen V)
    (hne : Nonempty U) (e : U ≃ₜ V) : OpenPartialHomeomorph U B :=
  e.transOpenPartialHomeomorph
    ((⟨V, hV⟩ : TopologicalSpace.Opens B).openPartialHomeomorphSubtypeCoe (hne.map e))

/-- Extend a homeomorphism of open subtypes to an open partial
homeomorphism of the ambient spaces. -/
def openSubsetChart {U : Set A} {V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hne : Nonempty U) (e : U ≃ₜ V) : OpenPartialHomeomorph A B := by
  letI : Nonempty B := (hne.map e).map Subtype.val
  exact (chartIntoAmbient hV hne e).lift_openEmbedding hU.isOpenEmbedding_subtypeVal

@[simp] theorem openSubsetChart_source {U : Set A} {V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hne : Nonempty U) (e : U ≃ₜ V) :
    (openSubsetChart hU hV hne e).source = U := by
  simp [openSubsetChart, chartIntoAmbient]

@[simp] theorem openSubsetChart_target {U : Set A} {V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hne : Nonempty U) (e : U ≃ₜ V) :
    (openSubsetChart hU hV hne e).target = V := by
  simp [openSubsetChart, chartIntoAmbient]

theorem openSubsetChart_apply {U : Set A} {V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hne : Nonempty U) (e : U ≃ₜ V) (x : U) :
    openSubsetChart hU hV hne e x.val = (e x).val := by
  letI : Nonempty B := (hne.map e).map Subtype.val
  exact (chartIntoAmbient hV hne e).lift_openEmbedding_apply hU.isOpenEmbedding_subtypeVal

theorem openSubsetChart_symm_apply {U : Set A} {V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hne : Nonempty U) (e : U ≃ₜ V) (x : V) :
    (openSubsetChart hU hV hne e).symm x.val = (e.symm x).val := by
  have he : openSubsetChart hU hV hne e (e.symm x).val = x.val := by
    rw [openSubsetChart_apply, e.apply_symm_apply]
  have hx : (e.symm x).val ∈ (openSubsetChart hU hV hne e).source := by
    rw [openSubsetChart_source]
    exact (e.symm x).property
  rw [← he, (openSubsetChart hU hV hne e).left_inv hx]

end OpenSubsets

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y]

private theorem sub_zero_injective {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W] (f : V →ₗ[ℝ] W) (h : ∀ x, f x = 0 → x = 0) :
    Injective f := by
  intro x y he
  have hz : f (x - y) = 0 := by rw [map_sub, he, sub_self]
  exact sub_eq_zero.mp (h _ hz)

/-- A real line can be chosen transverse to every image in a finite family
of injective codimension-one derivatives. Projection along that line is
invertible on each image. -/
theorem exists_common_projection {ι : Type*} [Finite ι] [Nonempty ι]
    (dim : Module.finrank ℝ Y = Module.finrank ℝ E + 1)
    (D : ι → E →L[ℝ] Y) (hD : ∀ i, Injective (D i)) :
    ∃ L : Y ≃L[ℝ] E × ℝ, ∀ i, ∃ P : E ≃L[ℝ] E,
      (P : E →L[ℝ] E) =
        (ContinuousLinearMap.fst ℝ E ℝ).comp ((L : Y →L[ℝ] E × ℝ).comp (D i)) := by
  let R (i : ι) := LinearMap.range (D i).toLinearMap
  have hR (i : ι) : R i ≠ ⊤ := by
    intro he
    have hs : Surjective (D i).toLinearMap := LinearMap.range_eq_top.mp he
    have hle := LinearMap.finrank_le_finrank_of_surjective hs
    omega
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top R hR
  let j : ι := Classical.choice inferInstance
  let M : (E × ℝ) →L[ℝ] Y :=
    (D j).comp (ContinuousLinearMap.fst ℝ E ℝ) +
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight v
  have hM (z : E × ℝ) : M z = D j z.1 + z.2 • v := rfl
  have hMinj : Injective M := by
    apply sub_zero_injective M.toLinearMap
    rintro ⟨x, t⟩ hz
    change M (x, t) = 0 at hz
    rw [hM] at hz
    change D j x + t • v = 0 at hz
    have ht : t = 0 := by
      by_contra hn
      have hm : t • v ∈ R j := by
        have he : t • v = -(D j x) := eq_neg_of_add_eq_zero_right hz
        exact he.symm ▸ (R j).neg_mem (LinearMap.mem_range_self (D j).toLinearMap x)
      exact hv j (((R j).smul_mem_iff hn).mp hm)
    have hx : x = 0 := hD j (by simpa [ht] using hz)
    simp [hx, ht]
  have hdim : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ Y := by
    simp [Module.finrank_prod, dim]
  let J : (E × ℝ) ≃L[ℝ] Y :=
    (LinearMap.linearEquivOfInjective M.toLinearMap hMinj hdim).toContinuousLinearEquiv
  let L := J.symm
  refine ⟨L, fun i => ?_⟩
  let F : E →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E ℝ).comp ((L : Y →L[ℝ] E × ℝ).comp (D i))
  have hF : Injective F := by
    apply sub_zero_injective F.toLinearMap
    intro z hz
    change (L (D i z)).1 = 0 at hz
    let t := (L (D i z)).2
    have he : L (D i z) = (0, t) := Prod.ext hz rfl
    have hm : D i z = t • v := by
      have he' := congrArg J he
      change J (J.symm (D i z)) = M (0, t) at he'
      simpa only [J.apply_symm_apply, hM, map_zero, zero_add] using he'
    have ht : t = 0 := by
      by_contra hn
      have hm' : t • v ∈ R i := hm ▸ LinearMap.mem_range_self (D i).toLinearMap z
      exact hv i (((R i).smul_mem_iff hn).mp hm')
    exact hD i (by simpa [ht] using hm)
  let P : E ≃L[ℝ] E :=
    (LinearMap.linearEquivOfInjective F.toLinearMap hF rfl).toContinuousLinearEquiv
  exact ⟨P, ContinuousLinearMap.ext fun _ => rfl⟩

variable {X : Type*} [TopologicalSpace X]

/-- An open source chart and an analytic local expression for an observation. -/
structure RegularChart (f : X → Y) (x : X) where
  chart : OpenPartialHomeomorph E X
  mem_target : x ∈ chart.target
  expression : E → Y
  expression_eq : EqOn expression (f ∘ chart) chart.source
  analytic : AnalyticAt ℝ expression (chart.symm x)
  derivative_injective : Injective (fderiv ℝ expression (chart.symm x))

private theorem graph_in_neighborhood {f : X → Y} {x : X} (c : RegularChart (E := E) f x)
    (L : Y ≃L[ℝ] E × ℝ) (P : E ≃L[ℝ] E)
    (hP : (P : E →L[ℝ] E) = (ContinuousLinearMap.fst ℝ E ℝ).comp
      ((L : Y →L[ℝ] E × ℝ).comp (fderiv ℝ c.expression (c.chart.symm x))))
    {V : Set X} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ (d : OpenPartialHomeomorph E X) (g : E → ℝ),
      (L (f x)).1 ∈ d.source ∧ d (L (f x)).1 = x ∧ d.target ⊆ V ∧
      AnalyticOnNhd ℝ g d.source ∧ ∀ t ∈ d.source, L (f (d t)) = (t, g t) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let u := c.chart.symm x
  let T (z : E) := (L (c.expression z)).1
  let N (z : E) := (L (c.expression z)).2
  have hu : u ∈ c.chart.source := c.chart.map_target c.mem_target
  have hc : c.chart u = x := c.chart.right_inv c.mem_target
  have hcenter : T u = (L (f x)).1 := by
    change (L (c.expression u)).1 = (L (f x)).1
    rw [c.expression_eq hu]
    simp only [Function.comp_apply, hc]
  have ha := ((L : Y →L[ℝ] E × ℝ).analyticAt (c.expression u)).comp c.analytic
  have hT : AnalyticAt ℝ T u :=
    ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt _).comp ha
  have hN : AnalyticAt ℝ N u :=
    ((ContinuousLinearMap.snd ℝ E ℝ).analyticAt _).comp ha
  have hF := ((L : Y →L[ℝ] E × ℝ).hasFDerivAt).comp u c.analytic.differentiableAt.hasFDerivAt
  have hTD : HasFDerivAt T (P : E →L[ℝ] E) u := by
    rw [hP]
    exact (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp u hF
  obtain ⟨e, U, g, he, heu, hU, hcenterU, hsub, _, hg, hgraph⟩ :=
    exists_analytic_graph T N u hT hN P hTD
  let a := OpenPartialHomeomorph.trans e.symm c.chart
  let b := a.restrOpen U hU
  let d := (b.symm.restrOpen V hV).symm
  have hTu : e.symm (T u) = u := by
    rw [← he]
    exact e.left_inv heu
  have hTa : T u ∈ a.source := by
    refine ⟨hsub hcenterU, ?_⟩
    change e.symm (T u) ∈ c.chart.source
    rwa [hTu]
  have hTb : T u ∈ b.source := ⟨hTa, hcenterU⟩
  have hb : b (T u) = x := by
    change c.chart (e.symm (T u)) = x
    rwa [hTu]
  have hTd : T u ∈ d.source := by
    have hbx : x ∈ b.target := hb ▸ b.map_source hTb
    have hx' : x ∈ (b.symm.restrOpen V hV).source := ⟨hbx, hx⟩
    have he' : (b.symm.restrOpen V hV) x = T u := by
      change b.symm x = T u
      rw [← hb, b.left_inv hTb]
    exact he' ▸ (b.symm.restrOpen V hV).map_source hx'
  have ds (t : E) (ht : t ∈ d.source) : t ∈ b.source := by
    have hx' : d t ∈ (b.symm.restrOpen V hV).source := d.map_source ht
    have hbd : d t ∈ b.target := hx'.1
    have h : b.symm (d t) ∈ b.source := b.map_target hbd
    change b.symm (d t) ∈ b.source at h
    have he' : b.symm (d t) = t := d.left_inv ht
    rwa [he'] at h
  refine ⟨d, g, hcenter ▸ hTd, ?_, fun _ ht => ht.2, ?_, ?_⟩
  · rw [← hcenter]
    exact hb
  · exact hg.mono fun t ht => (ds t ht).2
  · intro t ht
    have htb := ds t ht
    have htc : e.symm t ∈ c.chart.source := htb.1.2
    change L (f (c.chart (e.symm t))) = (t, g t)
    exact (congrArg L (c.expression_eq htc)).symm.trans (hgraph t htb.2)

private theorem injOn_of_graph {f : X → Y} (L : Y ≃L[ℝ] E × ℝ)
    (d : OpenPartialHomeomorph E X) (g : E → ℝ)
    (hgraph : ∀ t ∈ d.source, L (f (d t)) = (t, g t)) :
    InjOn f d.target := by
  intro x hx z hz h
  have he (a : X) (ha : a ∈ d.target) := hgraph (d.symm a) (d.map_target ha)
  have hcoord : d.symm x = d.symm z := by
    have hx' := congrArg Prod.fst (he x hx)
    have hz' := congrArg Prod.fst (he z hz)
    rw [d.right_inv hx, h] at hx'
    rw [d.right_inv hz] at hz'
    exact hx'.symm.trans hz'
  rw [← d.right_inv hx, ← d.right_inv hz, hcoord]

/-- Above a common ball, each point of the central fiber indexes an analytic
graph. Every point giving the same observation as any of these graph points
appears on exactly one of the charts. -/
structure FiberGraphs (f : X → Y) (y : Y) (G : Set X) where
  finite : (f ⁻¹' {y}).Finite
  coordinates : Y ≃L[ℝ] E × ℝ
  radius : ℝ
  positive_radius : 0 < radius
  charts : (f ⁻¹' {y}) → OpenPartialHomeomorph E X
  graphs : (f ⁻¹' {y}) → E → ℝ
  domain_subset : ∀ i, Metric.ball (coordinates y).1 radius ⊆ (charts i).source
  centers : ∀ i, charts i (coordinates y).1 = i.val
  target_subset : ∀ i, (charts i).target ⊆ G
  disjoint_targets : Pairwise fun i j => Disjoint (charts i).target (charts j).target
  analytic : ∀ i, AnalyticOnNhd ℝ (graphs i) (Metric.ball (coordinates y).1 radius)
  form : ∀ i t, t ∈ Metric.ball (coordinates y).1 radius →
    coordinates (f (charts i t)) = (t, graphs i t)
  covers : ∀ i t, t ∈ Metric.ball (coordinates y).1 radius →
    ∀ z, f z = f (charts i t) → ∃ j, z = charts j t

section Compact

variable [CompactSpace X] [T2Space X]

/-- The analytic graph family for a regular compact fiber can be chosen
within any open set containing the fiber. -/
theorem exists_fiber_graphs {f : X → Y} (hf : Continuous f) {y : Y} (hy : y ∈ range f)
    {G : Set X} (hG : IsOpen G) (hGf : f ⁻¹' {y} ⊆ G)
    (dim : Module.finrank ℝ Y = Module.finrank ℝ E + 1)
    (hreg : ∀ x ∈ f ⁻¹' {y}, Nonempty (RegularChart (E := E) f x)) :
    Nonempty (FiberGraphs (E := E) f y G) := by
  classical
  have hlocal (x : X) (hx : x ∈ f ⁻¹' {y}) :
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
    obtain ⟨c⟩ := hreg x hx
    obtain ⟨L, hL⟩ := exists_common_projection dim
      (fun _ : Unit => fderiv ℝ c.expression (c.chart.symm x))
      (fun _ => c.derivative_injective)
    obtain ⟨P, hP⟩ := hL ()
    obtain ⟨d, g, hd, he, _, _, hgraph⟩ :=
      graph_in_neighborhood c L P hP isOpen_univ (mem_univ x)
    exact ⟨d.target, d.open_target, he ▸ d.map_source hd, injOn_of_graph L d g hgraph⟩
  let I := f ⁻¹' {y}
  have hfinite : I.Finite := finite_fiber_of_local_injective hf y hlocal
  letI : Finite I := hfinite
  letI : Nonempty I := by
    obtain ⟨x, hx⟩ := hy
    exact ⟨⟨x, hx⟩⟩
  let c (i : I) : RegularChart (E := E) f i.val := Classical.choice (hreg i.val i.property)
  let D (i : I) := fderiv ℝ (c i).expression ((c i).chart.symm i.val)
  obtain ⟨L, hL⟩ := exists_common_projection dim D (fun i => (c i).derivative_injective)
  obtain ⟨U, hU, hdisj⟩ := hfinite.t2_separation
  have localGraphs (i : I) :
      ∃ (d : OpenPartialHomeomorph E X) (g : E → ℝ),
        (L y).1 ∈ d.source ∧ d (L y).1 = i.val ∧ d.target ⊆ U i.val ∩ G ∧
        AnalyticOnNhd ℝ g d.source ∧ ∀ t ∈ d.source, L (f (d t)) = (t, g t) := by
    obtain ⟨P, hP⟩ := hL i
    have hi : f i.val = y := i.property
    simpa only [hi] using
      graph_in_neighborhood (c i) L P hP ((hU i.val).2.inter hG)
        (show i.val ∈ U i.val ∩ G from ⟨(hU i.val).1, hGf i.property⟩)
  choose d g hd hcenter hsub ha hgraph using localGraphs
  have hcover : f ⁻¹' {y} ⊆ ⋃ i : I, (d i).target := by
    intro z hz
    let i : I := ⟨z, hz⟩
    have hm := (d i).map_source (hd i)
    rw [hcenter i] at hm
    exact mem_iUnion.mpr ⟨i, hm⟩
  obtain ⟨W, hW, hyW, hfW⟩ :=
    nearby_fibers_subset hf (isOpen_iUnion fun i : I => (d i).open_target) hcover
  let Q (i : I) (t : E) := L.symm (t, g i t)
  have hQ (i : I) : Q i (L y).1 = y := by
    have hi : f i.val = y := i.property
    have he := hgraph i _ (hd i)
    rw [hcenter i, hi] at he
    change L.symm ((L y).1, g i (L y).1) = y
    rw [← he, L.symm_apply_apply]
  have hlocalQ (i : I) : ContinuousAt (Q i) (L y).1 :=
    L.symm.continuous.continuousAt.comp
      (continuousAt_id.prodMk ((ha i _ (hd i)).continuousAt))
  have hsmall (i : I) :
      (d i).source ∩ (Q i) ⁻¹' W ∈ 𝓝 (L y).1 := by
    refine inter_mem ((d i).open_source.mem_nhds (hd i)) ((hlocalQ i).preimage_mem_nhds ?_)
    rw [hQ i]
    exact hW.mem_nhds hyW
  have hnhds : (⋂ i : I, (d i).source ∩ (Q i) ⁻¹' W) ∈ 𝓝 (L y).1 :=
    Filter.iInter_mem.mpr hsmall
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hrsub' (i : I) (t : E) (ht : t ∈ Metric.ball (L y).1 r) :
      t ∈ (d i).source ∧ Q i t ∈ W := mem_iInter.mp (hrsub ht) i
  refine ⟨⟨hfinite, L, r, hr, d, g, fun i t ht => (hrsub' i t ht).1, hcenter,
    fun i z hz => (hsub i hz).2, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    exact (hdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)).mono
      (fun _ hz => (hsub i hz).1) (fun _ hz => (hsub j hz).1)
  · exact fun i => (ha i).mono (fun t ht => (hrsub' i t ht).1)
  · exact fun i t ht => hgraph i t (hrsub' i t ht).1
  · intro i t ht z hz
    have hzW : f z ∈ W := by
      have he : f (d i t) = Q i t := L.injective <| by
        change L (f (d i t)) = L (L.symm (t, g i t))
        rw [L.apply_symm_apply]
        exact hgraph i t (hrsub' i t ht).1
      rw [hz, he]
      exact (hrsub' i t ht).2
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hfW hzW)
    have he := hgraph j ((d j).symm z) ((d j).map_target hj)
    rw [(d j).right_inv hj, hz, hgraph i t (hrsub' i t ht).1] at he
    have ht' : t = (d j).symm z := congrArg Prod.fst he
    refine ⟨j, ?_⟩
    rw [ht', (d j).right_inv hj]

end Compact

/-- Equal graphs give one-sided local image inclusion between their source
neighborhoods. This comparison is independent of the tangent projection. -/
theorem FiberGraphs.eventually_mem_image {f : X → Y} {y : Y} {G : Set X}
    (B : FiberGraphs (E := E) f y G) (i j : f ⁻¹' {y})
    (he : EqOn (B.graphs i) (B.graphs j) (Metric.ball (B.coordinates y).1 B.radius))
    {V : Set X} (hV : V ∈ 𝓝 j.val) :
    ∀ᶠ z in 𝓝 i.val, f z ∈ f '' V := by
  let t₀ := (B.coordinates y).1
  let U := Metric.ball t₀ B.radius
  have h₀ : t₀ ∈ U := Metric.mem_ball_self B.positive_radius
  have hchart (k : f ⁻¹' {y}) : t₀ ∈ (B.charts k).source := B.domain_subset k h₀
  have hi : i.val ∈ (B.charts i).target :=
    B.centers i ▸ (B.charts i).map_source (hchart i)
  have hj : ContinuousAt (B.charts j) t₀ := (B.charts j).continuousAt (hchart j)
  have hW : ∀ᶠ t in 𝓝 t₀, t ∈ U ∧ B.charts j t ∈ V := by
    have hu : ∀ᶠ t in 𝓝 t₀, t ∈ U := Metric.isOpen_ball.mem_nhds h₀
    have hv : ∀ᶠ t in 𝓝 t₀, B.charts j t ∈ V := hj.preimage_mem_nhds (by
      simpa only [t₀, B.centers j] using hV)
    exact hu.and hv
  have hk : (B.charts i).symm i.val = t₀ := by
    rw [← B.centers i]
    exact (B.charts i).left_inv (hchart i)
  have hT : Tendsto (B.charts i).symm (𝓝 i.val) (𝓝 t₀) :=
    hk ▸ ((B.charts i).symm.continuousAt hi).tendsto
  have hW' : ∀ᶠ z in 𝓝 i.val, (B.charts i).symm z ∈ U ∧
      B.charts j ((B.charts i).symm z) ∈ V := hT hW
  filter_upwards [(B.charts i).open_target.mem_nhds hi, hW'] with z hz ht
  let t := (B.charts i).symm z
  have htz : B.charts i t = z := (B.charts i).right_inv hz
  refine ⟨B.charts j t, ht.2, B.coordinates.injective ?_⟩
  rw [← htz, B.form j t ht.1, B.form i t ht.1, he ht.1]

/-- A source is ambiguous if a distinct point gives the same observation. -/
def ambiguous (f : X → Y) : Set X := {x | ∃ z, z ≠ x ∧ f z = f x}

/-- A member of the finite graph family defines the local ambiguity chart on
the open regular part of the source. -/
def FiberGraphs.ambiguityChart {f : X → Y} {y : Y} {G : Set X}
    (B : FiberGraphs (E := E) f y G) (hG : IsOpen G) (i : f ⁻¹' {y}) :
    AnalyticAmbiguityChart E (Subtype.val ⁻¹' ambiguous f)
      (⟨i.val, B.target_subset i (B.centers i ▸ (B.charts i).map_source
        (B.domain_subset i (Metric.mem_ball_self B.positive_radius)))⟩ : G) := by
  classical
  let U := Metric.ball (B.coordinates y).1 B.radius
  letI : Finite (f ⁻¹' {y}) := B.finite
  let I := {j : f ⁻¹' {y} // j ≠ i}
  letI : Fintype I := Fintype.ofFinite I
  let e := (Fintype.equivFin I).symm
  let toChart (t : U) : (B.charts i).source := ⟨t.val, B.domain_subset i t.property⟩
  let k (t : U) : G := ⟨B.charts i t.val,
    B.target_subset i ((B.charts i).map_source (toChart t).property)⟩
  have htoChart : IsOpenEmbedding toChart :=
    IsOpenEmbedding.of_comp toChart (B.charts i).open_source.isOpenEmbedding_subtypeVal
      Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  have hk : IsOpenEmbedding k := IsOpenEmbedding.of_comp k hG.isOpenEmbedding_subtypeVal
    ((B.charts i).isOpenEmbedding_restrict.comp htoChart)
  refine
    { domain := U
      isOpen_domain := Metric.isOpen_ball
      preconnected_domain := Metric.isPreconnected_ball
      toSource := k
      openEmbedding := hk
      center := ⟨(B.coordinates y).1, Metric.mem_ball_self B.positive_radius⟩
      center_eq := Subtype.ext (B.centers i)
      count := Fintype.card I
      graph := B.graphs i
      competitor := fun j => B.graphs (e j).val
      analytic_graph := B.analytic i
      analytic_competitor := fun j => B.analytic (e j).val
      mem_iff := ?_ }
  intro t
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨j, hj⟩ := B.covers i t.val t.property z he
    have hji : j ≠ i := by
      rintro rfl
      exact hz hj
    let j' : I := ⟨j, hji⟩
    refine ⟨e.symm j', ?_⟩
    rw [e.apply_symm_apply]
    have h := congrArg (fun w : Y => (B.coordinates w).2) he
    change (B.coordinates (f z)).2 = (B.coordinates (f (B.charts i t.val))).2 at h
    rw [hj, B.form j t.val t.property, B.form i t.val t.property] at h
    exact h.symm
  · rintro ⟨j, hj⟩
    let a := (e j).val
    have hai : a ≠ i := (e j).property
    refine ⟨B.charts a t.val, ?_, ?_⟩
    · intro he
      have ha := (B.charts a).map_source (B.domain_subset a t.property)
      have hi := (B.charts i).map_source (B.domain_subset i t.property)
      exact Set.disjoint_left.mp (B.disjoint_targets hai) ha (he.symm ▸ hi)
    · apply B.coordinates.injective
      change B.coordinates (f (B.charts a t.val)) = B.coordinates (f (B.charts i t.val))
      rw [B.form a t.val t.property, B.form i t.val t.property]
      exact Prod.ext rfl hj.symm

/-- Failure of local image inclusion separates the selected observation
graph from every competing graph in the ambiguity chart. -/
theorem FiberGraphs.ambiguityChart_distinct {f : X → Y} {y : Y} {G : Set X}
    (B : FiberGraphs (E := E) f y G) (hG : IsOpen G) (i : f ⁻¹' {y})
    (h : ∀ j : f ⁻¹' {y}, j ≠ i → ∃ V ∈ 𝓝 j.val,
      ¬ (∀ᶠ z in 𝓝 i.val, f z ∈ f '' V)) :
    ∀ k, ¬ EqOn (B.ambiguityChart hG i).graph
      ((B.ambiguityChart hG i).competitor k) (B.ambiguityChart hG i).domain := by
  classical
  letI : Finite (f ⁻¹' {y}) := B.finite
  let I := {j : f ⁻¹' {y} // j ≠ i}
  letI : Fintype I := Fintype.ofFinite I
  let e := (Fintype.equivFin I).symm
  intro k he
  obtain ⟨V, hV, hn⟩ := h (e k).val (e k).property
  exact hn (B.eventually_mem_image i (e k).val he hV)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactAnalyticCharts
