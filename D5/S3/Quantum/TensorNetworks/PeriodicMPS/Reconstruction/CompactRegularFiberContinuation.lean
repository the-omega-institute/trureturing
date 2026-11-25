/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/CompactRegularFiberContinuation
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/CompactRegularFiberContinuation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Generic singleton fibers on a compact source. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Geometry.HausdorffCodimTwoComplement
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSCompactAnalyticCharts
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSImmersionPullback

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactAnalyticCharts

open Set Filter Function
open scoped ENNReal NNReal Topology
open PeriodicMPSRegularComplement PeriodicMPSAnalyticBranchSeparation

open private inverse_neighborhood from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSImmersionPullback

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The inverse of a locally analytic immersion controls the dimension of every
subset of its regular preimage by the dimension of that subset's image. -/
theorem dimH_le_image_of_analytic_immersion {g : E → Y} {A : Set E}
    (hreg : ∀ z ∈ A, AnalyticAt ℝ g z ∧ Injective (fderiv ℝ g z)) :
    dimH A ≤ dimH (g '' A) := by
  by_contra! h
  obtain ⟨z, hz, hlocal⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH h
  obtain ⟨i, U, V, hU, hI, hmaps, hinv⟩ :=
    inverse_neighborhood (hreg z hz).1 (hreg z hz).2
  let T := A ∩ U
  have hT : T ∈ 𝓝[A] z :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU)
  have hsub : T ⊆ i '' (g '' T) := by
    intro w hw
    exact ⟨g w, ⟨w, hw, rfl⟩, hinv w hw.2⟩
  have hV : g '' T ⊆ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact hmaps hw.2
  exact (not_le_of_gt (hlocal T hT)) <|
    (dimH_mono hsub).trans <| ((hI.mono hV).dimH_image_le).trans <|
      dimH_mono (image_mono inter_subset_left)

variable {X : Type*} [MetricSpace X]

/-- In ordinary coordinates the excluded preimage is the union of the original
bad set and its pullback on the immersive part of the chart. Both obey the same
Hausdorff-dimension bound. -/
theorem dimH_chart_excluded {f : X → Y} {B : Set X} {s : ℝ≥0∞}
    (hB : dimH B ≤ s) (hvalues : dimH (f '' B) ≤ s)
    (c : OpenPartialHomeomorph E X) {K : ℝ≥0} (hc : LipschitzOnWith K c.symm c.target)
    {g : E → Y} (he : EqOn g (f ∘ c) c.source)
    (hreg : ∀ z ∈ c.source, c z ∉ B →
      AnalyticAt ℝ g z ∧ Injective (fderiv ℝ g z)) :
    dimH (c.source ∩ (f ∘ c) ⁻¹' (f '' B)) ≤ s := by
  let A := c.source ∩ (f ∘ c) ⁻¹' (f '' B)
  let C := c.symm '' (B ∩ c.target)
  have hC : dimH C ≤ s :=
    ((hc.mono inter_subset_right).dimH_image_le.trans (dimH_mono inter_subset_left)).trans hB
  have hDreg : ∀ z ∈ A \ C, AnalyticAt ℝ g z ∧ Injective (fderiv ℝ g z) := by
    intro z hz
    refine hreg z hz.1.1 fun hzB => hz.2 ?_
    exact ⟨c z, ⟨hzB, c.map_source hz.1.1⟩, c.left_inv hz.1.1⟩
  have hDvalues : g '' (A \ C) ⊆ f '' B := by
    rintro _ ⟨z, hz, rfl⟩
    rw [he hz.1.1]
    exact hz.1.2
  have hD : dimH (A \ C) ≤ s :=
    (dimH_le_image_of_analytic_immersion hDreg).trans ((dimH_mono hDvalues).trans hvalues)
  have hsub : A ⊆ C ∪ (A \ C) := by
    intro z hz
    by_cases hzC : z ∈ C
    · exact Or.inl hzC
    · exact Or.inr ⟨hz, hzC⟩
  apply (dimH_mono hsub).trans
  rw [dimH_union]
  exact max_le hC hD

/-- Removing all observation values from a compact bad set of codimension at least
two leaves an open, dense, path-connected source locus. The ordinary charts cover
a connected dense open subset containing every point outside the bad set. -/
theorem open_dense_pathConnected_of_bad_values {f : X → Y} (hf : Continuous f)
    {U B : Set X} (hUo : IsOpen U) (hUc : IsConnected U) (hUd : Dense U) (hcover : Bᶜ ⊆ U)
    (hBc : IsCompact B) (hd : 2 ≤ Module.finrank ℝ E)
    (hB : dimH B ≤ ((Module.finrank ℝ E - 2 : ℕ) : ℝ≥0∞))
    (hvalues : dimH (f '' B) ≤ ((Module.finrank ℝ E - 2 : ℕ) : ℝ≥0∞))
    (hcharts : ∀ x ∈ U, ∃ (c : OpenPartialHomeomorph E X) (K : ℝ≥0) (g : E → Y),
      x ∈ c.target ∧ LipschitzOnWith K c.symm c.target ∧
        EqOn g (f ∘ c) c.source ∧ ∀ z ∈ c.source, c z ∉ B →
          AnalyticAt ℝ g z ∧ Injective (fderiv ℝ g z)) :
    IsOpen (f ⁻¹' (f '' B)ᶜ) ∧ Dense (f ⁻¹' (f '' B)ᶜ) ∧
      IsPathConnected (f ⁻¹' (f '' B)ᶜ) := by
  let G := f ⁻¹' (f '' B)ᶜ
  have hGo : IsOpen G := (hBc.image hf).isClosed.isOpen_compl.preimage hf
  have hGB : G ⊆ Bᶜ := fun x hx hxB => hx ⟨x, hxB, rfl⟩
  have hlocal (x : X) (hx : x ∈ U) :
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ x ∈ closure G ∧ IsPathConnected (V ∩ G) := by
    obtain ⟨c, K, g, hxc, hc, he, hreg⟩ := hcharts x hx
    let a := c.symm x
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp c.open_source a (c.map_target hxc)
    let W := Metric.ball a r
    let A := c.source ∩ (f ∘ c) ⁻¹' (f '' B)
    have hdim := dimH_chart_excluded hB hvalues c hc he hreg
    have hlt : dimH A + 1 < Module.finrank ℝ E := by
      have hn : Module.finrank ℝ E - 2 + 1 < Module.finrank ℝ E := by omega
      apply (add_le_add_left hdim 1).trans_lt
      exact_mod_cast hn
    obtain ⟨hp, hreld⟩ := isPathConnected_diff_of_dimH_add_one_lt Metric.isOpen_ball
      ((convex_ball a r).isConnected ⟨a, Metric.mem_ball_self hr⟩) hlt
    let V := c '' W
    have heq : c '' (W \ A) = V ∩ G := by
      ext y
      constructor
      · rintro ⟨z, ⟨hz, hn⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, fun h => hn ⟨hrsub hz, h⟩⟩
      · rintro ⟨⟨z, hz, rfl⟩, hn⟩
        exact ⟨z, ⟨hz, fun h => hn h.2⟩, rfl⟩
    have ha : a ∈ W := Metric.mem_ball_self hr
    have hxG : x ∈ closure G := by
      have hct : ContinuousWithinAt c (W \ A) a :=
        (c.continuousOn a (hrsub ha)).mono (sdiff_subset.trans hrsub)
      have hcl := hct.mem_closure_image (hreld ha)
      rw [heq, show c a = x from c.right_inv hxc] at hcl
      exact closure_mono inter_subset_right hcl
    exact ⟨V, c.isOpen_image_of_subset_source Metric.isOpen_ball hrsub,
      ⟨a, ha, c.right_inv hxc⟩, hxG, heq ▸ hp.image' (c.continuousOn.mono
        (sdiff_subset.trans hrsub))⟩
  have hUG : U ⊆ closure G := fun x hx => (hlocal x hx).choose_spec.2.2.1
  refine ⟨hGo, fun x => closure_minimal hUG isClosed_closure (hUd x),
    isPathConnected_of_locally_pathConnected_inter hUo hUc (hGB.trans hcover) hUG ?_⟩
  intro x hx
  obtain ⟨V, hVo, hxV, _, hp⟩ := hlocal x hx
  exact ⟨V, hVo, hxV, hp⟩

variable [CompactSpace X]

/-- A compact singleton on an open dense path-connected regular locus propagates
to an open dense singleton-fiber locus in the full compact source. -/
theorem open_dense_singleton_of_good {f : X → Y} (hf : Continuous f) {G : Set X}
    (hGo : IsOpen G) (hGd : Dense G) (hGp : IsPathConnected G)
    (hsaturated : ∀ ⦃x y : X⦄, x ∈ G → f y = f x → y ∈ G)
    (hdim : Module.finrank ℝ Y = Module.finrank ℝ E + 1)
    (hreg : ∀ x ∈ G, Nonempty (RegularChart (E := E) f x))
    (hsingle : ∃ x ∈ G, ∀ y : X, f y = f x → y = x) :
    IsOpen {x ∈ G | ∀ y : X, f y = f x → y = x} ∧
      Dense {x ∈ G | ∀ y : X, f y = f x → y = x} := by
  classical
  let : PathConnectedSpace G := isPathConnected_iff_pathConnectedSpace.mp hGp
  let A : Set G := Subtype.val ⁻¹' ambiguous f
  let F (x : G) : FiberGraphs (E := E) f (f x.val) G := Classical.choice <|
    exists_fiber_graphs hf (mem_range_self x.val) hGo (fun _ hy => hsaturated x.property hy)
      hdim (fun y hy => hreg y (hsaturated x.property hy))
  let charts (x : G) : AnalyticAmbiguityChart E A x :=
    (F x).ambiguityChart hGo ⟨x.val, rfl⟩
  have hspecial : ∃ x : G, ∀ k, ¬ EqOn (charts x).graph ((charts x).competitor k)
      (charts x).domain := by
    obtain ⟨x, hx, hsingle⟩ := hsingle
    let p : G := ⟨x, hx⟩
    refine ⟨p, (F p).ambiguityChart_distinct hGo ⟨x, rfl⟩ ?_⟩
    intro y hy
    exact (hy (Subtype.ext (hsingle y.val y.property))).elim
  obtain ⟨hAo, hAd⟩ := open_dense_compl_of_analytic_fiber_charts charts hspecial
  have he : Subtype.val '' Aᶜ = {x ∈ G | ∀ y : X, f y = f x → y = x} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.property, fun y hy => ?_⟩
      by_contra hne
      exact hz ⟨y, hne, hy⟩
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rintro ⟨y, hne, hy⟩
      exact hne (h y hy)
  rw [← he]
  refine ⟨hGo.isOpenMap_subtype_val _ hAo, fun x =>
    closure_minimal ?_ isClosed_closure (hGd x)⟩
  intro x hx
  exact image_closure_subset_closure_image continuous_subtype_val ⟨⟨x, hx⟩, hAd _, rfl⟩

/-- The compact continuation bridge. An ordinary connected dense atlas and a
compact bad set with literal codimension-two bound suffice for generic singleton
fibers, provided a compact singleton can be found in the resulting dense locus. -/
theorem compact_generic_recovery_of_dimH_bad {f : X → Y} {L : ℝ≥0}
    (hf : LipschitzWith L f)
    {U B : Set X} (hUo : IsOpen U) (hUc : IsConnected U) (hUd : Dense U) (hcover : Bᶜ ⊆ U)
    (hBc : IsCompact B) (hd : 2 ≤ Module.finrank ℝ E)
    (hB : dimH B ≤ ((Module.finrank ℝ E - 2 : ℕ) : ℝ≥0∞))
    (hdim : Module.finrank ℝ Y = Module.finrank ℝ E + 1)
    (hcharts : ∀ x ∈ U, ∃ (c : OpenPartialHomeomorph E X) (K : ℝ≥0) (g : E → Y),
      x ∈ c.target ∧ LipschitzOnWith K c.symm c.target ∧
        EqOn g (f ∘ c) c.source ∧ ∀ z ∈ c.source, c z ∉ B →
          AnalyticAt ℝ g z ∧ Injective (fderiv ℝ g z))
    (hsingle : Dense (f ⁻¹' (f '' B)ᶜ) →
      ∃ x ∈ f ⁻¹' (f '' B)ᶜ, ∀ y : X, f y = f x → y = x) :
    IsOpen {x ∈ f ⁻¹' (f '' B)ᶜ | ∀ y : X, f y = f x → y = x} ∧
      Dense {x ∈ f ⁻¹' (f '' B)ᶜ | ∀ y : X, f y = f x → y = x} := by
  let G := f ⁻¹' (f '' B)ᶜ
  obtain ⟨hGo, hGd, hGp⟩ := open_dense_pathConnected_of_bad_values hf.continuous
    hUo hUc hUd hcover hBc hd hB ((hf.dimH_image_le B).trans hB) hcharts
  have hsaturated : ∀ ⦃x y : X⦄, x ∈ G → f y = f x → y ∈ G :=
    by
      intro x y hx hxy
      change f x ∉ f '' B at hx
      change f y ∉ f '' B
      rwa [hxy]
  apply open_dense_singleton_of_good hf.continuous hGo hGd hGp hsaturated hdim ?_
    (hsingle hGd)
  intro x hx
  have hxB : x ∉ B := fun hn => hx ⟨x, hn, rfl⟩
  obtain ⟨c, _, g, hxc, _, he, hreg⟩ := hcharts x (hcover hxB)
  have ba : c (c.symm x) ∉ B := by rwa [c.right_inv hxc]
  obtain ⟨ha, hi⟩ := hreg _ (c.map_target hxc) ba
  exact ⟨⟨c, hxc, g, he, ha, hi⟩⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactAnalyticCharts
