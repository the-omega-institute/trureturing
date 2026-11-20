/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticBranchSeparation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticBranchSeparation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Analytic.Uniqueness]
   utility: none
   digest: Distinct analytic graphs separate on a relatively open dense set. -/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Connected.Clopen

/-! A common chart of a regular observation fiber separates its distinct analytic sheets. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSAnalyticBranchSeparation

open Set Filter Topology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem open_dense_pair (U : Set E) (hU : IsOpen U) (hconn : IsPreconnected U)
    (f g : E → ℝ) (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hne : ¬ EqOn f g U) :
    IsOpen {x : U | f x ≠ g x} ∧ Dense {x : U | f x ≠ g x} := by
  constructor
  · exact isOpen_ne_fun hf.continuousOn.domRestrict hg.continuousOn.domRestrict
  · refine dense_iff_inter_open.mpr ?_
    intro V hv hV
    by_contra hempty
    obtain ⟨x, hx⟩ := hV
    let W := Subtype.val '' V
    have hw : IsOpen W := hU.isOpenMap_subtype_val _ hv
    have hxW : x.val ∈ W := ⟨x, hx, rfl⟩
    have he : f =ᶠ[𝓝 x.val] g := by
      filter_upwards [hw.mem_nhds hxW] with y hy
      obtain ⟨y, hy, rfl⟩ := hy
      by_contra hn
      exact hempty ⟨y, hy, hn⟩
    exact hne (hf.eqOn_of_preconnected_of_eventuallyEq hg hconn x.property he)

private theorem open_dense_finset {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (G : ι → Set X) (h : ∀ i ∈ s, IsOpen (G i) ∧ Dense (G i)) :
    IsOpen (⋂ i ∈ s, G i) ∧ Dense (⋂ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hmem : i ∈ insert i s := Finset.mem_insert_self i s
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.set_biInter_insert]
    exact ⟨(h i hmem).1.inter hs.1,
      (h i hmem).2.inter_of_isOpen_left hs.2 (h i hmem).1⟩

/-- When finitely many analytic sheets are pairwise distinct on a common connected chart,
all their values are different on one relatively open dense set. -/
theorem generic_injective_graph_values {ι : Type*} [Finite ι]
    (U : Set E) (hU : IsOpen U) (hconn : IsPreconnected U)
    (f : ι → E → ℝ) (hf : ∀ i, AnalyticOnNhd ℝ (f i) U)
    (hne : ∀ i j, i ≠ j → ¬ EqOn (f i) (f j) U) :
    IsOpen {x : U | Function.Injective (fun i => f i x)} ∧
      Dense {x : U | Function.Injective (fun i => f i x)} := by
  classical
  let _ := Fintype.ofFinite ι
  let pairs : Finset (ι × ι) := Finset.univ.filter fun p => p.1 ≠ p.2
  let G (p : ι × ι) : Set U := {x | f p.1 x ≠ f p.2 x}
  have h := open_dense_finset pairs G (fun p hp => open_dense_pair U hU hconn _ _
    (hf p.1) (hf p.2) (hne p.1 p.2 (Finset.mem_filter.mp hp).2))
  have he : (⋂ p ∈ pairs, G p) = {x : U | Function.Injective (fun i => f i x)} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, G, pairs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h₀ i j hij
      by_contra hn
      exact h₀ (i,j) hn hij
    · intro h₀ p hn he
      exact hn (h₀ he)
  rwa [he] at h

section Continuation

variable {X : Type*} [TopologicalSpace X]

/-- A source chart on which membership in `A` is exactly agreement with one of
finitely many competing analytic graphs. -/
structure AnalyticAmbiguityChart (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Set X) (x : X) where
  domain : Set E
  isOpen_domain : IsOpen domain
  preconnected_domain : IsPreconnected domain
  toSource : domain → X
  openEmbedding : IsOpenEmbedding toSource
  center : domain
  center_eq : toSource center = x
  count : ℕ
  graph : E → ℝ
  competitor : Fin count → E → ℝ
  analytic_graph : AnalyticOnNhd ℝ graph domain
  analytic_competitor : ∀ i, AnalyticOnNhd ℝ (competitor i) domain
  mem_iff : ∀ t : domain, toSource t ∈ A ↔ ∃ i, graph t = competitor i t

private theorem chart_unique_locus {A : Set X} {x : X} (c : AnalyticAmbiguityChart E A x)
    (h : ∀ i, ¬ EqOn c.graph (c.competitor i) c.domain) :
    IsOpen (c.toSource ⁻¹' Aᶜ) ∧ Dense (c.toSource ⁻¹' Aᶜ) := by
  classical
  let G (i : Fin c.count) : Set c.domain := {t | c.graph t ≠ c.competitor i t}
  have ho := open_dense_finset Finset.univ G (fun i _ =>
    open_dense_pair c.domain c.isOpen_domain c.preconnected_domain _ _
      c.analytic_graph (c.analytic_competitor i) (h i))
  have he : (⋂ i ∈ Finset.univ, G i) = c.toSource ⁻¹' Aᶜ := by
    ext t
    simp [G, c.mem_iff]
  rwa [he] at ho

/-- A chart with no repeated graph has empty intersection with the interior of
the ambiguity set. This also applies at a center where distinct graphs meet. -/
theorem AnalyticAmbiguityChart.not_mem_interior {A : Set X} {x : X}
    (c : AnalyticAmbiguityChart E A x)
    (h : ∀ i, ¬ EqOn c.graph (c.competitor i) c.domain) (t : c.domain) :
    c.toSource t ∉ interior A := by
  intro ht
  have hd := (chart_unique_locus c h).2
  let U := c.toSource ⁻¹' interior A
  have ⟨y, hy⟩ := hd.inter_open_nonempty U
    (isOpen_interior.preimage c.openEmbedding.continuous) ⟨t, ht⟩
  exact hy.2 (interior_subset hy.1)

/-- On a preconnected source, a point at which all competing graphs are
distinct rules out a repeated graph in every chart. The points with unique
observation then form an open dense set. -/
theorem open_dense_compl_of_analytic_fiber_charts [PreconnectedSpace X] {A : Set X}
    (charts : ∀ x, AnalyticAmbiguityChart E A x)
    (special : ∃ x, ∀ i, ¬ EqOn (charts x).graph ((charts x).competitor i) (charts x).domain) :
    IsOpen Aᶜ ∧ Dense Aᶜ := by
  classical
  have range_interior (x : X) (i : Fin (charts x).count)
      (hi : EqOn (charts x).graph ((charts x).competitor i) (charts x).domain) :
      range (charts x).toSource ⊆ interior A := by
    refine interior_maximal ?_ (charts x).openEmbedding.isOpen_range
    rintro _ ⟨t, rfl⟩
    exact ((charts x).mem_iff t).2 ⟨i, hi t.property⟩
  have center_mem (x : X) : x ∈ range (charts x).toSource :=
    ⟨(charts x).center, (charts x).center_eq⟩
  have hc : IsClosed (interior A) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have h : ∀ i, ¬ EqOn (charts x).graph ((charts x).competitor i) (charts x).domain :=
      fun i hi => hx (range_interior x i hi (center_mem x))
    refine Filter.mem_of_superset
      ((charts x).openEmbedding.isOpen_range.mem_nhds (center_mem x)) ?_
    rintro _ ⟨t, rfl⟩
    exact (charts x).not_mem_interior h t
  obtain ⟨x, hx⟩ := special
  have hspecial : x ∉ interior A := by
    rw [← (charts x).center_eq]
    exact (charts x).not_mem_interior hx (charts x).center
  have hempty : interior A = ∅ :=
    (isClopen_iff.mp ⟨hc, isOpen_interior⟩).resolve_right
      (fun h => hspecial (h.symm ▸ mem_univ x))
  refine ⟨isOpen_iff_mem_nhds.mpr ?_, interior_eq_empty_iff_dense_compl.mp hempty⟩
  intro z hz
  have h : ∀ i, ¬ EqOn (charts z).graph ((charts z).competitor i) (charts z).domain := by
    intro i hi
    have hmem := range_interior z i hi (center_mem z)
    simp [hempty] at hmem
  have hopen := (charts z).openEmbedding.isOpenMap _ (chart_unique_locus (charts z) h).1
  have hzcenter : (charts z).toSource (charts z).center ∈ Aᶜ := by
    rwa [(charts z).center_eq]
  have hz' : z ∈ (charts z).toSource '' ((charts z).toSource ⁻¹' Aᶜ) :=
    ⟨(charts z).center, hzcenter, (charts z).center_eq⟩
  exact Filter.mem_of_superset (hopen.mem_nhds hz') (image_preimage_subset _ _)

end Continuation

end D5.S3.Quantum.TensorNetworks.PeriodicMPSAnalyticBranchSeparation
