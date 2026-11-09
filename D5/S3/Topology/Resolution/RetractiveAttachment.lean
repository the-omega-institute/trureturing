/- GID: D5/S3/Topology/Resolution/RetractiveAttachment
   generality: G
   mirror-B: D5/B/S3/Topology/Resolution/RetractiveAttachment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal arbitrary-set continuous retractive attachments and their convergence. -/

import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
The carrier is literally `B ⊕ Σ i, P i`. The topology below is constructed,
not stored as an assumed field. Arbitrary continuous attachment maps are
allowed. Source: the supplied ordinary proof and independent review of
4 November 2026, sections on the stronger carrier and range multiplicity.
Classical topology only; original Efimov KPI 0, original problem unsolved.
-/

open Set Function Filter Topology TopologicalSpace

namespace D5.S3.Topology.Resolution.RetractiveAttachment

universe u v w
variable {B : Type u} {I : Type v} {P : I → Type w}
variable [TopologicalSpace B] [∀ i, TopologicalSpace (P i)]

def Space (t : ∀ i, P i → B) := B ⊕ Σ i, P i

def core (t : ∀ i, P i → B) (b : B) : Space t := Sum.inl b

def component (t : ∀ i, P i → B) (i : I) (z : P i) : Space t := Sum.inr ⟨i,z⟩

def collapse (t : ∀ i, P i → B) : Space t → B
  | Sum.inl b => b
  | Sum.inr ⟨i,z⟩ => t i z

def basic (t : ∀ i, P i → B) (U : Set B) (J : Finset I) : Set (Space t) :=
  {x | match x with
    | Sum.inl b => b ∈ U
    | Sum.inr ⟨i,z⟩ => i ∉ J ∧ t i z ∈ U}

instance topology (t : ∀ i, P i → B) : TopologicalSpace (Space t) where
  IsOpen s := (∀ i, IsOpen (component t i ⁻¹' s)) ∧
    ∀ b, core t b ∈ s → ∃ U, IsOpen U ∧ b ∈ U ∧ ∃ J : Finset I, basic t U J ⊆ s
  isOpen_univ := ⟨fun _ => isOpen_univ, fun _ _ => ⟨univ,isOpen_univ,mem_univ _,∅,subset_univ _⟩⟩
  isOpen_inter s r hs hr := by
    classical
    refine ⟨fun i => (hs.1 i).inter (hr.1 i), ?_⟩
    intro b hb
    obtain ⟨U,hU,hbU,J,hJ⟩ := hs.2 b hb.1
    obtain ⟨V,hV,hbV,L,hL⟩ := hr.2 b hb.2
    refine ⟨U ∩ V,hU.inter hV,⟨hbU,hbV⟩,J ∪ L,?_⟩
    intro x hx
    cases x with
    | inl b => exact ⟨hJ hx.1,hL hx.2⟩
    | inr z =>
      exact ⟨hJ ⟨fun h => hx.1 (Finset.mem_union_left _ h),hx.2.1⟩,
        hL ⟨fun h => hx.1 (Finset.mem_union_right _ h),hx.2.2⟩⟩
  isOpen_sUnion S hS := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [preimage_sUnion]
      exact isOpen_biUnion fun s hs => (hS s hs).1 i
    · intro b hb
      obtain ⟨s,hs,hbs⟩ := hb
      obtain ⟨U,hU,hbU,J,hJ⟩ := (hS s hs).2 b hbs
      exact ⟨U,hU,hbU,J,fun x hx => ⟨s,hs,hJ hx⟩⟩

variable (t : ∀ i, P i → B)

theorem is_open_iff (s : Set (Space t)) : IsOpen s ↔
    (∀ i, IsOpen (component t i ⁻¹' s)) ∧
    ∀ b, core t b ∈ s → ∃ U, IsOpen U ∧ b ∈ U ∧ ∃ J : Finset I, basic t U J ⊆ s := Iff.rfl

theorem continuous_core : Continuous (core t) := by
  apply continuous_def.mpr
  intro s hs
  rw [isOpen_iff_mem_nhds]
  intro b hb
  obtain ⟨U,hU,hbU,J,hJ⟩ := hs.2 b hb
  exact mem_of_superset (hU.mem_nhds hbU) (fun b hb => hJ hb)

theorem continuous_component (i : I) : Continuous (component t i) :=
  continuous_def.mpr fun _ hs => hs.1 i

theorem core_injective : Injective (core t) := Sum.inl_injective

theorem component_injective (i : I) : Injective (component t i) := by
  intro x y h
  exact sigma_mk_injective (Sum.inr.inj h)

theorem component_ne_core (i : I) (z : P i) (b : B) : component t i z ≠ core t b := by
  intro h
  have h' : (Sum.inr ⟨i,z⟩ : B ⊕ (Σ i, P i)) = Sum.inl b := h
  cases h'

theorem is_open_component_image (i : I) (V : Set (P i)) (hV : IsOpen V) :
    IsOpen (component t i '' V) := by
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : i = j
    · subst j
      simpa only [preimage_image_eq _ (component_injective t i)] using hV
    · have he : component t j ⁻¹' (component t i '' V) = ∅ := by
        ext z
        simp only [mem_preimage,mem_image,mem_empty_iff_false,iff_false]
        rintro ⟨y,hy,he⟩
        exact h (congrArg Sigma.fst (Sum.inr.inj he))
      rw [he]
      exact isOpen_empty
  · intro b hb
    obtain ⟨z,hz,he⟩ := hb
    exact (component_ne_core t i z b he).elim

theorem is_open_basic (ht : ∀ i, Continuous (t i)) (U : Set B) (hU : IsOpen U) (J : Finset I) :
    IsOpen (basic t U J) := by
  apply (is_open_iff t _).mpr
  refine ⟨fun i => ?_, fun b hb => ⟨U,hU,hb,J,Subset.rfl⟩⟩
  by_cases hi : i ∈ J
  · have he : component t i ⁻¹' basic t U J = ∅ := by ext z; simp [component,basic,hi]
    rw [he]
    exact isOpen_empty
  · have he : component t i ⁻¹' basic t U J = t i ⁻¹' U := by ext z; simp [component,basic,hi]
    rw [he]
    exact hU.preimage (ht i)

theorem continuous_retraction (ht : ∀ i, Continuous (t i)) :
    Continuous (collapse t) ∧ LeftInverse (collapse t) (core t) := by
  refine ⟨?_, fun _ => rfl⟩
  apply continuous_def.mpr
  intro U hU
  have he : collapse t ⁻¹' U = basic t U ∅ := by
    ext x
    cases x with
    | inl b => rfl
    | inr z =>
      rcases z with ⟨i,z⟩
      change (t i z ∈ U) ↔ (i ∉ (∅ : Finset I) ∧ t i z ∈ U)
      simp
  rw [he]
  exact is_open_basic t ht U hU ∅

theorem is_closed_component (ht : ∀ i, Continuous (t i)) (i : I) :
    IsClosed (range (component t i)) := by
  have he : (range (component t i))ᶜ = basic t univ {i} := by
    ext x
    cases x with
    | inl b =>
      change (core t b ∉ range (component t i)) ↔ b ∈ (univ : Set B)
      constructor
      · intro _; exact mem_univ _
      · rintro _ ⟨z,hz⟩
        exact component_ne_core t i z b hz
    | inr z =>
      rcases z with ⟨j,z⟩
      change (component t j z ∉ range (component t i)) ↔
        (j ∉ ({i} : Finset I) ∧ t j z ∈ (univ : Set B))
      constructor
      · intro hx
        refine ⟨?_,mem_univ _⟩
        intro hj
        have hj : j = i := Finset.mem_singleton.mp hj
        subst j
        exact hx ⟨z,rfl⟩
      · rintro ⟨hj,_⟩ ⟨y,hy⟩
        apply hj
        exact Finset.mem_singleton.mpr (congrArg Sigma.fst (Sum.inr.inj hy)).symm
  rw [← isOpen_compl_iff,he]
  exact is_open_basic t ht univ isOpen_univ {i}

theorem is_closed_core : IsClosed (range (core t)) := by
  rw [← isOpen_compl_iff]
  refine ⟨fun i => ?_, ?_⟩
  · have he : component t i ⁻¹' (range (core t))ᶜ = univ := by
      ext z
      change (component t i z ∉ range (core t)) ↔ True
      constructor
      · intro _; trivial
      · rintro _ ⟨b,hb⟩
        exact component_ne_core t i z b hb.symm
    rw [he]; exact isOpen_univ
  · intro b hb
    exact (hb ⟨b,rfl⟩).elim

/-- An open set containing the entire compact core contains every component
outside one finite exceptional set. Attachment maps may be nonconstant. -/
theorem finite_exception_of_contains_core [CompactSpace B]
    (W : Set (Space t)) (hW : IsOpen W) (hc : range (core t) ⊆ W) :
    ∃ J : Finset I, ∀ i, i ∉ J → range (component t i) ⊆ W := by
  classical
  choose U hU hbU J hJ using fun b => hW.2 b (hc ⟨b,rfl⟩)
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro b _; exact mem_iUnion.mpr ⟨b,hbU b⟩)
  refine ⟨s.biUnion J,?_⟩
  intro i hi x hx
  obtain ⟨z,rfl⟩ := hx
  obtain ⟨b,hb,ht⟩ := mem_iUnion₂.mp (hs (mem_univ (t i z)))
  exact hJ b ⟨fun hij => hi (Finset.mem_biUnion.mpr ⟨b,hb,hij⟩),ht⟩

theorem compact_space [CompactSpace B] [∀ i, CompactSpace (P i)] : CompactSpace (Space t) := by
  classical
  constructor
  apply isCompact_iff_finite_subcover.mpr
  intro A U hU hcover
  have hcore : IsCompact (range (core t)) := isCompact_range (continuous_core t)
  obtain ⟨s,hs⟩ := hcore.elim_finite_subcover U hU (subset_trans (subset_univ _) hcover)
  obtain ⟨J,hJ⟩ := finite_exception_of_contains_core t (⋃ a ∈ s, U a)
    (isOpen_biUnion fun a _ => hU a) hs
  have hcomp (i : I) : ∃ r : Finset A, range (component t i) ⊆ ⋃ a ∈ r, U a :=
    (isCompact_range (continuous_component t i)).elim_finite_subcover U hU
      (subset_trans (subset_univ _) hcover)
  choose r hr using hcomp
  refine ⟨s ∪ J.biUnion r,?_⟩
  intro x _
  cases x with
  | inl b =>
    obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp (hs ⟨b,rfl⟩)
    exact mem_iUnion₂.mpr ⟨a,Finset.mem_union_left _ ha,hx⟩
  | inr z =>
    rcases z with ⟨i,z⟩
    by_cases hi : i ∈ J
    · obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp (hr i ⟨z,rfl⟩)
      exact mem_iUnion₂.mpr ⟨a,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,ha⟩),hx⟩
    · obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp (hJ i hi ⟨z,rfl⟩)
      exact mem_iUnion₂.mpr ⟨a,Finset.mem_union_left _ ha,hx⟩

theorem hausdorff (ht : ∀ i, Continuous (t i)) [T2Space B] [∀ i, T2Space (P i)] :
    T2Space (Space t) := by
  classical
  constructor
  intro x y hxy
  cases x with
  | inl b =>
    cases y with
    | inl c =>
      obtain ⟨U,V,hU,hV,hb,hc,hd⟩ := t2_separation (fun h => hxy (congrArg Sum.inl h))
      refine ⟨basic t U ∅,basic t V ∅,is_open_basic t ht U hU ∅,
        is_open_basic t ht V hV ∅,hb,hc,?_⟩
      apply disjoint_left.mpr
      intro x hx hy
      cases x with
      | inl _ => exact disjoint_left.mp hd hx hy
      | inr _ => exact disjoint_left.mp hd hx.2 hy.2
    | inr z =>
      rcases z with ⟨i,z⟩
      refine ⟨(range (component t i))ᶜ,range (component t i),
        (is_closed_component t ht i).isOpen_compl,?_,?_,⟨z,rfl⟩,disjoint_compl_left⟩
      · simpa only [image_univ] using is_open_component_image t i univ isOpen_univ
      · rintro ⟨z,hz⟩
        exact component_ne_core t i z b hz
  | inr x =>
    rcases x with ⟨i,x⟩
    by_cases hy : y ∈ range (component t i)
    · obtain ⟨z,rfl⟩ := hy
      obtain ⟨U,V,hU,hV,hx,hz,hd⟩ := t2_separation (fun h => hxy (congrArg (component t i) h))
      refine ⟨component t i '' U,component t i '' V,is_open_component_image t i U hU,
        is_open_component_image t i V hV,⟨x,hx,rfl⟩,⟨z,hz,rfl⟩,?_⟩
      exact (Set.disjoint_image_iff (component_injective t i)).mpr hd
    · refine ⟨range (component t i),(range (component t i))ᶜ,?_,
        (is_closed_component t ht i).isOpen_compl,⟨x,rfl⟩,hy,disjoint_compl_right⟩
      simpa only [image_univ] using is_open_component_image t i univ isOpen_univ

/-- Exact clopen algebra, with actual component traces and one finite defect. -/
theorem is_clopen_iff [CompactSpace B] (ht : ∀ i, Continuous (t i)) (H : Set (Space t)) :
    IsClopen H ↔ IsClopen (core t ⁻¹' H) ∧
      (∀ i, IsClopen (component t i ⁻¹' H)) ∧
      ∃ J : Finset I, ∀ i, i ∉ J → component t i ⁻¹' H = t i ⁻¹' (core t ⁻¹' H) := by
  classical
  constructor
  · intro hH
    have hV := hH.preimage (continuous_core t)
    let V := core t ⁻¹' H
    let W := (H ∩ collapse t ⁻¹' V) ∪ (Hᶜ ∩ collapse t ⁻¹' Vᶜ)
    have hW : IsOpen W :=
      (hH.isOpen.inter (hV.isOpen.preimage (continuous_retraction t ht).1)).union
        (hH.compl.isOpen.inter (hV.compl.isOpen.preimage (continuous_retraction t ht).1))
    have hc : range (core t) ⊆ W := by
      rintro _ ⟨b,rfl⟩
      by_cases hb : core t b ∈ H
      · exact Or.inl ⟨hb,hb⟩
      · exact Or.inr ⟨hb,hb⟩
    obtain ⟨J,hJ⟩ := finite_exception_of_contains_core t W hW hc
    refine ⟨hV,fun i => hH.preimage (continuous_component t i),J,?_⟩
    intro i hi
    ext z
    obtain h | h := hJ i hi ⟨z,rfl⟩
    · exact iff_of_true h.1 h.2
    · exact iff_of_false h.1 h.2
  · rintro ⟨hV,hP,J,hJ⟩
    have hopen (S : Set (Space t)) (hS : IsOpen (core t ⁻¹' S))
        (hPS : ∀ i, IsOpen (component t i ⁻¹' S))
        (he : ∀ i, i ∉ J → component t i ⁻¹' S = t i ⁻¹' (core t ⁻¹' S)) : IsOpen S := by
      refine ⟨hPS,fun b hb => ⟨core t ⁻¹' S,hS,hb,J,?_⟩⟩
      intro x hx
      cases x with
      | inl _ => exact hx
      | inr z => exact (Set.ext_iff.mp (he z.1 hx.1) z.2).mpr hx.2
    refine ⟨isOpen_compl_iff.mp (hopen Hᶜ hV.compl.isOpen (fun i => (hP i).compl.isOpen) ?_),
      hopen H hV.isOpen (fun i => (hP i).isOpen) hJ⟩
    intro i hi
    ext z
    change (¬ component t i z ∈ H) ↔ ¬ core t (t i z) ∈ H
    exact not_congr (Set.ext_iff.mp (hJ i hi) z)

theorem is_clopen_basic [CompactSpace B] (ht : ∀ i, Continuous (t i))
    (U : Set B) (hU : IsClopen U) (J : Finset I) : IsClopen (basic t U J) := by
  apply (is_clopen_iff t ht _).mpr
  refine ⟨?_,?_,J,?_⟩
  · have he : core t ⁻¹' basic t U J = U := by ext b; rfl
    rw [he]
    exact hU
  · intro i
    by_cases hi : i ∈ J
    · have he : component t i ⁻¹' basic t U J = ∅ := by ext z; simp [component,basic,hi]
      rw [he]; exact isClopen_empty
    · have he : component t i ⁻¹' basic t U J = t i ⁻¹' U := by ext z; simp [component,basic,hi]
      rw [he]; exact hU.preimage (ht i)
  · intro i hi
    ext z
    simp [component,core,basic,hi]

theorem core_closed_embedding (ht : ∀ i, Continuous (t i)) : IsClosedEmbedding (core t) :=
  ⟨IsEmbedding.of_leftInverse (continuous_retraction t ht).2 (continuous_retraction t ht).1 (continuous_core t),
    is_closed_core t⟩

theorem component_clopen_embedding (i : I) [CompactSpace (P i)] [T2Space B] [∀ i, T2Space (P i)]
    (ht : ∀ i, Continuous (t i)) :
    IsClosedEmbedding (component t i) ∧ IsClopen (range (component t i)) ∧
      IsCompact (range (component t i)) := by
  let := hausdorff t ht
  refine ⟨(continuous_component t i).isClosedEmbedding (component_injective t i),
    ⟨is_closed_component t ht i, ?_⟩, isCompact_range (continuous_component t i)⟩
  simpa only [image_univ] using is_open_component_image t i univ isOpen_univ

theorem zero_dimensional [CompactSpace B] [T2Space B] [ZeroDimensionalSpace B]
    [∀ i, CompactSpace (P i)] [∀ i, T2Space (P i)] [∀ i, ZeroDimensionalSpace (P i)]
    (ht : ∀ i, Continuous (t i)) : ZeroDimensionalSpace (Space t) := by
  classical
  let := hausdorff t ht
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  apply isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.isOpen)
  intro x W hx hW
  cases x with
  | inl b =>
    obtain ⟨U,hU,hb,J,hJ⟩ := hW.2 b hx
    obtain ⟨V,hV,hbV,hVU⟩ := isTopologicalBasis_isClopen.exists_subset_of_mem_open hb hU
    refine ⟨basic t V J,is_clopen_basic t ht V hV J,hbV,?_⟩
    intro y hy
    apply hJ
    cases y with
    | inl _ => exact hVU hy
    | inr _ => exact ⟨hy.1,hVU hy.2⟩
  | inr z =>
    rcases z with ⟨i,z⟩
    have hzW : z ∈ component t i ⁻¹' W := hx
    obtain ⟨V,hV,hz,hVW⟩ :=
      (isTopologicalBasis_isClopen (X := P i)).exists_subset_of_mem_open hzW (hW.1 i)
    refine ⟨component t i '' V,?_,⟨z,hz,rfl⟩,?_⟩
    · exact ⟨(hV.isClosed.isCompact.image (continuous_component t i)).isClosed,
        is_open_component_image t i V hV.isOpen⟩
    · rintro _ ⟨z,hz,rfl⟩; exact hVW hz

/-- Transverse convergence is exactly convergence of the actual attachment images. -/
theorem transverse_tendsto_iff (ht : ∀ i, Continuous (t i))
    (a : ℕ → I) (ha : Injective a) (z : ∀ n, P (a n)) (b : B) :
    Tendsto (fun n => component t (a n) (z n)) atTop (𝓝 (core t b)) ↔
      Tendsto (fun n => t (a n) (z n)) atTop (𝓝 b) := by
  constructor
  · intro h
    exact (continuous_retraction t ht).1.continuousAt.tendsto.comp h
  · intro h
    apply tendsto_nhds.mpr
    intro W hW hb
    obtain ⟨U,hU,hbU,J,hJ⟩ := hW.2 b hb
    have havoid : ∀ᶠ n in atTop, a n ∉ J := by
      have he : ∀ᶠ i in cofinite, i ∉ J := J.finite_toSet.compl_mem_cofinite
      simpa only [Nat.cofinite_eq_atTop] using ha.tendsto_cofinite.eventually he
    filter_upwards [h.eventually (hU.mem_nhds hbU),havoid] with n hn hi
    exact hJ ⟨hi,hn⟩

/-- The actual set of component ranges through a specified core point. -/
def multiplicity (b : B) : Set I := {i | b ∈ range (t i)}

/-- Infinite actual range multiplicity constructs an injective convergent
natural sequence in the literal carrier, with its limit outside all terms. -/
theorem sequence_of_infinite_multiplicity (ht : ∀ i, Continuous (t i))
    (b : B) (hb : (multiplicity t b).Infinite) :
    ∃ x : ℕ → Space t, Injective x ∧ Tendsto x atTop (𝓝 (core t b)) ∧
      ∀ n, x n ≠ core t b := by
  classical
  let e : ℕ ↪ multiplicity t b := Set.Infinite.natEmbedding (multiplicity t b) hb
  choose z hz using fun n => (e n).property
  let x : ℕ → Space t := fun n => component t (e n).val (z n)
  have hi : Injective (fun n => (e n).val) := Subtype.val_injective.comp e.injective
  refine ⟨x,?_,?_,fun n => component_ne_core t _ _ _⟩
  · intro m n h
    exact hi (congrArg Sigma.fst (Sum.inr.inj h))
  · apply (transverse_tendsto_iff t ht _ hi z b).mpr
    have he : (fun n => t (e n).val (z n)) = fun _ => b := funext hz
    rw [he]
    exact tendsto_const_nhds

/-- Standard sequence-free predicate: actual natural sequences, injectivity,
and actual neighborhood-filter convergence. It permits the limit among the
terms, which is equivalent to deleting at most one term. -/
def NoConvergentInjectiveSequence (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : ℕ → X) (b : X), Injective x → ¬ Tendsto x atTop (𝓝 b)

/-- In a Hausdorff sequence-free space every convergent natural sequence is
eventually its limit. The proof extracts actual distinct off-limit values. -/
theorem eventually_eq_of_no_sequence {X : Type*} [TopologicalSpace X] [T2Space X]
    (hX : NoConvergentInjectiveSequence X) (x : ℕ → X) (b : X)
    (hx : Tendsto x atTop (𝓝 b)) : ∀ᶠ n in atTop, x n = b := by
  classical
  let S : Set X := range x \ {b}
  by_cases hS : S.Finite
  · have hb : b ∈ Sᶜ := by simp [S]
    filter_upwards [hx.eventually (hS.isClosed.isOpen_compl.mem_nhds hb)] with n hn
    by_contra hne
    exact hn ⟨mem_range_self n,hne⟩
  · let e : ℕ ↪ S := Set.Infinite.natEmbedding S hS
    choose k hk using fun n => (e n).property.1
    have hk_inj : Injective k := by
      intro m n h
      apply e.injective
      apply Subtype.ext
      exact (hk m).symm.trans ((congrArg x h).trans (hk n))
    have he_inj : Injective (fun n => (e n).val) := Subtype.val_injective.comp e.injective
    apply False.elim (hX _ b he_inj ?_)
    have hlim := hx.comp hk_inj.nat_tendsto_atTop
    exact hlim.congr' (Filter.Eventually.of_forall hk)

/-- Full arbitrary-set sequence characterization, including the empty index
set. All three conditions are necessary, with actual attachment ranges. -/
theorem no_sequence_iff [T2Space B] [∀ i, CompactSpace (P i)] [∀ i, T2Space (P i)]
    (ht : ∀ i, Continuous (t i)) :
    NoConvergentInjectiveSequence (Space t) ↔
      NoConvergentInjectiveSequence B ∧ (∀ i, NoConvergentInjectiveSequence (P i)) ∧
      ∀ b, (multiplicity t b).Finite := by
  classical
  constructor
  · intro hK
    refine ⟨?_,?_,?_⟩
    · intro x b hi hx
      exact hK _ (core t b) ((core_injective t).comp hi) ((continuous_core t).continuousAt.tendsto.comp hx)
    · intro i x b hi hx
      exact hK _ (component t i b) ((component_injective t i).comp hi)
        ((continuous_component t i).continuousAt.tendsto.comp hx)
    · intro b
      by_contra hb
      obtain ⟨x,hi,hx,_⟩ := sequence_of_infinite_multiplicity t ht b hb
      exact hK x (core t b) hi hx
  · rintro ⟨hB,hP,hM⟩ x y hi hx
    cases y with
    | inl b =>
      have he := eventually_eq_of_no_sequence hB (fun n => collapse t (x n)) b
        ((continuous_retraction t ht).1.continuousAt.tendsto.comp hx)
      have hne : ∀ᶠ n in atTop, x n ≠ core t b := by
        have h := hi.tendsto_cofinite.eventually (Set.finite_singleton (core t b)).compl_mem_cofinite
        simpa only [Nat.cofinite_eq_atTop,mem_compl_iff,mem_singleton_iff] using h
      have hav : ∀ᶠ n in atTop, ∀ i ∈ multiplicity t b, x n ∉ range (component t i) :=
        (Filter.eventually_all_finite (hM b)).mpr fun i _ =>
          hx.eventually ((is_closed_component t ht i).isOpen_compl.mem_nhds (by
            rintro ⟨z,hz⟩
            exact component_ne_core t i z b hz))
      obtain ⟨n,he,hne,hav⟩ := (he.and (hne.and hav)).exists
      cases hxn : x n with
      | inl c =>
        have hc : c = b := by simpa [hxn,collapse] using he
        exact hne (hxn.trans (congrArg Sum.inl hc))
      | inr z =>
        rcases z with ⟨i,z⟩
        have hz : t i z = b := by simpa [hxn,collapse] using he
        exact hav i ⟨z,hz⟩ ⟨z,hxn.symm⟩
    | inr z =>
      rcases z with ⟨i,z⟩
      have hopen : IsOpen (range (component t i)) := by
        simpa only [image_univ] using is_open_component_image t i univ isOpen_univ
      obtain ⟨N,hN⟩ := eventually_atTop.mp (hx.eventually (hopen.mem_nhds ⟨z,rfl⟩))
      choose p hp using fun n => hN (N+n) (by omega)
      have hp_inj : Injective p := by
        intro m n h
        have heq : N+m = N+n := hi ((hp m).symm.trans ((congrArg (component t i) h).trans (hp n)))
        omega
      have hshift : Injective (fun n : ℕ => N+n) := fun _ _ h => Nat.add_left_cancel h
      have hlim : Tendsto (fun n => component t i (p n)) atTop (𝓝 (component t i z)) :=
        (hx.comp hshift.nat_tendsto_atTop).congr' (Filter.Eventually.of_forall fun n => (hp n).symm)
      exact hP i p z hp_inj ((component_clopen_embedding t i ht).1.tendsto_nhds_iff.mpr hlim)

end D5.S3.Topology.Resolution.RetractiveAttachment
