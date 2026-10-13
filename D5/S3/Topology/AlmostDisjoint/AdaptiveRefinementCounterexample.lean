/- GID: D5/S3/Topology/AlmostDisjoint/AdaptiveRefinementCounterexample
   generality: G
   mirror-B: D5/B/S3/Topology/AlmostDisjoint/AdaptiveRefinementCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An actual compact open surjection has no finite closed open-restriction refinement. -/

import D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace
import D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.DisjointCover

open Set Filter Topology TopologicalSpace
open scoped OnePoint
open D5.S3.Topology.AlmostDisjoint.ColorFiberDiagonal

namespace D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample

-- Compactness/T2 of the total space is deliberately unnecessary here: each
-- section has compact domain, so its intersection with any closed K is compact.
private theorem open_closed_piece_partitions {T ι : Type*} [TopologicalSpace T]
    (p : T → OnePoint ℕ) (hp : Continuous p) (M : ι → Set ℕ) (d : ℕ → T)
    (s : ι → OnePoint ℕ → T) (hs : ∀ i, Continuous (s i))
    (hps : ∀ i b, p (s i b) = b) (hopen : ∀ i, IsOpen (range (s i)))
    (hsd : ∀ i n, n ∈ M i → s i (n : OnePoint ℕ) = d n)
    (K : Set T) (hK : IsClosed K)
    (hopenK : IsOpenMap (fun x : K => p x.val)) :
    Partitions M {n | d n ∈ K} := by
  classical
  intro i
  let E : Set (OnePoint ℕ) := p '' (K ∩ range (s i))
  have hEc : IsCompact E := by
    have h := ((isCompact_range (hs i)).inter_right hK).image hp
    simpa only [inter_comm,E] using h
  have hEo : IsOpen E := by
    have heq : E = (fun x : K => p x.val) '' {x : K | x.val ∈ range (s i)} := by
      ext b
      constructor
      · rintro ⟨t,⟨htK,hts⟩,hpt⟩
        exact ⟨⟨t,htK⟩,hts,hpt⟩
      · rintro ⟨t,hts,hpt⟩
        exact ⟨t.val,⟨t.property,hts⟩,hpt⟩
    rw [heq]
    exact hopenK _ ((hopen i).preimage continuous_subtype_val)
  have hchar (n : ℕ) (hn : n ∈ M i) :
      (n : OnePoint ℕ) ∈ E ↔ d n ∈ K := by
    constructor
    · rintro ⟨t,⟨htK,⟨b,rfl⟩⟩,hpt⟩
      have hb : b = (n : OnePoint ℕ) := (hps i b).symm.trans hpt
      rw [hb,hsd i n hn] at htK
      exact htK
    · intro hd
      refine ⟨d n,⟨hd,⟨(n : OnePoint ℕ),hsd i n hn⟩⟩,?_⟩
      simpa only [hsd i n hn] using hps i (n : OnePoint ℕ)
  by_cases hinf : (∞ : OnePoint ℕ) ∈ E
  · left
    have hfinite : (((↑) : ℕ → OnePoint ℕ) ⁻¹' E)ᶜ.Finite :=
      ((OnePoint.isOpen_iff_of_mem hinf).mp hEo).2.finite_of_discrete
    apply hfinite.subset
    rintro n ⟨hnM,hnD⟩ hnE
    exact hnD ((hchar n hnM).mp hnE)
  · right
    have hfinite : (((↑) : ℕ → OnePoint ℕ) ⁻¹' E).Finite :=
      ((OnePoint.isClosed_iff_of_notMem hinf).mp hEc.isClosed).2.finite_of_discrete
    apply hfinite.subset
    rintro n ⟨hnM,hnD⟩
    exact (hchar n hnM).mpr hnD



-- Consumed supplier for arbitrary finite closed refinements. Each
-- piece yields a partitioner; finite grouping gives one literal threshold set.
private theorem finite_union_partitioners {α ι β : Type*} (M : ι → Set α)
    (F : Finset β) (D : β → Set α) (hD : ∀ j ∈ F, Partitions M (D j)) :
    Partitions M (⋃ j ∈ F, D j) := by
  classical
  intro i
  by_cases hin : ∃ j ∈ F, (M i \ D j).Finite
  · obtain ⟨j,hj,hfin⟩ := hin
    left
    apply hfin.subset
    rintro x ⟨hx,hnot⟩
    refine ⟨hx,?_⟩
    intro hxj
    exact hnot (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hj,hxj⟩⟩)
  · right
    have hout (j : β) (hj : j ∈ F) : (M i ∩ D j).Finite := by
      rcases hD j hj i with h | h
      · exact False.elim (hin ⟨j,hj,h⟩)
      · exact h
    apply (F.finite_toSet.biUnion (fun j hj => hout j hj)).subset
    rintro x ⟨hx,hU⟩
    obtain ⟨j,hjU⟩ := mem_iUnion.mp hU
    obtain ⟨hj,hxj⟩ := mem_iUnion.mp hjU
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hj,hx,hxj⟩⟩

private theorem grouped_refinement_separator {T ι β : Type*}
    (M : ι → Set ℕ) (d : ℕ → T) (u : T → ℝ)
    (F : Finset β) (K : β → Set T) (side : β → Bool)
    (hcover : ∀ n, ∃ j ∈ F, d n ∈ K j)
    (hsub : ∀ j ∈ F, K j ⊆ (if side j then {x | (1:ℝ)/3 < u x}
      else {x | u x < (2:ℝ)/3}))
    (hpart : ∀ j ∈ F, Partitions M {n | d n ∈ K j}) :
    ∃ D : Set ℕ, Partitions M D ∧
      {n | u (d n) ≤ (1:ℝ)/3} ⊆ D ∧ D ⊆ {n | u (d n) < (2:ℝ)/3} := by
  classical
  let G := F.filter (fun j => side j = false)
  let D : Set ℕ := ⋃ j ∈ G, {n | d n ∈ K j}
  refine ⟨D,finite_union_partitioners M G _ (fun j hj => hpart j (Finset.mem_filter.mp hj).1),?_,?_⟩
  · intro n hn
    obtain ⟨j,hj,hnK⟩ := hcover n
    have hs : side j = false := by
      cases hb : side j
      · rfl
      · have hside : K j ⊆ {x | (1:ℝ)/3 < u x} := by
          simpa [hb] using hsub j hj
        have hlt : (1 : ℝ) / 3 < u (d n) := hside hnK
        exact False.elim (not_lt_of_ge hn hlt)
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hj,hs⟩,hnK⟩⟩
  · intro n hn
    obtain ⟨j,hjU⟩ := mem_iUnion.mp hn
    obtain ⟨hj,hnK⟩ := mem_iUnion.mp hjU
    obtain ⟨hjF,hjs⟩ := Finset.mem_filter.mp hj
    have hside : K j ⊆ {x | u x < (2:ℝ)/3} := by
      simpa [hjs] using hsub j hjF
    exact hside hnK




open D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily
open D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination

/-- A finite closed subordinate cover, with every restriction open into the whole base.
No individual piece is required to map onto. The finite label type permits empty
pieces and arbitrary repeated assignments to cover members. -/
def HasFiniteClosedRefinement {T B : Type*} [TopologicalSpace T] [TopologicalSpace B]
    (p : T → B) {ι : Type*} (U : ι → Set T) : Prop :=
  ∃ (m : ℕ) (K : Fin m → Set T) (side : Fin m → ι),
    (∀ j, IsClosed (K j)) ∧
    (∀ x, ∃ j, x ∈ K j) ∧
    (∀ j, K j ⊆ U (side j)) ∧
    (∀ j, IsOpenMap (fun x : K j => p x.val))

/-- A compact Hausdorff zero-dimensional resolution of the actual total space,
with a continuous onto resolving map and an open composite over the whole base.
There is no metrizability hypothesis on the resolution. -/
def HasOpenZeroDimensionalResolution {T B : Type*}
    [TopologicalSpace T] [TopologicalSpace B] (p : T → B) : Prop :=
  ∃ (Z : Type) (tZ : TopologicalSpace Z),
    letI := tZ
    CompactSpace Z ∧ T2Space Z ∧ TotallyDisconnectedSpace Z ∧
      ∃ r : Z → T, Continuous r ∧ Function.Surjective r ∧ IsOpenMap (p ∘ r)

private theorem literal_no_refinement (A : Set (Set ℕ)) (u : ℕ → unitInterval)
    (ell : A → unitInterval) (had : ADFamily A)
    (hc : ∀ a : A, ConvergesOn u a.val (ell a))
    (hno : ¬ ∃ D : Set ℕ, Partitions (fun a : A => a.val) D ∧
      {n | (u n : ℝ) ≤ (1:ℝ)/3} ⊆ D ∧ D ⊆ {n | (u n : ℝ) < (2:ℝ)/3}) :
    ¬ HasFiniteClosedRefinement (projection A u ell)
      (fun b : Bool => if b then {x | (1:ℝ)/3 < (x.val.2.1 : ℝ)}
        else {x | (x.val.2.1 : ℝ) < (2:ℝ)/3}) := by
  classical
  rintro ⟨m,K,side,hK,hcover,hsub,hopenK⟩
  obtain ⟨hclosed,hcompact,hp,hopen,honto,hs,hsclopen⟩ :=
    literal_closed_compact_open_surjection A u ell had.2 hc
  have hpart (j : Fin m) :
      Partitions (fun a : A => a.val) {n | naturalLift A u ell n ∈ K j} := by
    apply open_closed_piece_partitions (projection A u ell) hp
      (fun a : A => a.val) (naturalLift A u ell) (sectionLift A u ell) hs
      (fun _ _ => rfl) (fun a => (hsclopen a).isOpen) ?_ (K j) (hK j) (hopenK j)
    intro a n hn
    apply Subtype.ext
    simp [sectionLift,memberSection,valueSection,vectorSection,naturalLift,naturalPoint,hn]
  obtain ⟨D,hD,hL,hU⟩ := grouped_refinement_separator
    (fun a : A => a.val) (naturalLift A u ell) (fun x => (x.val.2.1 : ℝ))
    Finset.univ K side (fun n => by
      obtain ⟨j,hj⟩ := hcover (naturalLift A u ell n)
      exact ⟨j,Finset.mem_univ _,hj⟩)
    (fun j _ => hsub j) (fun j _ => hpart j)
  apply hno
  exact ⟨D,hD,hL,hU⟩


private theorem closed_refinement_of_open_resolution {T B Z : Type*}
    [TopologicalSpace T] [T2Space T] [TopologicalSpace B]
    [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z]
    (p : T → B) (r : Z → T) (hr : Continuous r) (hronto : Function.Surjective r)
    (hopen : IsOpenMap (p ∘ r)) (U : Bool → Set T)
    (hU : ∀ b, IsOpen (U b)) (hcover : ∀ x, ∃ b, x ∈ U b) :
    HasFiniteClosedRefinement p U := by
  classical
  let V : Bool → Opens Z := fun b => ⟨r ⁻¹' U b,(hU b).preimage hr⟩
  have hV : IsOpenCover V := IsOpenCover.of_sets (fun b => (V b).isOpen) (by
    ext z
    simp only [mem_iUnion,mem_univ,iff_true]
    exact hcover (r z))
  obtain ⟨m,W,hW,hcov,hdis⟩ := hV.exists_finite_nonempty_disjoint_clopen_cover
  choose side hside using fun j => (hW j).2
  let K : Fin m → Set T := fun j => r '' (W j : Set Z)
  refine ⟨m,K,side,?_,?_,?_,?_⟩
  · intro j
    exact ((W j).isClosed.isCompact.image hr).isClosed
  · intro t
    obtain ⟨z,rfl⟩ := hronto t
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcov (mem_univ z))
    exact ⟨j,mem_image_of_mem r hj⟩
  · intro j t ht
    obtain ⟨z,hz,rfl⟩ := ht
    exact hside j hz
  · intro j
    let f : {z : Z // z ∈ (W j : Set Z)} → K j :=
      fun z => ⟨r z.val,mem_image_of_mem r z.property⟩
    have hf : Continuous f :=
      (hr.comp continuous_subtype_val).subtype_mk (fun z => mem_image_of_mem r z.property)
    have hfo : Function.Surjective f := by
      intro t
      obtain ⟨z,hz,heq⟩ := t.property
      exact ⟨⟨z,hz⟩,Subtype.ext heq⟩
    apply IsOpenMap.of_comp hf hfo
    simpa only [Function.comp_def,f] using
      hopen.comp (W j).isOpen.isOpenMap_subtype_val


/-- The actual counterexample uses the previously constructed existential MAD
family, with no assumed no-separator input. -/
theorem exists_compact_open_map_no_finite_closed_refinement :
    ∃ (A : Set (Set ℕ)) (ell : A → unitInterval),
      ADFamily A ∧ (∀ a : A, ConvergesOn natValue a.val (ell a)) ∧
      IsClosed (literalSpace A natValue ell) ∧ IsCompact (literalSpace A natValue ell) ∧
      Continuous (projection A natValue ell) ∧ IsOpenMap (projection A natValue ell) ∧
      Function.Surjective (projection A natValue ell) ∧
      (let U : Bool → Set (Space A natValue ell) := fun b =>
        if b then {x | (1:ℝ)/3 < (x.val.2.1 : ℝ)}
        else {x | (x.val.2.1 : ℝ) < (2:ℝ)/3};
        (∀ b, IsOpen (U b)) ∧ (∀ x, ∃ b, x ∈ U b) ∧
          ¬ HasFiniteClosedRefinement (projection A natValue ell) U) ∧
      ¬ HasOpenZeroDimensionalResolution (projection A natValue ell) := by
  classical
  obtain ⟨N,hbranch,hmad,hconv,hideal,hno⟩ := exists_mad_no_threshold_partitioner
  let A : Set (Set ℕ) := range N
  let repr (a : A) : Branch := Classical.choose a.property
  have hrepr (a : A) : N (repr a) = a.val := Classical.choose_spec a.property
  let ell : A → unitInterval := fun a => limitValue (repr a)
  have had : ADFamily A := hmad.1
  have hc (a : A) : ConvergesOn natValue a.val (ell a) := by
    rw [← hrepr a]
    exact hconv (repr a)
  have hnoA : ¬ ∃ D : Set ℕ, Partitions (fun a : A => a.val) D ∧
      {n | (natValue n : ℝ) ≤ (1:ℝ)/3} ⊆ D ∧
      D ⊆ {n | (natValue n : ℝ) < (2:ℝ)/3} := by
    rintro ⟨D,hD,hL,hU⟩
    apply hno
    exact ⟨D,(fun x => hD ⟨N x,mem_range_self x⟩),hL,hU⟩
  obtain ⟨hclosed,hcompact,hp,hopen,honto,hs,hsclopen⟩ :=
    literal_closed_compact_open_surjection A natValue ell had.2 hc
  let U : Bool → Set (Space A natValue ell) := fun b =>
    if b then {x | (1:ℝ)/3 < (x.val.2.1 : ℝ)}
    else {x | (x.val.2.1 : ℝ) < (2:ℝ)/3}
  have hv : Continuous (fun x : Space A natValue ell => (x.val.2.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.fst.comp continuous_subtype_val)
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · exact isOpen_lt hv continuous_const
    · exact isOpen_lt continuous_const hv
  have hcover : ∀ x, ∃ b, x ∈ U b := by
    intro x
    by_cases h : (x.val.2.1 : ℝ) < (2:ℝ)/3
    · exact ⟨false,h⟩
    · refine ⟨true,?_⟩
      exact lt_of_lt_of_le (by norm_num : (1:ℝ)/3 < (2:ℝ)/3) (le_of_not_gt h)
  have hnoRef : ¬ HasFiniteClosedRefinement (projection A natValue ell) U :=
    literal_no_refinement A natValue ell had hc hnoA
  refine ⟨A,ell,had,hc,hclosed,hcompact,hp,hopen,honto,⟨hU,hcover,hnoRef⟩,?_⟩
  rintro ⟨Z,tZ,hcompactZ,hT2Z,hTDZ,r,hr,hronto,hrOpen⟩
  let : TopologicalSpace Z := tZ
  let : CompactSpace Z := hcompactZ
  let : T2Space Z := hT2Z
  let : TotallyDisconnectedSpace Z := hTDZ
  exact hnoRef (closed_refinement_of_open_resolution
    (projection A natValue ell) r hr hronto hrOpen U hU hcover)

end D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample
