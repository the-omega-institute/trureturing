/- GID: D5/S3/Topology/StoneCech/SectionClosedGraph
   generality: G
   mirror-B: D5/B/S3/Topology/StoneCech/SectionClosedGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual section-dense selectors carry a closed graph with finite unbounded cliques. -/

/-
# Closed fibre graphs on actual principal extensions

The vertex space is the actual principal extension of a section-good selector.
Adjacency is principal-only, between distinct points in the same q-fibre.
Closedness concerns the entire product, including its diagonal. Finite fibres
are used for clique finiteness and countable compactness, not for closedness.
-/

import D5.S3.Topology.StoneCech.SectionDenseSelector
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Compactness.CountablyCompact
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Function Topology Cardinal
open D5.S3.Topology.StoneCech.SectionGoodFreshClusters
open D5.S3.Topology.StoneCech.SectionDenseSelector

namespace D5.S3.Topology.StoneCech.SectionClosedGraph

variable {A B : Type}

/-- The subspace of principal ultrafilters together with the actual selector. -/
def principalExtension (Y : Set (Ultrafilter A)) : Set (Ultrafilter A) :=
  range (pure : A → Ultrafilter A) ∪ Y

/-- The principal embedding into the extension. -/
def principalEmbedding (Y : Set (Ultrafilter A)) : A ↪ principalExtension Y where
  toFun a := ⟨pure a, Or.inl ⟨a, rfl⟩⟩
  inj' := by
    intro a b h
    exact Ultrafilter.pure_injective (congrArg Subtype.val h)

/-- Distinct principal vertices are adjacent exactly in the same q-fibre. -/
def fibreGraph (q : A → B) (Y : Set (Ultrafilter A)) :
    SimpleGraph (principalExtension Y) where
  Adj x y := ∃ a b : A,
    x.val = pure a ∧ y.val = pure b ∧ a ≠ b ∧ q a = q b
  symm.symm := by
    rintro x y ⟨a, b, ha, hb, hab, hq⟩
    exact ⟨b, a, hb, ha, hab.symm, hq.symm⟩
  loopless.irrefl := by
    rintro x ⟨a, b, ha, hb, hab, _⟩
    exact hab (Ultrafilter.pure_injective (ha.symm.trans hb))

private def basic (Y : Set (Ultrafilter A)) (S : Set A) :
    Set (principalExtension Y) := {x | S ∈ x.val}

private theorem basic_isOpen (Y : Set (Ultrafilter A)) (S : Set A) :
    IsOpen (basic Y S) :=
  (ultrafilter_isOpen_basic S).preimage continuous_subtype_val

private theorem free_ne_pure {u : Ultrafilter A}
    (hu : (u : Filter A) ≤ cofinite) (a : A) : u ≠ pure a := by
  intro h
  have hc : ({a} : Set A)ᶜ ∈ u := hu (finite_singleton a).compl_mem_cofinite
  rw [h] at hc
  simpa using hc

/-- A section meets each fibre in at most one point; freeness excludes it. -/
private theorem fibre_compl_mem {q : A → B} {u : Ultrafilter A}
    (hu : u ∈ SectionGood q) (b : B) : (q ⁻¹' {b})ᶜ ∈ u := by
  apply Ultrafilter.compl_mem_iff_notMem.mpr
  intro hfibre
  obtain ⟨S, hS, hSinj⟩ := hu.2
  have hsmall : (S ∩ q ⁻¹' {b}).Subsingleton := by
    intro a ha c hc
    apply hSinj ha.1 hc.1
    exact (mem_singleton_iff.mp ha.2).trans (mem_singleton_iff.mp hc.2).symm
  have hc : (S ∩ q ⁻¹' {b})ᶜ ∈ u := hu.1 hsmall.finite.compl_mem_cofinite
  obtain ⟨a, ha, hna⟩ := u.nonempty_of_mem (inter_mem (inter_mem hS hfibre) hc)
  exact hna ha

private theorem exists_separating_set {u v : Ultrafilter B} (hne : u ≠ v) :
    ∃ T : Set B, T ∈ u ∧ Tᶜ ∈ v := by
  classical
  by_contra! h
  have hle : (v : Filter B) ≤ (u : Filter B) := by
    intro T hT
    exact Ultrafilter.compl_notMem_iff.mp (h T hT)
  exact hne (Ultrafilter.eq_of_le hle).symm

private theorem basic_prod_nonedge (q : A → B) (Y : Set (Ultrafilter A))
    (S T : Set A)
    (hST : ∀ a ∈ S, ∀ b ∈ T, a ≠ b → q a ≠ q b) :
    basic Y S ×ˢ basic Y T ⊆
      {p : principalExtension Y × principalExtension Y |
        ¬ (fibreGraph q Y).Adj p.1 p.2} := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨a, b, ha, hb, hab, hq⟩
  change S ∈ x.val at hx
  change T ∈ y.val at hy
  have hSa : a ∈ S := Ultrafilter.mem_pure.mp (ha ▸ hx)
  have hTb : b ∈ T := Ultrafilter.mem_pure.mp (hb ▸ hy)
  exact hST a hSa b hTb hab hq

/-- Full-product closedness, without any finite-fibre assumption. The equal
selector case uses a section square and therefore also treats the diagonal. -/
theorem isClosed_fibreGraph_adj (q : A → B) (Y : Set (Ultrafilter A))
    (hgood : Y ⊆ SectionGood q) (hproj : Set.InjOn (Ultrafilter.map q) Y) :
    IsClosed {p : principalExtension Y × principalExtension Y |
      (fibreGraph q Y).Adj p.1 p.2} := by
  classical
  apply isOpen_compl_iff.mp
  apply isOpen_prod_iff.mpr
  intro x y hxy
  change ¬ (fibreGraph q Y).Adj x y at hxy
  rcases x.property with hx | hx
  · obtain ⟨a, ha⟩ := hx
    rcases y.property with hy | hy
    · obtain ⟨b, hb⟩ := hy
      refine ⟨basic Y {a}, basic Y {b}, basic_isOpen Y {a},
        basic_isOpen Y {b}, ?_, ?_, ?_⟩
      · change {a} ∈ x.val
        rw [← ha]
        simp
      · change {b} ∈ y.val
        rw [← hb]
        simp
      · apply basic_prod_nonedge
        intro c hc d hd hcd hq
        have hca : c = a := mem_singleton_iff.mp hc
        have hdb : d = b := mem_singleton_iff.mp hd
        exact hxy ⟨c, d,
          ha.symm.trans (congrArg (pure : A → Ultrafilter A) hca.symm),
          hb.symm.trans (congrArg (pure : A → Ultrafilter A) hdb.symm), hcd, hq⟩
    · refine ⟨basic Y {a}, basic Y (q ⁻¹' {q a})ᶜ, basic_isOpen Y {a},
        basic_isOpen Y (q ⁻¹' {q a})ᶜ, ?_, fibre_compl_mem (hgood hy) (q a), ?_⟩
      · change {a} ∈ x.val
        rw [← ha]
        simp
      · apply basic_prod_nonedge
        intro c hc d hd _ hq
        apply hd
        change q d = q a
        exact hq.symm.trans (congrArg q (mem_singleton_iff.mp hc))
  · rcases y.property with hy | hy
    · obtain ⟨b, hb⟩ := hy
      refine ⟨basic Y (q ⁻¹' {q b})ᶜ, basic Y {b},
        basic_isOpen Y (q ⁻¹' {q b})ᶜ, basic_isOpen Y {b},
        fibre_compl_mem (hgood hx) (q b), ?_, ?_⟩
      · change {b} ∈ y.val
        rw [← hb]
        simp
      · apply basic_prod_nonedge
        intro c hc d hd _ hq
        apply hc
        change q c = q b
        exact hq.trans (congrArg q (mem_singleton_iff.mp hd))
    · by_cases hval : x.val = y.val
      · obtain ⟨S, hS, hSinj⟩ := (hgood hx).2
        refine ⟨basic Y S, basic Y S, basic_isOpen Y S, basic_isOpen Y S,
          hS, ?_, ?_⟩
        · change S ∈ y.val
          simpa [hval] using hS
        · apply basic_prod_nonedge
          intro a ha b hb hab hq
          exact hab (hSinj ha hb hq)
      · have hneq : Ultrafilter.map q x.val ≠ Ultrafilter.map q y.val := by
          intro h
          exact hval (hproj hx hy h)
        obtain ⟨T, hTx, hTy⟩ := exists_separating_set hneq
        refine ⟨basic Y (q ⁻¹' T), basic Y (q ⁻¹' Tᶜ),
          basic_isOpen Y (q ⁻¹' T), basic_isOpen Y (q ⁻¹' Tᶜ),
          Ultrafilter.mem_map.mp hTx, Ultrafilter.mem_map.mp hTy, ?_⟩
        apply basic_prod_nonedge
        intro a ha b hb _ hq
        exact hb (hq ▸ ha)

/-- The convergence of principal ultrafilters along a free ultrafilter yields
an actual punctured accumulation point, not a sequential-compactness claim. -/
private theorem free_accPt_pure_image {u : Ultrafilter A}
    (hu : (u : Filter A) ≤ cofinite) {S : Set A} (hS : S ∈ u) :
    AccPt u (𝓟 ((pure : A → Ultrafilter A) '' S)) := by
  apply accPt_iff_nhds.mpr
  intro W hW
  have hpre : (pure : A → Ultrafilter A) ⁻¹' W ∈ u := u.tendsto_pure_self hW
  obtain ⟨a, haS, haW⟩ := u.nonempty_of_mem (inter_mem hS hpre)
  refine ⟨pure a, ⟨haW, ⟨a, haS, rfl⟩⟩, ?_⟩
  intro h
  exact free_ne_pure hu a h.symm

/-- Finite fibres and section density make the actual principal extension
countably compact. An infinite subset is handled in the ambient T₁ space. -/
theorem isCountablyCompact_principalExtension (q : A → B)
    (Y : Set (Ultrafilter A)) (hgood : Y ⊆ SectionGood q)
    (hY : IsCountablyCompact Y)
    (hdense : ∀ S : Set A, S.Infinite → Set.InjOn q S → ∃ u ∈ Y, S ∈ u)
    (hfinite : ∀ b : B, (q ⁻¹' {b}).Finite) :
    IsCountablyCompact (principalExtension Y) := by
  classical
  apply isCountablyCompact_iff_infinite_subset_has_accPt.mpr
  intro C hCX hC
  by_cases hCY : (C ∩ Y).Infinite
  · obtain ⟨u, hu, hacc⟩ := hY.exists_accPt_of_infinite inter_subset_right hCY
    exact ⟨u, Or.inr hu, hacc.mono (principal_mono.mpr inter_subset_left)⟩
  · have hCYfin : (C ∩ Y).Finite := not_not.mp hCY
    have hCP : (C ∩ range (pure : A → Ultrafilter A)).Infinite := by
      intro hfin
      apply hC
      apply (hfin.union hCYfin).subset
      intro u hu
      rcases hCX hu with hp | hy
      · exact Or.inl ⟨hu, hp⟩
      · exact Or.inr ⟨hu, hy⟩
    let P : Set A := (pure : A → Ultrafilter A) ⁻¹' C
    have hPeq : (pure : A → Ultrafilter A) '' P =
        C ∩ range (pure : A → Ultrafilter A) := by
      ext u
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨ha, ⟨a, rfl⟩⟩
      · rintro ⟨hu, a, rfl⟩
        exact ⟨a, hu, rfl⟩
    have hP : P.Infinite := by
      apply Set.Infinite.of_image (pure : A → Ultrafilter A)
      rwa [hPeq]
    have hqP : (q '' P).Infinite := by
      intro hfin
      apply hP
      apply (hfin.preimage' (fun b _ => hfinite b)).subset
      intro a ha
      exact mem_image_of_mem q ha
    obtain ⟨S, hSP, hSinj, hSim⟩ :=
      (Set.surjOn_image q P).exists_subset_injOn_image_eq
    have hS : S.Infinite := by
      apply Set.Infinite.of_image q
      rwa [hSim]
    obtain ⟨u, huY, hSu⟩ := hdense S hS hSinj
    refine ⟨u, Or.inr huY, (free_accPt_pure_image (hgood huY).1 hSu).mono ?_⟩
    apply principal_mono.mpr
    rintro v ⟨a, ha, rfl⟩
    exact hSP ha

/-- Every clique is finite when every fibre is finite, including empty and
singleton cliques. A larger clique is forced into one principal fibre. -/
theorem fibreGraph_clique_finite (q : A → B) (Y : Set (Ultrafilter A))
    (hfinite : ∀ b : B, (q ⁻¹' {b}).Finite)
    {K : Set (principalExtension Y)} (hK : (fibreGraph q Y).IsClique K) :
    K.Finite := by
  classical
  by_cases hsub : K.Subsingleton
  · exact hsub.finite
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hsub
  obtain ⟨a, b, hxa, _, _, _⟩ := hK hx hy hxy
  apply ((hfinite (q a)).image (principalEmbedding Y)).subset
  intro z hz
  by_cases hzx : z = x
  · refine ⟨a, ?_, ?_⟩
    · change q a = q a
      rfl
    · apply Subtype.ext
      exact hxa.symm.trans (congrArg Subtype.val hzx).symm
  · obtain ⟨c, d, hxc, hzd, _, hqcd⟩ := hK hx hz (Ne.symm hzx)
    have hca : c = a := Ultrafilter.pure_injective (hxc.symm.trans hxa)
    refine ⟨d, ?_, ?_⟩
    · change q d = q a
      exact hqcd.symm.trans (congrArg q hca)
    · apply Subtype.ext
      exact hzd.symm

/-- The actual selector supplier constructs the countably compact vertex
space and its closed graph. Unbounded finite fibres give finite cliques of
every prescribed size; no selector existence premise is added. -/
theorem exists_countablyCompact_closed_fibreGraph [Countable A] (q : A → B)
    (hfinite : ∀ b : B, (q ⁻¹' {b}).Finite)
    (hunbounded : ∀ n : ℕ, ∃ b : B, n ≤ (q ⁻¹' {b}).ncard) :
    ∃ Y : Set (Ultrafilter A),
      Y ⊆ SectionGood q ∧ #Y ≤ 𝔠 ∧ Set.InjOn (Ultrafilter.map q) Y ∧
      IsCountablyCompact Y ∧
      (∀ S : Set A, S.Infinite → Set.InjOn q S → ∃ u ∈ Y, S ∈ u) ∧
      CountablyCompactSpace (principalExtension Y) ∧
      IsClosed {p : principalExtension Y × principalExtension Y |
        (fibreGraph q Y).Adj p.1 p.2} ∧
      (∀ K : Set (principalExtension Y), (fibreGraph q Y).IsClique K → K.Finite) ∧
      (∀ n : ℕ, ∃ K : Set (principalExtension Y),
        K.Finite ∧ (fibreGraph q Y).IsClique K ∧ K.ncard = n) := by
  classical
  obtain ⟨Y, hgood, hsmall, hproj, hY, hdense⟩ :=
    exists_countablyCompact_sectionDense_selector q
  refine ⟨Y, hgood, hsmall, hproj, hY, hdense,
    isCountablyCompact_iff_countablyCompactSpace.mp
      (isCountablyCompact_principalExtension q Y hgood hY hdense hfinite),
    isClosed_fibreGraph_adj q Y hgood hproj,
    fun K hK => fibreGraph_clique_finite q Y hfinite hK, ?_⟩
  intro n
  obtain ⟨b, hb⟩ := hunbounded n
  obtain ⟨T, hT, hcard⟩ := Set.exists_subset_card_eq hb
  refine ⟨principalEmbedding Y '' T, ((hfinite b).subset hT).image _, ?_, ?_⟩
  · rintro x ⟨a, ha, rfl⟩ z ⟨c, hc, rfl⟩ hne
    refine ⟨a, c, rfl, rfl, ?_, ?_⟩
    · intro h
      exact hne (congrArg (principalEmbedding Y) h)
    · have hqa : q a = b := hT ha
      have hqc : q c = b := hT hc
      exact hqa.trans hqc.symm
  · rw [Set.ncard_image_of_injective T (principalEmbedding Y).injective]
    exact hcard

end D5.S3.Topology.StoneCech.SectionClosedGraph
