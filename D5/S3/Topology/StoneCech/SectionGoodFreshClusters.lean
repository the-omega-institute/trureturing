/- GID: D5/S3/Topology/StoneCech/SectionGoodFreshClusters
   generality: G
   mirror-B: D5/B/S3/Topology/StoneCech/SectionGoodFreshClusters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Section-good ultrafilters supply fresh projected accumulation points. -/

import Mathlib.Topology.NatEmbedding
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.ClusterPt
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Finite
import Mathlib.SetTheory.Cardinal.Continuum
import D5.S3.Topology.StoneCech.FreeUltrafilterCardinality

/-!
# Fresh projected accumulation points on actual sections

For an arbitrary map, a section-good ultrafilter is free and contains a set
on which the map is injective. An injective sequence of distinct projected
values supplies more than continuum many projected accumulation values.

The supports are extracted in the actual image subspace, lifted to ambient
membership clopens, and disjointized by finite differences. Actual section
witnesses are spliced along these supports. The ultrafilter monad then
recovers every index set from the projected limit, including for principal
index ultrafilters. Free index ultrafilters give punctured accumulation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Function Topology Cardinal

namespace D5.S3.Topology.StoneCech.SectionGoodFreshClusters

/-- Free ultrafilters containing an actual injectivity set for `q`. -/
def SectionGood {A B : Type} (q : A → B) : Set (Ultrafilter A) :=
  {u | (u : Filter A) ≤ cofinite ∧ ∃ S ∈ u, Set.InjOn q S}

/-- Relative separation is converted to literal disjointness in the base set.
Only finitely many earlier clopens are removed from the support at each index. -/
private theorem extract_disjoint_supports {B : Type} (w : ℕ → Ultrafilter B)
    (hw : Function.Injective w) :
    ∃ k : ℕ → ℕ, Function.Injective k ∧ ∃ D : ℕ → Set B,
      (∀ n, D n ∈ w (k n)) ∧ Pairwise (Disjoint on D) := by
  classical
  let P : Set (Ultrafilter B) := range w
  let wp : ℕ → P := fun n => ⟨w n, mem_range_self n⟩
  have hwp : Function.Injective wp := by
    intro n m h
    exact hw (congrArg Subtype.val h)
  haveI : Infinite P := Infinite.of_injective wp hwp
  obtain ⟨U, hUinf, hUopen, hUdisj⟩ :=
    exists_seq_infinite_isOpen_pairwise_disjoint P
  choose p hp using fun n => (hUinf n).nonempty
  have hpinj : Function.Injective p := by
    intro n m h
    by_contra hnm
    exact Set.disjoint_left.mp (hUdisj hnm) (hp n) (h.symm ▸ hp m)
  have ambient (n : ℕ) :
      ∃ O : Set (Ultrafilter B), IsOpen O ∧
        (Subtype.val : P → Ultrafilter B) ⁻¹' O = U n :=
    (Topology.IsInducing.subtypeVal.isOpen_iff).mp (hUopen n)
  choose O hOopen hOeq using ambient
  have hpO (n : ℕ) : (p n).val ∈ O n := by
    change p n ∈ (Subtype.val : P → Ultrafilter B) ⁻¹' O n
    rw [hOeq n]
    exact hp n
  have basic (n : ℕ) : ∃ C : Set B, C ∈ (p n).val ∧
      {u : Ultrafilter B | C ∈ u} ⊆ O n := by
    obtain ⟨V, hV, hpV, hVO⟩ :=
      ultrafilterBasis_is_basis.isOpen_iff.mp (hOopen n) (p n).val (hpO n)
    obtain ⟨C, rfl⟩ := hV
    exact ⟨C, hpV, hVO⟩
  choose C hCp hCO using basic
  have hCmiss (n m : ℕ) (hnm : n ≠ m) : C m ∉ (p n).val := by
    intro hmem
    have hO : (p n).val ∈ O m := hCO m hmem
    have hU : p n ∈ U m := by
      rw [← hOeq m]
      exact hO
    exact Set.disjoint_left.mp (hUdisj hnm) (hp n) hU
  let D : ℕ → Set B := fun n => C n \ ⋃ m ∈ Finset.range n, C m
  have hDp (n : ℕ) : D n ∈ (p n).val := by
    have hfinite : (⋂ m ∈ Finset.range n, (C m)ᶜ) ∈ (p n).val := by
      apply (biInter_finset_mem (Finset.range n)).mpr
      intro m hm
      exact Ultrafilter.compl_mem_iff_notMem.mpr
        (hCmiss n m (Nat.ne_of_gt (Finset.mem_range.mp hm)))
    apply mem_of_superset (inter_mem (hCp n) hfinite)
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxunion
    obtain ⟨m, hm⟩ := mem_iUnion.mp hxunion
    obtain ⟨hmrange, hxm⟩ := mem_iUnion.mp hm
    exact (mem_iInter.mp (mem_iInter.mp hx.2 m) hmrange) hxm
  have hDlt {n m : ℕ} (hnm : n < m) : Disjoint (D n) (D m) := by
    apply Set.disjoint_left.mpr
    intro x hxn hxm
    exact hxm.2 (mem_iUnion.mpr ⟨n,
      mem_iUnion.mpr ⟨Finset.mem_range.mpr hnm, hxn.1⟩⟩)
  have hDdisj : Pairwise (Disjoint on D) := by
    intro n m hnm
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hDlt h
    · exact (hDlt h).symm
  choose k hk using fun n => (p n).property
  refine ⟨k, ?_, D, ?_, hDdisj⟩
  · intro n m h
    apply hpinj
    apply Subtype.ext
    exact (hk n).symm.trans ((congrArg w h).trans (hk m))
  · intro n
    rw [hk n]
    exact hDp n

/-- The union uses the given section witnesses and the disjoint base supports. -/
private theorem splice_sections {A B : Type} (q : A → B)
    (v : ℕ → Ultrafilter A) (hv : ∀ n, v n ∈ SectionGood q)
    (D : ℕ → Set B) (hD : ∀ n, D n ∈ Ultrafilter.map q (v n))
    (hdisj : Pairwise (Disjoint on D)) :
    ∃ S : Set A, Set.InjOn q S ∧ ∀ n, S ∈ v n := by
  classical
  choose T hTmem hTinj using fun n => (hv n).2
  let S : Set A := ⋃ n, T n ∩ q ⁻¹' D n
  refine ⟨S, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    obtain ⟨m, hym⟩ := mem_iUnion.mp hy
    have hnm : n = m := by
      by_contra hnm
      exact Set.disjoint_left.mp (hdisj hnm) hxn.2 (hxy.symm ▸ hym.2)
    subst m
    exact hTinj n hxn.1 hym.1 hxy
  · intro n
    apply mem_of_superset (inter_mem (hTmem n) (Ultrafilter.mem_map.mp (hD n)))
    exact subset_iUnion (fun m => T m ∩ q ⁻¹' D m) n

private def limit {A : Type} (v : ℕ → Ultrafilter A)
    (r : Ultrafilter ℕ) : Ultrafilter A :=
  joinM (Ultrafilter.map v r)

/-- This is the membership law of the actual monadic join, not an assumed limit law. -/
private theorem limit_mem {A : Type} (v : ℕ → Ultrafilter A)
    (r : Ultrafilter ℕ) (H : Set A) :
    H ∈ limit v r ↔ {n | H ∈ v n} ∈ r := by
  rfl

private theorem limit_good {A B : Type} (q : A → B)
    (v : ℕ → Ultrafilter A) (hv : ∀ n, v n ∈ SectionGood q)
    (S : Set A) (hSinj : Set.InjOn q S) (hSmem : ∀ n, S ∈ v n)
    (r : Ultrafilter ℕ) : limit v r ∈ SectionGood q := by
  refine ⟨?_, S, ?_, hSinj⟩
  · intro H hH
    apply (limit_mem v r H).mpr
    exact Filter.Eventually.of_forall (fun n => (hv n).1 hH)
  · apply (limit_mem v r S).mpr
    exact Filter.Eventually.of_forall hSmem

/-- A union of support blocks encodes exactly the selected indices at every term. -/
private theorem support_union_mem_iff {B : Type} (p : ℕ → Ultrafilter B)
    (D : ℕ → Set B) (hD : ∀ n, D n ∈ p n)
    (hdisj : Pairwise (Disjoint on D)) (J : Set ℕ) (n : ℕ) :
    (⋃ i ∈ J, D i) ∈ p n ↔ n ∈ J := by
  classical
  constructor
  · intro hJ
    by_contra hnJ
    obtain ⟨x, hxn, hxJ⟩ := (p n).nonempty_of_mem (inter_mem (hD n) hJ)
    obtain ⟨m, hm⟩ := mem_iUnion.mp hxJ
    obtain ⟨hmJ, hxm⟩ := mem_iUnion.mp hm
    have hmn : m ≠ n := by
      intro h
      exact hnJ (h ▸ hmJ)
    exact Set.disjoint_left.mp (hdisj hmn) hxm hxn
  · intro hnJ
    apply mem_of_superset (hD n)
    intro x hx
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hnJ, hx⟩⟩

/-- The readout works for all index ultrafilters, including principal ones. -/
private theorem limit_projection_readout {A B : Type} (q : A → B)
    (v : ℕ → Ultrafilter A) (D : ℕ → Set B)
    (hD : ∀ n, D n ∈ Ultrafilter.map q (v n))
    (hdisj : Pairwise (Disjoint on D)) (r : Ultrafilter ℕ) (J : Set ℕ) :
    (⋃ i ∈ J, D i) ∈ Ultrafilter.map q (limit v r) ↔ J ∈ r := by
  rw [Ultrafilter.mem_map, limit_mem]
  have hindices : {n | q ⁻¹' (⋃ i ∈ J, D i) ∈ v n} = J := by
    apply Set.ext
    intro n
    exact Ultrafilter.mem_map.symm.trans
      (support_union_mem_iff (fun n => Ultrafilter.map q (v n)) D hD hdisj J n)
  rw [hindices]

private theorem projection_limit_injective {A B : Type} (q : A → B)
    (v : ℕ → Ultrafilter A) (D : ℕ → Set B)
    (hD : ∀ n, D n ∈ Ultrafilter.map q (v n))
    (hdisj : Pairwise (Disjoint on D)) :
    Function.Injective (fun r : Ultrafilter ℕ => Ultrafilter.map q (limit v r)) := by
  intro r s hrs
  apply Ultrafilter.ext
  intro J
  calc
    J ∈ r ↔ (⋃ i ∈ J, D i) ∈ Ultrafilter.map q (limit v r) :=
      (limit_projection_readout q v D hD hdisj r J).symm
    _ ↔ (⋃ i ∈ J, D i) ∈ Ultrafilter.map q (limit v s) := by
      change Ultrafilter.map q (limit v r) = Ultrafilter.map q (limit v s) at hrs
      rw [hrs]
    _ ↔ J ∈ s := limit_projection_readout q v D hD hdisj s J

/-- Cofinite preimages remove the limiting point from each neighborhood witness. -/
private theorem limit_accPt {A : Type} (v : ℕ → Ultrafilter A)
    (hinj : Function.Injective v) (r : Ultrafilter ℕ)
    (hr : (r : Filter ℕ) ≤ cofinite) :
    AccPt (limit v r) (𝓟 (range v)) := by
  have hconv : (Ultrafilter.map v r : Filter (Ultrafilter A)) ≤ 𝓝 (limit v r) :=
    ultrafilter_converges_iff.mpr rfl
  have hcof : Filter.map v (r : Filter ℕ) ≤ cofinite :=
    (Filter.map_mono hr).trans hinj.tendsto_cofinite
  have hneq : {n | v n ≠ limit v r} ∈ r := by
    have hc : ({limit v r} : Set (Ultrafilter A))ᶜ ∈ cofinite :=
      (Set.finite_singleton (limit v r)).compl_mem_cofinite
    exact hcof hc
  apply accPt_iff_nhds.mpr
  intro W hW
  have hWindex : {n | v n ∈ W} ∈ r := hconv hW
  obtain ⟨n, hnW, hnne⟩ := r.nonempty_of_mem (inter_mem hWindex hneq)
  exact ⟨v n, ⟨hnW, mem_range_self n⟩, hnne⟩

/-- For an arbitrary projection, section-good ultrafilters supply a genuine
accumulation point whose projected value avoids any continuum-small set. -/
theorem exists_sectionGood_fresh_accPt {A B : Type} (q : A → B)
    (e : ℕ ↪ Ultrafilter A) (he : range e ⊆ SectionGood q)
    (hq : Function.Injective (fun n => Ultrafilter.map q (e n)))
    (F : Set (Ultrafilter B)) (hF : #F ≤ 𝔠) :
    ∃ u ∈ SectionGood q,
      AccPt u (𝓟 (range e)) ∧ Ultrafilter.map q u ∉ F := by
  classical
  obtain ⟨k, hk, D, hD, hdisj⟩ :=
    extract_disjoint_supports (fun n => Ultrafilter.map q (e n)) hq
  let v : ℕ → Ultrafilter A := fun n => e (k n)
  have hvgood (n : ℕ) : v n ∈ SectionGood q := he ⟨k n, rfl⟩
  have hvinj : Function.Injective v := by
    intro n m h
    exact hk (e.injective h)
  have hD' (n : ℕ) : D n ∈ Ultrafilter.map q (v n) := hD n
  obtain ⟨S, hSinj, hSmem⟩ := splice_sections q v hvgood D hD' hdisj
  have hgood (r : Ultrafilter ℕ) : limit v r ∈ SectionGood q :=
    limit_good q v hvgood S hSinj hSmem r
  have hprojection := projection_limit_injective q v D hD' hdisj
  have hfresh : ∃ r : {r : Ultrafilter ℕ // (r : Filter ℕ) ≤ cofinite},
      Ultrafilter.map q (limit v r.val) ∉ F := by
    by_contra! hall
    let f : {r : Ultrafilter ℕ // (r : Filter ℕ) ≤ cofinite} → F :=
      fun r => ⟨Ultrafilter.map q (limit v r.val), hall r⟩
    have hf : Function.Injective f := by
      intro r s hrs
      apply Subtype.ext
      exact hprojection (congrArg Subtype.val hrs)
    have hcard : 2 ^ 𝔠 ≤ 𝔠 :=
      (D5.S3.Topology.StoneCech.FreeUltrafilterCardinality.continuum_power_le_mk_freeUltrafilter_nat).trans
        ((Cardinal.mk_le_of_injective hf).trans hF)
    exact (not_le_of_gt (Cardinal.cantor 𝔠)) hcard
  obtain ⟨r, hr⟩ := hfresh
  refine ⟨limit v r.val, hgood r.val, ?_, hr⟩
  apply (limit_accPt v hvinj r.val r.property).mono
  apply Filter.principal_mono.mpr
  rintro _ ⟨n, rfl⟩
  exact ⟨k n, rfl⟩

end D5.S3.Topology.StoneCech.SectionGoodFreshClusters
