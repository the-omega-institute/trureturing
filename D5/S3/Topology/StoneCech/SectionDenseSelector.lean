/- GID: D5/S3/Topology/StoneCech/SectionDenseSelector
   generality: G
   mirror-B: D5/B/S3/Topology/StoneCech/SectionDenseSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual infinite sections seed a countably compact injective ultrafilter selector. -/

import D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure
import D5.S3.Topology.StoneCech.SectionGoodFreshClusters

/-!
# Section-dense selectors on a countable source

For each infinite injectivity set of an arbitrary map, push free ultrafilters
forward along an actual embedding into that set. The composite embedding
through the projection gives an injective family of projected values. The
free-ultrafilter lower bound and Cantor's theorem let each task avoid any
continuum-small forbidden set. Simultaneous fresh choice constructs the seed;
the fresh-cluster closing-off theorem preserves its section density.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Function Topology Cardinal
open D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure
open D5.S3.Topology.StoneCech.SectionGoodFreshClusters

namespace D5.S3.Topology.StoneCech.SectionDenseSelector

/-- An actual section embedding gives more than continuum many possible
projected values, so one remains outside a continuum-small forbidden set. -/
private theorem exists_section_fresh {A B : Type} (q : A → B)
    (S : Set A) (hS : S.Infinite) (hSinj : Set.InjOn q S)
    (F : Set (Ultrafilter B)) (hF : #F ≤ 𝔠) :
    ∃ u ∈ SectionGood q, S ∈ u ∧ Ultrafilter.map q u ∉ F := by
  classical
  let es : ℕ ↪ S := hS.natEmbedding S
  let e : ℕ ↪ A := es.trans (Function.Embedding.subtype S)
  have he_mem (n : ℕ) : e n ∈ S := (es n).property
  have hqe : Function.Injective (q ∘ e) := by
    intro n m h
    exact e.injective (hSinj (he_mem n) (he_mem m) h)
  let R := {r : Ultrafilter ℕ // (r : Filter ℕ) ≤ cofinite}
  let lift : R → Ultrafilter A := fun r => Ultrafilter.map e r.val
  have lift_free (r : R) : (lift r : Filter A) ≤ cofinite := by
    change Filter.map e (r.val : Filter ℕ) ≤ cofinite
    exact (Filter.map_mono r.property).trans e.injective.tendsto_cofinite
  have lift_section (r : R) : S ∈ lift r := by
    change S ∈ Ultrafilter.map e r.val
    apply Ultrafilter.mem_map.mpr
    exact Filter.Eventually.of_forall he_mem
  have lift_good (r : R) : lift r ∈ SectionGood q :=
    ⟨lift_free r, S, lift_section r, hSinj⟩
  have projection_injective :
      Function.Injective (fun r : R => Ultrafilter.map q (lift r)) := by
    intro r s hrs
    have hm : Ultrafilter.map (q ∘ e) r.val =
        Ultrafilter.map (q ∘ e) s.val := by
      simpa only [lift, Ultrafilter.map_map] using hrs
    apply Subtype.ext
    apply Ultrafilter.coe_injective
    apply Filter.map_injective hqe
    simpa only [Ultrafilter.coe_map] using
      congrArg (fun u : Ultrafilter B => (u : Filter B)) hm
  have fresh : ∃ r : R, Ultrafilter.map q (lift r) ∉ F := by
    by_contra! hall
    let f : R → F := fun r => ⟨Ultrafilter.map q (lift r), hall r⟩
    have hf : Function.Injective f := by
      intro r s hrs
      exact projection_injective (congrArg Subtype.val hrs)
    have hcard : 2 ^ 𝔠 ≤ 𝔠 :=
      (D5.S3.Topology.StoneCech.FreeUltrafilterCardinality.continuum_power_le_mk_freeUltrafilter_nat).trans
        ((Cardinal.mk_le_of_injective hf).trans hF)
    exact (not_le_of_gt (Cardinal.cantor 𝔠)) hcard
  obtain ⟨r, hr⟩ := fresh
  exact ⟨lift r, lift_good r, lift_section r, hr⟩

/-- Every infinite set on which `q` is injective belongs to a member of a
continuum-small, section-good, countably compact selector with distinct
projected values. Only the source is required to be countable. -/
theorem exists_countablyCompact_sectionDense_selector {A B : Type} [Countable A]
    (q : A → B) :
    ∃ Y : Set (Ultrafilter A),
      Y ⊆ SectionGood q ∧ #Y ≤ 𝔠 ∧ Set.InjOn (Ultrafilter.map q) Y ∧
      IsCountablyCompact Y ∧
      ∀ S : Set A, S.Infinite → Set.InjOn q S → ∃ u ∈ Y, S ∈ u := by
  classical
  let I := {S : Set A // S.Infinite ∧ Set.InjOn q S}
  let Q : Ultrafilter A → Ultrafilter B := Ultrafilter.map q
  let task : I → Set (Ultrafilter A) :=
    fun i => {u | u ∈ SectionGood q ∧ i.val ∈ u}
  have hI : #I ≤ 𝔠 := by
    calc
      #I ≤ #(Set A) := mk_subtype_le _
      _ = 2 ^ #A := mk_set
      _ ≤ 2 ^ ℵ₀ := power_le_power_left (by simp) (mk_le_aleph0 (α := A))
      _ = 𝔠 := two_power_aleph0
  have hempty : #(∅ : Set (Ultrafilter A)) ≤ 𝔠 := by simp
  have task_supply : ∀ i (F : Set (Ultrafilter B)), #F ≤ 𝔠 →
      ∃ u ∈ task i, Q u ∉ F := by
    intro i F hF
    obtain ⟨u, hgood, hsection, hfresh⟩ :=
      exists_section_fresh q i.val i.property.1 i.property.2 F hF
    exact ⟨u, ⟨hgood, hsection⟩, hfresh⟩
  obtain ⟨f, hf, hfinj, _⟩ :=
    exists_fresh_choice Q task (∅ : Set (Ultrafilter A)) hI hempty task_supply
  let seed : Set (Ultrafilter A) := range f
  have seed_good : seed ⊆ SectionGood q := by
    rintro u ⟨i, rfl⟩
    exact (hf i).1
  have seed_small : #seed ≤ 𝔠 := mk_range_le.trans hI
  have seed_inj : Set.InjOn Q seed := by
    rintro u ⟨i, rfl⟩ v ⟨j, rfl⟩ hij
    exact congrArg f (hfinj hij)
  have seed_dense : ∀ S : Set A, S.Infinite → Set.InjOn q S →
      ∃ u ∈ seed, S ∈ u := by
    intro S hS hSinj
    let i : I := ⟨S, hS, hSinj⟩
    exact ⟨f i, mem_range_self i, (hf i).2⟩
  have cluster_supply : FreshClusterSupply (SectionGood q) Q := by
    intro e he hqe F hF
    exact exists_sectionGood_fresh_accPt q e he hqe F hF
  obtain ⟨Y, hseed, hgood, hsmall, hinj, hcc⟩ :=
    exists_countablyCompact_injOn_extension (SectionGood q) Q cluster_supply seed
      seed_good seed_small seed_inj
  refine ⟨Y, hgood, hsmall, hinj, hcc, ?_⟩
  intro S hS hSinj
  obtain ⟨u, hu, hsection⟩ := seed_dense S hS hSinj
  exact ⟨u, hseed hu, hsection⟩

end D5.S3.Topology.StoneCech.SectionDenseSelector
