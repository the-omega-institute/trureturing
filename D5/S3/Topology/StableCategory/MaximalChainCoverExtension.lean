/- GID: D5/S3/Topology/StableCategory/MaximalChainCoverExtension
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/MaximalChainCoverExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maximal lower chains give a relative categorical two-cover extension. -/

import D5.S3.Topology.ConnectedCategoryGraft
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.NonemptyFiniteChains
import Mathlib.Order.Preorder.Finite

/-!
# Relative categorical two-cover of the chain subdivision

Sufficient direction of the relative two-cover criterion in
`graph-thickening-review.txt`, §4, for Question 6.3 of
https://arxiv.org/html/2609.39615v1#S6.Thmtheorem3.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.MaximalChainCoverExtension

open D5.S3.Topology.ConnectedCategoryGraft (Categorical HasCategoricalCover)
open PartialOrder (NonemptyFiniteChains)
open Relation (EqvGen)
open scoped Classical

variable {P : Type*} [PartialOrder P]

/-- The old region in the chain poset, formed by chains disjoint from `T`. -/
def chainsAvoiding (T : Set P) : Set (NonemptyFiniteChains P) :=
  {s | ∀ x ∈ s.finset, x ∉ T}

private def subchain (s : NonemptyFiniteChains P) {a : Finset P}
    (ha : a ⊆ s.finset) (hne : a.Nonempty) : NonemptyFiniteChains P :=
  ⟨a, hne, fun x y => s.comparable ⟨x.val, ha x.property⟩ ⟨y.val, ha y.property⟩⟩

private theorem le_of_mem_of_maximal (s : NonemptyFiniteChains P) {x t : P}
    (hx : x ∈ s.finset) (ht : t ∈ s.finset) (hmax : IsMax t) : x ≤ t :=
  (s.comparable ⟨x, hx⟩ ⟨t, ht⟩).elim id (fun h => hmax h)

private theorem exists_maximal_lower_chain [Finite P] {s : NonemptyFiniteChains P}
    {a : Finset P} (ha : a ⊆ s.finset) {t d : P}
    (hlt : ∀ x ∈ a, x < t) (hd : d < t) :
    ∃ M : NonemptyFiniteChains P, a ⊆ M.finset ∧
      Maximal (fun N : NonemptyFiniteChains P => ∀ x ∈ N.finset, x < t) M := by
  letI := Fintype.ofFinite P
  letI : Finite (NonemptyFiniteChains P) :=
    Finite.of_injective NonemptyFiniteChains.finset (fun _ _ h => NonemptyFiniteChains.ext h)
  let candidates : Set (NonemptyFiniteChains P) :=
    {M | a ⊆ M.finset ∧ ∀ x ∈ M.finset, x < t}
  have hne : candidates.Nonempty := by
    by_cases h : a.Nonempty
    · exact ⟨subchain s ha h, Finset.Subset.rfl, hlt⟩
    · -- A chain consisting only of the selected maximum leaves an empty lower chain.
      let singleton : NonemptyFiniteChains P :=
        ⟨{d}, Finset.singleton_nonempty d, by
          rintro ⟨x, hx⟩ ⟨y, hy⟩
          change x ≤ y ∨ y ≤ x
          rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
          exact Or.inl le_rfl⟩
      refine ⟨singleton, ?_⟩
      change a ⊆ singleton.finset ∧ ∀ x ∈ singleton.finset, x < t
      refine ⟨?_, ?_⟩
      · rw [Finset.not_nonempty_iff_eq_empty.mp h]
        exact Finset.empty_subset _
      · intro x hx
        change x ∈ ({d} : Finset P) at hx
        simpa only [Finset.mem_singleton.mp hx] using hd
  obtain ⟨M, hM⟩ := (Set.toFinite candidates).exists_maximal hne
  have hmem : a ⊆ M.finset ∧ ∀ x ∈ M.finset, x < t := hM.1
  refine ⟨M, hmem.1, hmem.2, ?_⟩
  intro N hN hMN
  exact hM.2 (show N ∈ candidates from ⟨fun x hx => hMN (hmem.1 hx), hN⟩) hMN

private def replacement {T : Set P} (c : T → P) (x : P) : P :=
  if hx : x ∈ T then c ⟨x, hx⟩ else x

private theorem image_replacement_eq {T : Set P} (c : T → P) {s : Finset P}
    (hs : ∀ x ∈ s, x ∉ T) : s.image (replacement c) = s := by
  calc
    s.image (replacement c) = s.image id :=
      Finset.image_congr fun x hx => dif_neg (hs x hx)
    _ = s := Finset.image_id

private def unionWithReplacement {T : Set P} (hT : ∀ t ∈ T, IsMax t)
    (c : T → P) (hc : ∀ t : T, c t < t.val) (s R : NonemptyFiniteChains P)
    (hR : R.finset = s.finset.image (replacement c)) : NonemptyFiniteChains P := by
  have hcross (x : P) (hx : x ∈ s.finset) (y : P) (hy : y ∈ R.finset) :
      x ≤ y ∨ y ≤ x := by
    by_cases hxT : x ∈ T
    · rw [hR] at hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hle : replacement c z ≤ z := by
        by_cases hzT : z ∈ T
        · simpa only [replacement, dif_pos hzT] using (hc ⟨z, hzT⟩).le
        · simp only [replacement, dif_neg hzT, le_refl]
      exact Or.inr (hle.trans (le_of_mem_of_maximal s hz hx (hT x hxT)))
    · have hxR : x ∈ R.finset := by
        rw [hR]
        exact Finset.mem_image.mpr ⟨x, hx, dif_neg hxT⟩
      exact R.comparable ⟨x, hxR⟩ ⟨y, hy⟩
  refine ⟨s.finset ∪ R.finset, s.nonempty.mono Finset.subset_union_left, ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  change x ≤ y ∨ y ≤ x
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact s.comparable ⟨x, hx⟩ ⟨y, hy⟩
  · exact hcross x hx y hy
  · exact (hcross y hy x hx).symm
  · exact R.comparable ⟨x, hx⟩ ⟨y, hy⟩

/-- Extend two prescribed categorical lower regions to a cover of the first
ordinary subdivision. The old inclusions are categorical in the ambient
chain poset. Each extended region retracts onto its prescribed old region
by a two-step fence of order maps inside the extended region. Both steps fix
the old region pointwise. Precomposing the given old contraction with the
retraction extends it with the same endpoint.

The lower and categorical witnesses together with coverage give
`HasCategoricalCover (NonemptyFiniteChains P) 2` with these very pieces. -/
theorem exists_relative_two_cover_of_maximal_lower_chains [Finite P]
    {T : Set P} (hT : ∀ t ∈ T, IsMax t)
    (E : Fin 2 → Set (NonemptyFiniteChains P))
    (hE : ∀ i, IsLowerSet (E i) ∧ Categorical (E i))
    (hE_old : ∀ i, E i ⊆ chainsAvoiding T)
    (hE_cover : ∀ s ∈ chainsAvoiding T, ∃ i, s ∈ E i)
    (c : Fin 2 → T → P) (hc : ∀ i (t : T), c i t < t.val)
    (hmax : ∀ (t : T) (M : NonemptyFiniteChains P),
      Maximal (fun N : NonemptyFiniteChains P => ∀ x ∈ N.finset, x < t.val) M →
      ∃ i, M ∈ E i ∧ c i t ∈ M.finset) :
    ∃ A : Fin 2 → Set (NonemptyFiniteChains P),
      ((∀ i, IsLowerSet (A i) ∧ Categorical (A i)) ∧ ∀ s, ∃ i, s ∈ A i) ∧
      (∀ i, A i ∩ chainsAvoiding T = E i) ∧
      ∀ i, ∃ (r : A i →o E i) (u : A i →o A i),
        (∀ s, s ≤ u s) ∧ (∀ s, (r s).val ≤ (u s).val) ∧
        ∀ (s : A i), s.val ∈ E i → (r s).val = s.val ∧ u s = s := by
  let A (i : Fin 2) : Set (NonemptyFiniteChains P) :=
    {s | ∃ R ∈ E i, R.finset = s.finset.image (replacement (c i))}
  have mem_old (i : Fin 2) (s : NonemptyFiniteChains P) (hs : s ∈ chainsAvoiding T) :
      s ∈ A i ↔ s ∈ E i := by
    have hfixed := image_replacement_eq (c i) hs
    constructor
    · rintro ⟨R, hR, hfin⟩
      have heq : R = s := NonemptyFiniteChains.ext (hfin.trans hfixed)
      simpa only [heq] using hR
    · exact fun h => ⟨s, h, hfixed.symm⟩
  have hrestrict (i : Fin 2) : A i ∩ chainsAvoiding T = E i := by
    apply Set.ext
    intro s
    exact ⟨fun h => (mem_old i s h.2).mp h.1,
      fun h => ⟨(mem_old i s (hE_old i h)).mpr h, hE_old i h⟩⟩
  have hmem_of_image_subset (i : Fin 2) (s : NonemptyFiniteChains P)
      {M : NonemptyFiniteChains P} (hM : M ∈ E i)
      (hsub : s.finset.image (replacement (c i)) ⊆ M.finset) : s ∈ A i := by
    let R := subchain M hsub (s.nonempty.image (replacement (c i)))
    exact ⟨R, (hE i).1 (show R ≤ M from hsub) hM, rfl⟩
  have hlower (i : Fin 2) : IsLowerSet (A i) := by
    intro s t hts hs
    obtain ⟨R, hR, hfin⟩ := hs
    apply hmem_of_image_subset i t hR
    rw [hfin]
    exact Finset.image_subset_image (show t.finset ⊆ s.finset from hts)
  have hcover (s : NonemptyFiniteChains P) : ∃ i, s ∈ A i := by
    by_cases hs : s ∈ chainsAvoiding T
    · obtain ⟨i, hi⟩ := hE_cover s hs
      exact ⟨i, (mem_old i s hs).mpr hi⟩
    have hhit : ∃ t ∈ s.finset, t ∈ T := by
      by_contra h
      exact hs (fun x hx hxT => h ⟨x, hx, hxT⟩)
    obtain ⟨t, ht, htT⟩ := hhit
    have htop (x : P) (hx : x ∈ s.finset) : x ≤ t :=
      le_of_mem_of_maximal s hx ht (hT t htT)
    have hlt (x : P) (hx : x ∈ s.finset.erase t) : x < t :=
      lt_of_le_of_ne (htop x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1
    obtain ⟨M, hsub, hM⟩ :=
      exists_maximal_lower_chain (Finset.erase_subset t s.finset) hlt (hc 0 ⟨t, htT⟩)
    obtain ⟨i, hi, hci⟩ := hmax ⟨t, htT⟩ M hM
    refine ⟨i, hmem_of_image_subset i s hi ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    by_cases hyT : y ∈ T
    · have heq : y = t := le_antisymm (htop y hy) (hT y hyT (htop y hy))
      subst y
      simpa only [replacement, dif_pos htT] using hci
    · have hne : y ≠ t := fun h => hyT (h.symm ▸ htT)
      have hym := hsub (Finset.mem_erase.mpr ⟨hne, hy⟩)
      simpa only [replacement, dif_neg hyT] using hym
  let target (i : Fin 2) (s : A i) :
      ∃ R ∈ E i, R.finset = s.val.finset.image (replacement (c i)) := s.property
  let r (i : Fin 2) : A i →o E i :=
    { toFun := fun s => ⟨(target i s).choose, (target i s).choose_spec.1⟩
      monotone' := by
        intro s t hst
        change (target i s).choose.finset ⊆ (target i t).choose.finset
        rw [(target i s).choose_spec.2, (target i t).choose_spec.2]
        exact Finset.image_subset_image (show s.val.finset ⊆ t.val.finset from hst) }
  have hr (i : Fin 2) (s : A i) :
      (r i s).val.finset = s.val.finset.image (replacement (c i)) :=
    (target i s).choose_spec.2
  let enlarged (i : Fin 2) (s : A i) : NonemptyFiniteChains P :=
    unionWithReplacement hT (c i) (hc i) s.val (r i s).val (hr i s)
  have enlarged_mem (i : Fin 2) (s : A i) : enlarged i s ∈ A i := by
    refine ⟨(r i s).val, (r i s).property, ?_⟩
    change (r i s).val.finset =
      (s.val.finset ∪ (r i s).val.finset).image (replacement (c i))
    rw [Finset.image_union, image_replacement_eq (c i) (hE_old i (r i s).property),
      ← hr i s, Finset.union_idempotent]
  let u (i : Fin 2) : A i →o A i :=
    { toFun := fun s => ⟨enlarged i s, enlarged_mem i s⟩
      monotone' := by
        intro s t hst
        change s.val.finset ∪ (r i s).val.finset ⊆ t.val.finset ∪ (r i t).val.finset
        exact Finset.union_subset_union
          (show s.val.finset ⊆ t.val.finset from hst)
          (show (r i s).val.finset ⊆ (r i t).val.finset from (r i).monotone hst) }
  have hstart (i : Fin 2) (s : A i) : s ≤ u i s := Finset.subset_union_left
  have hend (i : Fin 2) (s : A i) : (r i s).val ≤ (u i s).val :=
    Finset.subset_union_right
  have hfix (i : Fin 2) (s : A i) (hs : s.val ∈ E i) :
      (r i s).val = s.val ∧ u i s = s := by
    have heq : (r i s).val = s.val :=
      NonemptyFiniteChains.ext ((hr i s).trans (image_replacement_eq (c i) (hE_old i hs)))
    refine ⟨heq, Subtype.ext (NonemptyFiniteChains.ext ?_)⟩
    change s.val.finset ∪ (r i s).val.finset = s.val.finset
    rw [heq, Finset.union_idempotent]
  have hcat (i : Fin 2) : Categorical (A i) := by
    let incl : A i →o NonemptyFiniteChains P := (OrderEmbedding.subtype (A i)).toOrderHom
    let bridge : A i →o NonemptyFiniteChains P := incl.comp (u i)
    let oldIncl : E i →o NonemptyFiniteChains P := (OrderEmbedding.subtype (E i)).toOrderHom
    have up : incl ≤ bridge := fun s => hstart i s
    have down : oldIncl.comp (r i) ≤ bridge := fun s => hend i s
    have transport {f g : E i →o NonemptyFiniteChains P} (h : EqvGen (· ≤ ·) f g) :
        EqvGen (· ≤ ·) (f.comp (r i)) (g.comp (r i)) := by
      induction h with
      | rel f g hfg => exact .rel _ _ (fun s => OrderHom.le_def.mp hfg (r i s))
      | refl => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
    obtain ⟨p, hp⟩ := (hE i).2
    have hcontract := transport hp
    rw [OrderHom.const_comp] at hcontract
    exact ⟨p, .trans _ _ _ (.rel _ _ up)
      (.trans _ _ _ (.symm _ _ (.rel _ _ down)) hcontract)⟩
  exact ⟨A, ⟨fun i => ⟨hlower i, hcat i⟩, hcover⟩, hrestrict,
    fun i => ⟨r i, u i, hstart i, hend i, hfix i⟩⟩

end D5.S3.Topology.StableCategory.MaximalChainCoverExtension
