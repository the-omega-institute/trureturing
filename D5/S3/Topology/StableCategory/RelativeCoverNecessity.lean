/- GID: D5/S3/Topology/StableCategory/RelativeCoverNecessity
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/RelativeCoverNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative two-covers are characterized by predecessor transversals. -/

import D5.S3.Topology.StableCategory.MaximalChainCoverExtension

/-!
# The relative order-fence criterion for the chain poset

For Question 6.3, a side that covers a maximal lower chain with the selected
maximum adjoined must admit a common strict predecessor. The two-cover
criterion combines this obstruction with the existing extension theorem.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.RelativeCoverNecessity

open D5.S3.Topology.ConnectedCategoryGraft (Categorical)
open MaximalChainCoverExtension
  (chainsAvoiding exists_relative_two_cover_of_maximal_lower_chains)
open PartialOrder (NonemptyFiniteChains)
open Relation (EqvGen)

variable {P X : Type*} [PartialOrder P] [PartialOrder X]

/-- Order maps from a side to the ambient poset fixing its prescribed old points. -/
abbrev FixedOrderMaps (A E : Set X) :=
  {f : A →o X // ∀ s : A, s.val ∈ E → f s = s.val}

/-- The inclusion as a row of a relative order fence. -/
def FixedOrderMaps.inclusion (A E : Set X) : FixedOrderMaps A E :=
  ⟨(OrderEmbedding.subtype A).toOrderHom, fun _ _ => rfl⟩

/-- A fence from inclusion to a map landing in the prescribed old region.
Every row, including each intermediate row, fixes the old points of the side. -/
def RelativeOrderFence (A E : Set X) : Prop :=
  ∃ f : FixedOrderMaps A E,
    EqvGen (fun f g : FixedOrderMaps A E => f.val ≤ g.val)
      (FixedOrderMaps.inclusion A E) f ∧
    ∀ s : A, f.val s ∈ E

/-- A chain all of whose elements are strictly below `t`. -/
def StrictLowerChain (t : P) (M : NonemptyFiniteChains P) : Prop :=
  ∀ x ∈ M.finset, x < t

/-- The chain consisting of the single element `t`. -/
def singletonChain (t : P) : NonemptyFiniteChains P :=
  ⟨{t}, Finset.singleton_nonempty t, by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    change x ≤ y ∨ y ≤ x
    rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
    exact Or.inl le_rfl⟩

/-- A singleton is minimal because chains are nonempty. -/
theorem isMin_singletonChain (t : P) : IsMin (singletonChain t) := by
  intro S hS
  change S.finset ⊆ ({t} : Finset P) at hS
  change ({t} : Finset P) ⊆ S.finset
  obtain ⟨x, hx⟩ := S.nonempty
  have hxt : x = t := Finset.mem_singleton.mp (hS hx)
  exact Finset.singleton_subset_iff.mpr (by simpa only [hxt] using hx)

/-- Adjoin `t` to a strict lower chain. -/
def adjoinTop (t : P) (M : NonemptyFiniteChains P) (hM : StrictLowerChain t M) :
    NonemptyFiniteChains P := by
  classical
  refine ⟨insert t M.finset, ⟨t, Finset.mem_insert_self t M.finset⟩, ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  change x ≤ y ∨ y ≤ x
  rcases Finset.mem_insert.mp hx with hxt | hx
  · rcases Finset.mem_insert.mp hy with hyt | hy
    · exact Or.inl (hxt.trans hyt.symm).le
    · exact Or.inr ((hM y hy).le.trans hxt.symm.le)
  · rcases Finset.mem_insert.mp hy with hyt | hy
    · exact Or.inl ((hM x hx).le.trans hyt.symm.le)
    · exact M.comparable ⟨x, hx⟩ ⟨y, hy⟩

/-- The lower chain is a subchain of the join. -/
theorem le_adjoinTop (t : P) (M : NonemptyFiniteChains P) (hM : StrictLowerChain t M) :
    M ≤ adjoinTop t M hM := by
  classical
  change M.finset ⊆ insert t M.finset
  intro x hx
  exact Finset.mem_insert_of_mem hx

/-- The top singleton is a subchain of the join. -/
theorem singletonChain_le_adjoinTop (t : P) (M : NonemptyFiniteChains P)
    (hM : StrictLowerChain t M) : singletonChain t ≤ adjoinTop t M hM := by
  classical
  change ({t} : Finset P) ⊆ insert t M.finset
  exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self t M.finset)

/-- Adjoining a maximal element to a maximal strict lower chain gives a
maximal element of the entire chain poset. -/
theorem isMax_adjoinTop {t : P} (ht : IsMax t) {M : NonemptyFiniteChains P}
    (hM : Maximal (StrictLowerChain t) M) : IsMax (adjoinTop t M hM.1) := by
  classical
  intro S hMS
  change insert t M.finset ⊆ S.finset at hMS
  change S.finset ⊆ insert t M.finset
  have htS : t ∈ S.finset := hMS (Finset.mem_insert_self t M.finset)
  have hsub : M.finset ⊆ S.finset.erase t := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨(hM.1 x hx).ne, hMS (Finset.mem_insert_of_mem hx)⟩
  let N : NonemptyFiniteChains P :=
    ⟨S.finset.erase t, M.nonempty.mono hsub, by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      exact S.comparable ⟨x, (Finset.mem_erase.mp hx).2⟩ ⟨y, (Finset.mem_erase.mp hy).2⟩⟩
  have hN : StrictLowerChain t N := by
    intro x hx
    change x ∈ S.finset.erase t at hx
    obtain ⟨hne, hxS⟩ := Finset.mem_erase.mp hx
    have hle : x ≤ t :=
      (S.comparable ⟨x, hxS⟩ ⟨t, htS⟩).elim id (fun h => ht h)
    exact lt_of_le_of_ne hle hne
  have hNM : N ≤ M := hM.2 hN (show M ≤ N from hsub)
  intro x hx
  by_cases hxt : x = t
  · exact Finset.mem_insert.mpr (Or.inl hxt)
  · have hxN : x ∈ N.finset := Finset.mem_erase.mpr ⟨hxt, hx⟩
    exact Finset.mem_insert_of_mem (hNM hxN)

private theorem mem_old_of_adjoinTop_mem {T : Set P} (hT : ∀ t ∈ T, IsMax t)
    {A E : Set (NonemptyFiniteChains P)} (hA : IsLowerSet A)
    (hrestrict : A ∩ chainsAvoiding T = E) {t : P} {M : NonemptyFiniteChains P}
    (hM : StrictLowerChain t M) (hjoin : adjoinTop t M hM ∈ A) : M ∈ E := by
  rw [← hrestrict]
  refine ⟨hA (le_adjoinTop t M hM) hjoin, ?_⟩
  intro x hx hxT
  exact (hM x hx).not_ge (hT x hxT (hM x hx).le)

/-- A relative fence on a lower side containing at least one maximal join
forces a strict predecessor common to every maximal lower chain whose join
lies in that side. -/
theorem exists_common_strict_predecessor_of_relative_fence
    {T : Set P} (hT : ∀ t ∈ T, IsMax t)
    {A E : Set (NonemptyFiniteChains P)} (hA : IsLowerSet A)
    (hrestrict : A ∩ chainsAvoiding T = E) {t : P} (ht : t ∈ T)
    (hcovered : ∃ (M : NonemptyFiniteChains P) (hM : Maximal (StrictLowerChain t) M),
      adjoinTop t M hM.1 ∈ A)
    (hfence : RelativeOrderFence A E) :
    ∃ c : P, c < t ∧ ∀ (M : NonemptyFiniteChains P) (hM : Maximal (StrictLowerChain t) M),
      adjoinTop t M hM.1 ∈ A → c ∈ M.finset := by
  classical
  obtain ⟨M₀, hM₀, hjoin₀⟩ := hcovered
  let s : A := ⟨singletonChain t, hA (singletonChain_le_adjoinTop t M₀ hM₀.1) hjoin₀⟩
  obtain ⟨last, hf, hlast⟩ := hfence
  by_contra hnone
  have down {f g : FixedOrderMaps A E} (hfg : f.val ≤ g.val)
      (hg : g.val s = singletonChain t) : f.val s = singletonChain t := by
    have hle := OrderHom.le_def.mp hfg s
    rw [hg] at hle
    exact le_antisymm hle (isMin_singletonChain t hle)
  have up {f g : FixedOrderMaps A E} (hfg : f.val ≤ g.val)
      (hfs : f.val s = singletonChain t) : g.val s = singletonChain t := by
    have hsle : singletonChain t ≤ g.val s :=
      hfs.symm.le.trans (OrderHom.le_def.mp hfg s)
    -- Each covered join contains the old fixed chain and the singleton.
    have hbound (M : NonemptyFiniteChains P) (hM : Maximal (StrictLowerChain t) M)
        (hjoin : adjoinTop t M hM.1 ∈ A) : g.val s ≤ adjoinTop t M hM.1 := by
      let j : A := ⟨adjoinTop t M hM.1, hjoin⟩
      let m : A := ⟨M, hA (le_adjoinTop t M hM.1) hjoin⟩
      have hsj : s ≤ j := singletonChain_le_adjoinTop t M hM.1
      have hmj : m ≤ j := le_adjoinTop t M hM.1
      have hmfix : g.val m = M :=
        g.property m (mem_old_of_adjoinTop_mem hT hA hrestrict hM.1 hjoin)
      have hmle : M ≤ g.val j := hmfix.symm.le.trans (g.val.monotone hmj)
      have htle : singletonChain t ≤ g.val j := hsle.trans (g.val.monotone hsj)
      have hjle : j.val ≤ g.val j := by
        change insert t M.finset ⊆ (g.val j).finset
        intro x hx
        rcases Finset.mem_insert.mp hx with hxt | hx
        · exact htle (Finset.mem_singleton.mpr hxt)
        · exact hmle hx
      exact (g.val.monotone hsj).trans (isMax_adjoinTop (hT t ht) hM hjle)
    refine le_antisymm ?_ hsle
    change (g.val s).finset ⊆ ({t} : Finset P)
    intro x hx
    by_cases hxt : x = t
    · exact Finset.mem_singleton.mpr hxt
    · exfalso
      have hmem (M : NonemptyFiniteChains P) (hM : Maximal (StrictLowerChain t) M)
          (hjoin : adjoinTop t M hM.1 ∈ A) : x ∈ M.finset := by
        have hxjoin : x ∈ insert t M.finset := hbound M hM hjoin hx
        exact (Finset.mem_insert.mp hxjoin).resolve_left hxt
      exact hnone ⟨x, hM₀.1 x (hmem M₀ hM₀ hjoin₀), hmem⟩
  have preserve {f g : FixedOrderMaps A E}
      (h : EqvGen (fun f g : FixedOrderMaps A E => f.val ≤ g.val) f g) :
      f.val s = singletonChain t ↔ g.val s = singletonChain t := by
    induction h with
    | rel _ _ hfg => exact ⟨up hfg, down hfg⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hfixed : last.val s = singletonChain t := (preserve hf).mp rfl
  have hsE := hlast s
  rw [hfixed, ← hrestrict] at hsE
  exact hsE.2 t (Finset.mem_singleton_self t) ht

/-- Extract the dependent predecessor assignment used by the sufficient
extension theorem. On a side with no covered maximal join at `t`, any strict
predecessor of `t` gives a value for the assignment. -/
theorem exists_predecessor_assignment_of_relative_two_cover
    {T : Set P} (hT : ∀ t ∈ T, IsMax t)
    (hlt : ∀ t : T, ∃ x : P, x < t.val)
    {A E : Fin 2 → Set (NonemptyFiniteChains P)}
    (hA : ∀ i, IsLowerSet (A i)) (hcover : ∀ s, ∃ i, s ∈ A i)
    (hrestrict : ∀ i, A i ∩ chainsAvoiding T = E i)
    (hfence : ∀ i, RelativeOrderFence (A i) (E i)) :
    ∃ c : Fin 2 → T → P, (∀ i (t : T), c i t < t.val) ∧
      ∀ (t : T) (M : NonemptyFiniteChains P),
        Maximal (StrictLowerChain t.val) M → ∃ i, M ∈ E i ∧ c i t ∈ M.finset := by
  classical
  have hex (i : Fin 2) (t : T) :
      ∃ x : P, x < t.val ∧
        ∀ (M : NonemptyFiniteChains P) (hM : Maximal (StrictLowerChain t.val) M),
          adjoinTop t.val M hM.1 ∈ A i → x ∈ M.finset := by
    by_cases h : ∃ (M : NonemptyFiniteChains P) (hM : Maximal (StrictLowerChain t.val) M),
        adjoinTop t.val M hM.1 ∈ A i
    · exact exists_common_strict_predecessor_of_relative_fence hT (hA i) (hrestrict i)
        t.property h (hfence i)
    · obtain ⟨x, hx⟩ := hlt t
      exact ⟨x, hx, fun M hM ha => (h ⟨M, hM, ha⟩).elim⟩
  let c (i : Fin 2) (t : T) : P := (hex i t).choose
  refine ⟨c, fun i t => (hex i t).choose_spec.1, ?_⟩
  intro t M hM
  obtain ⟨i, hi⟩ := hcover (adjoinTop t.val M hM.1)
  exact ⟨i, mem_old_of_adjoinTop_mem hT (hA i) (hrestrict i) hM.1 hi,
    (hex i t).choose_spec.2 M hM hi⟩

/-- A prescribed categorical lower two-cover of the old region extends
with relative order fences exactly when it has the dependent predecessor
assignment of the maximal-lower-chain criterion. -/
theorem exists_relative_two_cover_iff [Finite P]
    {T : Set P} (hT : ∀ t ∈ T, IsMax t)
    (hlt : ∀ t : T, ∃ x : P, x < t.val)
    (E : Fin 2 → Set (NonemptyFiniteChains P))
    (hE : ∀ i, IsLowerSet (E i) ∧ Categorical (E i))
    (hE_old : ∀ i, E i ⊆ chainsAvoiding T)
    (hE_cover : ∀ s ∈ chainsAvoiding T, ∃ i, s ∈ E i) :
    (∃ A : Fin 2 → Set (NonemptyFiniteChains P),
      ((∀ i, IsLowerSet (A i) ∧ Categorical (A i)) ∧ ∀ s, ∃ i, s ∈ A i) ∧
      (∀ i, A i ∩ chainsAvoiding T = E i) ∧
      ∀ i, RelativeOrderFence (A i) (E i)) ↔
    (∃ c : Fin 2 → T → P, (∀ i (t : T), c i t < t.val) ∧
      ∀ (t : T) (M : NonemptyFiniteChains P),
        Maximal (StrictLowerChain t.val) M → ∃ i, M ∈ E i ∧ c i t ∈ M.finset) := by
  constructor
  · rintro ⟨A, ⟨hA, hcover⟩, hrestrict, hfence⟩
    exact exists_predecessor_assignment_of_relative_two_cover hT hlt
      (fun i => (hA i).1) hcover hrestrict hfence
  · rintro ⟨c, hc, hmax⟩
    obtain ⟨A, hA, hrestrict, hrows⟩ :=
      exists_relative_two_cover_of_maximal_lower_chains hT E hE hE_old hE_cover c hc hmax
    refine ⟨A, hA, hrestrict, ?_⟩
    intro i
    obtain ⟨r, u, hstart, hend, hfix⟩ := hrows i
    let up : FixedOrderMaps (A i) (E i) :=
      ⟨(OrderEmbedding.subtype (A i)).toOrderHom.comp u, by
        intro s hs
        change (u s).val = s.val
        exact congrArg (fun a : A i => a.val) (hfix s hs).2⟩
    let last : FixedOrderMaps (A i) (E i) :=
      ⟨(OrderEmbedding.subtype (E i)).toOrderHom.comp r, by
        intro s hs
        change (r s).val = s.val
        exact (hfix s hs).1⟩
    have hup : (FixedOrderMaps.inclusion (A i) (E i)).val ≤ up.val :=
      OrderHom.le_def.mpr hstart
    have hdown : last.val ≤ up.val := OrderHom.le_def.mpr hend
    exact ⟨last, .trans _ _ _ (.rel _ _ hup) (.symm _ _ (.rel _ _ hdown)),
      fun s => (r s).property⟩

end D5.S3.Topology.StableCategory.RelativeCoverNecessity
