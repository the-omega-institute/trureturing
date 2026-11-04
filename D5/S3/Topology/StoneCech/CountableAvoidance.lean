/- GID: D5/S3/Topology/StoneCech/CountableAvoidance
   generality: G
   mirror-B: D5/B/S3/Topology/StoneCech/CountableAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Infinite thinning removes every principal to free collision. -/

import D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! # Countable free-ultrafilter avoidance and full-domain thinning -/

open Set Filter Topology Function

noncomputable section

namespace D5.S3.Topology.StoneCech.CountableAvoidance

open D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation

/-- The ultrafilter and universal-property realizations of the Stone–Čech
compactification agree on a discrete space. -/
def ultrafilterHomeomorph {α : Type*} [TopologicalSpace α] [DiscreteTopology α] :
    Ultrafilter α ≃ₜ StoneCech α := by
  let f : Ultrafilter α → StoneCech α := Ultrafilter.extend stoneCechUnit
  let g : StoneCech α → Ultrafilter α :=
    stoneCechExtend (continuous_of_discreteTopology : Continuous (pure : α → Ultrafilter α))
  have hf : Continuous f := continuous_ultrafilter_extend _
  have hg : Continuous g := continuous_stoneCechExtend _
  have hgf : g ∘ f = id := denseRange_pure.equalizer (hg.comp hf) continuous_id (by
    ext a
    simp only [comp_apply, f, ultrafilter_extend_pure, g, stoneCechExtend_stoneCechUnit,
      id_eq])
  have hfg : f ∘ g = id := denseRange_stoneCechUnit.equalizer (hf.comp hg) continuous_id (by
    ext a
    simp only [comp_apply, g, stoneCechExtend_stoneCechUnit, f, ultrafilter_extend_pure,
      id_eq])
  exact {
    toFun := f
    invFun := g
    left_inv := congrFun hgf
    right_inv := congrFun hfg
    continuous_toFun := hf
    continuous_invFun := hg }

/-- A countable family of free ultrafilters misses one infinite subset of ℕ. -/
theorem exists_infinite_notMem (p : ℕ → Ultrafilter ℕ)
    (hp : ∀ n, (p n : Filter ℕ) ≤ cofinite) :
    ∃ A : Set ℕ, A.Infinite ∧ ∀ n, A ∉ p n := by
  classical
  have step (n : ℕ) (A : {A : Set ℕ // A.Infinite}) :
      ∃ B : Set ℕ, B ⊆ A.val ∧ B.Infinite ∧ B ∉ p n := by
    obtain ⟨T, V, hTA, hVA, hT, hV, hTV⟩ := split_pool A.property
    by_cases hTp : T ∈ p n
    · refine ⟨V, hVA, hV, ?_⟩
      intro hVp
      have := inter_mem hTp hVp
      rw [Set.disjoint_iff_inter_eq_empty.mp hTV] at this
      exact (Filter.empty_notMem (p n : Filter ℕ)) this
    · exact ⟨T, hTA, hT, hTp⟩
  choose next hsub hinf hnot using step
  let pools : ℕ → {A : Set ℕ // A.Infinite} :=
    fun n => Nat.rec ⟨univ, Set.infinite_univ⟩
      (fun n A => ⟨next n A, hinf n A⟩) n
  let A : ℕ → Set ℕ := fun n => (pools n).val
  have hdec (n : ℕ) : A (n + 1) ⊆ A n := hsub n (pools n)
  obtain ⟨S, hS, _, hfin⟩ := diagonal_pool A (fun n => (pools n).property) hdec
  refine ⟨S, hS, ?_⟩
  intro n hSp
  apply hnot n (pools n)
  have hc : (S \ A (n + 1))ᶜ ∈ p n := hp n (hfin (n + 1)).compl_mem_cofinite
  exact mem_of_superset (inter_mem hSp hc) (by
    intro x hx
    by_contra hxa
    exact hx.2 ⟨hx.1, hxa⟩)

/-- Mapping ultrafilters along a function is continuous in the Stone topology. -/
theorem continuous_map {α β : Type*} (j : α → β) :
    Continuous (Ultrafilter.map j) := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨A, rfl⟩
  exact ultrafilter_isOpen_basic (j ⁻¹' A)

/-- Separate injection on principals and on free points can be made a full
injection by an actual infinite subsequence. No cardinal hypothesis is used. -/
theorem exists_strictMono_injective_reindex {Y : Type*}
    (h : Ultrafilter ℕ → Y)
    (hprincipal : Injective (h ∘ (pure : ℕ → Ultrafilter ℕ)))
    (hfree : Set.InjOn h {p | (p : Filter ℕ) ≤ cofinite}) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ Injective (h ∘ Ultrafilter.map j) := by
  classical
  let bad (n : ℕ) : Prop :=
    ∃ p : Ultrafilter ℕ, (p : Filter ℕ) ≤ cofinite ∧ h p = h (pure n)
  let p (n : ℕ) : Ultrafilter ℕ :=
    if hn : bad n then hn.choose else hyperfilter ℕ
  have hp (n : ℕ) : (p n : Filter ℕ) ≤ cofinite := by
    dsimp [p]
    split_ifs with hn
    · exact hn.choose_spec.1
    · exact hyperfilter_le_cofinite
  obtain ⟨A, hA, havoid⟩ := exists_infinite_notMem p hp
  have hcross (n : ℕ) (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ cofinite)
      (hAq : A ∈ q) : h q ≠ h (pure n) := by
    intro heq
    have hn : bad n := ⟨q, hq, heq⟩
    have hpn : p n = hn.choose := dite_eq_left hn
    have he : q = p n := hfree hq (hp n) (by
      rw [hpn]
      exact heq.trans hn.choose_spec.2.symm)
    exact havoid n (he ▸ hAq)
  have hinj : Set.InjOn h {q | A ∈ q} := by
    intro q hq t ht heq
    rcases q.le_cofinite_or_eq_pure with hqfree | ⟨n, rfl⟩
    · rcases t.le_cofinite_or_eq_pure with htfree | ⟨m, rfl⟩
      · exact hfree hqfree htfree heq
      · exact (hcross m q hqfree hq heq).elim
    · rcases t.le_cofinite_or_eq_pure with htfree | ⟨m, rfl⟩
      · exact (hcross n t htfree ht heq.symm).elim
      · exact congrArg pure (hprincipal heq)
  obtain ⟨j, hj, hjA⟩ := enumerate_pool hA
  refine ⟨j, hj, ?_⟩
  intro q t heq
  have hm (q : Ultrafilter ℕ) : A ∈ Ultrafilter.map j q := by
    apply Ultrafilter.mem_map.mpr
    exact mem_of_superset univ_mem (fun n _ => hjA n)
  have hmap : Ultrafilter.map j q = Ultrafilter.map j t := hinj (hm q) (hm t) heq
  apply Ultrafilter.coe_injective
  exact (Filter.map_injective hj.injective) (congrArg Ultrafilter.toFilter hmap)

#print axioms exists_infinite_notMem
#print axioms exists_strictMono_injective_reindex

end D5.S3.Topology.StoneCech.CountableAvoidance
