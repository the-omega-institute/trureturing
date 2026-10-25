/- GID: D5/S3/Topology/StoneCech/HistoricalFilterCollision
   generality: G
   mirror-B: D5/B/S3/Topology/StoneCech/HistoricalFilterCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed free historical ultrafilters collide under continuous observables. -/

module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Compactification.StoneCech

@[expose] public section

/-!
# Historical filters and fixed free collisions

An arbitrary nonempty family directed downwards modulo finite sets has two
free ultrafilter extensions when every member meets both fixed disjoint
reservoirs infinitely. Each observable may converge on its own historical
set. The ultrafilters are fixed before choosing any observable.

The classical ultrafilter lemma and Hausdorff uniqueness of limits are the
only extension and uniqueness mechanisms. No common pseudointersection,
last historical set, countability of the index type, or CH is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Function
open scoped Topology

universe u v w z

namespace D5.S3.Topology.StoneCech.HistoricalFilterCollision

private theorem cofinite_principal_le_of_finite_sdiff {s t : Set ℕ}
    (h : (s \ t).Finite) : cofinite ⊓ 𝓟 s ≤ cofinite ⊓ 𝓟 t := by
  calc
    cofinite ⊓ 𝓟 s = cofinite ⊓ 𝓟 (s \ (s \ t)) :=
      (h.cofinite_inf_principal_sdiff (s := s)).symm
    _ ≤ cofinite ⊓ 𝓟 t := inf_le_inf_left _ (principal_mono.2 (by
      intro x hx
      by_contra hxt
      exact hx.2 ⟨hx.1, hxt⟩))

private theorem exists_free_extension {I : Type u} [Nonempty I]
    (J : I → Set ℕ)
    (hd : ∀ i j, ∃ k, (J k \ J i).Finite ∧ (J k \ J j).Finite)
    (N : Set ℕ) (hinf : ∀ i, (J i ∩ N).Infinite) :
    ∃ u : Ultrafilter ℕ, (u : Filter ℕ) ≤ cofinite ∧ N ∈ u ∧ ∀ i, J i ∈ u := by
  classical
  let F : I → Filter ℕ := fun i => cofinite ⊓ 𝓟 (J i ∩ N)
  have hmono {i k : I} (h : (J k \ J i).Finite) : F k ≤ F i := by
    apply cofinite_principal_le_of_finite_sdiff
    apply h.subset
    intro n hn
    refine ⟨hn.1.1, ?_⟩
    intro hni
    exact hn.2 ⟨hni, hn.1.2⟩
  have hdir : Directed (· ≥ ·) F := by
    intro i j
    obtain ⟨k, hki, hkj⟩ := hd i j
    exact ⟨k, hmono hki, hmono hkj⟩
  have hn : ∀ i, (F i).NeBot := fun i => cofinite_inf_principal_neBot_iff.2 (hinf i)
  let f : Filter ℕ := ⨅ i, F i
  have : f.NeBot := iInf_neBot_of_directed' hdir hn
  let u : Ultrafilter ℕ := Ultrafilter.of f
  have hu (i : I) : (u : Filter ℕ) ≤ F i :=
    (Ultrafilter.of_le f).trans (iInf_le F i)
  have hm (i : I) : J i ∩ N ∈ (u : Filter ℕ) :=
    le_principal_iff.1 ((hu i).trans inf_le_right)
  exact ⟨u, (hu (Classical.arbitrary I)).trans inf_le_left,
    mem_of_superset (hm (Classical.arbitrary I)) inter_subset_right,
    fun i => mem_of_superset (hm i) inter_subset_left⟩

/-- Two fixed distinct free ultrafilters contain every historical set and
respectively the two original reservoirs. The index type is arbitrary;
only pairwise downward directedness modulo finite sets is required. -/
theorem exists_distinct_free_ultrafilters {I : Type u} [Nonempty I]
    (J : I → Set ℕ)
    (hd : ∀ i j, ∃ k, (J k \ J i).Finite ∧ (J k \ J j).Finite)
    (N₀ N₁ : Set ℕ) (hdis : Disjoint N₀ N₁)
    (hinf₀ : ∀ i, (J i ∩ N₀).Infinite) (hinf₁ : ∀ i, (J i ∩ N₁).Infinite) :
    ∃ u₀ u₁ : Ultrafilter ℕ,
      (u₀ : Filter ℕ) ≤ cofinite ∧ (u₁ : Filter ℕ) ≤ cofinite ∧
      N₀ ∈ u₀ ∧ N₁ ∈ u₁ ∧ (∀ i, J i ∈ u₀) ∧ (∀ i, J i ∈ u₁) ∧ u₀ ≠ u₁ := by
  obtain ⟨u₀, hf₀, hN₀, hJ₀⟩ := exists_free_extension J hd N₀ hinf₀
  obtain ⟨u₁, hf₁, hN₁, hJ₁⟩ := exists_free_extension J hd N₁ hinf₁
  refine ⟨u₀, u₁, hf₀, hf₁, hN₀, hN₁, hJ₀, hJ₁, ?_⟩
  intro heq
  have hN₁' : N₁ ∈ (u₀ : Filter ℕ) := heq.symm ▸ hN₁
  exact (Filter.NeBot.not_disjoint inferInstance hN₀ hN₁') hdis

/-- Any already chosen free pair containing the whole history collides
under a continuous map if separating continuous Hausdorff-valued
observables converge, each on its own historical set. No common stage
for the observables is assumed. -/
theorem eq_of_historical_observables {I : Type u} (J : I → Set ℕ)
    (u₀ u₁ : Ultrafilter ℕ)
    (hf₀ : (u₀ : Filter ℕ) ≤ cofinite) (hf₁ : (u₁ : Filter ℕ) ≤ cofinite)
    (hJ₀ : ∀ i, J i ∈ u₀) (hJ₁ : ∀ i, J i ∈ u₁)
    {X : Type v} [TopologicalSpace X] (V : Ultrafilter ℕ → X) (hV : Continuous V)
    {A : Type w} {Y : A → Type z} [∀ a, TopologicalSpace (Y a)] [∀ a, T2Space (Y a)]
    (phi : ∀ a, X → Y a) (hphi : ∀ a, Continuous (phi a))
    (hsep : ∀ x y, (∀ a, phi a x = phi a y) → x = y)
    (hconv : ∀ a, ∃ i L, Tendsto (fun n => phi a (V (pure n)))
      (cofinite ⊓ 𝓟 (J i)) (𝓝 L)) : V u₀ = V u₁ := by
  apply hsep
  intro a
  obtain ⟨i, L, hi⟩ := hconv a
  have hle₀ : (u₀ : Filter ℕ) ≤ cofinite ⊓ 𝓟 (J i) :=
    le_inf hf₀ (le_principal_iff.2 (hJ₀ i))
  have hle₁ : (u₁ : Filter ℕ) ≤ cofinite ⊓ 𝓟 (J i) :=
    le_inf hf₁ (le_principal_iff.2 (hJ₁ i))
  have hlim₀ : Tendsto (fun n => phi a (V (pure n))) (u₀ : Filter ℕ)
      (𝓝 (phi a (V u₀))) :=
    ((hphi a).comp hV).tendsto u₀ |>.comp (Ultrafilter.tendsto_pure_self u₀)
  have hlim₁ : Tendsto (fun n => phi a (V (pure n))) (u₁ : Filter ℕ)
      (𝓝 (phi a (V u₁))) :=
    ((hphi a).comp hV).tendsto u₁ |>.comp (Ultrafilter.tendsto_pure_self u₁)
  exact (tendsto_nhds_unique hlim₀ (hi.mono_left hle₀)).trans
    (tendsto_nhds_unique hlim₁ (hi.mono_left hle₁)).symm

end D5.S3.Topology.StoneCech.HistoricalFilterCollision
