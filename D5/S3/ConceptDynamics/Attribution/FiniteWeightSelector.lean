/- GID: D5/S3/ConceptDynamics/Attribution/FiniteWeightSelector
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/FiniteWeightSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singleton weight fibers characterize admissible equivariant selection on finite tests. -/

import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic

namespace D5.S3.ConceptDynamics.Attribution.FiniteWeightSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false

private def permute {I R : Type*} (g : Equiv.Perm I) (w : I → R) : I → R :=
  w ∘ g.symm

private def SingletonWeight {I R : Type*} (w : I → R) (i : I) : Prop :=
  ∀ j, w j = w i → j = i

private theorem singleton_permute_iff {I R : Type*} (g : Equiv.Perm I)
    (w : I → R) (i : I) : SingletonWeight (permute g w) (g i) ↔ SingletonWeight w i := by
  constructor
  · intro h j hj
    apply g.injective
    apply h
    simpa [permute] using hj
  · intro h j hj
    apply g.symm.injective
    rw [Equiv.symm_apply_apply]
    apply h
    simpa [permute] using hj

/-- A permutation-covariant admissible selector exists exactly when every profile
has an admissible label whose weight occurs at only one label. -/
theorem exists_equivariant_selector_iff {I R : Type*} [Fintype I] [LinearOrder R]
    (D : Set (I → R)) (closed : ∀ (g : Equiv.Perm I) w, w ∈ D → w ∘ g.symm ∈ D)
    (allowed : (I → R) → I → Prop)
    (covariant : ∀ (g : Equiv.Perm I) w i, allowed (w ∘ g.symm) (g i) ↔ allowed w i) :
    (∃ choose : D → I,
      (∀ w, allowed w.1 (choose w)) ∧
      (∀ (g : Equiv.Perm I) (w : D),
        choose ⟨w.1 ∘ g.symm, closed g w.1 w.2⟩ = g (choose w))) ↔
    (∀ w ∈ D, ∃ i, allowed w i ∧ ∀ j, w j = w i → j = i) := by
  classical
  constructor
  · rintro ⟨choose, ha, he⟩ w hw
    let input : D := ⟨w, hw⟩
    refine ⟨choose input, ha input, ?_⟩
    intro j hj
    let g : Equiv.Perm I := Equiv.swap j (choose input)
    have fix : permute g w = w := by
      funext k
      have step := Equiv.apply_swap_eq_self hj k
      simpa [permute, g] using step
    have hsame : (⟨permute g w, closed g w hw⟩ : D) = input := Subtype.ext fix
    have hc : choose input = g (choose input) := by
      have step := he g input
      change choose (⟨permute g w, closed g w hw⟩ : D) = g (choose input) at step
      rwa [hsame] at step
    simpa [g] using hc.symm
  · intro h
    have exists_max (w : D) :
        ∃ i, allowed w.1 i ∧ SingletonWeight w.1 i ∧
          (∀ j, allowed w.1 j → SingletonWeight w.1 j → w.1 j ≤ w.1 i) := by
      let eligible : Finset I :=
        Finset.univ.filter (fun i => allowed w.1 i ∧ SingletonWeight w.1 i)
      obtain ⟨i, hi⟩ := h w.1 w.2
      have hNE : eligible.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image eligible w.1 hNE
      obtain ⟨ha, hs⟩ := (Finset.mem_filter.mp hj).2
      exact ⟨j, ha, hs, fun k hka hks => hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hka, hks⟩)⟩
    choose choose ha hu hm using exists_max
    refine ⟨choose, ha, ?_⟩
    intro g w
    let next : D := ⟨permute g w.1, closed g w.1 w.2⟩
    change choose next = g (choose w)
    let j := g.symm (choose next)
    have hgj : g j = choose next := g.apply_symm_apply _
    have hja : allowed w.1 j := (covariant g w.1 j).mp (hgj ▸ ha next)
    have hju : SingletonWeight w.1 j := (singleton_permute_iff g w.1 j).mp (hgj ▸ hu next)
    have hl : w.1 j ≤ w.1 (choose w) := hm w j hja hju
    have hr : w.1 (choose w) ≤ w.1 j := by
      have hnext := hm next (g (choose w)) ((covariant g w.1 _).mpr (ha w))
        ((singleton_permute_iff g w.1 _).mpr (hu w))
      change w.1 (g.symm (g (choose w))) ≤ w.1 j at hnext
      simpa only [Equiv.symm_apply_apply] using hnext
    rw [← hgj, hu w j (le_antisymm hl hr)]

end D5.S3.ConceptDynamics.Attribution.FiniteWeightSelector
