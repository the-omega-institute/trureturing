/- GID: D5/S3/FiniteGroups/Partitions/UniformPartitionMaximality
   generality: G
   mirror-B: none(waiver:no-separate-boolean-mirror-claimed)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform partition automorphisms are maximal among finite relation symmetries. -/

import D5.S3.FiniteGroups.Partitions.UniformPartitionAutomorphisms
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Order.Atoms

set_option autoImplicit false

/-! Finite uniform-partition automorphisms are maximal among relation symmetries. -/

namespace D5.S3.FiniteGroups.UniformPartitionMaximality

open Equiv
open UniformPartitionAutomorphisms
open scoped Classical

variable {K L : Type*}

private theorem swap_mem {u v : K × L} (h : u.1 = v.1) :
    swap u v ∈ Aut K L := by
  classical
  have hf (x : K × L) : (swap u v x).1 = x.1 := by
    by_cases hu : x = u
    · subst x; simpa using h.symm
    by_cases hv : x = v
    · subst x; simpa using h
    · rw [swap_apply_of_ne_of_ne hu hv]
  intro x y
  change (swap u v x).1 = (swap u v y).1 ↔ x.1 = y.1
  rw [hf, hf]

private theorem cross_transport {u v x y : K × L}
    (huv : u.1 ≠ v.1) (hxy : x.1 ≠ y.1) :
    ∃ w : Aut K L, w.val u = x ∧ w.val v = y := by
  classical
  obtain ⟨α, hαu, hαv⟩ :=
    (MulAction.is_two_pretransitive_iff (G := Perm K) (α := K)).mp
      (Equiv.Perm.isMultiplyPretransitive K 2) huv hxy
  change α u.1 = x.1 at hαu
  change α v.1 = y.1 at hαv
  let σ : K → Perm L := fun k =>
    if k = x.1 then swap u.2 x.2 else swap v.2 y.2
  refine ⟨assemble σ α, ?_, ?_⟩
  · apply Prod.ext
    · exact hαu
    · change σ (α u.1) u.2 = x.2
      simp [σ, hαu]
  · apply Prod.ext
    · exact hαv
    · change σ (α v.1) v.2 = y.2
      simp [σ, hαv, hxy.symm]

private theorem conjugate_swap (p : Perm (K × L)) (u v : K × L) :
    p * swap u v * p⁻¹ = swap (p u) (p v) := by
  exact symm_trans_swap_trans u v p

private theorem overgroup_eq_top [Finite K] [Finite L]
    (H : Subgroup (Perm (K × L))) (hWH : Aut K L ≤ H)
    (q : Perm (K × L)) (hq : q ∉ Aut K L) (hqH : q ∈ H) : H = ⊤ := by
  classical
  have hbad : ∃ p : Perm (K × L), p ∈ H ∧
      ∃ u v : K × L, u.1 = v.1 ∧ (p u).1 ≠ (p v).1 := by
    by_contra hn
    have hp : ∀ p : Perm (K × L), p ∈ H → ∀ u v : K × L,
        u.1 = v.1 → (p u).1 = (p v).1 := by
      intro p hp u v huv
      by_contra hne
      exact hn ⟨p, hp, u, v, huv, hne⟩
    apply hq
    intro u v
    constructor
    · intro he
      simpa using hp q⁻¹ (H.inv_mem hqH) (q u) (q v) he
    · exact hp q hqH u v
  obtain ⟨p, hp, u, v, huv, hpuv⟩ := hbad
  have hc : swap (p u) (p v) ∈ H := by
    rw [← conjugate_swap]
    exact H.mul_mem (H.mul_mem hp (hWH (swap_mem huv))) (H.inv_mem hp)
  have hall (x y : K × L) : swap x y ∈ H := by
    by_cases hxy : x.1 = y.1
    · exact hWH (swap_mem hxy)
    · obtain ⟨w, hwx, hwy⟩ := cross_transport hpuv hxy
      have hw : w.val ∈ H := hWH w.property
      have hh := H.mul_mem (H.mul_mem hw hc) (H.inv_mem hw)
      rw [conjugate_swap, hwx, hwy] at hh
      exact hh
  apply top_unique
  rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro s ⟨x, y, hxy, rfl⟩
  exact hall x y

private theorem aut_ne_top [Nontrivial K] [Nontrivial L] :
    Aut K L ≠ ⊤ := by
  classical
  obtain ⟨k₀, k₁, hk⟩ := exists_pair_ne K
  obtain ⟨l₀, l₁, hl⟩ := exists_pair_ne L
  intro ht
  have hs : swap (k₀, l₀) (k₁, l₀) ∈ Aut K L := by rw [ht]; trivial
  have he := (hs (k₀, l₀) (k₀, l₁)).mpr rfl
  have hfix : swap (k₀, l₀) (k₁, l₀) (k₀, l₁) = (k₀, l₁) := by
    apply swap_apply_of_ne_of_ne
    · intro h; exact hl (congrArg Prod.snd h).symm
    · intro h; exact hl (congrArg Prod.snd h).symm
  rw [swap_apply_left, hfix] at he
  exact hk he.symm

theorem isCoatom_aut [Finite K] [Finite L] [Nontrivial K] [Nontrivial L] :
    IsCoatom (Aut K L) := by
  apply SetLike.isCoatom_iff.mpr
  exact ⟨aut_ne_top, fun H q hWH hq hqH => overgroup_eq_top H hWH q hq hqH⟩

theorem closure_aut_union_singleton [Finite K] [Finite L]
    (q : Perm (K × L)) (hq : q ∉ Aut K L) :
    Subgroup.closure ((Aut K L : Set (Perm (K × L))) ∪ {q}) = ⊤ := by
  refine overgroup_eq_top _ ?_ q hq ?_
  · intro w hw
    exact Subgroup.subset_closure (Set.mem_union_left _ hw)
  · exact Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton q))


end D5.S3.FiniteGroups.UniformPartitionMaximality
