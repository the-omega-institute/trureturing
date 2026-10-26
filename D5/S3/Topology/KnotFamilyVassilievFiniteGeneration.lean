/- GID: D5/S3/Topology/KnotFamilyVassilievFiniteGeneration
   generality: G
   mirror-B: D5/B/S3/Topology/KnotFamilyVassilievFiniteGeneration
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Subalgebras of univariate polynomial rings over fields are finitely generated. -/

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! Finite generation for subalgebras of univariate polynomial rings. -/

namespace D5.S3.Topology.KnotFamilyVassilievFiniteGeneration

open Polynomial

def claim : Prop :=
  ∀ (ι : Type) (p : ι → Polynomial ℚ), ∃ s : Finset ι,
    Algebra.adjoin ℚ (p '' (s : Set ι)) = Algebra.adjoin ℚ (Set.range p)

private theorem fg_of_constant {k : Type*} [Field k] (a : Subalgebra k (Polynomial k))
    (h : ∀ f ∈ a, f.natDegree = 0) : a.FG := by
  have ha : a = ⊥ := by
    refine le_antisymm (fun f hf ↦ ?_) bot_le
    rw [eq_C_of_natDegree_eq_zero (h f hf)]
    exact (⊥ : Subalgebra k (Polynomial k)).algebraMap_mem (f.coeff 0)
  rw [ha]
  exact Subalgebra.fg_bot

private theorem integral_X {k : Type*} [Field k] (a : Subalgebra k (Polynomial k))
    (f : Polynomial k) (hf : f ∈ a) (hd : 0 < f.natDegree) :
    IsIntegral a (X : Polynomial k) := by
  have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd)
  let q : Polynomial k := C f.leadingCoeff⁻¹ * f
  have hq : q.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hc)
  have hqd : q.natDegree ≠ 0 := by
    rw [natDegree_C_mul (inv_ne_zero hc)]
    exact Nat.ne_of_gt hd
  have hqa : (q.map (algebraMap k a)).Monic := hq.map _
  have hqad : (q.map (algebraMap k a)).natDegree ≠ 0 := by
    rw [hq.natDegree_map _]
    exact hqd
  apply IsIntegral.of_aeval_monic hqa hqad
  rw [aeval_map_algebraMap, aeval_X_left_apply]
  exact isIntegral_algebraMap (R := a) (x := ⟨q, a.mul_mem (a.algebraMap_mem _) hf⟩)

private theorem finite_of_integral_X {k : Type*} [Field k]
    (a : Subalgebra k (Polynomial k)) (h : IsIntegral a (X : Polynomial k)) :
    Module.Finite a (Polynomial k) := by
  have ht : Algebra.adjoin a {(X : Polynomial k)} = ⊤ := by
    apply Subalgebra.restrictScalars_injective k
    rw [Subalgebra.restrictScalars_top]
    apply top_unique
    rw [← Polynomial.adjoin_X]
    apply Algebra.adjoin_le
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Algebra.subset_adjoin (R := a) (s := {(X : Polynomial k)}) rfl
  exact Module.Finite.of_fg_top (by
    simpa only [ht, Algebra.top_toSubmodule] using h.fg_adjoin_singleton)

private theorem fg_of_finite {k : Type*} [Field k] (a : Subalgebra k (Polynomial k))
    (h : Module.Finite a (Polynomial k)) : a.FG := by
  exact a.fg_top.mp (fg_of_fg_of_fg (A := k) (B := a) (C := Polynomial k)
    Algebra.FiniteType.out h.fg_top Subtype.val_injective)

theorem subalgebra_fg {k : Type*} [Field k] (a : Subalgebra k (Polynomial k)) : a.FG := by
  by_cases h : ∀ f ∈ a, f.natDegree = 0
  · exact fg_of_constant a h
  · push Not at h
    obtain ⟨f, hf, hd⟩ := h
    exact fg_of_finite a (finite_of_integral_X a (integral_X a f hf (Nat.pos_of_ne_zero hd)))

private theorem finite_subfamily {k : Type*} [Field k] {ι : Type*}
    (p : ι → Polynomial k) (h : (Algebra.adjoin k (Set.range p)).FG) :
    ∃ s : Finset ι,
      Algebra.adjoin k (p '' (s : Set ι)) = Algebra.adjoin k (Set.range p) := by
  classical
  have hm (s t : Finset ι) (hst : s ⊆ t) :
      Algebra.adjoin k (p '' (s : Set ι)) ≤ Algebra.adjoin k (p '' (t : Set ι)) :=
    Algebra.adjoin_mono (Set.image_mono hst)
  have hsupp (x : Polynomial k) (hx : x ∈ Algebra.adjoin k (Set.range p)) :
      ∃ s : Finset ι, x ∈ Algebra.adjoin k (p '' (s : Set ι)) := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨{i}, Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, rfl⟩⟩
    | algebraMap r => exact ⟨∅, Subalgebra.algebraMap_mem _ r⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s ∪ t, Subalgebra.add_mem _
        (hm s (s ∪ t) Finset.subset_union_left hs)
        (hm t (s ∪ t) Finset.subset_union_right ht)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s ∪ t, Subalgebra.mul_mem _
        (hm s (s ∪ t) Finset.subset_union_left hs)
        (hm t (s ∪ t) Finset.subset_union_right ht)⟩
  obtain ⟨t, ht⟩ := h
  choose! s hs using fun (x : Polynomial k) (hx : x ∈ t) ↦
    hsupp x (by rw [← ht]; exact Algebra.subset_adjoin hx)
  refine ⟨t.biUnion s, le_antisymm ?_ ?_⟩
  · apply Algebra.adjoin_mono
    rintro _ ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  · rw [← ht]
    apply Algebra.adjoin_le
    intro x hx
    exact hm (s x) (t.biUnion s)
      (fun i hi ↦ Finset.mem_biUnion.mpr ⟨x, hx, hi⟩) (hs x hx)

theorem result : claim := by
  intro ι p
  exact finite_subfamily p (subalgebra_fg (Algebra.adjoin ℚ (Set.range p)))

end D5.S3.Topology.KnotFamilyVassilievFiniteGeneration
