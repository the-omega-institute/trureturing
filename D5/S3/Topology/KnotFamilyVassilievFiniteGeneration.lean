/- GID: D5/S3/Topology/KnotFamilyVassilievFiniteGeneration
   generality: G
   mirror-B: D5/B/S3/Topology/KnotFamilyVassilievFiniteGeneration
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every subalgebra of a polynomial ring over a field is finitely generated. -/

import Mathlib.RingTheory.Adjoin.Tower
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
  sorry

private theorem fg_of_finite {k : Type*} [Field k] (a : Subalgebra k (Polynomial k))
    (h : Module.Finite a (Polynomial k)) : a.FG := by
  sorry

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
  sorry

theorem result : claim := by
  intro ι p
  exact finite_subfamily p (subalgebra_fg (Algebra.adjoin ℚ (Set.range p)))

end D5.S3.Topology.KnotFamilyVassilievFiniteGeneration
