/- GID: D5/S3/Topology/KnotFamilyVassilievFiniteGeneration
   generality: G
   mirror-B: D5/B/S3/Topology/KnotFamilyVassilievFiniteGeneration
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every subalgebra of a polynomial ring over a field is finitely generated. -/

import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

namespace D5.S3.Topology.KnotFamilyVassilievFiniteGeneration

open Polynomial

def claim : Prop :=
  ∀ (ι : Type) (p : ι → Polynomial ℚ), ∃ s : Finset ι,
    Algebra.adjoin ℚ (p '' (s : Set ι)) = Algebra.adjoin ℚ (Set.range p)

private theorem fg_of_constant {k : Type*} [Field k] (a : Subalgebra k (Polynomial k))
    (h : ∀ f ∈ a, f.natDegree = 0) : a.FG := by
  sorry

private theorem integral_X {k : Type*} [Field k] (a : Subalgebra k (Polynomial k))
    (f : Polynomial k) (hf : f ∈ a) (hd : 0 < f.natDegree) :
    IsIntegral a (X : Polynomial k) := by
  sorry

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
  · push_neg at h
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
