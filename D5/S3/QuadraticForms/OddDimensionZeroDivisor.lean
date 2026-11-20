/- GID: D5/S3/QuadraticForms/OddDimensionZeroDivisor
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/OddDimensionZeroDivisor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bilinear maps have zero divisors when polynomials of the source degree have roots. -/

import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Zero divisors of bilinear maps

Let `m : U × V → W` be bilinear over a field `K` with `dim W ≤ dim U` and `dim V ≥ 2`. If
`dim W < dim U`, or if `dim W = dim U` and every polynomial over `K` whose degree is `dim U` has
a root, then `m a b = 0` for some nonzero `a`, `b`. Over the real numbers the root condition
holds in every odd dimension of `U`; over an algebraically closed field in every dimension.

The argument: choose linearly independent `b`, `c`. If `m(·, b)` is not injective it has a
nonzero kernel vector. Otherwise it is an isomorphism `U ≃ W`, and an eigenvector `a` of
`m(·, b)⁻¹ ∘ m(·, c)` with eigenvalue `μ` satisfies `m a (c - μ • b) = 0`.
-/

namespace D5.S3.QuadraticForms.OddDimensionZeroDivisor

open Module

/-- Over a real closed field, every endomorphism of a space of odd finite dimension has an
eigenvalue: its characteristic polynomial has odd degree. -/
theorem exists_hasEigenvalue_of_odd_finrank {K U : Type*} [Field K] [IsRealClosed K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U] (f : Module.End K U)
    (h : Odd (Module.finrank K U)) : ∃ μ : K, f.HasEigenvalue μ :=
  (IsRealClosed.exists_isRoot_of_odd_natDegree (f := f.charpoly)
      (by rwa [LinearMap.charpoly_natDegree])).imp
    fun μ hμ => (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hμ

/-- A bilinear map `m : U × V → W` with `dim W ≤ dim U` and `dim V ≥ 2` has a zero divisor when
`dim W < dim U`, or when `dim W = dim U` and every polynomial of degree `dim U` has a root. -/
theorem exists_zero_divisor {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (m : U →ₗ[K] V →ₗ[K] W)
    (hroot : Module.finrank K W = Module.finrank K U →
      ∀ f : Polynomial K, f.natDegree = Module.finrank K U → ∃ x, f.IsRoot x)
    (hW : Module.finrank K W ≤ Module.finrank K U) (hV : 2 ≤ Module.finrank K V) :
    ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ m a b = 0 := by
  classical
  -- `dim U = 0` (in particular `U` infinite-dimensional) forces `dim W = 0 = dim U`, and then
  -- the root condition is refuted by the constant `1`.
  have hUpos : 0 < finrank K U := by
    rcases Nat.eq_zero_or_pos (finrank K U) with h0 | hpos
    · obtain ⟨x, hx⟩ := hroot (by omega) 1 (by simp [h0])
      simp at hx
    · exact hpos
  have : FiniteDimensional K U := Module.finite_of_finrank_pos hUpos
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨b, hb⟩ := exists_ne (0 : V)
  obtain ⟨c, hbc⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K) (by omega) hb
  by_cases hinj : Function.Injective (m.flip b)
  · have hdim : finrank K U = finrank K W :=
      le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) hW
    set e : U ≃ₗ[K] W := (m.flip b).linearEquivOfInjective hinj hdim
    set f : Module.End K U := e.symm.toLinearMap ∘ₗ m.flip c
    obtain ⟨μ, hμ⟩ := hroot hdim.symm f.charpoly (LinearMap.charpoly_natDegree f)
    obtain ⟨a, ha⟩ :=
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hμ).exists_hasEigenvector
    have hfa : f a = μ • a := Module.End.mem_eigenspace_iff.1 ha.1
    have hmac : m a c = μ • m a b := by
      have h1 : e (f a) = m a c := by simp [f]
      rw [← h1, hfa, map_smul]
      rfl
    refine ⟨a, c - μ • b, ha.2, ?_, ?_⟩
    · intro h0
      have := (LinearIndependent.pair_iff.1 hbc) (-μ) 1 (by rw [← h0]; module)
      exact one_ne_zero this.2
    · rw [map_sub, map_smul, hmac, sub_self]
  · rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨a, hab, ha⟩ := hinj
    exact ⟨a, b, ha, hb, hab⟩

end D5.S3.QuadraticForms.OddDimensionZeroDivisor
