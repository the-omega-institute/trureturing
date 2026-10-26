/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum
   mirror-E: none(waiver:full-source-maximum)
   anchors: []
   utility: none
   digest: The full automorphism maximum of positive finite dimensional perfect complex evolution algebras is attained in every dimension. -/

import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-! Full bilinear evolution automorphisms, their sharp bound, and attaining products. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximum

open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
open D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight

private theorem identity_weight (n : ℕ) :
    weight (1 : Equiv.Perm (Fin n)).partition.parts = n.factorial := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [Equiv.Perm.parts_partition, weight]
  · simp [Equiv.Perm.parts_partition, weight, hn]

private theorem maximizer_permutation {n : ℕ} (hn : 1 ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), weight σ.partition.parts = maximumWeight n := by
  classical
  by_cases hlarge : 7 ≤ n
  · exact ⟨1, (identity_weight n).trans (maximum_weight_eq_factorial hlarge).symm⟩
  have hsmall := maximum_weight_small
  interval_cases n
  · exact ⟨1, by simpa [identity_weight] using hsmall.1.symm⟩
  · obtain ⟨σ,hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin 2) (m := {2})).mpr
      (by norm_num)
    refine ⟨σ, ?_⟩
    rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hσ]
    norm_num [weight, hsmall.2.1]
  · obtain ⟨σ,hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin 3) (m := {3})).mpr
      (by norm_num)
    refine ⟨σ, ?_⟩
    rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hσ]
    norm_num [weight, hsmall.2.2.1]
  · obtain ⟨σ,hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin 4) (m := {2,2})).mpr
      (by norm_num)
    refine ⟨σ, ?_⟩
    rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hσ]
    norm_num [weight, hsmall.2.2.2.1]
  · obtain ⟨σ,hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin 5) (m := {5})).mpr
      (by norm_num)
    refine ⟨σ, ?_⟩
    rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hσ]
    norm_num [weight, hsmall.2.2.2.2.1]
  · obtain ⟨σ,hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin 6) (m := {2,2,2})).mpr
      (by norm_num)
    refine ⟨σ, ?_⟩
    rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hσ]
    norm_num [weight, hsmall.2.2.2.2.2]

/-- Conjecture 3's universal full-group bound and an actual perfect attaining algebra
in every positive dimension. The multiplication need not be associative. -/
theorem result (n : ℕ) (hn : 1 ≤ n) :
    (∀ (A : Type*) [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
      (ι : Type*) [Fintype ι] (hd : Module.finrank ℂ A = n)
      (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (b : Module.Basis ι ℂ A),
      (∀ i j : ι, i ≠ j → μ (b i) (b j) = 0) → productSpan μ = ⊤ →
        Finite (Aut μ) ∧ Nat.card (Aut μ) ≤ maximumWeight n) ∧
    (∃ μ : Product n, Module.finrank ℂ (Coord n) = n ∧ commutative μ ∧
      hasNaturalBasis μ ∧ productSpan μ = ⊤ ∧
      Finite (Aut μ) ∧ Nat.card (Aut μ) = maximumWeight n) := by
  constructor
  · intro A _ _ _ ι _ hd μ b hb hp
    exact finite_and_bound hn hd μ b hb hp
  · obtain ⟨σ,hσ⟩ := maximizer_permutation hn
    obtain ⟨hc,hb,hp,hf,hcard⟩ := permutation_family σ
    refine ⟨permutationProduct σ, Module.finrank_fin_fun ℂ, hc, hb, ?_, hf,
      hcard.trans hσ⟩
    simpa only [productSpan, perfect, square, Submodule.mem_top, true_and] using hp

#print axioms result

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximum
