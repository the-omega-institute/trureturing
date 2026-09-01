/- GID: D5/S3/Observer/Hankel/HankelMinimalStateDimension
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/HankelMinimalStateDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hankel rank bounds every realization and is attained by the canonical quotient. -/

import D5.S3.Observer.Hankel.HankelRankMinimality
import D5.S3.Observer.Linear.ReachableObservableQuotientDescent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.HankelMinimalStateDimension

open D5.S3.Observer.Hankel.HankelRankMinimality
open D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
open D5.S3.Observer.LinearMemory.ZeroMemoryCriterion
open Module

/-- Corollary 244.1, source lines 19958--19970. Equality of every Markov
parameter is the complete input-output behavior from lines 19866--19872.
Every finite-dimensional realization of that behavior has state dimension at
least the stable Hankel rank, and the reachable-state quotient by its
all-future unobservable part attains that rank. The quotient is the carrier of
the system whose dynamics, input, and output descend in
`reachable_observable_quotient_descent`. -/
theorem hankel_rank_lower_bound_and_quotient_attainment
    {K V V' U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (A' : V' →ₗ[K] V') (B' : U →ₗ[K] V') (C' : V' →ₗ[K] Y)
    (sameBehavior : ∀ k : ℕ,
      markovParameter A' B' C' k = markovParameter A B C k)
    (rows columns : ℕ)
    (rowsLarge : finrank K V ≤ rows)
    (columnsLarge : finrank K V ≤ columns) :
    finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
        finrank K V' ∧
      finrank K
          ((reachableSubspace A B) ⧸
            (eventualKernel C A).comap (reachableSubspace A B).subtype) =
        finrank K (LinearMap.range (finiteHankel A B C rows columns)) := by
  constructor
  · have hankelEquality :
        finiteHankel A' B' C' rows columns =
          finiteHankel A B C rows columns := by
      apply LinearMap.ext
      intro input
      funext row
      simp only [finiteHankel, LinearMap.pi_apply, LinearMap.lsum_apply,
        LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro column _
      rw [sameBehavior]
    rw [← hankelEquality,
      finiteHankel_eq_observability_comp_controllability,
      LinearMap.range_comp]
    exact
      (Submodule.finrank_map_le
        (finiteObservability A' C' rows)
        (LinearMap.range (finiteControllability A' B' columns))).trans
        (LinearMap.range (finiteControllability A' B' columns)).finrank_le
  · let reachable := reachableSubspace A B
    let invisible := eventualKernel C A
    let residual : Submodule K reachable := invisible.comap reachable.subtype
    change finrank K (reachable ⧸ residual) =
      finrank K (LinearMap.range (finiteHankel A B C rows columns))
    have residualFinrank :
        finrank K residual =
          finrank K (reachable ⊓ invisible : Submodule K V) := by
      calc
        finrank K residual =
            finrank K (residual.map reachable.subtype) := by
          symm
          exact Submodule.finrank_map_subtype_eq reachable residual
        _ = finrank K (reachable ⊓ invisible : Submodule K V) := by
          change
            finrank K
                ((invisible.comap reachable.subtype).map reachable.subtype) =
              finrank K (reachable ⊓ invisible : Submodule K V)
          rw [Submodule.map_comap_subtype]
    rw [Submodule.finrank_quotient, residualFinrank]
    simpa only [reachable, invisible] using
      (hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim
        A B C rows columns rowsLarge columnsLarge).symm

#print axioms hankel_rank_lower_bound_and_quotient_attainment

/- Reverse probe for CAS-A1: the first public leaf recovers the promised lower
bound without inspecting the proof term. -/
example
    {K V V' U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V']
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : ℕ)
    (publicConclusion :
      finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
          finrank K V' ∧
        finrank K
            ((reachableSubspace A B) ⧸
              (eventualKernel C A).comap (reachableSubspace A B).subtype) =
          finrank K (LinearMap.range (finiteHankel A B C rows columns))) :
    finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
      finrank K V' :=
  publicConclusion.1

/- Reverse probe for CAS-A2: quotient attainment and rank-nullity recover the
dimension balance behind the stable Hankel-rank formula. -/
example
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : ℕ)
    (attainment :
      finrank K
          ((reachableSubspace A B) ⧸
            (eventualKernel C A).comap (reachableSubspace A B).subtype) =
        finrank K (LinearMap.range (finiteHankel A B C rows columns))) :
    finrank K (LinearMap.range (finiteHankel A B C rows columns)) +
        finrank K
          ((eventualKernel C A).comap (reachableSubspace A B).subtype) =
      finrank K (reachableSubspace A B) := by
  rw [← attainment]
  exact Submodule.finrank_quotient_add_finrank _

/- Trivialization probe for CAS-A1: a zero-dimensional state cannot reproduce
the nonzero Markov behavior of the one-dimensional identity input/readout
system, so `sameBehavior` prevents the `Unit`/zero-state collapse. -/
example :
    ¬ ∀ k : ℕ,
      markovParameter
          (0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin 0 → ℚ))
          (0 : ℚ →ₗ[ℚ] (Fin 0 → ℚ))
          (0 : (Fin 0 → ℚ) →ₗ[ℚ] ℚ) k =
        markovParameter
          (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id LinearMap.id k := by
  intro sameBehavior
  have atZero := congrArg (fun map : ℚ →ₗ[ℚ] ℚ => map 1) (sameBehavior 0)
  norm_num [markovParameter] at atZero

end D5.S3.Observer.Hankel.HankelMinimalStateDimension
