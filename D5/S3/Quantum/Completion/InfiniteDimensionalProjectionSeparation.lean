/- GID: D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dense finite-dimensional projection towers converge pointwise but not uniformly. -/

/- Library-search audit trail (2026-08-22):
   * The frozen repository theorem `increasing_projection_strong_limit` gives the exact
     pointwise convergence leg for increasing projection stages and is applied directly.
   * Pinned-Mathlib and Loogle searches found the exact supporting declarations
     `Submodule.starProjection_orthogonal`, `Submodule.norm_starProjection`,
     `FiniteDimensional.of_surjective`, and `Module.Finite.not_linearIndependent_of_infinite`;
     all applicable hits are used directly below.
   * LeanSearch for increasing finite-dimensional Hilbert subspaces converging strongly but
     not in operator norm returned only supporting finite-dimensional closure and operator
     topology declarations, with no theorem packaging all source clauses.
   * Repository searches found no declaration combining finite-stage nontermination,
     pointwise completion, failure of operator-norm completion, and the norm-one identity. -/

import D5.S3.Quantum.Completion.IncreasingProjectionStrongLimit
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

namespace D5.S3.Quantum.Completion.InfiniteDimensionalProjectionSeparation

open Filter
open Topology
open scoped lp
open D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction
open D5.S3.Quantum.Completion.IncreasingProjectionStrongLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {K H : Type*} [RCLike K] [NormedAddCommGroup H]
  [InnerProductSpace K H] [CompleteSpace H]

local instance finiteStageCompleteSpace
    (S : Nat -> Submodule K H) [forall n, FiniteDimensional K (S n)] (n : Nat) :
    CompleteSpace (S n) :=
  FiniteDimensional.complete K (S n)

/-- An increasing tower of finite-dimensional subspaces with dense cumulative span in an
infinite-dimensional Hilbert space never reaches the whole space at a finite stage. Its
orthogonal projections converge on every vector, but their distance from the identity has
operator norm one at every stage and therefore cannot converge to zero. -/
theorem infinite_dimensional_projection_separation
    (S : Nat -> Submodule K H)
    [forall n, FiniteDimensional K (S n)]
    (hInfinite : ¬ FiniteDimensional K H)
    (hS : Monotone S)
    (hDense : cumulativeSpace S = ⊤) :
    (forall n, S n ≠ ⊤) /\
      (forall x, Tendsto (fun n => (S n).starProjection x) atTop (nhds x)) /\
      (¬ Tendsto
        (fun n => ‖ContinuousLinearMap.id K H - (S n).starProjection‖)
        atTop (nhds 0)) /\
      (forall n, ‖ContinuousLinearMap.id K H - (S n).starProjection‖ = 1) := by
  have hProper : forall n, S n ≠ ⊤ := by
    intro n htop
    apply hInfinite
    apply FiniteDimensional.of_surjective (S n).subtype
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [htop]
    exact Submodule.mem_top
  letI : (cumulativeSpace S).HasOrthogonalProjection := by
    rw [hDense]
    infer_instance
  have hPointwise :
      forall x, Tendsto (fun n => (S n).starProjection x) atTop (nhds x) := by
    intro x
    have hLimit := (increasing_projection_strong_limit S hS).1 x
    have hProjection : (cumulativeSpace S).starProjection x = x := by
      apply Submodule.starProjection_eq_self_iff.mpr
      rw [hDense]
      exact Submodule.mem_top
    simpa only [hProjection] using hLimit
  have hNorm :
      forall n, ‖ContinuousLinearMap.id K H - (S n).starProjection‖ = 1 := by
    intro n
    have hOrthogonal : (S n)ᗮ ≠ ⊥ := by
      intro hbot
      exact hProper n ((Submodule.orthogonal_eq_bot_iff).mp hbot)
    calc
      ‖ContinuousLinearMap.id K H - (S n).starProjection‖ =
          ‖(S n)ᗮ.starProjection‖ := by
            rw [Submodule.starProjection_orthogonal]
      _ = 1 := (S n)ᗮ.norm_starProjection hOrthogonal
  have hNotUniform :
      ¬ Tendsto
        (fun n => ‖ContinuousLinearMap.id K H - (S n).starProjection‖)
        atTop (nhds 0) := by
    intro hUniform
    have hOne : Tendsto (fun _n : Nat => (1 : Real)) atTop (nhds 0) := by
      simpa only [hNorm] using hUniform
    exact zero_ne_one (tendsto_nhds_unique hOne tendsto_const_nhds)
  exact ⟨hProper, hPointwise, hNotUniform, hNorm⟩

/-- The standard Hilbert basis of real square-summable sequences supplies a concrete tower
satisfying every hypothesis of the separation theorem. -/
example :
    let H := lp (fun _ : Nat => Real) 2
    exists S : Nat -> Submodule Real H,
      (forall n, FiniteDimensional Real (S n)) /\
      (¬ FiniteDimensional Real H) /\
      Monotone S /\
      cumulativeSpace S = ⊤ := by
  let H := lp (fun _ : Nat => Real) 2
  let b : HilbertBasis Nat Real H := default
  let S : Nat -> Submodule Real H := fun n =>
    Submodule.span Real (Set.range fun i : Fin n => b i)
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro n
    exact Module.Finite.span_of_finite Real (Set.finite_range fun i : Fin n => b i)
  · intro hFinite
    letI : FiniteDimensional Real H := hFinite
    exact Module.Finite.not_linearIndependent_of_infinite b b.orthonormal.linearIndependent
  · intro m n hmn
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.isLt hmn⟩, rfl⟩
  · have hSpan : Submodule.span Real (Set.range b) ≤ iSup S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply (le_iSup S (i + 1))
      exact Submodule.subset_span ⟨⟨i, Nat.lt_succ_self i⟩, rfl⟩
    apply le_antisymm le_top
    rw [cumulativeSpace, ← b.dense_span]
    exact Submodule.topologicalClosure_mono hSpan

/-- The concrete Hilbert-space carrier used above is inhabited. -/
example : Nonempty (lp (fun _ : Nat => Real) 2) := ⟨0⟩

#print axioms infinite_dimensional_projection_separation

end D5.S3.Quantum.Completion.InfiniteDimensionalProjectionSeparation
