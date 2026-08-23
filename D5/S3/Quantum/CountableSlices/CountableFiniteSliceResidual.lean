/- GID: D5/S3/Quantum/CountableSlices/CountableFiniteSliceResidual
   generality: G
   mirror-B: D5/B/S3/Quantum/CountableSlices/CountableFiniteSliceResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Countably many finite Hilbert slices leave a residual in a nonseparable space. -/

import D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Metrizable.Basic

/- Library-search audit trail (2026-08-23):
   * The completion family's frozen `cumulativeSpace` and `residualSpace`
     construct the source's closed cumulative and orthogonal residual spaces;
     they are imported rather than redeclared.
   * Repository search found no theorem combining countable finite-slice
     separability with the nonseparable residual consequence.
   * Pinned Mathlib has no exact combined theorem. The supporting results
     `TopologicalSpace.IsSeparable.iUnion`, `TopologicalSpace.IsSeparable.span`,
     `TopologicalSpace.IsSeparable.closure`,
     `TopologicalSpace.IsSeparable.separableSpace`, and
     `Submodule.orthogonal_eq_bot_iff` are all applied below. -/

noncomputable section

open scoped InnerProductSpace
open TopologicalSpace

namespace D5.S3.Quantum.CountableSlices.CountableFiniteSliceResidual

open D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A finite initial space followed by countably many finite orthogonal slices
has separable cumulative closure. Hence a nonseparable ambient Hilbert space
has a nonzero orthogonal residual after every such countable recursion. -/
theorem countable_finite_slice_separable_and_residual
    (S0 : Submodule 𝕜 H) (slice : Nat -> Submodule 𝕜 H)
    [FiniteDimensional 𝕜 S0] [forall n, FiniteDimensional 𝕜 (slice n)]
    (_hSlice : forall n,
      slice n <= (S0 ⊔ ⨆ i : Fin n, slice i.1)ᗮ) :
    let stages : Nat -> Submodule 𝕜 H := fun n =>
      S0 ⊔ ⨆ i : Fin n, slice i.1
    SeparableSpace (cumulativeSpace stages) /\
      (Not (SeparableSpace H) -> Not (residualSpace stages = ⊥)) := by
  let stages : Nat -> Submodule 𝕜 H := fun n =>
    S0 ⊔ ⨆ i : Fin n, slice i.1
  change SeparableSpace (cumulativeSpace stages) /\
    (Not (SeparableSpace H) -> Not (residualSpace stages = ⊥))
  have hStageFinite (n : Nat) : FiniteDimensional 𝕜 (stages n) := by
    dsimp only [stages]
    infer_instance
  have hStageSeparable : forall n, IsSeparable (stages n : Set H) := by
    intro n
    letI : FiniteDimensional 𝕜 (stages n) := hStageFinite n
    let basis := Module.finBasis 𝕜 (stages n)
    have hSpan :
        IsSeparable (Submodule.span 𝕜 (Set.range basis) : Set (stages n)) :=
      (Set.finite_range basis).isSeparable.span
    have hUniv : IsSeparable (Set.univ : Set (stages n)) := by
      simpa only [basis.span_eq, Submodule.top_coe] using hSpan
    have hImage := hUniv.image (continuous_subtype_val : Continuous ((↑) : stages n -> H))
    have hCoe :
        ((fun x : stages n => (x : H)) '' Set.univ) = (stages n : Set H) := by
      ext x
      simp
    rw [← hCoe]
    exact hImage
  have hUnion : IsSeparable (⋃ n, (stages n : Set H)) :=
    IsSeparable.iUnion hStageSeparable
  have hSup : IsSeparable ((⨆ n, stages n : Submodule 𝕜 H) : Set H) := by
    rw [Submodule.iSup_eq_span]
    exact hUnion.span
  have hCumulative : IsSeparable (cumulativeSpace stages : Set H) := by
    rw [cumulativeSpace, Submodule.topologicalClosure_coe]
    exact hSup.closure
  refine And.intro hCumulative.separableSpace ?_
  intro hNonseparable hResidual
  letI : (cumulativeSpace stages).HasOrthogonalProjection := by
    rw [cumulativeSpace]
    infer_instance
  have hTop : cumulativeSpace stages = ⊤ := by
    apply (Submodule.orthogonal_eq_bot_iff).mp
    simpa only [residualSpace] using hResidual
  apply hNonseparable
  apply isSeparable_univ_iff.mp
  simpa only [hTop, Submodule.top_coe] using hCumulative

example :
    forall n,
      (⊥ : Submodule Real Real) <=
        ((⊤ : Submodule Real Real) ⊔
          ⨆ _i : Fin n, (⊥ : Submodule Real Real))ᗮ := by
  intro n
  simp

example :
    SeparableSpace
        (cumulativeSpace (fun _n : Nat => (⊤ : Submodule Real Real))) /\
      (Not (SeparableSpace Real) ->
        Not (residualSpace (fun _n : Nat => (⊤ : Submodule Real Real)) = ⊥)) := by
  have hCumulative :
      cumulativeSpace (fun _n : Nat => (⊤ : Submodule Real Real)) = ⊤ := by
    simp [cumulativeSpace]
  constructor
  case left =>
    rw [hCumulative]
    infer_instance
  case right =>
    intro hNonseparable
    exact (hNonseparable inferInstance).elim

#print axioms countable_finite_slice_separable_and_residual

end D5.S3.Quantum.CountableSlices.CountableFiniteSliceResidual
