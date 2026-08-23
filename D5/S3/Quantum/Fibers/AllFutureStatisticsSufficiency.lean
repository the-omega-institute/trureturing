/- GID: D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/AllFutureStatisticsSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical predictive projection is equivalent to all future statistics. -/

import D5.S3.Quantum.Fibers.MinimalPredictiveSummary

/- Library-search audit trail (2026-08-23):
   * Exact frozen family objects `HermitianTraceZero`, `predictiveSpace`, and
     `predictiveProjection` supply the source carrier, all-iterate visible
     space, and canonical predictive state. They are imported directly.
   * The related frozen theorem
     `future_statistics_iff_annihilates_infinite_system` reaches annihilation
     of the Heisenberg span, but does not expose canonical projection equality.
   * Repository search found no theorem directly equating two values of
     `predictiveProjection` with every iterated-effect expectation.
   * Pinned-Mathlib exact hits `Submodule.projectionOnto_apply_eq_zero_iff`
     and `Submodule.span_induction` are applied below. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix
open ClosedSubmodule

namespace D5.S3.Quantum.Fibers.AllFutureStatisticsSufficiency

open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Fibers.MinimalPredictiveSummary

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {d : Type*} [Fintype d] [DecidableEq d]

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix d d ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix d d ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- Two centered density-state coordinates have the same canonical predictive
state if and only if every centered effect has the same expectation after
every finite Heisenberg iterate. -/
theorem all_future_statistics_sufficiency
    {r : Nat}
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ]
      HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d))
    (rho sigma : HermitianTraceZero (d := d)) :
    predictiveProjection heisenberg effects rho =
        predictiveProjection heisenberg effects sigma ↔
      ∀ n effectIndex,
        inner ℝ rho ((heisenberg^[n]) (effects effectIndex)) =
          inner ℝ sigma ((heisenberg^[n]) (effects effectIndex)) := by
  let visible := predictiveSpace heisenberg effects
  let projection := predictiveProjection heisenberg effects
  change projection rho = projection sigma ↔ _
  constructor
  · intro hprojection n effectIndex
    have hzero : projection (rho - sigma) = 0 := by
      rw [map_sub, hprojection, sub_self]
    have horthogonal : rho - sigma ∈ visibleᗮ :=
      (Submodule.projectionOnto_apply_eq_zero_iff
        visible.isCompl_orthogonal).mp hzero
    have hgenerator :
        (heisenberg^[n]) (effects effectIndex) ∈ visible := by
      apply Submodule.subset_span
      exact ⟨(n, effectIndex), rfl⟩
    have hinner := (Submodule.mem_orthogonal' visible (rho - sigma)).mp
      horthogonal _ hgenerator
    simpa [inner_sub_left, sub_eq_zero] using hinner
  · intro hfuture
    have horthogonal : rho - sigma ∈ visibleᗮ := by
      rw [Submodule.mem_orthogonal']
      intro observable hobservable
      refine Submodule.span_induction ?_ (by simp) ?_ ?_ hobservable
      · rintro generator ⟨⟨n, effectIndex⟩, rfl⟩
        simpa [inner_sub_left, sub_eq_zero] using hfuture n effectIndex
      · intro left right _ _ hleft hright
        simp [inner_add_right, hleft, hright]
      · intro scalar observable _ hobservable
        simp [inner_smul_right, hobservable]
    have hzero : projection (rho - sigma) = 0 :=
      (Submodule.projectionOnto_apply_eq_zero_iff
        visible.isCompl_orthogonal).mpr horthogonal
    have hsub : projection rho - projection sigma = 0 := by
      simpa only [map_sub] using hzero
    exact sub_eq_zero.mp hsub

example {r : Nat}
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ]
      HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d))
    (rho sigma : HermitianTraceZero (d := d)) :
    predictiveProjection heisenberg effects rho =
        predictiveProjection heisenberg effects sigma ↔
      ∀ n effectIndex,
        inner ℝ rho ((heisenberg^[n]) (effects effectIndex)) =
          inner ℝ sigma ((heisenberg^[n]) (effects effectIndex)) :=
  all_future_statistics_sufficiency heisenberg effects rho sigma

#print axioms all_future_statistics_sufficiency

end D5.S3.Quantum.Fibers.AllFutureStatisticsSufficiency
