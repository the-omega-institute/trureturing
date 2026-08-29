/- GID: D5/S3/Analytic/Adelic/FiniteToroidalFrameReconstruction
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/FiniteToroidalFrameReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compact nonvanishing twist covers yield finite weighted frames that reconstruct xi. -/

import D5.S3.Analytic.Adelic.ToroidalCechCompletion
import Mathlib.Analysis.InnerProductSpace.PiL2

/- Library-search audit trail (2026-08-28):
   * Exact repository searches for a finite toroidal frame, compact
     pointwise-nonvanishing period reconstruction, and the weighted-frame body
     below found no whole-statement owner or reusable generic D5 primitive.
   * `weightedEffectAnalysis` has a related square-root weighting shape, but
     its carrier is the source-specific real traceless-Hermitian space and its
     output is a linear map, not a complex period frame.
   * The canonical `nonvanishingDomain` construction is imported from the
     preceding toroidal completion module rather than redeclared.
   * Pinned Mathlib supplies `IsCompact.elim_finite_subcover`, the canonical
     `EuclideanSpace`, and the inner-product identities applied below. It has
     no completed-zeta or toroidal-period reconstruction theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.FiniteToroidalFrameReconstruction

open D5.S3.Analytic.Adelic.ToroidalCechCompletion
open D5.S3.Zeros.CompletedZeta

/-- The source's positive-square-root weighted coordinates on a finite set of
quadratic-period readouts. -/
def weightedFrame {Index : Type*} (selected : Finset Index)
    (weights : Index -> Real) (readout : Index -> ℂ -> ℂ) (point : ℂ) :
    EuclideanSpace ℂ selected :=
  WithLp.toLp 2 fun index =>
    (Real.sqrt (weights index.1) : ℂ) * readout index.1 point

/--
Pointwise nonvanishing twists over a compact spectral window admit a finite
subfamily. For every positive weighting of that subfamily, its carrier frame
is nonzero at every point and the corresponding period frame reconstructs the
canonical completed-zeta value. Because Lean inner products are conjugate
linear in the first variable, `inner carrier period` is the formal counterpart
of the source's first-linear `inner period carrier`.
-/
theorem finite_toroidal_frame_reconstruction {Index : Type*} (window : Set ℂ)
    (period twist : Index -> ℂ -> ℂ)
    (twistContinuous : ∀ index, Continuous (twist index))
    (factorization : ∀ index point,
      period index point = xiReading point * twist index point)
    (windowCompact : IsCompact window)
    (pointwiseNonvanishing : ∀ point ∈ window, ∃ index, twist index point ≠ 0) :
    ∃ selected : Finset Index,
      (∀ point ∈ window, ∃ index, index ∈ selected ∧ twist index point ≠ 0) ∧
      ∀ weights : Index -> Real,
        (∀ index ∈ selected, 0 < weights index) ->
        ∀ point ∈ window,
          weightedFrame selected weights twist point ≠ 0 ∧
          xiReading point =
            inner ℂ (weightedFrame selected weights twist point)
                (weightedFrame selected weights period point) /
              (‖weightedFrame selected weights twist point‖ : ℂ) ^ 2 := by
  classical
  let domain : Index -> Set ℂ := fun index => {point | twist index point ≠ 0}
  have domainOpen : ∀ index, IsOpen (domain index) := by
    intro index
    have asPreimage :
        domain index = (twist index) ⁻¹' ({0}ᶜ : Set ℂ) := by
      ext point
      simp [domain]
    rw [asPreimage]
    exact isOpen_compl_singleton.preimage (twistContinuous index)
  have domainCover : window ⊆ ⋃ index, domain index := by
    intro point pointInWindow
    obtain ⟨index, nonzero⟩ := pointwiseNonvanishing point pointInWindow
    exact Set.mem_iUnion.mpr ⟨index, nonzero⟩
  obtain ⟨selected, selectedCover⟩ :=
    windowCompact.elim_finite_subcover domain domainOpen domainCover
  have finiteNonvanishing :
      ∀ point ∈ window, ∃ index, index ∈ selected ∧ twist index point ≠ 0 := by
    intro point pointInWindow
    have covered := selectedCover pointInWindow
    obtain ⟨index, coveredByIndex⟩ := Set.mem_iUnion.mp covered
    obtain ⟨indexSelected, pointInDomain⟩ := Set.mem_iUnion.mp coveredByIndex
    exact ⟨index, indexSelected, pointInDomain⟩
  refine ⟨selected, finiteNonvanishing, ?_⟩
  intro weights weightsPositive point pointInWindow
  obtain ⟨index, indexSelected, twistNonzero⟩ :=
    finiteNonvanishing point pointInWindow
  have coordinateNonzero :
      weightedFrame selected weights twist point ⟨index, indexSelected⟩ ≠ 0 := by
    change (Real.sqrt (weights index) : ℂ) * twist index point ≠ 0
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2
        (weightsPositive index indexSelected)).ne')
      twistNonzero
  have carrierNonzero : weightedFrame selected weights twist point ≠ 0 := by
    intro frameZero
    apply coordinateNonzero
    simpa using congrArg
      (fun frame : EuclideanSpace ℂ selected => frame ⟨index, indexSelected⟩)
      frameZero
  have frameFactorization :
      weightedFrame selected weights period point =
        xiReading point • weightedFrame selected weights twist point := by
    apply PiLp.ext
    intro selectedIndex
    change
      (Real.sqrt (weights selectedIndex.1) : ℂ) *
          period selectedIndex.1 point =
        xiReading point *
          ((Real.sqrt (weights selectedIndex.1) : ℂ) *
            twist selectedIndex.1 point)
    rw [factorization]
    ring
  refine ⟨carrierNonzero, ?_⟩
  rw [frameFactorization, inner_smul_right, inner_self_eq_norm_sq_to_K]
  exact (mul_div_cancel_right₀ (xiReading point)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr carrierNonzero)))).symm

#print axioms weightedFrame
#print axioms finite_toroidal_frame_reconstruction

end D5.S3.Analytic.Adelic.FiniteToroidalFrameReconstruction
