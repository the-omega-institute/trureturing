/- GID: D5/S3/Quantum/Fibers/MinimalPredictiveSummary
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/MinimalPredictiveSummary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every linear future-sufficient summary factors uniquely onto the predictive space. -/

import D5.S3.Quantum.Fibers.CenteredEffectTowerStability
import Mathlib.LinearAlgebra.Isomorphisms

/- Library-search audit trail (2026-08-23):
   * Exact repository hits `HermitianTraceZero` and `towerSpace` supply the
     source's real traceless-Hermitian carrier and centered Heisenberg family;
     they are imported rather than redeclared.
   * Repository searches found scalar-valued `payoff_price_factorization_iff`
     and set-valued `causal_state_factorization`, but no vector-valued linear
     theorem combining unique factorization through `LinearMap.range` with the
     required finrank inequality.
   * Pinned Mathlib exact hits `LinearMap.quotKerEquivRange`, `Submodule.liftQ`,
     `Submodule.orthogonalProjectionOnto_eq_zero_iff`, `Submodule.span_induction`,
     and `LinearMap.finrank_le_finrank_of_surjective` are applied below. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix
open ClosedSubmodule

namespace D5.S3.Quantum.Fibers.MinimalPredictiveSummary

open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {d : Type*} [Fintype d] [Nonempty d] [DecidableEq d]

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix d d ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix d d ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- The source's final visible space, constructed as the real span of every
centered effect under every finite Heisenberg iterate. -/
def predictiveSpace {r : Nat}
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ] HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d)) :
    Submodule ℝ (HermitianTraceZero (d := d)) :=
  Submodule.span ℝ (Set.range fun index : Nat × Fin (r + 1) =>
    (heisenberg^[index.1]) (effects index.2))

/-- The canonical orthogonal projection onto the final predictive space,
viewed as an algebraic real-linear map. -/
noncomputable def predictiveProjection {r : Nat}
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ] HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d)) :
    HermitianTraceZero (d := d) →ₗ[ℝ] predictiveSpace heisenberg effects :=
  (predictiveSpace heisenberg effects).projectionOnto
    (predictiveSpace heisenberg effects)ᗮ
    (predictiveSpace heisenberg effects).isCompl_orthogonal

/-- If a linear summary determines every centered Heisenberg expectation,
orthogonal projection onto the final predictive space factors through its
attainable range in exactly one way, forcing the stated dimension bound. -/
theorem minimal_predictive_summary
    {r : Nat} {W : Type*} [AddCommGroup W] [Module ℝ W]
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ] HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d))
    (summary : HermitianTraceZero (d := d) →ₗ[ℝ] W)
    (determinesFuture : ∀ x y, summary x = summary y ->
      ∀ n effectIndex,
        inner ℝ x ((heisenberg^[n]) (effects effectIndex)) =
          inner ℝ y ((heisenberg^[n]) (effects effectIndex))) :
    (∃! factor : LinearMap.range summary →ₗ[ℝ]
        predictiveSpace heisenberg effects,
      predictiveProjection heisenberg effects =
        factor.comp summary.rangeRestrict) ∧
    Module.finrank ℝ (predictiveSpace heisenberg effects) ≤
      Module.finrank ℝ (LinearMap.range summary) := by
  let visible := predictiveSpace heisenberg effects
  let projection : HermitianTraceZero (d := d) →ₗ[ℝ] visible :=
    predictiveProjection heisenberg effects
  have hker : summary.ker ≤ projection.ker := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply (Submodule.projectionOnto_apply_eq_zero_iff
      visible.isCompl_orthogonal).mpr
    rw [Submodule.mem_orthogonal']
    intro observable hobservable
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hobservable
    · rintro generator ⟨⟨n, effectIndex⟩, rfl⟩
      have hfuture := determinesFuture x 0 (by simpa using hx) n effectIndex
      simpa using hfuture
    · intro left right _ _ hleft hright
      simp [inner_add_right, hleft, hright]
    · intro scalar observable _ hobservable
      simp [inner_smul_right, hobservable]
  let factor : LinearMap.range summary →ₗ[ℝ] visible :=
    (summary.ker.liftQ projection hker).comp
      summary.quotKerEquivRange.symm.toLinearMap
  have factorizes :
      projection = factor.comp summary.rangeRestrict := by
    apply LinearMap.ext
    intro x
    change projection x =
      (summary.ker.liftQ projection hker)
        (summary.quotKerEquivRange.symm
          ⟨summary x, summary.mem_range_self x⟩)
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    exact (LinearMap.congr_fun
      (summary.ker.liftQ_mkQ projection hker) x).symm
  have uniqueFactor : ∀ other : LinearMap.range summary →ₗ[ℝ] visible,
      projection = other.comp summary.rangeRestrict -> other = factor := by
    intro other hother
    apply LinearMap.ext
    intro value
    obtain ⟨x, hx⟩ := value.property
    have hvalue : value = ⟨summary x, summary.mem_range_self x⟩ :=
      Subtype.ext hx.symm
    rw [hvalue]
    have hotherAt := LinearMap.congr_fun hother x
    have hfactorAt := LinearMap.congr_fun factorizes x
    exact hotherAt.symm.trans hfactorAt
  have factorSurjective : Function.Surjective factor := by
    intro value
    refine ⟨⟨summary value.1, summary.mem_range_self value.1⟩, ?_⟩
    have hfactorAt := LinearMap.congr_fun factorizes value.1
    calc
      factor ⟨summary value.1, summary.mem_range_self value.1⟩ =
          projection value.1 := hfactorAt.symm
      _ = value := by
        exact Submodule.projectionOnto_apply_left
          visible.isCompl_orthogonal value
  refine ⟨⟨factor, factorizes, uniqueFactor⟩, ?_⟩
  exact LinearMap.finrank_le_finrank_of_surjective factorSurjective

#print axioms minimal_predictive_summary

end D5.S3.Quantum.Fibers.MinimalPredictiveSummary
