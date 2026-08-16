/- GID: D5/S3/Quantum/Algebra/UnitaryNaturalSelector
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/UnitaryNaturalSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No unit choice on finite subspaces is natural under every unitary symmetry. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/- Library-search audit trail (2026-08-16):
   * Repository search found unit-vector existence in `FiniteLayerProjectionEscape`, but no
     declaration excluding a simultaneous unitary-natural choice.
   * Loogle found `LinearIsometryEquiv.neg`, `finiteDimensional_bot`, and the
     `FiniteDimensional` instance for `Submodule.map`; all are applied below.
   * Pinned-Mathlib name and source searches found no theorem for the full no-go statement.
   * The attempted LeanSearch `/api/search` request returned HTTP 404. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Algebra.UnitaryNaturalSelector

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- On an infinite-dimensional inner-product space, unit vectors cannot be chosen in the orthogonal
complements of all finite-dimensional subspaces in a way that is natural under every surjective
linear isometry. -/
theorem no_unitary_natural_orthogonal_selector
    (_hInfinite : ¬ FiniteDimensional 𝕜 H) :
    ¬ ∃ η : (M : Submodule 𝕜 H) → [FiniteDimensional 𝕜 M] → H,
      (∀ (M : Submodule 𝕜 H) [FiniteDimensional 𝕜 M],
          η M ∈ Mᗮ ∧ ‖η M‖ = 1) ∧
        ∀ (U : H ≃ₗᵢ[𝕜] H) (M : Submodule 𝕜 H) [FiniteDimensional 𝕜 M],
          η (M.map U.toLinearEquiv.toLinearMap) = U (η M) := by
  rintro ⟨η, hselector, hnatural⟩
  let M : Submodule 𝕜 H := ⊥
  letI : FiniteDimensional 𝕜 M := by
    dsimp [M]
    infer_instance
  have hneg := hnatural (LinearIsometryEquiv.neg 𝕜) M
  have hfixed : η M = -η M := by
    simpa [M] using hneg
  have hsum : η M + η M = 0 := by
    calc
      η M + η M = -η M + η M := congrArg (fun x => x + η M) hfixed
      _ = 0 := neg_add_cancel (η M)
  have hzero : η M = 0 := by
    apply smul_right_injective H (two_ne_zero : (2 : 𝕜) ≠ 0)
    simpa [two_smul] using hsum
  have hnorm := (hselector M).2
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

#print axioms no_unitary_natural_orthogonal_selector

end D5.S3.Quantum.Algebra.UnitaryNaturalSelector
