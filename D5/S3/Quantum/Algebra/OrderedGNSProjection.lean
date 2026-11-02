/- GID: D5/S3/Quantum/Algebra/OrderedGNSProjection
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OrderedGNSProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered comparisons characterize faithful-state matrix conditional expectations. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

noncomputable section

namespace D5.S3.Quantum.Algebra.OrderedGNSProjection

open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The original complex, ordered matrix-state evaluation. -/
def state (rho x : Matrix n n ℂ) : ℂ := trace (rho * x)

private theorem state_star (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (x : Matrix n n ℂ) : state rho (star x) = star (state rho x) := by
  simp only [state, star_eq_conjTranspose, ← trace_conjTranspose, conjTranspose_mul,
    hrho.isHermitian.eq, trace_mul_comm]

private theorem state_nonneg (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    {x : Matrix n n ℂ} (hx : x.PosSemidef) : 0 ≤ (state rho x).re :=
  RHLinalg.trace_mul_nonneg_of_posSemidef hrho.posSemidef hx

private theorem state_square_faithful (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (x : Matrix n n ℂ) (hx : state rho (star x * x) = 0) : x = 0 := by
  letI := rho.toMatrixNormedAddCommGroup hrho
  letI := rho.toMatrixInnerProductSpace hrho.posSemidef
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change trace (x * rho * xᴴ) = 0
  simpa only [state, star_eq_conjTranspose, ← mul_assoc,
    trace_mul_cycle x rho xᴴ] using hx

/-- A faithful state separates the positive cone using compressions internal to
any unital star-subalgebra. -/
theorem positive_of_internal_compressions
    (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (y : Matrix n n ℂ) (hy : y.IsHermitian) (hyA : y ∈ A)
    (htest : ∀ q ∈ A, 0 ≤ (state rho (star q * y * q)).re) :
    y.PosSemidef := by
  letI : IsClosed (A : Set (Matrix n n ℂ)) :=
    A.toSubmodule.closed_of_finiteDimensional
  let f : ℝ → ℝ := fun t => Real.sqrt t⁻
  let q : Matrix n n ℂ := cfc f y
  let z : Matrix n n ℂ := cfc (fun t : ℝ => t⁻) y
  have hqA : q ∈ A := cfc_mem f hyA
  have hq : IsSelfAdjoint q := by
    exact cfc_predicate _ _
  have hz : IsSelfAdjoint z := by
    exact cfc_predicate _ _
  have hprod : star q * y * q = -(star z * z) := by
    rw [hq.star_eq, hz.star_eq]
    change cfc f y * y * cfc f y = -(cfc (fun t : ℝ => t⁻) y *
      cfc (fun t : ℝ => t⁻) y)
    rw [← cfc_id' ℝ y hy.isSelfAdjoint, ← cfc_mul, ← cfc_mul, ← cfc_mul, ← cfc_neg]
    apply cfc_congr
    intro t ht
    dsimp [f]
    have hs := Real.mul_self_sqrt (negPart_nonneg t)
    by_cases h : 0 ≤ t
    · simp [negPart_eq_zero.mpr h]
    · have hn : t⁻ = -t := by simp [negPart_def, max_eq_right (le_of_not_ge h)]
      rw [hn] at hs ⊢
      nlinarith
  have hn : 0 ≤ (state rho (star z * z)).re :=
    state_nonneg rho hrho (posSemidef_conjTranspose_mul_self z)
  have hp := htest q hqA
  rw [hprod] at hp
  have heq : state rho (star z * z) = 0 := by
    have hre : (state rho (star z * z)).re = 0 := by
      simpa [state] using le_antisymm (by simpa [state] using hp) hn
    have hstar := state_star rho hrho (star z * z)
    have him : (state rho (star z * z)).im = 0 := by
      have hc := congrArg Complex.im hstar
      simp only [star_mul, star_star] at hc
      simpa using hc
    exact Complex.ext hre him
  have hz0 := state_square_faithful rho hrho z heq
  have hneg : y⁻ = 0 := by
    simpa [z, CFC.negPart_def, cfcₙ_eq_cfc (hf0 := by simp)] using hz0
  exact (CFC.negPart_eq_zero_iff y hy.isSelfAdjoint).mp hneg |>.posSemidef

end D5.S3.Quantum.Algebra.OrderedGNSProjection
