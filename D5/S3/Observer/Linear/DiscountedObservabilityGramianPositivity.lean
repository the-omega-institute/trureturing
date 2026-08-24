/- GID: D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/DiscountedObservabilityGramianPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A convergent discounted observability Gramian is positive semidefinite. -/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.InfiniteSum.Order

/- Library-search audit trail (2026-08-25):
   * Repository searches in the Observer and ObserverMemory families found no
     existing discounted observability Gramian construction or positivity theorem.
   * Exact pinned-Mathlib component hits `LinearMap.adjoint`,
     `ContinuousLinearMap.isPositive_adjoint_comp_self`,
     `ContinuousLinearMap.norm_adjoint_comp_self`,
     `ContinuousLinearMap.opNorm_comp_le`, `Summable.of_norm_bounded`,
     `summable_geometric_of_lt_one`, `ContinuousLinearMap.map_tsum`, and
     `tsum_nonneg` supply the adjoint, convergence, and positivity steps.
   * Pinned-Mathlib searches for a packaged discounted observability Gramian
     theorem found no exact hit. -/

namespace D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity

open InnerProductSpace RCLike
open scoped InnerProduct ComplexConjugate ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The readout after `n` applications of the evolution, bundled continuously
on the finite-dimensional source carrier. -/
noncomputable def observedIterate
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (n : ℕ) : V →L[𝕜] Y :=
  (C.comp (T ^ n)).toContinuousLinearMap

/-- The `n`th weighted Gram term in the discounted observability series. -/
noncomputable def discountedGramianTerm
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (β : ℝ) (n : ℕ) : V →L[𝕜] V := by
  letI := FiniteDimensional.complete 𝕜 V
  letI := FiniteDimensional.complete 𝕜 Y
  exact ((β ^ n : ℝ) : 𝕜) •
    ((observedIterate T C n)† ∘L observedIterate T C n)

/-- The source norm condition makes the discounted Gram terms summable. -/
theorem discounted_gramian_term_summable
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (β : ℝ)
    (hβ0 : 0 < β)
    (hconv : Real.sqrt β * ‖T.toContinuousLinearMap‖ < 1) :
    Summable (discountedGramianTerm T C β) := by
  letI := FiniteDimensional.complete 𝕜 V
  letI := FiniteDimensional.complete 𝕜 Y
  have hβ : 0 ≤ β := hβ0.le
  have hq0 : 0 ≤ β * ‖T.toContinuousLinearMap‖ ^ 2 :=
    mul_nonneg hβ (sq_nonneg _)
  have hq1 : β * ‖T.toContinuousLinearMap‖ ^ 2 < 1 := by
    calc
      β * ‖T.toContinuousLinearMap‖ ^ 2 =
          (Real.sqrt β * ‖T.toContinuousLinearMap‖) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hβ]
      _ < 1 ^ 2 := (sq_lt_sq₀
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (by positivity)).2 hconv
      _ = 1 := one_pow 2
  have hmajor : Summable
      (fun n : ℕ => ‖C.toContinuousLinearMap‖ ^ 2 *
        (β * ‖T.toContinuousLinearMap‖ ^ 2) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hTpow : ∀ n : ℕ,
      ‖T.toContinuousLinearMap ^ n‖ ≤ ‖T.toContinuousLinearMap‖ ^ n := by
    intro n
    induction n with
    | zero =>
        simpa only [pow_zero, ContinuousLinearMap.one_def] using
          (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := V))
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
  apply Summable.of_norm_bounded hmajor
  intro n
  let U := observedIterate T C n
  have hU : ‖U‖ ≤ ‖C.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap‖ ^ n := by
    calc
      ‖U‖ = ‖C.toContinuousLinearMap ∘L T.toContinuousLinearMap ^ n‖ := by
        congr 1
        ext x
        simp [U, observedIterate, LinearMap.comp_apply, Module.End.coe_pow]
      _ ≤ ‖C.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap ^ n‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖C.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap‖ ^ n :=
        mul_le_mul_of_nonneg_left (hTpow n) (norm_nonneg _)
  rw [discountedGramianTerm]
  simp only [norm_smul, RCLike.norm_ofReal, abs_pow, abs_of_pos hβ0,
    ContinuousLinearMap.norm_adjoint_comp_self]
  calc
    β ^ n * (‖U‖ * ‖U‖) ≤
        β ^ n * ((‖C.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap‖ ^ n) *
          (‖C.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap‖ ^ n)) :=
      mul_le_mul_of_nonneg_left
        (mul_self_le_mul_self (norm_nonneg _) hU) (pow_nonneg hβ _)
    _ = ‖C.toContinuousLinearMap‖ ^ 2 *
        (β * ‖T.toContinuousLinearMap‖ ^ 2) ^ n := by ring

/-- The norm-convergent discounted observability Gramian constructed from the
evolution and readout maps. -/
noncomputable def discountedObservabilityGramian
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (β : ℝ) : V →L[𝕜] V :=
  ∑' n : ℕ, discountedGramianTerm T C β n

/-- Under the source's discount range and norm convergence premise, the
discounted observability Gramian is positive semidefinite. -/
theorem discounted_observability_gramian_nonnegative
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hconv : Real.sqrt β * ‖T.toContinuousLinearMap‖ < 1) :
    0 ≤ discountedObservabilityGramian T C β := by
  have _hβ1 : β ≤ 1 := hβ1.le
  letI := FiniteDimensional.complete 𝕜 V
  letI := FiniteDimensional.complete 𝕜 Y
  have hsum := discounted_gramian_term_summable T C β hβ0 hconv
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  apply ContinuousLinearMap.isPositive_def'.mpr
  constructor
  · rw [isSelfAdjoint_iff]
    change star (∑' n : ℕ, discountedGramianTerm T C β n) =
      ∑' n : ℕ, discountedGramianTerm T C β n
    rw [tsum_star]
    congr 1
    funext n
    exact (ContinuousLinearMap.isPositive_adjoint_comp_self
      (observedIterate T C n)).smul_of_nonneg
        (RCLike.ofReal_nonneg.mpr (pow_nonneg hβ0.le n)) |>.isSelfAdjoint.star_eq
  · intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    rw [inner_re_symm]
    change 0 ≤ RCLike.re (inner 𝕜 x
      (((ContinuousLinearMap.apply 𝕜 V) x)
        (∑' n : ℕ, discountedGramianTerm T C β n)))
    rw [((ContinuousLinearMap.apply 𝕜 V) x).map_tsum hsum]
    have hvsum := hsum.mapL ((ContinuousLinearMap.apply 𝕜 V) x)
    change 0 ≤ RCLike.re ((innerSL 𝕜 x)
      (∑' z : ℕ, ((ContinuousLinearMap.apply 𝕜 V) x)
        (discountedGramianTerm T C β z)))
    rw [(innerSL 𝕜 x).map_tsum hvsum]
    have hisum := hvsum.mapL (innerSL 𝕜 x)
    change 0 ≤ RCLike.reCLM
      (∑' z : ℕ, (innerSL 𝕜 x) (((ContinuousLinearMap.apply 𝕜 V) x)
        (discountedGramianTerm T C β z)))
    rw [RCLike.reCLM.map_tsum hisum]
    apply tsum_nonneg
    intro n
    change 0 ≤ RCLike.re (inner 𝕜 x (discountedGramianTerm T C β n x))
    rw [inner_re_symm]
    exact ((ContinuousLinearMap.isPositive_adjoint_comp_self
      (observedIterate T C n)).smul_of_nonneg
        (RCLike.ofReal_nonneg.mpr
          (pow_nonneg hβ0.le n))).re_inner_nonneg_left x

#print axioms discounted_gramian_term_summable
#print axioms discounted_observability_gramian_nonnegative

end D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity
