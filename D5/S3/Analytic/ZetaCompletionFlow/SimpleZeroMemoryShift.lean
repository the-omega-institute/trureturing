/- GID: D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroMemoryShift
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaCompletionFlow/SimpleZeroMemoryShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct the locally unique simple-zero branch and its quadratic
     memory-shift expansion. -/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic

/-!
# Simple-zero memory shift

The source formula omits the equation defining its displaced zero. The positive first-order sign
corresponds to the closed-loop equation `F z - kappa * A z ^ 2 = 0`; this module makes that equation
explicit. The implicit branch is locally unique and its analytic Taylor expansion has a genuine
quadratic remainder.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.ZetaCompletionFlow.SimpleZeroMemoryShift

open Asymptotics Filter
open scoped ContDiff Topology

/-- A simple zero of `F` has a locally unique branch under the closed-loop perturbation
`F z - kappa * A z ^ 2`. Its first-order displacement is `A rho ^ 2 / deriv F rho`, and the
remaining displacement is bounded by a constant times `kappa ^ 2` near zero. -/
theorem simple_zero_memory_shift
    (F A : ℂ → ℂ) (rho : ℂ)
    (hF : AnalyticAt ℂ F rho) (hA : AnalyticAt ℂ A rho)
    (hzero : F rho = 0) (hsimple : deriv F rho ≠ 0) :
    ∃ branch : ℂ → ℂ,
      branch 0 = rho ∧
      (∀ᶠ kappa in 𝓝 0, F (branch kappa) - kappa * A (branch kappa) ^ 2 = 0) ∧
      (∀ᶠ p : ℂ × ℂ in 𝓝 (0, rho),
        F p.2 - p.1 * A p.2 ^ 2 = 0 ↔ branch p.1 = p.2) ∧
      (fun kappa => branch kappa - rho - kappa * (A rho) ^ 2 / deriv F rho) =O[𝓝 0]
        (fun kappa => kappa ^ 2) := by
  let G : ℂ × ℂ → ℂ := fun p => F p.2 - p.1 * A p.2 ^ 2
  have hG : AnalyticAt ℂ G (0, rho) := by
    dsimp only [G]
    exact (hF.comp analyticAt_snd).sub
      (analyticAt_fst.mul ((hA.comp analyticAt_snd).pow 2))
  have hright :
      fderiv ℂ G (0, rho) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
        ContinuousLinearMap.toSpanSingleton ℂ (deriv F rho) := by
    have hcomposition := hG.hasStrictFDerivAt.hasFDerivAt.comp rho
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) (0 : ℂ) rho)
    have hdirect : HasFDerivAt (fun z : ℂ => G (0, z))
        (ContinuousLinearMap.toSpanSingleton ℂ (deriv F rho)) rho := by
      simpa [G] using hF.hasStrictDerivAt.hasDerivAt.hasFDerivAt
    exact hcomposition.unique hdirect
  let derivativeEquiv : ℂ ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv F rho) hsimple)
  have hinvertible :
      (fderiv ℂ G (0, rho) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [hright]
    have heq : ContinuousLinearMap.toSpanSingleton ℂ (deriv F rho) =
        (derivativeEquiv : ℂ →L[ℂ] ℂ) := by
      ext z
      simp [derivativeEquiv, ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
    rw [heq]
    exact ContinuousLinearMap.isInvertible_equiv
  have hGcont : ContDiffAt ℂ ω G (0, rho) := hG.contDiffAt
  have homega : (ω : ℕ∞ω) ≠ 0 := by simp
  let branch : ℂ → ℂ := hGcont.implicitFunction homega hinvertible
  have hbranchBase : branch 0 = rho := by
    simpa [branch] using hGcont.implicitFunction_apply_self homega hinvertible
  have hbranchZero :
      ∀ᶠ kappa in 𝓝 0, F (branch kappa) - kappa * A (branch kappa) ^ 2 = 0 := by
    simpa [branch, G, hzero] using
      hGcont.eventually_apply_implicitFunction homega hinvertible
  have hbranchUnique :
      ∀ᶠ p : ℂ × ℂ in 𝓝 (0, rho),
        F p.2 - p.1 * A p.2 ^ 2 = 0 ↔ branch p.1 = p.2 := by
    simpa [branch, G, hzero] using
      hGcont.eventually_apply_eq_iff_implicitFunction homega hinvertible
  have hbranchCont : ContDiffAt ℂ ω branch 0 := by
    simpa [branch] using hGcont.contDiffAt_implicitFunction homega hinvertible
  have hbranchAnalytic : AnalyticAt ℂ branch 0 := hbranchCont.analyticAt
  have hbranchDeriv : HasDerivAt branch (deriv branch 0) 0 :=
    hbranchAnalytic.hasStrictDerivAt.hasDerivAt
  have hFAtBranch : HasDerivAt F (deriv F rho) (branch 0) := by
    rw [hbranchBase]
    exact hF.hasStrictDerivAt.hasDerivAt
  have hAAtBranch : HasDerivAt A (deriv A rho) (branch 0) := by
    rw [hbranchBase]
    exact hA.hasStrictDerivAt.hasDerivAt
  have hFcomp : HasDerivAt (fun kappa => F (branch kappa))
      (deriv F rho * deriv branch 0) 0 := by
    simpa only [Function.comp_apply] using! hFAtBranch.comp 0 hbranchDeriv
  have hAcomp : HasDerivAt (fun kappa => A (branch kappa))
      (deriv A rho * deriv branch 0) 0 := by
    simpa only [Function.comp_apply] using! hAAtBranch.comp 0 hbranchDeriv
  have hforcing : HasDerivAt (fun kappa : ℂ => kappa * A (branch kappa) ^ 2)
      ((A rho) ^ 2) 0 := by
    simpa [hbranchBase] using!
      (hasDerivAt_id (x := (0 : ℂ))).mul (hAcomp.pow 2)
  have hequation : HasDerivAt
      (fun kappa : ℂ => F (branch kappa) - kappa * A (branch kappa) ^ 2)
      (deriv F rho * deriv branch 0 - (A rho) ^ 2) 0 :=
    hFcomp.sub hforcing
  have hzeroEq :
      (fun kappa : ℂ => F (branch kappa) - kappa * A (branch kappa) ^ 2) =ᶠ[𝓝 0]
        (fun _ => 0) := hbranchZero
  have hderivEquation : deriv F rho * deriv branch 0 - (A rho) ^ 2 = 0 := by
    have hconst := hequation.congr_of_eventuallyEq hzeroEq.symm
    exact hconst.unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
  have hbranchDerivative : deriv branch 0 = (A rho) ^ 2 / deriv F rho := by
    apply (eq_div_iff hsimple).2
    rw [mul_comm]
    exact sub_eq_zero.mp hderivEquation
  obtain ⟨R, hRanalytic, hTaylor⟩ :=
    hbranchAnalytic.exists_eq_sum_add_pow_mul 2
  have hTaylorLinear (kappa : ℂ) :
      branch kappa = branch 0 + kappa * deriv branch 0 + kappa ^ 2 * R kappa := by
    simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] using hTaylor kappa
  have hquadratic :
      (fun kappa : ℂ => kappa ^ 2 * R kappa) =O[𝓝 0] (fun kappa => kappa ^ 2) := by
    simpa using
      (isBigO_refl (fun kappa : ℂ => kappa ^ 2) (𝓝 0)).mul
        hRanalytic.continuousAt.isBigO
  refine ⟨branch, hbranchBase, hbranchZero, hbranchUnique, ?_⟩
  refine hquadratic.congr_left (fun kappa => ?_)
  rw [hTaylorLinear, hbranchBase, hbranchDerivative]
  ring

#print axioms simple_zero_memory_shift

end D5.S3.Analytic.ZetaCompletionFlow.SimpleZeroMemoryShift
