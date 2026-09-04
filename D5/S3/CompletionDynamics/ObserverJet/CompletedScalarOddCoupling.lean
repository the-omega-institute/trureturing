/- GID: D5/S3/CompletionDynamics/ObserverJet/CompletedScalarOddCoupling
   generality: G
   mirror-B: D5/B/S3/CompletionDynamics/ObserverJet/CompletedScalarOddCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflection invariance removes every odd homogeneous term and the linear response. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.ObserverJet.CompletedScalarOddCoupling

/-- Reflection invariance removes every odd homogeneous term from an analytic scalar
readout, so its derivative vanishes and its first possible nonconstant term is at
least quadratic. -/
theorem completed_scalar_has_no_linear_odd_coupling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (completedScalar : E → ℝ)
    (series : FormalMultilinearSeries ℝ E ℝ)
    (hSeries : HasFPowerSeriesAt completedScalar series 0)
    (hExchange : ∀ u, completedScalar u = completedScalar (-u)) :
    fderiv ℝ completedScalar 0 = 0 ∧
      (∀ n, Odd n → ∀ u, series n (fun _ => u) = 0) ∧
      (∀ n, 0 < n →
        (∃ u, series n (fun _ => u) ≠ 0) →
        Even n ∧ 2 ≤ n) := by
  have oddTerms : ∀ n, Odd n → ∀ u, series n (fun _ => u) = 0 := by
    intro n hn u
    let line : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight u
    have hSeriesPositive : HasFPowerSeriesAt completedScalar series (line 0) := by
      simpa using hSeries
    have hSeriesNegative : HasFPowerSeriesAt completedScalar series ((-line) 0) := by
      simpa using hSeries
    have hPositive := hSeriesPositive.compContinuousLinearMap (u := line) (x := (0 : ℝ))
    have hNegative := hSeriesNegative.compContinuousLinearMap (u := -line) (x := (0 : ℝ))
    have hFunctions : completedScalar ∘ line = completedScalar ∘ (-line) := by
      funext t
      simpa [line] using hExchange (line t)
    have hNegative' :
        HasFPowerSeriesAt (completedScalar ∘ line)
          (series.compContinuousLinearMap (-line)) 0 := by
      rw [hFunctions]
      exact hNegative
    have hSeriesEq := hPositive.eq_formalMultilinearSeries hNegative'
    have hCoefficient := congrArg (fun p => p n (fun _ => (1 : ℝ))) hSeriesEq
    have hNegated :
        series n (fun _ => -u) = (-1 : ℝ) ^ n • series n (fun _ => u) := by
      simpa only [neg_one_smul, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] using
        (series n).map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => u)
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply] at hCoefficient
    have hLine : line ∘ (fun _ : Fin n => (1 : ℝ)) = fun _ => u := by
      funext i
      simp [line]
    have hNegativeLine : (-line) ∘ (fun _ : Fin n => (1 : ℝ)) = fun _ => -u := by
      funext i
      simp [line]
    rw [hLine, hNegativeLine] at hCoefficient
    rw [hNegated, hn.neg_one_pow] at hCoefficient
    simp only [neg_one_smul] at hCoefficient
    linarith
  refine ⟨?_, oddTerms, ?_⟩
  · rw [hSeries.hasFDerivAt.fderiv]
    ext u
    rw [continuousMultilinearCurryFin1_apply]
    have hVector : Fin.snoc 0 u = fun _ : Fin 1 => u := by
      funext i
      fin_cases i
      rfl
    rw [hVector]
    exact oddTerms 1 odd_one u
  · intro n hn hNonzero
    have hNotOdd : ¬ Odd n := by
      intro hOdd
      obtain ⟨u, hu⟩ := hNonzero
      exact hu (oddTerms n hOdd u)
    have hEven := Nat.not_odd_iff_even.mp hNotOdd
    refine ⟨hEven, ?_⟩
    obtain ⟨k, rfl⟩ := hEven
    omega

#print axioms completed_scalar_has_no_linear_odd_coupling

end D5.S3.CompletionDynamics.ObserverJet.CompletedScalarOddCoupling
