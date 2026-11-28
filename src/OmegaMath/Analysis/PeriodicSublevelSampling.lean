import OmegaMath.Analysis.PeriodicSublevelSandwich

/-!
Omega original.

Normalized sampling of fixed smooth windows determines the weighted mass of
a shrinking periodic sublevel at finitely many regular zeros.
-/

namespace Omega.Analysis.PeriodicSublevelSampling

open Filter MeasureTheory Set
open scoped ContDiff Topology
open PeriodicSublevelSandwich

/-- Smooth window convergence transfers to a strict sublevel, including an empty zero set. -/
theorem tendsto_weighted_sublevel {ι α β : Type*} [Fintype ι]
    (l : Filter α) (q : Plane) {F : Plane → Plane} (hF : Continuous F)
    (hperiod : ∀ (a : Fin 2 → ℤ) (x : Plane), F (latticeVector a + x) = F x)
    (z : ι → Plane) (hz : Function.Injective z)
    (hcell : ∀ i, z i ∈ openCell q)
    (hzero : ∀ x ∈ closedCell q, F x = 0 ↔ ∃ i, x = z i)
    (A : ι → Plane ≃L[ℝ] Plane) (hA : ∀ i, HasFDerivAt F (A i : Plane →L[ℝ] Plane) (z i))
    (s : α → Finset β) (p : α → β → Plane) (w : α → β → ℝ)
    (hw : ∀ n, ∀ j ∈ s n, 0 ≤ w n j)
    (ε : α → ℝ) (hεpos : ∀ᶠ n in l, 0 < ε n) (hε : Tendsto ε l (𝓝 0))
    (hsample : ∀ (g : Plane → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → ∀ center : Plane,
      Tendsto (fun n => (∑ j ∈ s n, w n j *
        ∑' a : Fin 2 → ℤ, g ((ε n)⁻¹ • (latticeVector a + p n j - center))) / (ε n) ^ 2)
        l (𝓝 (∫ u, g u))) :
    Tendsto (fun n => (∑ j ∈ s n, w n j * (if ‖F (p n j)‖ < ε n then 1 else 0)) / (ε n) ^ 2)
      l (𝓝 (Real.pi * ∑ i, |LinearMap.det ((A i).toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹)) := by
  classical
  let C := Real.pi * ∑ i, |LinearMap.det ((A i).toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have family_limit (g : ι → Plane → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
      (hg' : ∀ i, HasCompactSupport (g i)) :
      Tendsto (fun n => (∑ j ∈ s n, w n j *
        ∑ i, ∑' a : Fin 2 → ℤ, g i ((ε n)⁻¹ • (latticeVector a + p n j - z i))) / (ε n) ^ 2)
        l (𝓝 (∑ i, ∫ u, g i u)) := by
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hsample (g i) (hg i) (hg' i) (z i))
    convert hsum using 1
    ext n
    rw [← Finset.sum_div]
    congr 1
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  change Tendsto _ l (𝓝 C)
  refine Metric.tendsto_nhds.2 fun τ hτ => ?_
  let a := min (1 / 4 : ℝ) (τ / (12 * (C + 1)))
  have ha : 0 < a := lt_min (by norm_num) (div_pos hτ (by positivity))
  have ha₁ : a ≤ 1 / 4 := min_le_left _ _
  have haτ : a * (12 * (C + 1)) ≤ τ :=
    (le_div_iff₀ (by positivity : 0 < 12 * (C + 1))).1 (min_le_right _ _)
  let ρ := 1 - a
  let σ := 1 + 2 * a
  have hη : 0 < a / 2 := by linarith
  have hη₁ : a / 2 < 1 := by linarith
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρ' : ρ < (1 + a / 2)⁻¹ := by
    dsimp [ρ]
    rw [← one_div]
    apply (lt_div_iff₀ (by linarith : 0 < 1 + a / 2)).2
    nlinarith [sq_nonneg a]
  have hσ : (1 - a / 2)⁻¹ < σ := by
    dsimp [σ]
    have ha₂ : a * a ≤ a / 4 := by nlinarith [mul_le_mul_of_nonneg_right ha₁ ha.le]
    rw [← one_div]
    apply (div_lt_iff₀ (by linarith : 0 < 1 - a / 2)).2
    nlinarith
  have hρmass : C - τ / 2 ≤ ρ ^ 2 * C := by
    dsimp [ρ]
    nlinarith [mul_nonneg (sq_nonneg a) hC, mul_nonneg ha.le hC]
  have hσmass : σ ^ 2 * C ≤ C + τ / 2 := by
    dsimp [σ]
    have haC : 0 ≤ a * C := mul_nonneg ha.le hC
    nlinarith [mul_le_mul_of_nonneg_right ha₁ haC]
  obtain ⟨lower, upper, cutoff, hcutoff, hsmooth, hlower, hupper, hbracket⟩ :=
    periodic_test_sandwich q hF hperiod z hz hcell hzero A hA hη hη₁ hρ hρ' hσ
  have radius_mass (r : ℝ) : r ^ 2 * C =
      Real.pi * r ^ 2 * ∑ i, |LinearMap.det ((A i).toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹ := by
    dsimp only [C]
    rw [← mul_assoc, mul_comm (r ^ 2) Real.pi]
  have hlower_mass : ρ ^ 2 * C ≤ ∑ i, ∫ u, lower i u := (radius_mass ρ).trans_le hlower
  have hupper_mass : (∑ i, ∫ u, upper i u) ≤ σ ^ 2 * C := hupper.trans_eq (radius_mass σ).symm
  have hlower_limit := family_limit lower (fun i => (hsmooth i).1) (fun i => (hsmooth i).2.2.1)
  have hupper_limit := family_limit upper (fun i => (hsmooth i).2.1) (fun i => (hsmooth i).2.2.2)
  have hcut : ∀ᶠ n in l, ε n < cutoff := (tendsto_order.1 hε).2 cutoff hcutoff
  filter_upwards [hεpos, hcut, Metric.tendsto_nhds.1 hlower_limit (τ / 2) (by linarith),
    Metric.tendsto_nhds.1 hupper_limit (τ / 2) (by linarith)] with n hpos hsmall hL hU
  have hl := div_le_div_of_nonneg_right (Finset.sum_le_sum fun j hj =>
    mul_le_mul_of_nonneg_left (hbracket (ε n) ⟨hpos, hsmall⟩ (p n j)).1 (hw n j hj))
    (sq_nonneg (ε n))
  have hu := div_le_div_of_nonneg_right (Finset.sum_le_sum fun j hj =>
    mul_le_mul_of_nonneg_left (hbracket (ε n) ⟨hpos, hsmall⟩ (p n j)).2 (hw n j hj))
    (sq_nonneg (ε n))
  rw [Real.dist_eq, abs_lt] at hL hU ⊢
  exact ⟨by linarith only [hρmass, hlower_mass, hL.1, hl],
    by linarith only [hσmass, hupper_mass, hU.2, hu]⟩

end Omega.Analysis.PeriodicSublevelSampling
