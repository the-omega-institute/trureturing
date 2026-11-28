/- GID: D5/S3/Fourier/Asymptotics/PeriodicSublevelSandwich
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/PeriodicSublevelSandwich
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Periodized smooth tests bound the whole sublevel of a planar map with isolated regular zeros. -/

import D5.S3.Analysis.PeriodicSublevelSandwich

/-! Publication reference for periodic sublevel bounds in the two-clock argument. -/

namespace D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich

open Omega.Analysis.PeriodicSublevelSandwich MeasureTheory Set
open scoped ContDiff

/-- The periodic window bounds for an enumerated finite family of regular zeros. -/
theorem periodic_test_sandwich {n : ℕ}
    (q : Plane) {F : Plane → Plane} (hF : Continuous F)
    (hperiod : ∀ (a : Fin 2 → ℤ) (x : Plane), F (latticeVector a + x) = F x)
    (z : Fin n → Plane) (hz : Function.Injective z)
    (hcell : ∀ i, z i ∈ openCell q)
    (hzero : ∀ x ∈ closedCell q, F x = 0 ↔ ∃ i, x = z i)
    (A : Fin n → Plane ≃L[ℝ] Plane) (hA : ∀ i, HasFDerivAt F (A i : Plane →L[ℝ] Plane) (z i))
    {η ρ σ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hρ : 0 < ρ) (hρ' : ρ < (1 + η)⁻¹) (hσ : (1 - η)⁻¹ < σ) :
    let D := ∑ i, |LinearMap.det ((A i).toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹
    ∃ (lower upper : Fin n → Plane → ℝ) (δ : ℝ),
      0 < δ ∧
      (∀ i, ContDiff ℝ ∞ (lower i) ∧ ContDiff ℝ ∞ (upper i) ∧
        HasCompactSupport (lower i) ∧ HasCompactSupport (upper i)) ∧
      Real.pi * ρ ^ 2 * D ≤ ∑ i, ∫ u, lower i u ∧
      (∑ i, ∫ u, upper i u) ≤ Real.pi * σ ^ 2 * D ∧
      ∀ ε ∈ Ioo 0 δ, ∀ x,
        (∑ i, ∑' a : Fin 2 → ℤ, lower i (ε⁻¹ • (latticeVector a + x - z i))) ≤
          (if ‖F x‖ < ε then 1 else 0) ∧
        (if ‖F x‖ < ε then 1 else 0) ≤
          (∑ i, ∑' a : Fin 2 → ℤ, upper i (ε⁻¹ • (latticeVector a + x - z i))) :=
  Omega.Analysis.PeriodicSublevelSandwich.periodic_test_sandwich q hF hperiod z hz hcell hzero A hA hη hη1 hρ hρ' hσ

#print axioms periodic_test_sandwich

end D5.S3.Fourier.Asymptotics.PeriodicSublevelSandwich
