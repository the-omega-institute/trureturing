/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonPhysicalSpectrum
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonPhysicalSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete multiplicity, invariant-space and real-dimension transport for positive physical parameters. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealBoundary

/-! Full spectral and Jordan consequences of differentiated physical scaling. -/
noncomputable section
open scoped BigOperators

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
open AlternatingPolygonSpectrum AlternatingPolygonModes AlternatingPolygonJordan
open AlternatingPolygonNeutral AlternatingPolygonDecomposition AlternatingPolygonRealSpaces
open AlternatingPolygonTransport

/-- Algebraic multiplicities are preserved at every scaled complex value, including zero. -/
theorem physical_algebraic_multiplicity (m : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω)
    (μ : ℂ) :
    (parameterOperator m b Ω).charpoly.rootMultiplicity ((2 * Ω : ℂ) * μ) =
      (actualOperator m).charpoly.rootMultiplicity μ := by
  rw [← LinearMap.finrank_maxGenEigenspace_eq,
    ← LinearMap.finrank_maxGenEigenspace_eq]
  exact congrArg (fun S : Submodule ℂ (Cartesian m) => Module.finrank ℂ S)
    (parameter_genEigenspace m hb hΩ μ ⊤)

theorem physical_geometric_multiplicity (m : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω)
    (μ : ℂ) :
    Module.finrank ℂ ((parameterOperator m b Ω).eigenspace ((2 * Ω : ℂ) * μ)) =
      Module.finrank ℂ ((actualOperator m).eigenspace μ) :=
  congrArg (fun S : Submodule ℂ (Cartesian m) => Module.finrank ℂ S)
    (parameter_genEigenspace m hb hΩ μ 1)

/-- Every nonzero eigenvalue of the actual physical derivative is semisimple. -/
theorem physical_nonzero_semisimple (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) {ν : ℂ} (hν : ν ≠ 0) :
    (parameterOperator m b Ω).maxGenEigenspace ν =
      (parameterOperator m b Ω).eigenspace ν := by
  have ha : (2 * Ω : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 : ℝ) * Ω ≠ 0)
  have he : (2 * Ω : ℂ) * (ν / (2 * Ω : ℂ)) = ν := mul_div_cancel₀ _ ha
  change (parameterOperator m b Ω).genEigenspace ν ⊤ =
    (parameterOperator m b Ω).genEigenspace ν 1
  rw [← he, parameter_genEigenspace m hb hΩ _ ⊤,
    parameter_genEigenspace m hb hΩ _ 1]
  exact actual_nonzero_semisimple m hm (div_ne_zero hν ha)

/-- Every actual invariant block is preserved by positive parameter scaling. -/
theorem physical_block_restriction (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) (q : ZMod (2 * m)) (w : ℂ × ℂ) :
    parameterOperator m b Ω (block m q w) = block m q
      ((2 * Ω : ℂ) * ((ell m q : ℂ) * w.2),
        (2 * Ω : ℂ) * (((ell m (q + m) + 1 : ℝ) : ℂ) * w.1)) := by
  rw [parameterOperator_eq m hb hΩ, LinearMap.smul_apply, block_restriction m hm,
    ← map_smul]
  rfl

def physicalRealOperator (m : ℕ) (b Ω : ℝ) : Module.End ℝ (RealCartesian m) :=
  (AlternatingPolygonParameters.jacobian (2 * m) b Ω
    (AlternatingPolygonParameters.radius b Ω • polygon (2 * m))).toLin'

theorem physicalRealOperator_eq (m : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    physicalRealOperator m b Ω = (2 * Ω) • realOperator m := by
  have hR := ne_of_gt (AlternatingPolygonParameters.radius_pos hb hΩ)
  have hbR : b = 4 * Ω * AlternatingPolygonParameters.radius b Ω ^ 2 := by
    rw [AlternatingPolygonParameters.radius_sq hb hΩ]
    field_simp
  unfold physicalRealOperator realOperator
  rw [AlternatingPolygonParameters.jacobian_scaling _ hR hbR, map_smul]

theorem physical_real_eigenspace (m : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) (μ : ℝ) :
    (physicalRealOperator m b Ω).eigenspace (2 * Ω * μ) = (realOperator m).eigenspace μ := by
  rw [physicalRealOperator_eq m hb hΩ]
  exact smul_genEigenspace _ (by positivity) μ 1

/-- The positive physical eigenvalues are exhausted by the scaled canonical roots. -/
theorem physical_positive_eigenvalue_iff (m : ℕ) (hm : 3 ≤ m)
    {b Ω μ : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) (hμ : 0 < μ) :
    (physicalRealOperator m b Ω).HasEigenvalue μ ↔
      ∃ k : Fin (m - 2), μ = 2 * Ω * positiveRoot m (k.val + 2) := by
  have ha : 0 < 2 * Ω := by positivity
  have he : 2 * Ω * (μ / (2 * Ω)) = μ := mul_div_cancel₀ _ (ne_of_gt ha)
  have hs : (physicalRealOperator m b Ω).HasEigenvalue μ ↔
      (realOperator m).HasEigenvalue (μ / (2 * Ω)) := by
    have hs' := physical_real_eigenspace m hb hΩ (μ / (2 * Ω))
    rw [he] at hs'
    simp only [Module.End.hasEigenvalue_iff, hs']
  rw [hs, AlternatingPolygonRealBoundary.positive_eigenvalue_iff m hm (div_pos hμ ha)]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (div_eq_iff (ne_of_gt ha)).mp hk |>.trans (mul_comm _ _)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, mul_div_cancel_left₀ _ (ne_of_gt ha)⟩

/-- The negative physical eigenvalues are exhausted by the scaled canonical roots. -/
theorem physical_negative_eigenvalue_iff (m : ℕ) (hm : 3 ≤ m)
    {b Ω μ : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) (hμ : μ < 0) :
    (physicalRealOperator m b Ω).HasEigenvalue μ ↔
      ∃ k : Fin (m - 2), μ = 2 * Ω * (-positiveRoot m (k.val + 2)) := by
  have ha : 0 < 2 * Ω := by positivity
  have he : 2 * Ω * (μ / (2 * Ω)) = μ := mul_div_cancel₀ _ (ne_of_gt ha)
  have hs : (physicalRealOperator m b Ω).HasEigenvalue μ ↔
      (realOperator m).HasEigenvalue (μ / (2 * Ω)) := by
    have hs' := physical_real_eigenspace m hb hΩ (μ / (2 * Ω))
    rw [he] at hs'
    simp only [Module.End.hasEigenvalue_iff, hs']
  rw [hs, AlternatingPolygonRealBoundary.negative_eigenvalue_iff m hm
    (div_neg_of_neg_of_pos hμ ha)]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (div_eq_iff (ne_of_gt ha)).mp hk |>.trans (mul_comm _ _)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, mul_div_cancel_left₀ _ (ne_of_gt ha)⟩

private theorem spectralSum_range (m : ℕ) (s : ℝ) :
    (spectralSum m s).range =
      ⨆ k : Fin (m - 2), (realOperator m).eigenspace (s * positiveRoot m (k.val + 2)) := by
  classical
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    change (∑ k, (w k).val) ∈ _
    apply (⨆ k : Fin (m - 2),
      (realOperator m).eigenspace (s * positiveRoot m (k.val + 2))).sum_mem
    intro k _
    exact Submodule.mem_iSup_of_mem k (w k).property
  · apply iSup_le
    intro k v hv
    let w : ∀ j : Fin (m - 2),
        (realOperator m).eigenspace (s * positiveRoot m (j.val + 2)) := Pi.single k ⟨v, hv⟩
    refine ⟨w, ?_⟩
    change (∑ j : Fin (m - 2), (w j).val) = v
    rw [Finset.sum_eq_single k]
    · simp only [w, Pi.single_eq_same]
    · intro j _ hj
      simp [w, Pi.single_eq_of_ne hj]
    · simp

/-- These are the actual real negative and positive spectral sums of the physical derivative. -/
def physicalStableSpace (m : ℕ) (b Ω : ℝ) : Submodule ℝ (RealCartesian m) :=
  ⨆ k : Fin (m - 2), (physicalRealOperator m b Ω).eigenspace
    (2 * Ω * (-positiveRoot m (k.val + 2)))

def physicalUnstableSpace (m : ℕ) (b Ω : ℝ) : Submodule ℝ (RealCartesian m) :=
  ⨆ k : Fin (m - 2), (physicalRealOperator m b Ω).eigenspace
    (2 * Ω * positiveRoot m (k.val + 2))

/-- The finite block description equals the sum over every negative real eigenvalue. -/
theorem physical_stable_exhaustive (m : ℕ) (hm : 3 ≤ m)
    {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    physicalStableSpace m b Ω =
      ⨆ μ : ℝ, ⨆ _ : μ < 0, (physicalRealOperator m b Ω).eigenspace μ := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply le_iSup_of_le (2 * Ω * (-positiveRoot m (k.val + 2)))
    apply le_iSup_of_le (mul_neg_of_pos_of_neg (by positivity)
      (neg_neg_of_pos (positiveRoot_pos m _ (by omega) (by omega))))
    exact le_rfl
  · apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    by_cases he : (physicalRealOperator m b Ω).HasEigenvalue μ
    · obtain ⟨k, rfl⟩ := (physical_negative_eigenvalue_iff m hm hb hΩ hμ).mp he
      exact le_iSup (fun k : Fin (m - 2) => (physicalRealOperator m b Ω).eigenspace
        (2 * Ω * (-positiveRoot m (k.val + 2)))) k
    · rw [Module.End.hasEigenvalue_iff] at he
      rw [not_not.mp he]
      exact bot_le

/-- The finite block description equals the sum over every positive real eigenvalue. -/
theorem physical_unstable_exhaustive (m : ℕ) (hm : 3 ≤ m)
    {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    physicalUnstableSpace m b Ω =
      ⨆ μ : ℝ, ⨆ _ : 0 < μ, (physicalRealOperator m b Ω).eigenspace μ := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply le_iSup_of_le (2 * Ω * positiveRoot m (k.val + 2))
    apply le_iSup_of_le (mul_pos (by positivity)
      (positiveRoot_pos m _ (by omega) (by omega)))
    exact le_rfl
  · apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    by_cases he : (physicalRealOperator m b Ω).HasEigenvalue μ
    · obtain ⟨k, rfl⟩ := (physical_positive_eigenvalue_iff m hm hb hΩ hμ).mp he
      exact le_iSup (fun k : Fin (m - 2) => (physicalRealOperator m b Ω).eigenspace
        (2 * Ω * positiveRoot m (k.val + 2))) k
    · rw [Module.End.hasEigenvalue_iff] at he
      rw [not_not.mp he]
      exact bot_le

theorem physical_real_spaces (m : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    physicalStableSpace m b Ω = stableSpace m ∧
      physicalUnstableSpace m b Ω = unstableSpace m := by
  simp only [physicalStableSpace, physicalUnstableSpace, physical_real_eigenspace m hb hΩ,
    stableSpace, unstableSpace, spectralSum_range, neg_one_mul, one_mul, and_self]

theorem physical_real_dimensions (m : ℕ) [NeZero (2 * m)] (hm : 3 ≤ m)
    {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    Module.finrank ℝ (physicalStableSpace m b Ω) = 2 * (m - 2) ∧
      Module.finrank ℝ (physicalUnstableSpace m b Ω) = 2 * (m - 2) := by
  rw [(physical_real_spaces m hb hΩ).1, (physical_real_spaces m hb hΩ).2]
  exact ⟨stable_finrank m hm, unstable_finrank m hm⟩

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
