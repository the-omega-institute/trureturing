import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.L1BalancedRadius
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Normed.Operator.LinearIsometry

compile_only_with_mathlib

/-! Omega original.

Coordinates of a finite counting-measure space give the real L1 norm exactly.
-/

namespace ChordalL1

open MeasureTheory

private noncomputable def coordinates {I : Type*} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] :
    Lp ℝ 1 (Measure.count : Measure I) →ₗᵢ[ℝ] PiLp 1 (fun _ : I => ℝ) where
  toFun f := WithLp.toLp 1 (fun i => f i)
  map_add' f g := by
    ext i
    exact Measure.ae_count_iff.mp (Lp.coeFn_add f g) i
  map_smul' r f := by
    ext i
    exact Measure.ae_count_iff.mp (Lp.coeFn_smul r f) i
  norm_map' f := by
    rw [L1.norm_eq_integral_norm, integral_count, PiLp.norm_eq_of_L1]
    rfl

/-- Finite-dimensional real L1 is the Lp space of counting measure. -/
noncomputable def countingCoordinates {I : Type*} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] :
    Lp ℝ 1 (Measure.count : Measure I) ≃ₗᵢ[ℝ] PiLp 1 (fun _ : I => ℝ) :=
  LinearIsometryEquiv.ofSurjective coordinates fun f => by
    have hi : Integrable (fun i => f i) (Measure.count : Measure I) := Integrable.of_finite
    have h := (memLp_one_iff_integrable.mpr hi)
    refine ⟨h.toLp _, ?_⟩
    apply PiLp.ext
    exact Measure.ae_count_iff.mp (h.coeFn_toLp)

theorem exists_counting_radius_obstruction (m : ℕ) (hm : 0 < m) :
    letI : MeasurableSpace (BalancedCutCoordinate m) := ⊤
    let μ : Measure (BalancedCutCoordinate m) := Measure.count
    ∃ x : Fin (2 * m) → Lp ℝ 1 μ, (∀ a b, ‖x a - x b‖ ≤ 1) ∧
      ∀ y, ∃ a, 1 - 1 / (2 * (m : ℝ)) ≤ ‖x a - y‖ := by
  let : MeasurableSpace (BalancedCutCoordinate m) := ⊤
  let : MeasurableSingletonClass (BalancedCutCoordinate m) := ⟨fun _ => trivial⟩
  let e := countingCoordinates (I := BalancedCutCoordinate m)
  obtain ⟨x, hd, hr⟩ := exists_balanced_l1_family m hm
  refine ⟨fun a => e.symm (x a), ?_, ?_⟩
  · intro a b
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact hd _ _
  · intro y
    obtain ⟨a, ha⟩ := hr ((2 : ℝ) • e y)
    refine ⟨a, ?_⟩
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ha
    have he : ‖e.symm (x a) - y‖ = ‖x a - e y‖ := by
      rw [← e.norm_map, map_sub, e.apply_symm_apply]
    rw [he]
    have hmR : (m : ℝ) ≠ 0 := by positivity
    linarith only [ha, show (2 : ℝ) / (2 * (m : ℝ)) = 2 * (1 / (2 * (m : ℝ))) by ring]

end ChordalL1
