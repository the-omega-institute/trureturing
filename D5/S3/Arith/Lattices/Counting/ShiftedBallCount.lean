/- GID: D5/S3/Arith/Lattices/Counting/ShiftedBallCount
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Counting/ShiftedBallCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.BoxIntegral.UnitPartition]
   utility: none
   digest: Integer grid points in a shifted three-dimensional ball have normalized limit 4π/3. -/

module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import OmegaBuild.Commands

/-! Normalized integer grid counts in three-dimensional Euclidean balls. -/

compile_only_with_mathlib

@[expose] public section

namespace D5.S3.Arith.Lattices.Counting.ShiftedBallCount

open Filter Set Metric MeasureTheory
open scoped Topology Pointwise

abbrev P := Fin 3 → ℝ
abbrev E := EuclideanSpace ℝ (Fin 3)

noncomputable def toEuclid : P ≃L[ℝ] E := (PiLp.continuousLinearEquiv 2 ℝ _).symm

def grid : Set P := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

def body (c : E) (r : ℝ) : Set P := toEuclid ⁻¹' closedBall c r

private theorem body_measurable (c : E) (r : ℝ) : MeasurableSet (body c r) :=
  isClosed_closedBall.measurableSet.preimage toEuclid.continuous.measurable

theorem body_bounded (c : E) (r : ℝ) : Bornology.IsBounded (body c r) := by
  have he : body c r = toEuclid.symm '' closedBall c r := by
    rw [body, ← toEuclid.image_symm_eq_preimage]
  rw [he]
  exact toEuclid.symm.toContinuousLinearMap.lipschitzWith.isBounded_image (isBounded_closedBall)

private theorem body_frontier : volume (frontier (body 0 1)) = 0 := by
  change volume (frontier (toEuclid.toHomeomorph ⁻¹' closedBall 0 1)) = 0
  rw [← toEuclid.toHomeomorph.preimage_frontier, frontier_closedBall _ one_ne_zero]
  change volume (WithLp.toLp 2 ⁻¹' sphere (0 : E) 1) = 0
  exact ((PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    (isClosed_sphere.measurableSet.nullMeasurableSet)).trans (Measure.addHaar_sphere volume _ _)

private theorem body_volume : volume.real (body 0 1) = 4 * Real.pi / 3 := by
  change (volume (WithLp.toLp 2 ⁻¹' closedBall (0 : E) 1)).toReal = _
  rw [(PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    (isClosed_closedBall.measurableSet.nullMeasurableSet),
    EuclideanSpace.volume_closedBall_fin_three, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity)]
  ring

private theorem body_scale {r : ℝ} (hr : 0 < r) : r • body 0 1 = body 0 r := by
  ext p
  simp only [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', body, Set.mem_preimage, map_smul,
    mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [inv_mul_le_iff₀ hr, mul_one]

private theorem body_mono (c : E) {r s : ℝ} (h : r ≤ s) : body c r ⊆ body c s :=
  Set.preimage_mono (closedBall_subset_closedBall h)

noncomputable def centerCount (c : E) (r : ℝ) : ℕ := (body c r ∩ grid).ncard

private theorem centerCount_zero (r : ℝ) (hr : 0 < r) : centerCount 0 r =
    Nat.card ↑(body 0 1 ∩ r⁻¹ • grid) := by
  rw [centerCount, Set.ncard, ← body_scale hr]
  apply Nat.card_congr
  refine (Equiv.smulRight (α := ℝ) hr.ne').symm.subtypeEquiv fun x => ?_
  change x ∈ r • body 0 1 ∩ grid ↔ r⁻¹ • x ∈ body 0 1 ∩ r⁻¹ • grid
  simp only [mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne',
    Set.smul_mem_smul_set_iff₀ (inv_ne_zero hr.ne')]

private theorem centered_limit :
    Tendsto (fun r : ℝ => (centerCount 0 r : ℝ) / r^3) atTop (𝓝 (4 * Real.pi / 3)) := by
  have h := tendsto_card_div_pow_atTop_volume' (body 0 1) (body_bounded 0 1)
    (body_measurable 0 1) body_frontier (fun x y hx hxy => by
      rw [body_scale hx, body_scale (hx.trans_le hxy)]
      exact body_mono 0 hxy)
  rw [body_volume, Fintype.card_fin] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [centerCount_zero r hr]
  rfl


private theorem shift_ratio_limit (a : ℝ) :
    Tendsto (fun r : ℝ => ((r+a)/r)^3) atTop (𝓝 1) := by
  have h : Tendsto (fun r : ℝ => (1 + a * r⁻¹)^3) atTop (𝓝 ((1 + a * 0)^3)) :=
    (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul a)).pow 3
  simp only [mul_zero, add_zero, one_pow] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  congr 1
  field_simp

private theorem radius_shift_limit (a : ℝ) :
    Tendsto (fun r : ℝ => (centerCount 0 (r+a) : ℝ)/r^3) atTop (𝓝 (4 * Real.pi / 3)) := by
  have h := (centered_limit.comp (tendsto_atTop_add_const_right atTop a tendsto_id)).mul
    (shift_ratio_limit a)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-a)] with r hr ha
  have hpos : 0 < r + a := by linarith
  dsimp
  field_simp

private theorem count_mono {c c' : E} {r s : ℝ} (h : r + dist c c' ≤ s) :
    centerCount c r ≤ centerCount c' s := by
  apply Set.ncard_le_ncard
  · intro p hp
    have hp' : dist (toEuclid p) c ≤ r := hp.1
    exact ⟨(dist_triangle (toEuclid p) c c').trans ((add_le_add_left hp' _).trans h), hp.2⟩
  · change (body c' s ∩ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3))) : Set P)).Finite
    exact ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin 3)) (body_bounded c' s)

/-- The normalized integer grid count of a closed ball with any fixed center. -/
theorem shifted_limit (c : E) :
    Tendsto (fun r : ℝ => (centerCount c r : ℝ) / r^3) atTop (𝓝 (4 * Real.pi / 3)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (radius_shift_limit (-dist (0 : E) c)) (radius_shift_limit (dist (0 : E) c))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (count_mono (by linarith))) (by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Nat.cast_le.mpr (count_mono (by rw [dist_comm c 0]))

end D5.S3.Arith.Lattices.Counting.ShiftedBallCount
