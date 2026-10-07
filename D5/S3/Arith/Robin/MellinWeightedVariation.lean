/- GID: D5/S3/Arith/Robin/MellinWeightedVariation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/MellinWeightedVariation
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A finite absolute Mellin moment bounds the complete weighted Robin kernel variation. -/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology
open MeasureTheory Set Filter

namespace D5.S3.Arith.Robin.MellinWeightedVariation

/-- The positive derivative weight of the Robin price 1/(t log t), for t > 1. -/
noncomputable def weight (t : ℝ) : ℝ :=
  (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)

private lemma weight_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ weight t := by
  unfold weight
  positivity [Real.log_pos ht]

noncomputable def scaleWeight (s y : ℝ) : ℝ :=
  ((Real.log (s * y))⁻¹ + (Real.log (s * y))⁻¹ ^ 2) / (s * y ^ 2)

noncomputable def scaleDerivative (s y : ℝ) : ℝ :=
  -((Real.log (s * y))⁻¹ + 2 * (Real.log (s * y))⁻¹ ^ 2 +
    2 * (Real.log (s * y))⁻¹ ^ 3) / (s ^ 2 * y ^ 2)

private lemma scaleWeight_eq (s y : ℝ) : scaleWeight s y = s * weight (s * y) := by
  unfold scaleWeight weight
  by_cases hs : s = 0
  · simp [hs]
  by_cases hy : y = 0
  · simp [hy]
  by_cases hl : Real.log (s * y) = 0
  · simp [hl]
  field_simp
  <;> ring

private lemma hasDerivAt_scaleWeight {s y : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hsy : 1 < s * y) : HasDerivAt (fun r => scaleWeight r y) (scaleDerivative s y) s := by
  have hl : 0 < Real.log (s * y) := Real.log_pos hsy
  have hp : 0 < s * y := mul_pos hs hy
  have hdlog := (Real.hasDerivAt_log hp.ne').comp s ((hasDerivAt_id s).mul_const y)
  have hdinv := (hasDerivAt_inv hl.ne').comp s hdlog
  have hd : HasDerivAt (fun r => scaleWeight r y)
      (((-(Real.log (s * y) ^ 2)⁻¹ * (1 * y * (s * y)⁻¹) +
        2 * (Real.log (s * y))⁻¹ ^ (2 - 1) *
          (-(Real.log (s * y) ^ 2)⁻¹ * (1 * y * (s * y)⁻¹))) * (s * y ^ 2) -
        ((Real.log (s * y))⁻¹ + (Real.log (s * y))⁻¹ ^ 2) * (1 * y ^ 2)) /
          (s * y ^ 2) ^ 2) s := by
    simpa [scaleWeight, Function.comp_def,
      mul_comm, mul_left_comm, mul_assoc] using!
      (hdinv.add (hdinv.pow 2)).fun_div ((hasDerivAt_id s).mul_const (y ^ 2))
        (mul_ne_zero hs.ne' (pow_ne_zero _ hy.ne'))
  convert hd using 1
  unfold scaleDerivative
  norm_num
  field_simp [hs.ne', hy.ne', hl.ne']
  <;> ring

noncomputable def logDerivativeBound (x : ℝ) : ℝ :=
  (Real.log x)⁻¹ + 2 * (Real.log x)⁻¹ ^ 2 + 2 * (Real.log x)⁻¹ ^ 3

noncomputable def clippedKernel (x s y : ℝ) : ℝ :=
  (Ioi (x / s)).indicator (scaleWeight s) y

noncomputable def chi (a s : ℝ) : ℝ := if s ≤ a then 1 else 0
noncomputable def potential (a α s : ℝ) : ℝ := (max s a) ^ (α - 1)

noncomputable def variationConstant (x α : ℝ) : ℝ :=
  ((1 + (Real.log x)⁻¹) +
    (1 + 2 * (Real.log x)⁻¹ + 2 * (Real.log x)⁻¹ ^ 2) / (1 - α)) *
      x ^ (α - 1) / Real.log x

private lemma scaleDerivative_nonpos {s y : ℝ} (hs : 0 < s) (hy : 0 < y) (hsy : 1 < s * y) :
    scaleDerivative s y ≤ 0 := by
  have hl := Real.log_pos hsy
  unfold scaleDerivative
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (by positivity)
  · positivity

private lemma neg_scaleDerivative_bound {x s y : ℝ} (hx : 1 < x) (hs : 0 < s) (hy : 0 < y)
    (hxy : x ≤ s * y) :
    -scaleDerivative s y ≤ logDerivativeBound x / (s ^ 2 * y ^ 2) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hl : 0 < Real.log (s * y) := Real.log_pos (hx.trans_le hxy)
  have hlog := Real.log_le_log (show 0 < x by linarith) hxy
  have hinv := inv_anti₀ hlx hlog
  have hp : 0 ≤ (Real.log (s * y))⁻¹ := inv_nonneg.mpr hl.le
  have hq : 0 ≤ (Real.log x)⁻¹ := inv_nonneg.mpr hlx.le
  unfold scaleDerivative logDerivativeBound
  rw [neg_div, neg_neg]
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr

private lemma scaleWeight_nonneg {s y : ℝ} (hs : 0 < s) (hy : 0 < y) (hsy : 1 < s * y) :
    0 ≤ scaleWeight s y := by
  unfold scaleWeight
  positivity [Real.log_pos hsy]

private lemma scaleWeight_antitone {x y a b : ℝ} (hx : 1 < x) (hy : 0 < y)
    (ha : 0 < a) (hab : a ≤ b) (hxa : x ≤ a * y) : scaleWeight b y ≤ scaleWeight a y := by
  have hd : ∀ s ∈ Icc a b, HasDerivAt (fun r => scaleWeight r y) (scaleDerivative s y) s := by
    intro s hs
    exact hasDerivAt_scaleWeight (ha.trans_le hs.1) hy
      (hx.trans_le (hxa.trans (mul_le_mul_of_nonneg_right hs.1 hy.le)))
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (HasDerivAt.continuousOn hd)
    (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
    (fun s hs => scaleDerivative_nonpos (ha.trans_le (interior_subset hs).1) hy
      (hx.trans_le (hxa.trans
        (mul_le_mul_of_nonneg_right (interior_subset hs).1 hy.le))))
  exact hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

private lemma weighted_scale_drop {x y m α : ℝ} (hx : 1 < x) (hy : 0 < y) (hm : 0 < m)
    (hα : 0 < α) (hα1 : α < 1) (hxm : x ≤ m * y) :
    m ^ α * (scaleWeight m y - scaleWeight (m + 1) y) ≤
      logDerivativeBound x / ((1 - α) * y ^ 2) *
        (m ^ (α - 1) - (m + 1) ^ (α - 1)) := by
  let C := logDerivativeBound x / ((1 - α) * y ^ 2)
  have hC : 0 ≤ C := by unfold C logDerivativeBound; positivity [Real.log_pos hx]
  have hd : ∀ s ∈ Icc m (m + 1), HasDerivAt
      (fun r => m ^ α * scaleWeight r y - C * r ^ (α - 1))
      (m ^ α * scaleDerivative s y - C * ((α - 1) * s ^ (α - 1 - 1))) s := by
    intro s hs
    have hsp := hm.trans_le hs.1
    have hsy := hx.trans_le (hxm.trans (mul_le_mul_of_nonneg_right hs.1 hy.le))
    simpa only using! ((hasDerivAt_scaleWeight hsp hy hsy).const_mul (m ^ α)).sub
      ((Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hsp.ne')).const_mul C)
  have hnonneg : ∀ s ∈ Icc m (m + 1),
      0 ≤ m ^ α * scaleDerivative s y - C * ((α - 1) * s ^ (α - 1 - 1)) := by
    intro s hs
    have hsp := hm.trans_le hs.1
    have hsy := hxm.trans (mul_le_mul_of_nonneg_right hs.1 hy.le)
    have hr := neg_scaleDerivative_bound hx hsp hy hsy
    have hp : m ^ α ≤ s ^ α := Real.rpow_le_rpow hm.le hs.1 hα.le
    have hnn := neg_nonneg.mpr (scaleDerivative_nonpos hsp hy (hx.trans_le hsy))
    have hmul := (mul_le_mul_of_nonneg_right hp hnn).trans
      (mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hsp.le α))
    have heq : s ^ α * (logDerivativeBound x / (s ^ 2 * y ^ 2)) =
        -(C * ((α - 1) * s ^ (α - 1 - 1))) := by
      unfold C
      rw [show α - 1 - 1 = α - 2 by ring, Real.rpow_sub hsp]
      simp only [Real.rpow_two]
      field_simp [hsp.ne', hy.ne', (sub_pos.mpr hα1).ne']
      <;> ring
    rw [heq] at hmul
    nlinarith
  have hmon := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc m (m + 1))
    (HasDerivAt.continuousOn hd)
    (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
    (fun s hs => hnonneg s (interior_subset hs))
  have h := hmon (left_mem_Icc.mpr (by linarith))
    (right_mem_Icc.mpr (by linarith)) (by linarith)
  dsimp at h
  change _ ≤ C * _
  nlinarith

private lemma clippedKernel_eq {x s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    clippedKernel x s y = if x / y < s then scaleWeight s y else 0 := by
  have heq : x / s < y ↔ x / y < s := by
    rw [div_lt_iff₀ hs, div_lt_iff₀ hy]
    simp [mul_comm]
  simp [clippedKernel, Set.indicator, heq]

private lemma potential_antitone {a α r s : ℝ} (ha : 0 < a) (hα1 : α < 1) (hrs : r ≤ s) :
    potential a α s ≤ potential a α r := by
  unfold potential
  exact Real.rpow_le_rpow_of_nonpos (ha.trans_le (le_max_right _ _))
    (max_le_max_right a hrs) (by linarith)

private lemma weighted_clipped_step {x y m α : ℝ} (hx : 1 < x) (hy : 0 < y) (hm : 0 < m)
    (hα : 0 < α) (hα1 : α < 1) :
    m ^ α * |clippedKernel x m y - clippedKernel x (m + 1) y| ≤
      (x / y) ^ (α + 1) * weight x * (chi (x / y) m - chi (x / y) (m + 1)) +
      logDerivativeBound x / ((1 - α) * y ^ 2) *
        (potential (x / y) α m - potential (x / y) α (m + 1)) := by
  have hxpos : 0 < x := by linarith
  have ha : 0 < x / y := div_pos hxpos hy
  have hm1 : 0 < m + 1 := by linarith
  have hC : 0 ≤ logDerivativeBound x / ((1 - α) * y ^ 2) := by
    unfold logDerivativeBound
    positivity [Real.log_pos hx]
  rw [clippedKernel_eq hm hy, clippedKernel_eq hm1 hy]
  by_cases ham : x / y < m
  · have ham1 : x / y < m + 1 := by linarith
    have hxm : x ≤ m * y := ((div_le_iff₀ hy).mp ham.le)
    have hdrop := scaleWeight_antitone (b := m + 1) hx hy hm (by linarith) hxm
    simp only [if_pos ham, if_pos ham1]
    rw [abs_of_nonneg (sub_nonneg.mpr hdrop)]
    simpa [chi, potential, not_le.mpr ham, not_le.mpr ham1,
      max_eq_left ham.le, max_eq_left ham1.le] using weighted_scale_drop hx hy hm hα hα1 hxm
  · have hma : m ≤ x / y := le_of_not_gt ham
    by_cases ham1 : x / y < m + 1
    · have hfy := scaleWeight_antitone hx hy ha ham1.le
        (by rw [div_mul_cancel₀ _ hy.ne'])
      have hfx : scaleWeight (x / y) y = (x / y) * weight x := by
        rw [scaleWeight_eq, div_mul_cancel₀ _ hy.ne']
      rw [hfx] at hfy
      have hq : 0 ≤ scaleWeight (m + 1) y := scaleWeight_nonneg hm1 hy
        (hx.trans_le ((div_le_iff₀ hy).mp ham1.le))
      have hpow := Real.rpow_le_rpow hm.le hma hα.le
      have hmul := (mul_le_mul_of_nonneg_right hpow hq).trans
        (mul_le_mul_of_nonneg_left hfy (Real.rpow_nonneg ha.le α))
      have heq : (x / y) ^ α * ((x / y) * weight x) =
          (x / y) ^ (α + 1) * weight x := by
        rw [Real.rpow_add ha, Real.rpow_one]
        ring
      rw [heq] at hmul
      have hpot := potential_antitone ha hα1 (show m ≤ m + 1 by linarith)
      simp only [if_neg ham, if_pos ham1, zero_sub, abs_neg, abs_of_nonneg hq]
      simp only [chi, if_pos hma, if_neg (not_le.mpr ham1), sub_zero, mul_one]
      exact hmul.trans (le_add_of_nonneg_right
        (mul_nonneg hC (sub_nonneg.mpr hpot)))
    · have hm1a : m + 1 ≤ x / y := le_of_not_gt ham1
      simp [if_neg ham, if_neg ham1, chi, hma, hm1a, potential,
        max_eq_right hma, max_eq_right hm1a]

private lemma coefficient_identity {x y α : ℝ} (hx : 1 < x) (hy : 0 < y) (hα1 : α < 1) :
    (x / y) ^ (α + 1) * weight x +
      logDerivativeBound x / ((1 - α) * y ^ 2) * (x / y) ^ (α - 1) =
      variationConstant x α * y ^ (-α - 1) := by
  have hxpos : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hxp : x ^ (α + 1) = x ^ (α - 1) * x ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hyp : y ^ (α + 1) = y ^ (α - 1) * y ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hy]
    congr 1
    ring
  have hyp0 : y ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  have hyn : y ^ (-α - 1) = (y ^ (α + 1))⁻¹ := by
    rw [show -α - 1 = -(α + 1) by ring, Real.rpow_neg hy.le]
  unfold logDerivativeBound variationConstant weight
  rw [Real.div_rpow hxpos.le hy.le, Real.div_rpow hxpos.le hy.le, hxp, hyn, hyp]
  field_simp [hxpos.ne', hy.ne', hl.ne', hyp0, (sub_pos.mpr hα1).ne']
  <;> ring

theorem clipped_kernel_prefix_bound (N : ℕ) {x y α : ℝ}
    (hx : 1 < x) (hy : 0 < y) (hα : 0 < α) (hα1 : α < 1) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ α *
      |clippedKernel x (j + 1) y - clippedKernel x (j + 2) y|) ≤
        variationConstant x α * y ^ (-α - 1) := by
  have ha : 0 < x / y := div_pos (by linarith) hy
  have hC : 0 ≤ logDerivativeBound x / ((1 - α) * y ^ 2) := by
    unfold logDerivativeBound
    positivity [Real.log_pos hx]
  have hX : 0 ≤ (x / y) ^ (α + 1) * weight x :=
    mul_nonneg (Real.rpow_nonneg ha.le _) (weight_nonneg hx)
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j _ =>
    weighted_clipped_step hx hy
      (show 0 < (j + 1 : ℝ) by positivity) hα hα1)
  have htelχ : (∑ j ∈ Finset.range N, (chi (x / y) (j + 1) - chi (x / y) (j + 2))) =
      chi (x / y) 1 - chi (x / y) (N + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, zero_add, one_add_one_eq_two] using
      (Finset.sum_range_sub' (fun j : ℕ => chi (x / y) (j + 1)) N)
  have htelH : (∑ j ∈ Finset.range N,
      (potential (x / y) α (j + 1) - potential (x / y) α (j + 2))) =
        potential (x / y) α 1 - potential (x / y) α (N + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, zero_add, one_add_one_eq_two] using
      (Finset.sum_range_sub' (fun j : ℕ => potential (x / y) α (j + 1)) N)
  have hχ : chi (x / y) 1 - chi (x / y) (N + 1) ≤ 1 := by
    unfold chi
    split_ifs <;> norm_num
  have hH : potential (x / y) α 1 - potential (x / y) α (N + 1) ≤
      (x / y) ^ (α - 1) := by
    have hstart : potential (x / y) α 1 ≤ (x / y) ^ (α - 1) := by
      unfold potential
      exact Real.rpow_le_rpow_of_nonpos ha (le_max_right _ _) (by linarith)
    have hend : 0 ≤ potential (x / y) α (N + 1) := by
      unfold potential
      exact Real.rpow_nonneg (ha.le.trans (le_max_right _ _)) _
    linarith
  calc
    _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hsum
    _ = (x / y) ^ (α + 1) * weight x * (chi (x / y) 1 - chi (x / y) (N + 1)) +
        logDerivativeBound x / ((1 - α) * y ^ 2) *
          (potential (x / y) α 1 - potential (x / y) α (N + 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htelχ, htelH]
    _ ≤ (x / y) ^ (α + 1) * weight x +
        logDerivativeBound x / ((1 - α) * y ^ 2) * (x / y) ^ (α - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hχ hX, mul_le_mul_of_nonneg_left hH hC]
    _ = _ := coefficient_identity hx hy hα1

private lemma measurable_clippedKernel (x s : ℝ) : Measurable (clippedKernel x s) := by
  unfold clippedKernel
  apply Measurable.indicator _ measurableSet_Ioi
  unfold scaleWeight
  fun_prop

private lemma clipped_kernel_majorant {x s y α : ℝ} (hx : 1 < x) (hs : 0 < s)
    (hy : 0 < y) (hα1 : α < 1) :
    0 ≤ clippedKernel x s y ∧
      clippedKernel x s y ≤
        (((Real.log x)⁻¹ + (Real.log x)⁻¹ ^ 2) / s * (x / s) ^ (α - 1)) *
          y ^ (-α - 1) := by
  have hxpos : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  by_cases hcut : x / s < y
  · have hxy : x < s * y := by simpa [mul_comm] using (div_lt_iff₀ hs).mp hcut
    have hsy := hx.trans hxy
    have hl : 0 < Real.log (s * y) := Real.log_pos hsy
    have hlog := Real.log_le_log hxpos hxy.le
    have hinv := inv_anti₀ hlx hlog
    have hp : 0 ≤ (Real.log (s * y))⁻¹ := inv_nonneg.mpr hl.le
    have hq : 0 ≤ (Real.log x)⁻¹ := inv_nonneg.mpr hlx.le
    have hnum : (Real.log (s * y))⁻¹ + (Real.log (s * y))⁻¹ ^ 2 ≤
        (Real.log x)⁻¹ + (Real.log x)⁻¹ ^ 2 := by gcongr
    have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hxpos hs) hcut.le
      (show α - 1 ≤ 0 by linarith)
    simp only [clippedKernel, Set.indicator, Set.mem_Ioi, if_pos hcut]
    refine ⟨scaleWeight_nonneg hs hy hsy, ?_⟩
    calc
      scaleWeight s y =
          ((Real.log (s * y))⁻¹ + (Real.log (s * y))⁻¹ ^ 2) / s * y ^ (-2 : ℝ) := by
        unfold scaleWeight
        rw [Real.rpow_neg hy.le, Real.rpow_two]
        ring
      _ ≤ ((Real.log x)⁻¹ + (Real.log x)⁻¹ ^ 2) / s * y ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnum hs.le)
          (Real.rpow_nonneg hy.le _)
      _ = (((Real.log x)⁻¹ + (Real.log x)⁻¹ ^ 2) / s * y ^ (α - 1)) *
          y ^ (-α - 1) := by
        rw [mul_assoc, ← Real.rpow_add hy]
        congr 2
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy.le _)
        apply mul_le_mul_of_nonneg_left hpow
        positivity
  · simp only [clippedKernel, Set.indicator, Set.mem_Ioi, if_neg hcut]
    exact ⟨le_rfl, by positivity⟩

noncomputable def genericP (ρ : ℝ → ℝ) (x s : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ρ y * clippedKernel x s y

noncomputable def mellinMass (ρ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), |ρ y| * y ^ (-α - 1)

private lemma generic_P_integrable (ρ : ℝ → ℝ) {x s α : ℝ} (hx : 1 < x) (hs : 0 < s)
    (hα1 : α < 1) (hρ : Measurable ρ)
    (hM : IntegrableOn (fun y => |ρ y| * y ^ (-α - 1)) (Ioi 0)) :
    IntegrableOn (fun y => ρ y * clippedKernel x s y) (Ioi 0) := by
  let C := ((Real.log x)⁻¹ + (Real.log x)⁻¹ ^ 2) / s * (x / s) ^ (α - 1)
  apply Integrable.mono' (hM.const_mul C)
  · exact (hρ.mul (measurable_clippedKernel x s)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hq := clipped_kernel_majorant hx hs hy hα1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hq.1]
    have h := mul_le_mul_of_nonneg_left hq.2 (abs_nonneg (ρ y))
    dsimp [C]
    nlinarith

theorem generic_weighted_prefix (ρ : ℝ → ℝ) (N : ℕ) {x α : ℝ}
    (hx : 1 < x) (hα : 0 < α) (hα1 : α < 1) (hρ : Measurable ρ)
    (hM : IntegrableOn (fun y => |ρ y| * y ^ (-α - 1)) (Ioi 0)) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ α *
      |genericP ρ x (j + 1) - genericP ρ x (j + 2)|) ≤
        variationConstant x α * mellinMass ρ α := by
  let F := fun j : ℕ => fun y : ℝ => (j + 1 : ℝ) ^ α *
    ‖ρ y * clippedKernel x (j + 1) y - ρ y * clippedKernel x (j + 2) y‖
  have hiP : ∀ m : ℕ, IntegrableOn (fun y => ρ y * clippedKernel x (m + 1) y) (Ioi 0) := by
    intro m
    exact generic_P_integrable ρ hx (by positivity) hα1 hρ hM
  have hiF : ∀ j : ℕ, IntegrableOn (F j) (Ioi 0) := by
    intro j
    simpa only [F, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two, Pi.sub_apply] using!
      ((hiP j).sub (hiP (j + 1))).norm.const_mul ((j + 1 : ℝ) ^ α)
  have hsingle : ∀ j : ℕ,
      (j + 1 : ℝ) ^ α * |genericP ρ x (j + 1) - genericP ρ x (j + 2)| ≤
        ∫ y in Ioi (0 : ℝ), F j y := by
    intro j
    have hi₂ : IntegrableOn (fun y => ρ y * clippedKernel x (j + 2) y) (Ioi 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hiP (j + 1)
    unfold genericP
    rw [← integral_sub (hiP j) hi₂]
    have h := norm_integral_le_integral_norm
      (fun y => ρ y * clippedKernel x (j + 1) y - ρ y * clippedKernel x (j + 2) y)
      (μ := volume.restrict (Ioi (0 : ℝ)))
    rw [Real.norm_eq_abs] at h
    dsimp [F]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hsumInt := integrable_finsetSum (Finset.range N) (fun j _ => hiF j)
  have hmajor := hM.const_mul (variationConstant x α)
  calc
    _ ≤ ∑ j ∈ Finset.range N, ∫ y in Ioi (0 : ℝ), F j y := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_add, Nat.cast_one] using hsingle j
    _ = ∫ y in Ioi (0 : ℝ), ∑ j ∈ Finset.range N, F j y := by
      rw [integral_finsetSum _ (fun j _ => hiF j)]
    _ ≤ ∫ y in Ioi (0 : ℝ), variationConstant x α * (|ρ y| * y ^ (-α - 1)) := by
      apply setIntegral_mono_on hsumInt hmajor measurableSet_Ioi
      intro y hy
      have hprefix := mul_le_mul_of_nonneg_left
        (clipped_kernel_prefix_bound N hx hy hα hα1) (abs_nonneg (ρ y))
      have heq : (∑ j ∈ Finset.range N, F j y) =
          |ρ y| * (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ α *
            |clippedKernel x (j + 1) y - clippedKernel x (j + 2) y|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [F]
        rw [show ρ y * clippedKernel x (j + 1) y -
          ρ y * clippedKernel x (j + 2) y = ρ y *
            (clippedKernel x (j + 1) y - clippedKernel x (j + 2) y) by ring,
          abs_mul]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      nlinarith
    _ = _ := by rw [integral_const_mul]; rfl

/-- Complete generic weighted variation estimate for the fixed Robin weight. -/
theorem mellin_weighted_variation (ρ : ℝ → ℝ) {x α : ℝ}
    (hx : 1 < x) (hα : 0 < α) (hα1 : α < 1) (hρ : Measurable ρ)
    (hM : IntegrableOn (fun y => |ρ y| * y ^ (-α - 1)) (Ioi 0)) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ α *
      |genericP ρ x (j + 1) - genericP ρ x (j + 2)|) ∧
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ α *
      |genericP ρ x (j + 1) - genericP ρ x (j + 2)|) ≤
        variationConstant x α * mellinMass ρ α := by
  have hnonneg : ∀ j : ℕ, 0 ≤ ((j + 1 : ℕ) : ℝ) ^ α *
      |genericP ρ x (j + 1) - genericP ρ x (j + 2)| := by intro j; positivity
  have hprefix := fun N => generic_weighted_prefix ρ N hx hα hα1 hρ hM
  exact ⟨summable_of_sum_range_le hnonneg hprefix,
    Real.tsum_le_of_sum_range_le hnonneg hprefix⟩

end D5.S3.Arith.Robin.MellinWeightedVariation
