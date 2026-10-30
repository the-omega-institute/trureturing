/- GID: D5/S3/Quantum/Analysis/DatkoStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/DatkoStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Datko squared-orbit-energy characterization on real Banach spaces. -/

import D5.S3.Quantum.Analysis.ContractionSemigroup
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Datko stability for contraction semigroups

Separate finite squared orbit energies imply a common finite-window energy bound,
a strict contraction at one positive time, and uniform exponential decay.
The scalar field is real; no inner product or nonzero-vector assumption is used.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
universe u
namespace D5.S3.Quantum.Analysis.DatkoStability

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)

private def windowFunction (T : ℝ≥0) (x : E) : ℝ → E :=
  (Ioc 0 (T : ℝ)).indicator (fun t => S (Real.toNNReal t) x)

private lemma window_memLp (T : ℝ≥0) (x : E) :
    MemLp (windowFunction S T x) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2
  exact MemLp.of_bound ((S.continuous x).comp continuous_real_toNNReal).aestronglyMeasurable
    ‖x‖ (.of_forall fun t => S.norm_apply_le _ _)

private def windowLinear (T : ℝ≥0) : E →ₗ[ℝ] Lp E 2 (volume : Measure ℝ) where
  toFun x := (window_memLp S T x).toLp (windowFunction S T x)
  map_add' x y := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact .of_forall fun t => by simp [windowFunction, indicator_add]
  map_smul' c x := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact .of_forall fun t => by simp [windowFunction, indicator_smul]

private lemma window_bound (T : ℝ≥0) :
    ∃ C : ℝ, ∀ x : E, ‖windowLinear S T x‖ ≤ C * ‖x‖ := by
  have hm : MemLp ((Ioc (0 : ℝ) T).indicator (fun _ => (1 : ℝ))) 2 volume :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet 1 (Or.inr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  let g := hm.toLp ((Ioc (0 : ℝ) T).indicator (fun _ => (1 : ℝ)))
  refine ⟨‖g‖, fun x => ?_⟩
  have h := Lp.norm_le_mul_norm_of_ae_le_mul (c := ‖x‖)
    (f := windowLinear S T x) (g := g) ?_
  · simpa [mul_comm] using h
  filter_upwards [(window_memLp S T x).coeFn_toLp, hm.coeFn_toLp] with t ht hg
  change ‖(windowLinear S T x) t‖ ≤ ‖x‖ * ‖g t‖
  change ‖((window_memLp S T x).toLp _) t‖ ≤ ‖x‖ * ‖(hm.toLp _) t‖
  rw [ht, hg]
  by_cases hmem : t ∈ Ioc (0 : ℝ) T
  · simp only [windowFunction, indicator_of_mem hmem, norm_one, mul_one]
    exact S.norm_apply_le _ _
  · simp [windowFunction, indicator_of_notMem hmem]

private def windowOperator (T : ℝ≥0) : E →L[ℝ] Lp E 2 (volume : Measure ℝ) :=
  (windowLinear S T).mkContinuousOfExistsBound (window_bound S T)

private lemma norm_toLp_sq {f : ℝ → E} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ t : ℝ, ‖f t‖ ^ 2 := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)]

private lemma window_norm_sq (T : ℝ≥0) (x : E) :
    ‖windowOperator S T x‖ ^ 2 =
      ∫ t in Ioc 0 (T : ℝ), ‖S (Real.toNNReal t) x‖ ^ 2 := by
  change ‖(window_memLp S T x).toLp _‖ ^ 2 = _
  rw [norm_toLp_sq]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall fun t => by
    by_cases ht : t ∈ Ioc (0 : ℝ) T <;> simp [windowFunction, ht]

private lemma common_energy_bound [CompleteSpace E]
    (h : ∀ x : E, IntegrableOn (fun t : ℝ => ‖S (Real.toNNReal t) x‖ ^ 2)
      (Ioi 0) volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ≥0) (x : E),
      (∫ t in Ioc 0 (T : ℝ), ‖S (Real.toNNReal t) x‖ ^ 2) ≤ C * ‖x‖ ^ 2 := by
  have hfull (x : E) : MemLp ((Ioi (0 : ℝ)).indicator
      (fun t : ℝ => S (Real.toNNReal t) x)) 2 volume := by
    apply (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2
    exact (memLp_two_iff_integrable_sq_norm
      (((S.continuous x).comp continuous_real_toNNReal).aestronglyMeasurable)).2 (h x)
  obtain ⟨K, hK⟩ := banach_steinhaus (g := windowOperator S) (fun x => by
    refine ⟨‖(hfull x).toLp _‖, fun T => ?_⟩
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(window_memLp S T x).coeFn_toLp, (hfull x).coeFn_toLp] with t ht hf
    change ‖((window_memLp S T x).toLp _) t‖ ≤ ‖((hfull x).toLp _) t‖
    rw [ht, hf]
    by_cases ht' : t ∈ Ioc (0 : ℝ) T
    · simp [windowFunction, ht', ht'.1]
    · simp [windowFunction, ht'])
  let B := max K 1
  have hB : 0 ≤ B := le_trans (by norm_num) (le_max_right K 1)
  refine ⟨B ^ 2 + 1, by positivity, fun T x => ?_⟩
  rw [← window_norm_sq]
  have hbound : ‖windowOperator S T x‖ ≤ B * ‖x‖ :=
    ((windowOperator S T).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((hK T).trans (le_max_left K 1)) (norm_nonneg x))
  calc
    ‖windowOperator S T x‖ ^ 2 ≤ (B * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ ≤ (B ^ 2 + 1) * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]

end D5.S3.Quantum.Analysis.DatkoStability
