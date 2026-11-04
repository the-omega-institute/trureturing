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
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet 1
      (Or.inr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
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

omit [NormedSpace ℝ E] in
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

private lemma orbit_norm_antitone (x : E) :
    Antitone (fun t : ℝ≥0 => ‖S t x‖) := by
  intro s t hst
  change ‖S t x‖ ≤ ‖S s x‖
  rw [← tsub_add_cancel_of_le hst, S.add_apply]
  exact S.norm_apply_le _ _

private lemma strict_time_of_common_energy {C : ℝ} (hC : 0 < C)
    (h : ∀ (T : ℝ≥0) (x : E),
      (∫ t in Ioc 0 (T : ℝ), ‖S (Real.toNNReal t) x‖ ^ 2) ≤ C * ‖x‖ ^ 2) :
    ∃ τ : ℝ≥0, 0 < τ ∧ ‖S τ‖ ≤ 1 / 2 := by
  let τ : ℝ≥0 := ⟨4 * C + 1, by positivity⟩
  have hτ : 0 < (τ : ℝ) := by change 0 < 4 * C + 1; positivity
  refine ⟨τ, by exact_mod_cast hτ, (S τ).opNorm_le_bound (by norm_num) fun x => ?_⟩
  have hi : IntegrableOn (fun t : ℝ => ‖S (Real.toNNReal t) x‖ ^ 2)
      (Ioc 0 (τ : ℝ)) volume :=
    ((((S.continuous x).comp continuous_real_toNNReal).norm.pow 2).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hlower : (τ : ℝ) * ‖S τ x‖ ^ 2 ≤
      ∫ t in Ioc 0 (τ : ℝ), ‖S (Real.toNNReal t) x‖ ^ 2 := by
    have hmono := setIntegral_mono_on
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      hi measurableSet_Ioc (fun t ht =>
        pow_le_pow_left₀ (norm_nonneg _)
          (orbit_norm_antitone S x (Real.toNNReal_le_iff_le_coe.2 ht.2)) 2)
    simpa [setIntegral_const, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal hτ.le] using hmono
  have henergy := hlower.trans (h τ x)
  have hratio : C / (τ : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hτ).2
    change C ≤ 1 / 4 * (4 * C + 1)
    linarith
  have hsq : ‖S τ x‖ ^ 2 ≤ C / (τ : ℝ) * ‖x‖ ^ 2 := by
    have hh := (le_div_iff₀ hτ).2
      (show ‖S τ x‖ ^ 2 * (τ : ℝ) ≤ C * ‖x‖ ^ 2 by nlinarith only [henergy])
    simpa [div_mul_eq_mul_div] using hh
  have hsq' := hsq.trans (mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖x‖))
  nlinarith [norm_nonneg (S τ x), norm_nonneg x]

private lemma exponential_of_strict_time {τ : ℝ≥0} (hτ : 0 < τ)
    (hq : ‖S τ‖ ≤ 1 / 2) :
    ∃ M ω : ℝ, 1 ≤ M ∧ 0 < ω ∧
      ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (-ω * (t : ℝ)) := by
  have hτr : 0 < (τ : ℝ) := hτ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let φ : Multiplicative ℝ≥0 →* (E →L[ℝ] E) := {
    toFun := fun t => S t.toAdd
    map_one' := S.zero
    map_mul' := fun s t => S.add s.toAdd t.toAdd }
  have hpow (n : ℕ) : ‖S (n • τ)‖ ≤ (1 / 2 : ℝ) ^ n := by
    cases n with
    | zero => simpa using S.norm_operator_le_one 0
    | succ n =>
      have hm : S ((n + 1) • τ) = (S τ) ^ (n + 1) := by
        simpa [φ] using φ.map_pow (Multiplicative.ofAdd τ) (n + 1)
      rw [hm]
      exact (norm_pow_le' (S τ) (Nat.succ_pos n)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hq _)
  refine ⟨2, Real.log 2 / (τ : ℝ), by norm_num, div_pos hlog hτr, fun t => ?_⟩
  let n := ⌊(t : ℝ) / (τ : ℝ)⌋₊
  have hnt : (n : ℝ) * (τ : ℝ) ≤ (t : ℝ) :=
    (le_div_iff₀ hτr).1 (Nat.floor_le (div_nonneg t.coe_nonneg hτr.le))
  have hnn : n • τ ≤ t := by
    simpa only [nsmul_eq_mul] using
      (show (n : ℝ≥0) * τ ≤ t by exact_mod_cast hnt)
  have hmono : ‖S t‖ ≤ ‖S (n • τ)‖ :=
    (S t).opNorm_le_bound (norm_nonneg _) (fun x =>
      (orbit_norm_antitone S x hnn).trans ((S (n • τ)).le_opNorm x))
  have hupper : (t : ℝ) / (τ : ℝ) ≤ (n : ℝ) + 1 :=
    (Nat.lt_floor_add_one ((t : ℝ) / (τ : ℝ))).le
  have hexponent : -(n : ℝ) * Real.log 2 ≤
      Real.log 2 - (Real.log 2 / (τ : ℝ)) * (t : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hupper hlog.le
    have he : Real.log 2 * ((t : ℝ) / (τ : ℝ)) =
        (Real.log 2 / (τ : ℝ)) * (t : ℝ) := by ring
    rw [he] at hm
    nlinarith
  calc
    ‖S t‖ ≤ (1 / 2 : ℝ) ^ n := hmono.trans (hpow n)
    _ = Real.exp (-(n : ℝ) * Real.log 2) := by
      rw [show -(n : ℝ) * Real.log 2 = (n : ℝ) * (-Real.log 2) by ring,
        Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    _ ≤ Real.exp (Real.log 2 - (Real.log 2 / (τ : ℝ)) * (t : ℝ)) :=
      Real.exp_le_exp.mpr hexponent
    _ = 2 * Real.exp (-(Real.log 2 / (τ : ℝ)) * (t : ℝ)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
      congr 2
      ring

private lemma integrable_orbit_of_exponential
    (h : ∃ M ω : ℝ, 1 ≤ M ∧ 0 < ω ∧
      ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (-ω * (t : ℝ))) :
    ∀ x : E, IntegrableOn (fun t : ℝ => ‖S (Real.toNNReal t) x‖ ^ 2)
      (Ioi 0) volume := by
  obtain ⟨M, ω, hM, hω, hb⟩ := h
  intro x
  have hi := (integrableOn_exp_mul_Ioi (a := -2 * ω) (by linarith) 0).const_mul
    (M ^ 2 * ‖x‖ ^ 2)
  apply hi.mono' (((S.continuous x).comp continuous_real_toNNReal).norm.pow 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb' : ‖S (Real.toNNReal t) x‖ ≤ M * Real.exp (-ω * t) * ‖x‖ := by
    have hc := ((S (Real.toNNReal t)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hb (Real.toNNReal t)) (norm_nonneg x))
    simpa [Real.coe_toNNReal t ht.le] using hc
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb' 2
  have he : Real.exp (-ω * t) ^ 2 = Real.exp ((-2 * ω) * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    ‖S (Real.toNNReal t) x‖ ^ 2 ≤ (M * Real.exp (-ω * t) * ‖x‖) ^ 2 := hs
    _ = M ^ 2 * ‖x‖ ^ 2 * Real.exp ((-2 * ω) * t) := by
      rw [mul_pow, mul_pow, he]
      ring

/-- Datko's squared-orbit-energy criterion for an arbitrary real Banach space.
The energy bound is assumed separately for each vector. The conclusion has one
pair of constants controlling the operator norm at every nonnegative time. -/
theorem integrable_sq_orbit_iff_exponential_stability [CompleteSpace E] :
    (∀ x : E, IntegrableOn (fun t : ℝ => ‖S (Real.toNNReal t) x‖ ^ 2)
      (Ioi 0) volume) ↔
    ∃ M ω : ℝ, 1 ≤ M ∧ 0 < ω ∧
      ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (-ω * (t : ℝ)) := by
  constructor
  · intro h
    obtain ⟨C, hC, hb⟩ := common_energy_bound S h
    obtain ⟨τ, hτ, hq⟩ := strict_time_of_common_energy S hC hb
    exact exponential_of_strict_time S hτ hq
  · exact integrable_orbit_of_exponential S

end D5.S3.Quantum.Analysis.DatkoStability
