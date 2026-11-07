/- GID: D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation
   generality: I
   mirror-B: D5/B/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A smooth even alpha-unpredictable function has neither ordinary Cesaro mean. -/

/-
admission_basis: open-problem-resolution (#26750; Refuted)
Direct frozen dependencies: none (Mathlib only).
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The source predicates and both interval-integral expressions retain the statement of #26750;
the construction uses Mathlib's normalized bump, convolution, Nat.bodd and Bool.toNat directly.
The average-existence question is in journal Remark 1, not in arXiv:2608.09809v2.
The statement includes all real return and divergence sequences; integer shifts are witnesses.
No claim is made about bounded primitives, bounded remainders or generalized invariant means.
bounded_locally_integrable: proof_shape: bind-only; escape_witness: none; consumers: smooth_contDiff, smooth_uniformContinuous, smooth_integral_error.
smooth_contDiff: proof_shape: bind-only; escape_witness: none; consumers: smooth_uniformContinuous, symmetric_mean_eq.
smooth_bound: proof_shape: bind-only; escape_witness: none; consumers: smooth_alpha.
smooth_uniformContinuous: proof_shape: bind-only; escape_witness: none; consumers: smooth_alpha.
smooth_local_return: proof_shape: bind-only; escape_witness: none; consumers: smooth_alpha.
smooth_plateau: proof_shape: bind-only; escape_witness: none; consumers: smoothed_cell.
shifted_interval_error: proof_shape: bind-only; escape_witness: none; consumers: smooth_integral_error.
smooth_integral_error: proof_shape: bind-only; escape_witness: none; consumers: endpoint_error.
words_prefix_succ: proof_shape: bind-only; escape_witness: none; consumers: words_prefix.
words_prefix: proof_shape: content; escape_witness: none; consumers: bit_eq_word.
words_length_ge: proof_shape: content; escape_witness: none; consumers: bit_eq_word, universal_word, endpoint_error, no_one_sided_mean.
prefix_getD: proof_shape: bind-only; escape_witness: none; consumers: bit_eq_word.
bit_eq_word: proof_shape: content; escape_witness: none; consumers: universal_word, step_integral_endpoint.
enumeration_infix: proof_shape: bind-only; escape_witness: none; consumers: universal_word.
universal_word: proof_shape: content; escape_witness: none; consumers: central_return, zero_one_cells.
occupation_bound: proof_shape: bind-only; escape_witness: none; consumers: endpoint_occupation_bound.
endpoint_occupation_bound: proof_shape: bind-only; escape_witness: none; consumers: endpoint_error.
intBit_nat: proof_shape: bind-only; escape_witness: none; consumers: central_return, cell_value.
intBit_reflect: proof_shape: bind-only; escape_witness: none; consumers: step_even_ae.
step_measurable: proof_shape: bind-only; escape_witness: none; consumers: step_integral_endpoint, smooth_alpha, endpoint_error, symmetric_mean_eq.
step_bound: proof_shape: bind-only; escape_witness: none; consumers: step_integral_endpoint, smooth_alpha, endpoint_error, symmetric_mean_eq.
central_return: proof_shape: content; escape_witness: none; consumers: smooth_alpha.
step_local_return: proof_shape: bind-only; escape_witness: none; consumers: smooth_alpha.
cell_value: proof_shape: bind-only; escape_witness: none; consumers: step_integral_endpoint, smoothed_cell.
step_even_ae: proof_shape: bind-only; escape_witness: none; consumers: smooth_even.
sum_realBit: proof_shape: bind-only; escape_witness: none; consumers: sum_getD_count.
sum_getD_count: proof_shape: bind-only; escape_witness: none; consumers: step_integral_endpoint.
step_integral_endpoint: proof_shape: content; escape_witness: none; consumers: endpoint_error.
zero_one_cells: proof_shape: content; escape_witness: none; consumers: smooth_alpha.
increasing_selection: proof_shape: bind-only; escape_witness: none; consumers: smooth_alpha.
smooth_even: proof_shape: bind-only; escape_witness: none; consumers: symmetric_mean_eq.
smoothed_cell: proof_shape: bind-only; escape_witness: none; consumers: smooth_alpha.
smooth_alpha: proof_shape: content; escape_witness: none; consumers: result.
endpoint_error: proof_shape: content; escape_witness: none; consumers: no_one_sided_mean.
no_one_sided_mean: proof_shape: content; escape_witness: none; consumers: result.
symmetric_mean_eq: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: content; escape_witness: none; consumers: none (settling result).
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Common
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Data.Nat.Bits

namespace D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation

open Filter
open scoped Topology

/-- The source's Definition 1, with its particular return sequence retained. -/
def PoissonReturn (f : ℝ → ℝ) (q : ℕ → ℝ) : Prop :=
  UniformContinuous f ∧
  (∃ M : ℝ, ∀ t : ℝ, |f t| ≤ M) ∧
  StrictMono q ∧ Tendsto q atTop atTop ∧
  ∀ (a b ε : ℝ), a ≤ b → 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : ℝ, t ∈ Set.Icc a b → |f (t + q n) - f t| < ε

/-- Poisson stability in journal Definition 1. -/
def IsPoissonStable (f : ℝ → ℝ) : Prop :=
  ∃ q : ℕ → ℝ, PoissonReturn f q

/-- Journal Definition 2: recurrence and separation use the same q. -/
def IsAlphaUnpredictable (f : ℝ → ℝ) : Prop :=
  ∃ q : ℕ → ℝ, PoissonReturn f q ∧
    ∃ (s : ℕ → ℝ) (ε₀ δ : ℝ),
      StrictMono s ∧ Tendsto s atTop atTop ∧ 0 < ε₀ ∧ 0 < δ ∧
      ∀ n : ℕ, ∀ t : ℝ, t ∈ Set.Icc (s n) (s n + δ) →
        ε₀ < |f (t + q n) - f t|

/-- Remark 1 under either ordinary Cesaro convention. Negating this disjunction
refutes each universal reading; the even witness refutes both at once. -/
def claim : Prop :=
  (∀ f : ℝ → ℝ, IsAlphaUnpredictable f →
    ∃ m : ℝ, Tendsto
      (fun T : ℝ => (∫ t in (0 : ℝ)..T, f t) / T) atTop (nhds m)) ∨
  (∀ f : ℝ → ℝ, IsAlphaUnpredictable f →
    ∃ m : ℝ, Tendsto
      (fun T : ℝ => (∫ t in -T..T, f t) / (2 * T)) atTop (nhds m))

end D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation

namespace D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation

open MeasureTheory Filter Set
open scoped Convolution Topology ContDiff

private noncomputable def bump : ContDiffBump (0 : ℝ) :=
  ⟨1/8, 1/4, by norm_num, by norm_num⟩

private theorem bounded_locally_integrable {v : ℝ → ℝ} (hv : Measurable v)
    (hb : ∀ x, |v x| ≤ 1) : LocallyIntegrable v volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  apply IntegrableOn.of_bound hK.measure_lt_top hv.aestronglyMeasurable.restrict 1
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x

private theorem smooth_contDiff {v : ℝ → ℝ} (hv : Measurable v) (hb : ∀ x, |v x| ≤ 1) :
    ContDiff ℝ ∞ (((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v)) := by
  exact bump.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) bump.contDiff_normed (bounded_locally_integrable hv hb)

private theorem smooth_bound {v : ℝ → ℝ} (hb : ∀ x, |v x| ≤ 1) (x : ℝ) : |((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x| ≤ 1 := by
  change |∫ u : ℝ, (bump.normed volume) u * v (x-u)| ≤ 1
  calc
    _ ≤ ∫ u : ℝ, ‖(bump.normed volume) u * v (x-u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, (bump.normed volume) u := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun u => norm_nonneg _
      · exact bump.integrable_normed
      · exact Eventually.of_forall fun u => by
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, show |(bump.normed volume) u| = (bump.normed volume) u from abs_of_nonneg (bump.nonneg_normed u)]
          exact mul_le_of_le_one_right (bump.nonneg_normed u) (hb _)
    _ = 1 := bump.integral_normed

private theorem smooth_uniformContinuous {v : ℝ → ℝ} (hv : Measurable v)
    (hb : ∀ x, |v x| ≤ 1) : UniformContinuous (((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v)) := by
  let C : ℝ := ∫ u : ℝ, ‖deriv (bump.normed volume) u‖
  have hkd : Integrable (deriv (bump.normed volume)) :=
    ((show ContDiff ℝ 1 (bump.normed volume) from bump.contDiff_normed).continuous_deriv (by decide)).integrable_of_hasCompactSupport
      bump.hasCompactSupport_normed.deriv
  have hC : 0 ≤ C := integral_nonneg fun u => norm_nonneg _
  have hd (x : ℝ) : HasDerivAt (((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v))
      ((deriv (bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x) x :=
    bump.hasCompactSupport_normed.hasDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) bump.contDiff_normed (bounded_locally_integrable hv hb) x
  have hbd (x : ℝ) : ‖deriv (((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v)) x‖ ≤ C := by
    rw [(hd x).deriv]
    change ‖∫ u : ℝ, deriv (bump.normed volume) u * v (x-u)‖ ≤ C
    apply norm_integral_le_of_norm_le hkd.norm
    exact Eventually.of_forall fun u => by
      rw [norm_mul, Real.norm_eq_abs (v _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb _)
  apply (lipschitzWith_of_nnnorm_deriv_le (C := ⟨C, hC⟩)
    ((smooth_contDiff hv hb).differentiable (by simp)) (fun x => hbd x)).uniformContinuous

private theorem smooth_local_return {v : ℝ → ℝ} {q r : ℝ}
    (h : ∀ x : ℝ, |x| ≤ r + 1 → v (x+q) = v x) {t : ℝ} (ht : |t| ≤ r) :
    ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) (t+q) = ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) t := by
  change (∫ u : ℝ, (bump.normed volume) u * v (t+q-u)) = ∫ u : ℝ, (bump.normed volume) u * v (t-u)
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  dsimp only
  by_cases hu : (bump.normed volume) u = 0
  · simp [hu]
  · have hus : |u| < (1/4 : ℝ) := by
      have hh : u ∈ Function.support (bump.normed volume) := hu
      rw [bump.support_normed_eq] at hh
      simpa [bump, Metric.mem_ball, Real.dist_eq] using hh
    have htu : |t-u| ≤ r + 1 := by
      have ha := abs_sub t u
      linarith
    rw [show t+q-u = (t-u)+q by ring, h _ htu]

private theorem smooth_plateau {v : ℝ → ℝ} {t c : ℝ}
    (h : ∀ x : ℝ, |x-t| < (1/4 : ℝ) → v x = c) : ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) t = c := by
  have ht : v t = c := h t (by norm_num)
  rw [← ht]
  exact bump.normed_convolution_eq_right fun x hx => by
    apply (h x (by simpa [bump, Metric.mem_ball, Real.dist_eq] using hx)).trans ht.symm

private theorem shifted_interval_error {v : ℝ → ℝ} (hv : LocallyIntegrable v volume)
    (hb : ∀ x, |v x| ≤ 1) (a b u : ℝ) :
    |(∫ x in a-u..b-u, v x) - (∫ x in a..b, v x)| ≤ 2 * |u| := by
  have hi (c d : ℝ) : IntervalIntegrable v volume c d := (hv.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  rw [intervalIntegral.integral_interval_sub_interval_comm (hi _ _) (hi _ _) (hi _ _)]
  calc
    _ ≤ |∫ x in a-u..a, v x| + |∫ x in b-u..b, v x| := abs_sub _ _
    _ ≤ 1 * |a-(a-u)| + 1 * |b-(b-u)| := add_le_add
      (by simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_of_norm_le_const (a := a-u) (b := a) (f := v) fun x _ => by simpa only [Real.norm_eq_abs] using hb x))
      (by simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_of_norm_le_const (a := b-u) (b := b) (f := v) fun x _ => by simpa only [Real.norm_eq_abs] using hb x))
    _ = 2 * |u| := by simp; ring

end D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation

namespace D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation
open MeasureTheory Filter Set
open scoped Convolution Topology ContDiff

private theorem smooth_integral_error {v : ℝ → ℝ} (hv : Measurable v)
    (hb : ∀ x, |v x| ≤ 1) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) t) - (∫ t in (0:ℝ)..T, v t)| ≤ (1/2 : ℝ) := by
  have hkint : Integrable (bump.normed volume) := bump.integrable_normed
  let μ : Measure ℝ := volume.restrict (uIoc 0 T)
  have : IsFiniteMeasure μ := by dsimp [μ, uIoc]; infer_instance
  have hp : Integrable (fun p : ℝ × ℝ => (bump.normed volume) p.2 * v (p.1-p.2)) (μ.prod volume) := by
    have hi := (integrable_const (1 : ℝ) (μ := μ)).mul_prod hkint
    have hm := hi.mul_bdd (c := 1)
      (hv.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply] using hb (p.1-p.2))
    simpa only [one_mul, Function.comp_apply, Pi.sub_apply] using hm
  have hfub : (∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) t) =
      ∫ u : ℝ, (bump.normed volume) u * (∫ t in (0:ℝ)..T, v (t-u)) := by
    change (∫ t in (0:ℝ)..T, ∫ u : ℝ, (bump.normed volume) u * v (t-u)) = _
    rw [intervalIntegral_integral_swap hp]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => intervalIntegral.integral_const_mul _ _
  have hiu : Integrable (fun u : ℝ => (bump.normed volume) u * (∫ t in (0:ℝ)..T, v (t-u))) := by
    have hh := hp.integral_prod_right
    simpa only [μ, uIoc_of_le hT, ← intervalIntegral.integral_of_le hT,
      intervalIntegral.integral_const_mul] using hh
  let I : ℝ := ∫ t in (0:ℝ)..T, v t
  have hi : (∫ u : ℝ, (bump.normed volume) u * I) = I := by
    exact ContDiffBump.integral_normed_smul bump volume I
  rw [hfub]
  change |(∫ u : ℝ, (bump.normed volume) u * (∫ t in (0:ℝ)..T, v (t-u))) - I| ≤ _
  rw [← hi, ← integral_sub hiu (hkint.mul_const I)]
  change |∫ u : ℝ, (bump.normed volume) u * (∫ t in (0:ℝ)..T, v (t-u)) - (bump.normed volume) u * I| ≤ _
  calc
    _ ≤ ∫ u : ℝ, (1/2 : ℝ) * (bump.normed volume) u := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hkint.const_mul (1/2 : ℝ))
      exact Eventually.of_forall fun u => by
        rw [← mul_sub, Real.norm_eq_abs, abs_mul,
          show |(bump.normed volume) u| = (bump.normed volume) u from abs_of_nonneg (bump.nonneg_normed u)]
        by_cases hu : (bump.normed volume) u = 0
        · simp [hu]
        · have hus : |u| < (1/4 : ℝ) := by
            have hh : u ∈ Function.support (bump.normed volume) := hu
            rw [bump.support_normed_eq] at hh
            simpa [bump, Metric.mem_ball, Real.dist_eq] using hh
          have hshift := shifted_interval_error (bounded_locally_integrable hv hb) hb 0 T u
          rw [intervalIntegral.integral_comp_sub_right]
          dsimp only [I]
          simp only [zero_sub] at hshift
          have he : |(∫ t in -u..T-u, v t) - (∫ t in (0:ℝ)..T, v t)| ≤ (1/2 : ℝ) :=
            hshift.trans (by linarith)
          simpa only [zero_sub, mul_comm] using
            mul_le_mul_of_nonneg_left he (show 0 ≤ (bump.normed volume) u from bump.nonneg_normed u)
    _ = (1/2 : ℝ) := by
      rw [integral_const_mul]
      change (1/2 : ℝ) * (∫ u : ℝ, bump.normed volume u) = _
      rw [bump.integral_normed, mul_one]

end D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation

namespace D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation

set_option autoImplicit false

private noncomputable def enumeration (n : ℕ) : List Bool :=
  ((Finset.univ : Finset (Fin n → Bool)).toList.map List.ofFn).flatten

private noncomputable def words : ℕ → List Bool
  | 0 => []
  | n + 1 =>
    let u := words n ++ enumeration (n + 1)
    u ++ List.replicate ((n + 1)^2 * (u.length + 1)) (Nat.bodd (n + 1))

private noncomputable def bit (k : ℕ) : Bool := (words (k + 1)).getD k false

private theorem words_prefix_succ (n : ℕ) : words n <+: words (n + 1) := by
  exact (List.prefix_append _ _).trans (List.prefix_append _ _)

private theorem words_prefix {n m : ℕ} (h : n ≤ m) : words n <+: words m := by
  induction h with
  | refl => exact List.prefix_refl _
  | step h ih => exact ih.trans (words_prefix_succ _)

private theorem words_length_ge (n : ℕ) : n ≤ (words n).length := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    have hsq : 1 ≤ (n + 1)^2 := by exact Nat.one_le_pow' 2 n
    have hm := Nat.le_mul_of_pos_left ((words n ++ enumeration (n + 1)).length + 1) hsq
    simp only [words, List.length_append, List.length_replicate] at *
    omega

private theorem prefix_getD {u v : List Bool} (h : u <+: v) {k : ℕ} (hk : k < u.length) :
    v.getD k false = u.getD k false := by
  obtain ⟨s, rfl⟩ := h
  exact List.getD_append _ _ _ _ hk

private theorem bit_eq_word {n k : ℕ} (hk : k < (words n).length) :
    bit k = (words n).getD k false := by
  unfold bit
  have hu := words_length_ge (k + 1)
  by_cases h : n ≤ k + 1
  · exact prefix_getD (words_prefix h) hk
  · exact (prefix_getD (words_prefix (by omega)) (by omega)).symm

private theorem enumeration_infix (w : List Bool) : w <:+: enumeration w.length := by
  classical
  have hf : List.ofFn (fun i : Fin w.length => w[i]) = w := List.ofFn_getElem
  have hm : w ∈ (Finset.univ : Finset (Fin w.length → Bool)).toList.map List.ofFn := by
    apply List.mem_map.mpr
    exact ⟨(fun i : Fin w.length => w[i]), by simp, hf⟩
  obtain ⟨u, v, he⟩ := List.mem_iff_append.mp hm
  unfold enumeration
  rw [he]
  exact ⟨u.flatten, v.flatten, by simp⟩

private theorem universal_word (w : List Bool) (K : ℕ) :
    ∃ j : ℕ, K ≤ j ∧ ∀ i : ℕ, i < w.length → bit (j + i) = w.getD i false := by
  let n := max (K + 1) w.length
  let v := w ++ List.replicate (n - w.length) false
  have hv : v.length = n := by simp [v]; omega
  have hwv : w <+: v := List.prefix_append _ _
  have hve : v <:+: enumeration n := by simpa only [hv] using enumeration_infix v
  have hwe : w <:+: enumeration n := hwv.isInfix.trans hve
  obtain ⟨p, s, he⟩ := hwe
  have hn : 0 < n := by dsimp [n]; omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have he' : p ++ w ++ s = enumeration (m + 1) := by simpa only [hm] using he
  have hel := congrArg List.length he'
  simp only [List.length_append] at hel
  refine ⟨(words m).length + p.length, ?_, ?_⟩
  · have hl := words_length_ge m
    dsimp [n] at hm
    omega
  · intro i hi
    have hid : (words (m + 1)).getD ((words m).length + p.length + i) false =
        w.getD i false := by
      simp only [words, ← he', List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hiEq : (words m).length + p.length + i - (words m).length - p.length = i := by omega
      rw [hiEq, List.getD_append _ _ _ _ hi]
    rw [bit_eq_word, hid]
    simp only [words, List.length_append, List.length_replicate]
    omega


open scoped BigOperators

private theorem occupation_bound (u : List Bool) (b : Bool) {n : ℕ} (hn : 0 < n) :
    let w := u ++ List.replicate (n^2 * (u.length + 1)) b
    |((w.count true : ℝ) / (w.length : ℝ)) - (b.toNat : ℝ)| ≤
      1 / ((n : ℝ)^2 + 1) := by
  have hc := List.count_le_length (a := true) (l := u)
  have hcR : (u.count true : ℝ) ≤ (u.length : ℝ) := by exact Nat.cast_le.mpr hc
  have hnR : (1 : ℝ) ≤ n := by exact Nat.one_le_cast.mpr hn
  have hL : 0 ≤ (u.length : ℝ) := Nat.cast_nonneg _
  have hc0 : 0 ≤ (u.count true : ℝ) := Nat.cast_nonneg _
  have hd : 0 < (u.length : ℝ) + (n : ℝ)^2 * ((u.length : ℝ) + 1) := by nlinarith
  have he : 0 < (n : ℝ)^2 + 1 := by positivity
  have hrat (c : ℝ) (hc : c ≤ (u.length : ℝ)) :
      c / ((u.length : ℝ) + (n : ℝ)^2 * ((u.length : ℝ) + 1)) ≤
        1 / ((n : ℝ)^2 + 1) := by
    rw [div_le_div_iff₀ hd he]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (n : ℝ))]
  dsimp only
  cases b <;>
    simp [List.count_append, List.count_replicate, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  · rw [abs_of_nonneg (div_nonneg hc0 hd.le)]
    simpa only [one_div] using hrat (u.count true : ℝ) hcR
  · have hle : ((u.count true : ℝ) + (n : ℝ)^2 * ((u.length : ℝ) + 1)) /
        ((u.length : ℝ) + (n : ℝ)^2 * ((u.length : ℝ) + 1)) ≤ 1 :=
      (div_le_one hd).mpr (by linarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, one_sub_div hd.ne']
    have heq : (u.length : ℝ) + (n : ℝ)^2 * ((u.length : ℝ) + 1) -
        ((u.count true : ℝ) + (n : ℝ)^2 * ((u.length : ℝ) + 1)) =
        (u.length : ℝ) - (u.count true : ℝ) := by linarith
    rw [heq]
    simpa only [one_div] using hrat ((u.length : ℝ) - (u.count true : ℝ)) (by linarith)

private theorem endpoint_occupation_bound {n : ℕ} (hn : 0 < n) :
    |((words n).count true : ℝ) / ((words n).length : ℝ) -
      ((Nat.bodd n).toNat : ℝ)| ≤ 1 / ((n : ℝ)^2 + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact occupation_bound (words m ++ enumeration (m + 1)) (Nat.bodd (m + 1)) hn


open Filter MeasureTheory Set
open scoped Topology BigOperators

private noncomputable def intBit (k : ℤ) : Bool :=
  if 0 ≤ k then bit k.toNat else bit (-k-1).toNat

private noncomputable def stepFun (t : ℝ) : ℝ := ((intBit ⌊t⌋).toNat : ℝ)

private theorem intBit_nat (k : ℕ) : intBit k = bit k := by
  exact Bool.le_antisymm (fun a => a) fun a => a

private theorem intBit_reflect (k : ℤ) : intBit (-k-1) = intBit k := by
  unfold intBit
  split_ifs <;> congr 1 <;> omega

private theorem step_measurable : Measurable stepFun :=
  (measurable_of_countable ((fun b : Bool => (b.toNat : ℝ)) ∘ intBit)).comp Int.measurable_floor

private theorem step_bound (t : ℝ) : |stepFun t| ≤ 1 := by
  cases h : intBit ⌊t⌋ <;> simp [stepFun, h]

private theorem central_return (n K : ℕ) :
    ∃ q : ℕ, K < q ∧ ∀ k : ℤ, -(n : ℤ)-1 ≤ k → k ≤ (n : ℤ)+1 →
      intBit (k+q) = intBit k := by
  let w := List.ofFn (fun i : Fin (2*n+3) => intBit ((i : ℕ) - ((n : ℤ)+1)))
  obtain ⟨j, hj, hw⟩ := universal_word w (K+n+2)
  refine ⟨j+n+1, by omega, ?_⟩
  intro k hk1 hk2
  let i : ℕ := (k+((n : ℤ)+1)).toNat
  have hi0 : 0 ≤ k+((n : ℤ)+1) := by omega
  have hi : i < 2*n+3 := by dsimp [i]; omega
  have hik : (i : ℤ) = k+((n : ℤ)+1) := Int.toNat_of_nonneg hi0
  have hval := hw i (by simpa only [w, List.length_ofFn] using hi)
  have hget : w.getD i false = intBit k := by
    rw [List.getD_eq_getElem _ _ (by simpa only [w, List.length_ofFn] using hi)]
    simp only [w, List.getElem_ofFn]
    congr 1
    omega
  rw [hget] at hval
  have heq : k+(j+n+1 : ℕ) = ((j+i : ℕ) : ℤ) := by push_cast; omega
  rw [heq, intBit_nat, hval]

private theorem step_local_return (n q : ℕ)
    (h : ∀ k : ℤ, -(n : ℤ)-1 ≤ k → k ≤ (n : ℤ)+1 → intBit (k+q) = intBit k)
    {t : ℝ} (ht : |t| ≤ (n : ℝ)+1) : stepFun (t+q) = stepFun t := by
  unfold stepFun
  rw [Int.floor_add_natCast]
  apply congrArg (fun b : Bool => (b.toNat : ℝ))
  apply h
  · have hf := Int.lt_floor_add_one t
    have ha := (abs_le.mp ht).1
    have hn : -(n : ℝ)-1 < (⌊t⌋ : ℝ)+1 := by linarith
    have hn' : -(n : ℤ)-1 < ⌊t⌋+1 := by exact_mod_cast hn
    omega
  · have hf := Int.floor_le t
    have ha := (abs_le.mp ht).2
    have hn : (⌊t⌋ : ℝ) ≤ (n : ℝ)+1 := by exact hf.trans ha
    exact_mod_cast hn

private theorem cell_value (k : ℕ) {t : ℝ} (ht : t ∈ Ico (k : ℝ) ((k : ℝ)+1)) :
    stepFun t = ((bit k).toNat : ℝ) := by
  unfold stepFun
  rw [Int.floor_eq_iff.mpr (by exact_mod_cast ht), intBit_nat]



private theorem step_even_ae : ∀ᵐ t : ℝ, stepFun (-t) = stepFun t := by
  filter_upwards [(Set.countable_range (fun k : ℤ => (k : ℝ))).ae_notMem volume] with t ht
  unfold stepFun
  rw [Int.floor_neg, (Int.ceil_eq_floor_add_one_iff_notMem t).mpr ht]
  have he : -(⌊t⌋ + 1) = -⌊t⌋-1 := by exact neg_add' ⌊t⌋ 1
  rw [he, intBit_reflect]

private theorem sum_realBit (w : List Bool) : (w.map (fun b : Bool => (b.toNat : ℝ))).sum = (w.count true : ℝ) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    cases b <;> simp [Nat.cast_add, add_comm]

private theorem sum_getD_count (w : List Bool) :
    (∑ k ∈ Finset.range w.length, ((w.getD k false).toNat : ℝ)) =
      (w.count true : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [List.getD_eq_getElem _ _ (Fin.is_lt _)]
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map w (fun b : Bool => (b.toNat : ℝ))]
  exact sum_realBit w

private theorem step_integral_endpoint (n : ℕ) :
    (∫ t in (0:ℝ)..((words n).length : ℝ), stepFun t) = ((words n).count true : ℝ) := by
  have hi (a b : ℝ) : IntervalIntegrable stepFun volume a b := by
    apply IntegrableOn.intervalIntegrable
    exact IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
      step_measurable.aestronglyMeasurable.restrict 1
      (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using step_bound t)
  have hcell (k : ℕ) : (∫ t in (k:ℝ)..((k:ℝ)+1), stepFun t) = ((bit k).toNat : ℝ) := by
    calc
      _ = ∫ t in (k:ℝ)..((k:ℝ)+1), ((bit k).toNat : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        exact cell_value k ⟨ht.1.le, ht.2⟩
      _ = _ := by simp
  calc
    _ = ∑ k ∈ Finset.range (words n).length,
        ∫ t in (k:ℝ)..((k+1:ℕ):ℝ), stepFun t := by
      simpa only [Nat.cast_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun k : ℕ => (k : ℝ)) (fun k _ => hi _ _)).symm
    _ = ∑ k ∈ Finset.range (words n).length, ((bit k).toNat : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [Nat.cast_add, Nat.cast_one] using hcell k
    _ = ∑ k ∈ Finset.range (words n).length, (((words n).getD k false).toNat : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [bit_eq_word (Finset.mem_range.mp hk)]
    _ = _ := sum_getD_count _

private theorem zero_one_cells (q K : ℕ) (hq : 0 < q) :
    ∃ j : ℕ, K < j ∧ bit j = false ∧ bit (j+q) = true := by
  let w := List.replicate q false ++ [true]
  obtain ⟨j, hj, h⟩ := universal_word w (K+1)
  have h0 := h 0 (by simp only [w, List.length_append, List.length_replicate, List.length_singleton]; omega)
  have h1 := h q (by simp only [w, List.length_append, List.length_replicate, List.length_singleton]; omega)
  have he0 : w.getD 0 false = false := by
    dsimp [w]
    rw [List.getD_append _ _ _ _ (by simpa using hq), List.getD_replicate false hq]
  have he1 : w.getD q false = true := by
    dsimp [w]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  refine ⟨j, by omega, ?_, ?_⟩
  · simpa only [Nat.add_zero, he0] using h0
  · simpa only [he1] using h1

private theorem increasing_selection (P : ℕ → ℕ → Prop)
    (h : ∀ n K : ℕ, ∃ k : ℕ, K < k ∧ P n k) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, P n (f n) := by
  exact extraction_forall_of_frequently (fun n => frequently_atTop'.mpr (h n))


end D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation


namespace D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation
open Filter MeasureTheory Set
open scoped Topology BigOperators Convolution ContDiff

private theorem smooth_even (t : ℝ) : ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) (-t) = ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t := by
  exact convolution_neg_of_neg_eq (ContinuousLinearMap.lsmul ℝ ℝ)
    (Eventually.of_forall fun u => bump.normed_neg u) step_even_ae

private theorem smoothed_cell (k : ℕ) {t : ℝ}
    (ht : (k : ℝ) + 3/8 ≤ t ∧ t ≤ (k : ℝ) + 5/8) :
    ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t = ((bit k).toNat : ℝ) := by
  apply smooth_plateau
  intro x hx
  apply cell_value
  have hh := abs_lt.mp hx
  constructor <;> linarith

private theorem smooth_alpha : IsAlphaUnpredictable (((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun)) := by
  obtain ⟨q, hq, hret⟩ := increasing_selection
    (fun n q => 0 < q ∧ ∀ k : ℤ, -(n : ℤ)-1 ≤ k → k ≤ (n : ℤ)+1 → intBit (k+q) = intBit k)
    (fun n K => by
      obtain ⟨q, hq, hr⟩ := central_return n K
      exact ⟨q, hq, by omega, hr⟩)
  obtain ⟨j, hj, hjbit⟩ := increasing_selection
    (fun n j => bit j = false ∧ bit (j+q n) = true)
    (fun n K => zero_one_cells (q n) K (hret n).1)
  refine ⟨(fun n => (q n : ℝ)), ?_, (fun n => (j n : ℝ)+1/2), 1/2, 1/8,
    ?_, ?_, by norm_num, by norm_num, ?_⟩
  · refine ⟨smooth_uniformContinuous step_measurable step_bound,
      ⟨1, smooth_bound step_bound⟩,
      (fun n m h => by change (q n : ℝ) < (q m : ℝ); exact_mod_cast hq h),
      tendsto_natCast_atTop_atTop.comp hq.tendsto_atTop, ?_⟩
    intro a b ε hab hε
    obtain ⟨N, hN⟩ := exists_nat_gt (max |a| |b|)
    refine ⟨N, ?_⟩
    intro n hn t ht
    have hnR : (N : ℝ) ≤ n := by exact Nat.cast_le.mpr hn
    have ht' : |t| ≤ (n : ℝ) := by
      apply abs_le.mpr
      have hleft := neg_abs_le a
      have hright := le_abs_self b
      constructor <;> have hmax1 := le_max_left |a| |b| <;>
        have hmax2 := le_max_right |a| |b| <;> linarith [ht.1, ht.2]
    have hh := smooth_local_return (fun x hx => step_local_return n (q n) (hret n).2 hx) ht'
    rw [hh, sub_self, abs_zero]
    exact hε
  · intro n m h
    have hh : (j n : ℝ) < (j m : ℝ) := by exact Nat.cast_lt.mpr (hj h)
    linarith
  · exact tendsto_atTop_add_const_right atTop (1/2 : ℝ)
      (tendsto_natCast_atTop_atTop.comp hj.tendsto_atTop)
  · intro n t ht
    have h0 : ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t = 0 := by
      simpa only [(hjbit n).1, Bool.toNat_false, Nat.cast_zero] using
        smoothed_cell (j n) (t := t) (by constructor <;> linarith [ht.1, ht.2])
    have h1 : ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) (t+(q n : ℝ)) = 1 := by
      simpa only [(hjbit n).2, Bool.toNat_true, Nat.cast_one] using
        smoothed_cell (j n+q n) (t := t+(q n : ℝ))
          (by push_cast; constructor <;> linarith [ht.1, ht.2])
    rw [h0, h1]
    norm_num

end D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation


namespace D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation
open Filter MeasureTheory Set
open scoped Topology BigOperators Convolution ContDiff

private theorem endpoint_error {n : ℕ} (hn : 0 < n) :
    |(∫ t in (0:ℝ)..((words n).length : ℝ), ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) / ((words n).length : ℝ) -
      ((Nat.bodd n).toNat : ℝ)| ≤ 2 / (n : ℝ) := by
  let T : ℝ := (words n).length
  have hnR : (0 : ℝ) < n := by exact Nat.cast_pos'.mpr hn
  have hle : (n : ℝ) ≤ T := by dsimp [T]; exact_mod_cast words_length_ge n
  have hT : 0 < T := hnR.trans_le hle
  have hsm := smooth_integral_error step_measurable step_bound hT.le
  have hocc := endpoint_occupation_bound hn
  change |((words n).count true : ℝ) / T - ((Nat.bodd n).toNat : ℝ)| ≤ _ at hocc
  have heq : (∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) / T - ((Nat.bodd n).toNat : ℝ) =
      ((∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) - (∫ t in (0:ℝ)..T, stepFun t)) / T +
      (((words n).count true : ℝ) / T - ((Nat.bodd n).toNat : ℝ)) := by
    dsimp only [T]
    rw [step_integral_endpoint]
    ring
  change |(∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) / T - ((Nat.bodd n).toNat : ℝ)| ≤ _
  rw [heq]
  have hs : |((∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) - (∫ t in (0:ℝ)..T, stepFun t)) / T|
      ≤ 1 / (n : ℝ) := by
    rw [abs_div, abs_of_pos hT]
    apply (div_le_iff₀ hT).mpr
    have he : (1/2 : ℝ) ≤ 1 / (n : ℝ) * T := by
      rw [div_mul_eq_mul_div, one_mul]
      apply (le_div_iff₀ hnR).mpr
      nlinarith
    exact hsm.trans he
  have ho : 1 / ((n : ℝ)^2 + 1) ≤ 1 / (n : ℝ) := by
    apply one_div_le_one_div_of_le hnR
    have hn1 : (1 : ℝ) ≤ n := by exact Nat.one_le_cast.mpr hn
    nlinarith
  calc
    _ ≤ |((∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) - (∫ t in (0:ℝ)..T, stepFun t)) / T| +
        |((words n).count true : ℝ) / T - ((Nat.bodd n).toNat : ℝ)| := abs_add_le _ _
    _ ≤ 1/(n:ℝ) + 1/(n:ℝ) := add_le_add hs (hocc.trans ho)
    _ = 2/(n:ℝ) := by ring

private theorem no_one_sided_mean : ¬ ∃ m : ℝ, Tendsto
    (fun T : ℝ => (∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) / T) atTop (nhds m) := by
  intro ⟨m, hm⟩
  have htimes : Tendsto (fun n : ℕ => ((words n).length : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by exact_mod_cast words_length_ge n)
      tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ =>
      (∫ t in (0:ℝ)..((words n).length : ℝ), ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) / ((words n).length : ℝ) -
        ((Nat.bodd n).toNat : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero_norm'
      (a := fun n : ℕ => 2 / (n : ℝ))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      simpa only [Real.norm_eq_abs] using endpoint_error (by omega : 0 < n)
    · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ => ((Nat.bodd n).toNat : ℝ)) atTop (nhds m) := by
    have h := (hm.comp htimes).sub herr
    convert h using 1
    · funext n
      dsimp only [Function.comp_apply]
      ring
    · simp
  have he : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun n => by omega)).tendsto_atTop
  have ho : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun n => by omega)).tendsto_atTop
  have hm0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds m) := by
    simpa [Function.comp_def, Bool.toNat, Nat.bodd_mul] using hp.comp he
  have hm1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds m) := by
    simpa [Function.comp_def, Bool.toNat, Nat.bodd_mul, Nat.bodd_add] using hp.comp ho
  have hz : (0 : ℝ) = m := tendsto_nhds_unique tendsto_const_nhds hm0
  have ho' : (1 : ℝ) = m := tendsto_nhds_unique tendsto_const_nhds hm1
  linarith

private theorem symmetric_mean_eq (T : ℝ) :
    (∫ t in -T..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) / (2*T) =
      (∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) / T := by
  have hc : Continuous (((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun)) := (smooth_contDiff step_measurable step_bound).continuous
  have he : (∫ t in -T..(0:ℝ), ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) =
      (∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) t) := by
    calc
      _ = ∫ t in (0:ℝ)..T, ((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun) (-t) := by
        rw [intervalIntegral.integral_comp_neg]
        simp
      _ = _ := intervalIntegral.integral_congr (fun t _ => smooth_even t)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-T) 0) (hc.intervalIntegrable 0 T), he]
  by_cases hT : T = 0
  · simp [hT]
  · field_simp
    ring

theorem result : ¬ claim := by
  intro h
  rcases h with h | h
  · exact no_one_sided_mean (h (((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun)) smooth_alpha)
  · obtain ⟨m, hm⟩ := h (((bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] stepFun)) smooth_alpha
    apply no_one_sided_mean
    exact ⟨m, by simpa only [symmetric_mean_eq] using hm⟩

end D5.S1.Dynamics.Recurrence.AlphaUnpredictableAverageRefutation


