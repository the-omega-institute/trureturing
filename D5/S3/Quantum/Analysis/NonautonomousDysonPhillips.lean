/- GID: D5/S3/Quantum/Analysis/NonautonomousDysonPhillips
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NonautonomousDysonPhillips
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered nonautonomous Bochner iterates on complex Banach spaces. -/

import D5.S3.Quantum.Analysis.DysonPhillipsPerturbation
import Mathlib.Topology.Order.ProjIcc

open scoped Nat Topology NNReal
open MeasureTheory intervalIntegral Filter

namespace D5.S3.Quantum.Analysis.NonautonomousDysonPhillips

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A complex contraction semigroup with strong continuity on nonnegative times. -/
structure Contraction (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  operator : ℝ≥0 → E →L[ℂ] E
  zero : operator 0 = 1
  add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  norm_le : ∀ t, ‖operator t‖ ≤ 1
  continuous : ∀ x, Continuous (fun t => operator t x)

namespace Contraction

private noncomputable def realSemigroup (S : Contraction E) :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E where
  operator t := (S.operator t).restrictScalars ℝ
  operator_zero := by ext x; exact congrArg (fun A : E →L[ℂ] E => A x) S.zero
  operator_add s t := by ext x; exact congrArg (fun A : E →L[ℂ] E => A x) (S.add s t)
  opNorm_le_one t := by rw [ContinuousLinearMap.norm_restrictScalars]; exact S.norm_le t
  continuous_orbit x := S.continuous x

/-- The auxiliary real-time extension evaluates the original semigroup at `max t 0`. -/
noncomputable def action (S : Contraction E) (t : ℝ) : E →L[ℂ] E :=
  S.operator (Real.toNNReal t)

private theorem action_bound (S : Contraction E) (t : ℝ) (x : E) :
    ‖S.action t x‖ ≤ ‖x‖ :=
  S.realSemigroup.norm_apply_le (Real.toNNReal t) x

private theorem action_continuous (S : Contraction E) :
    Continuous fun p : ℝ × E => S.action p.1 p.2 :=
  S.realSemigroup.continuous_operator_apply
    (continuous_real_toNNReal.comp continuous_fst) continuous_snd

end Contraction

variable (S : Contraction E) (B : ℝ → E →L[ℂ] E)

/-- The causal integral uses absolute coefficient time and the displayed left order. -/
noncomputable def causal (r : ℝ) (v : ℝ → E) (t : ℝ) : E :=
  ∫ s in r..t, S.action (t - s) (B s (v s))

/-- Iteration starts with the supplied vector trajectory. -/
noncomputable def causalIterate (r : ℝ) (v : ℝ → E) : ℕ → ℝ → E
  | 0 => v
  | n + 1 => causal S B r (causalIterate r v n)

private noncomputable def extend {F : Type*} (f : ℝ → F) {r T : ℝ} (h : r ≤ T) : ℝ → F :=
  fun s => f (Set.projIcc r T h s)

private theorem extend_eq {F : Type*} (f : ℝ → F) {r T : ℝ} (h : r ≤ T)
    {s : ℝ} (hs : s ∈ Set.Icc r T) : extend f h s = f s := by
  simp only [extend, Set.projIcc_of_mem hs]

private theorem continuous_extend {F : Type*} [TopologicalSpace F] {f : ℝ → F}
    {r T : ℝ} (h : r ≤ T) (hf : ContinuousOn f (Set.Icc r T)) :
    Continuous (extend f h) :=
  (continuousOn_iff_continuous_restrict.mp hf).comp Set.continuous_projIcc

private theorem causal_continuous {r T : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) {v : ℝ → E}
    (hv : ContinuousOn v (Set.Icc r T)) :
    ContinuousOn (causal S B r v) (Set.Icc r T) := by
  let F : ℝ → E := causal S (extend B hrT) r (extend v hrT)
  have hF : Continuous F := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun t s => S.action (t - s) (extend B hrT s (extend v hrT s)))
      _ continuous_id
    exact S.action_continuous.comp
      ((continuous_fst.sub continuous_snd).prodMk
        (((continuous_extend hrT hB).comp continuous_snd).clm_apply
          ((continuous_extend hrT hv).comp continuous_snd)))
  apply hF.continuousOn.congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht.1] at hs
  have hsT : s ∈ Set.Icc r T := ⟨hs.1, hs.2.trans ht.2⟩
  simp only [F, causal, extend_eq _ hrT hsT]

private theorem causal_integrand_continuous {r T t : ℝ}
    (hB : ContinuousOn B (Set.Icc r T)) {v : ℝ → E}
    (hv : ContinuousOn v (Set.Icc r T)) (ht : t ∈ Set.Icc r T) :
    ContinuousOn (fun s => S.action (t - s) (B s (v s))) (Set.Icc r t) := by
  exact S.action_continuous.comp_continuousOn
    ((continuous_const.sub continuous_id).continuousOn.prodMk
      ((hB.mono (Set.Icc_subset_Icc le_rfl ht.2)).clm_apply
        (hv.mono (Set.Icc_subset_Icc le_rfl ht.2))))

private theorem iterate_continuous {r T : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) {v : ℝ → E}
    (hv : ContinuousOn v (Set.Icc r T)) (n : ℕ) :
    ContinuousOn (causalIterate S B r v n) (Set.Icc r T) := by
  induction n with
  | zero => exact hv
  | succ n ih => exact causal_continuous S B hrT hB ih

/-- The actual causal iterates satisfy the factorial majorant for every index. -/
theorem causal_iterate_bound {r T M C : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M)
    {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r T)) (hC : 0 ≤ C)
    (hvC : ∀ s ∈ Set.Icc r T, ‖v s‖ ≤ C)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc r T) :
    ‖causalIterate S B r v n t‖ ≤ C * ((M * (t - r)) ^ n / n !) := by
  induction n generalizing t with
  | zero => simpa [causalIterate] using hvC t ht
  | succ n ih =>
    change ‖∫ s in r..t, S.action (t - s) (B s (causalIterate S B r v n s))‖ ≤ _
    have hint := causal_integrand_continuous S B hB (iterate_continuous S B hrT hB hv n) ht
    calc
      _ ≤ ∫ s in r..t, ‖S.action (t - s) (B s (causalIterate S B r v n s))‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in r..t, C * (M * ((M * (s - r)) ^ n / n !)) := by
        apply intervalIntegral.integral_mono_on ht.1
          (hint.norm.intervalIntegrable_of_Icc ht.1)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        intro s hs
        have hsT : s ∈ Set.Icc r T := ⟨hs.1, hs.2.trans ht.2⟩
        calc
          _ ≤ ‖B s (causalIterate S B r v n s)‖ := S.action_bound _ _
          _ ≤ ‖B s‖ * ‖causalIterate S B r v n s‖ := (B s).le_opNorm _
          _ ≤ M * (C * ((M * (s - r)) ^ n / n !)) := by
            exact mul_le_mul (hBM s hsT) (ih hsT) (norm_nonneg _) hM
          _ = C * (M * ((M * (s - r)) ^ n / n !)) := by ring
      _ = C * ((M * (t - r)) ^ (n + 1) / (n + 1)!) := by
        simp_rw [mul_pow, mul_div_assoc]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
        rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ => s ^ n) r]
        simp only [sub_self, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
          Nat.factorial_succ]
        push_cast
        field_simp
        ring

end D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
