/- GID: D5/S3/Quantum/Analysis/NonautonomousDysonPhillips
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NonautonomousDysonPhillips
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered nonautonomous Bochner iterates on complex Banach spaces. -/

import D5.S3.Quantum.Analysis.DysonPhillipsPerturbation
import Mathlib.Topology.Order.ProjIcc

/-! # Nonautonomous Dyson–Phillips integrals

All recursions use vector-valued Bochner integrals and absolute coefficient time.
-/

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
  simp only [extend, Set.projIcc_of_mem h hs]

private theorem continuous_extend {F : Type*} [TopologicalSpace F] {f : ℝ → F}
    {r T : ℝ} (h : r ≤ T) (hf : ContinuousOn f (Set.Icc r T)) :
    Continuous (extend f h) :=
  (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc

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
  simp only [extend_eq _ hrT hsT]

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
    {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r T)) 
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

/-- The ordered Dyson terms are these same causal iterates of the initial orbit. -/
noncomputable def term (n : ℕ) (t r : ℝ) (x : E) : E :=
  causalIterate S B r (fun s => S.action (s - r) x) n t

private theorem term_zero (t r : ℝ) (x : E) :
    term S B 0 t r x = S.action (t - r) x := rfl

private theorem term_succ (n : ℕ) (t r : ℝ) (x : E) :
    term S B (n + 1) t r x = ∫ s in r..t, S.action (t - s) (B s (term S B n s r x)) := rfl

private theorem orbit_continuous (r : ℝ) (x : E) :
    Continuous fun s => S.action (s - r) x :=
  S.action_continuous.comp ((continuous_id.sub continuous_const).prodMk continuous_const)

private theorem term_continuous {r T : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (n : ℕ) (x : E) :
    ContinuousOn (fun t => term S B n t r x) (Set.Icc r T) :=
  iterate_continuous S B hrT hB (orbit_continuous S r x).continuousOn n

private theorem term_bound {r T M : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc r T) (x : E) :
    ‖term S B n t r x‖ ≤ (M * (t - r)) ^ n / n ! * ‖x‖ := by
  simpa only [mul_comm] using causal_iterate_bound S B hrT hB hM hBM
    (orbit_continuous S r x).continuousOn (fun s _ => S.action_bound (s - r) x) n ht

private theorem term_locality {B' : ℝ → E →L[ℂ] E} {r T : ℝ}
    (hBB : Set.EqOn B B' (Set.Icc r T)) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc r T) (x : E) : term S B n t r x = term S B' n t r x := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [term_succ]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    have hsT : s ∈ Set.Icc r T := ⟨hs.1, hs.2.trans ht.2⟩
    rw [hBB hsT, ih hsT]

private theorem term_global_continuous (hB : Continuous B) (n : ℕ) (x : E) :
    Continuous fun p : ℝ × ℝ => term S B n p.1 p.2 x := by
  induction n with
  | zero =>
    exact S.action_continuous.comp
      ((continuous_fst.sub continuous_snd).prodMk continuous_const)
  | succ n ih =>
    let f : (ℝ × ℝ) → ℝ → E := fun p s => S.action (p.1 - s) (B s (term S B n s p.2 x))
    have hf : Continuous f.uncurry := S.action_continuous.comp
      ((continuous_fst.fst.sub continuous_snd).prodMk
        ((hB.comp continuous_snd).clm_apply
          (ih.comp (continuous_snd.prodMk continuous_fst.snd))))
    have hleft := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := 0) hf continuous_fst
    have hright := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := 0) hf continuous_snd
    apply (hleft.sub hright).congr
    intro p
    exact intervalIntegral.integral_interval_sub_left
      ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)

/-- The closed time triangle, with the final time as first coordinate. -/
def triangle (T : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}

private theorem term_joint_continuous {T : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (n : ℕ) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => term S B n p.1 p.2 x) (triangle T) := by
  apply (term_global_continuous S (extend B hT) (continuous_extend hT hB) n x).continuousOn.congr
  intro p hp
  exact (term_locality S B (fun s hs => (extend_eq B hT ⟨hp.1.trans hs.1, hs.2⟩).symm)
    n ⟨hp.2.1, hp.2.2⟩ x).symm

private theorem term_add {r T : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc r T) (x y : E) :
    term S B n t r (x + y) = term S B n t r x + term S B n t r y := by
  induction n generalizing t with
  | zero => exact map_add _ _ _
  | succ n ih =>
    simp only [term_succ]
    calc
      _ = ∫ s in r..t, (S.action (t - s) (B s (term S B n s r x)) +
          S.action (t - s) (B s (term S B n s r y))) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le ht.1] at hs
        rw [ih ⟨hs.1, hs.2.trans ht.2⟩, map_add, map_add]
      _ = _ := intervalIntegral.integral_add
        ((causal_integrand_continuous S B hB (term_continuous S B hrT hB n x) ht)
          .intervalIntegrable_of_Icc ht.1)
        ((causal_integrand_continuous S B hB (term_continuous S B hrT hB n y) ht)
          .intervalIntegrable_of_Icc ht.1)

private theorem term_smul (n : ℕ) (t r : ℝ) (c : ℂ) (x : E) :
    term S B n t r (c • x) = c • term S B n t r x := by
  induction n generalizing t with
  | zero => exact map_smul _ _ _
  | succ n ih =>
    simp only [term_succ, ih, map_smul]
    exact intervalIntegral.integral_smul c _

variable [CompleteSpace E]

/-- The vectorwise sum is defined independently of a norm bound or a horizon. -/
noncomputable def sum (t r : ℝ) (x : E) : E := ∑' n, term S B n t r x

private theorem summable_norm_term {r T M : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc r T) (x : E) :
    Summable fun n => ‖term S B n t r x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => term_bound S B hrT hB hM hBM n ht x)
    ((Real.summable_pow_div_factorial (M * (t - r))).mul_right _)

private theorem coefficient_bound {r t : ℝ} (hB : ContinuousOn B (Set.Icc r t)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc r t, ‖B s‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  exact ⟨max M 0, le_max_right _ _, fun s hs => (hM s hs).trans (le_max_left _ _)⟩

private theorem sum_bound {r T M : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc r T) (x : E) :
    ‖sum S B t r x‖ ≤ Real.exp (M * (t - r)) * ‖x‖ := by
  have hn := summable_norm_term S B hrT hB hM hBM ht x
  calc
    _ ≤ ∑' n, ‖term S B n t r x‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, (M * (t - r)) ^ n / n ! * ‖x‖ := hn.tsum_le_tsum
      (fun n => term_bound S B hrT hB hM hBM n ht x)
      ((Real.summable_pow_div_factorial _).mul_right _)
    _ = _ := by
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ, ← (expSeries_div_hasSum_exp (M * (t - r))).tsum_eq]

private noncomputable def sumLinear {t r : ℝ}
    (h : r ≤ t ∧ ContinuousOn B (Set.Icc r t)) : E →ₗ[ℂ] E where
  toFun := sum S B t r
  map_add' x y := by
    obtain ⟨M, hM, hBM⟩ := coefficient_bound B h.2
    simp only [sum, term_add S B h.1 h.2 _ ⟨h.1, le_rfl⟩]
    exact (summable_norm_term S B h.1 h.2 hM hBM ⟨h.1, le_rfl⟩ x).of_norm.tsum_add
      (summable_norm_term S B h.1 h.2 hM hBM ⟨h.1, le_rfl⟩ y).of_norm
  map_smul' c x := by
    simp only [sum, term_smul]
    exact tsum_const_smul'' c

/-- A single bounded complex-linear map, independent of the chosen majorant and horizon. -/
noncomputable def evolution (t r : ℝ) : E →L[ℂ] E := by
  classical
  exact if h : r ≤ t ∧ ContinuousOn B (Set.Icc r t) then
    (sumLinear S B h).mkContinuous
      (Real.exp ((coefficient_bound B h.2).choose * (t - r)))
      (sum_bound S B h.1 h.2 (coefficient_bound B h.2).choose_spec.1
        (coefficient_bound B h.2).choose_spec.2 ⟨h.1, le_rfl⟩)
    else 0

private theorem evolution_apply {t r : ℝ}
    (h : r ≤ t ∧ ContinuousOn B (Set.Icc r t)) (x : E) :
    evolution S B t r x = sum S B t r x := by
  classical
  simp only [evolution, dif_pos h, LinearMap.mkContinuous_apply, sumLinear, LinearMap.coe_mk,
    AddHom.coe_mk]

private theorem sum_joint_continuous {T M : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => sum S B p.1 p.2 x) (triangle T) := by
  apply continuousOn_tsum (u := fun n => (M * T) ^ n / n ! * ‖x‖)
    (fun n => term_joint_continuous S B hT hB n x)
    ((Real.summable_pow_div_factorial _).mul_right _) _
  intro n p hp
  have hBr := hB.mono (Set.Icc_subset_Icc hp.1 le_rfl)
  have hBMr : ∀ s ∈ Set.Icc p.2 T, ‖B s‖ ≤ M := fun s hs => hBM s ⟨hp.1.trans hs.1, hs.2⟩
  apply (term_bound S B (hp.2.1.trans hp.2.2) hBr hM hBMr n ⟨hp.2.1, hp.2.2⟩ x).trans
  gcongr
  linarith [hp.1, hp.2.2]

end D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
