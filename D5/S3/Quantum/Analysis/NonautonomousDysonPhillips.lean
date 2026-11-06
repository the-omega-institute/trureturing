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
open NormedSpace MeasureTheory intervalIntegral Filter

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
  simpa only [term, mul_comm] using causal_iterate_bound S B hrT hB hM hBM
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
    dsimp only
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
      (μ := volume) (a₀ := 0) hf continuous_fst
    have hright := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0) hf continuous_snd
    apply (hleft.sub hright).congr
    intro p
    exact intervalIntegral.integral_interval_sub_left (μ := volume) (f := f p)
      ((hf.uncurry_left p).intervalIntegrable 0 p.1)
      ((hf.uncurry_left p).intervalIntegrable 0 p.2)

/-- The closed time triangle, with the final time as first coordinate. -/
def triangle (T : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}

private theorem term_joint_continuous {T : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (n : ℕ) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => term S B n p.1 p.2 x) (triangle T) := by
  apply (term_global_continuous S (extend B hT) (continuous_extend hT hB) n x).continuousOn.congr
  intro p hp
  exact (term_locality S B (fun s hs => (extend_eq B hT ⟨hp.1.trans hs.1, hs.2⟩).symm)
    n ⟨hp.2.1, hp.2.2⟩ x)

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
        dsimp only
        rw [ih ⟨hs.1, hs.2.trans ht.2⟩, map_add, map_add]
      _ = _ := intervalIntegral.integral_add
        ((causal_integrand_continuous S B hB (term_continuous S B hrT hB n x) ht).intervalIntegrable_of_Icc ht.1)
        ((causal_integrand_continuous S B hB (term_continuous S B hrT hB n y) ht).intervalIntegrable_of_Icc ht.1)

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

omit [CompleteSpace E] in
private theorem summable_norm_term {r T M : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc r T) (x : E) :
    Summable fun n => ‖term S B n t r x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => term_bound S B hrT hB hM hBM n ht x)
    ((Real.summable_pow_div_factorial (M * (t - r))).mul_right _)

omit [CompleteSpace E] in
private theorem coefficient_bound {r t : ℝ} (hB : ContinuousOn B (Set.Icc r t)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc r t, ‖B s‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  exact ⟨max M 0, le_max_right _ _, fun s hs => (hM s hs).trans (le_max_left _ _)⟩

omit [CompleteSpace E] in
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
  simp only [evolution, dite_eq_left h, LinearMap.mkContinuous_apply, sumLinear, LinearMap.coe_mk,
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
  gcongr <;> nlinarith [hp.1, hp.2.1, hp.2.2]

private theorem sum_mild {r T M : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc r T) (x : E) :
    sum S B t r x = S.action (t - r) x +
      ∫ s in r..t, S.action (t - s) (B s (sum S B s r x)) := by
  have hsum := (summable_norm_term S B hrT hB hM hBM ht x).of_norm
  rw [sum, hsum.tsum_eq_zero_add, term_zero]
  congr 1
  have hi : HasSum (fun n => ∫ s in r..t, S.action (t - s) (B s (term S B n s r x)))
      (∫ s in r..t, S.action (t - s) (B s (sum S B s r x))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun n _ => M * ((M * (t - r)) ^ n / n ! * ‖x‖))
    · intro n
      exact ((causal_integrand_continuous S B hB (term_continuous S B hrT hB n x) ht).intervalIntegrable_of_Icc ht.1).aestronglyMeasurable_restrict_uIoc
    · intro n
      exact Filter.Eventually.of_forall fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        have hsT : s ∈ Set.Icc r T := ⟨hs.1.le, hs.2.trans ht.2⟩
        calc
          _ ≤ ‖B s (term S B n s r x)‖ := S.action_bound _ _
          _ ≤ ‖B s‖ * ‖term S B n s r x‖ := (B s).le_opNorm _
          _ ≤ M * ((M * (s - r)) ^ n / n ! * ‖x‖) :=
            mul_le_mul (hBM s hsT) (term_bound S B hrT hB hM hBM n hsT x)
              (norm_nonneg _) hM
          _ ≤ M * ((M * (t - r)) ^ n / n ! * ‖x‖) := by
            gcongr <;> nlinarith [hs.1, hs.2]
    · exact Filter.Eventually.of_forall fun _ _ =>
        ((Real.summable_pow_div_factorial _).mul_right _).mul_left _
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        exact ((S.action (t - s)).comp (B s)).hasSum
          (summable_norm_term S B hrT hB hM hBM ⟨hs.1.le, hs.2.trans ht.2⟩ x).of_norm.hasSum
  simpa only [term_succ] using hi.tsum_eq

omit [CompleteSpace E] in
private theorem sum_diagonal (r : ℝ) (x : E) : sum S B r r x = x := by
  have h : ∀ n, term S B n r r x = if n = 0 then x else 0 := by
    intro n
    cases n with
    | zero => simp [term_zero, Contraction.action, S.zero]
    | succ n => simp [term_succ]
  simp only [sum, h]
  exact tsum_ite_eq 0 (fun _ => x)

private theorem sum_continuous {T M r : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) (hr : 0 ≤ r) (x : E) :
    ContinuousOn (fun t => sum S B t r x) (Set.Icc r T) :=
  (sum_joint_continuous S B hT hB hM hBM x).comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨hr, ht.1, ht.2⟩)

private theorem sum_unique {T M r : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) (hr : r ∈ Set.Icc 0 T)
    {X : ℝ → E} (hX : ContinuousOn X (Set.Icc r T)) (x : E)
    (hXeq : ∀ t ∈ Set.Icc r T, X t = S.action (t - r) x +
      ∫ s in r..t, S.action (t - s) (B s (X s))) :
    ∀ t ∈ Set.Icc r T, X t = sum S B t r x := by
  let Y : ℝ → E := fun t => X t - sum S B t r x
  have hBr := hB.mono (Set.Icc_subset_Icc hr.1 le_rfl)
  have hBMr : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M := fun s hs => hBM s ⟨hr.1.trans hs.1, hs.2⟩
  have hSc := sum_continuous S B hT hB hM hBM hr.1 x
  have hYc : ContinuousOn Y (Set.Icc r T) := hX.sub hSc
  have hYeq : ∀ t ∈ Set.Icc r T, Y t = causal S B r Y t := by
    intro t ht
    have hiX := (causal_integrand_continuous S B hBr hX ht).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hiS := (causal_integrand_continuous S B hBr hSc ht).intervalIntegrable_of_Icc (μ := volume) ht.1
    change X t - sum S B t r x = ∫ s in r..t, S.action (t - s) (B s (Y s))
    rw [hXeq t ht, sum_mild S B hr.2 hBr hM hBMr ht x]
    rw [show (∫ s in r..t, S.action (t - s) (B s (Y s))) =
      (∫ s in r..t, S.action (t - s) (B s (X s))) -
      (∫ s in r..t, S.action (t - s) (B s (sum S B s r x))) by
        simp only [Y, map_sub]
        exact intervalIntegral.integral_sub hiX hiS]
    abel
  have hIter : ∀ n, Set.EqOn (causalIterate S B r Y n) Y (Set.Icc r T) := by
    intro n
    induction n with
    | zero => intro t _; rfl
    | succ n ih =>
      intro t ht
      rw [hYeq t ht]
      change (∫ s in r..t, S.action (t - s) (B s (causalIterate S B r Y n s))) = _
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht.1] at hs
      dsimp only
      rw [ih ⟨hs.1, hs.2.trans ht.2⟩]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hYc
  intro t ht
  have hb : ∀ n, ‖Y t‖ ≤ C * ((M * (t - r)) ^ n / n !) := by
    intro n
    rw [← hIter n ht]
    exact causal_iterate_bound S B hr.2 hBr hM hBMr hYc hC n ht
  have hlim : Tendsto (fun n : ℕ => C * ((M * (t - r)) ^ n / n !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (M * (t - r))).const_mul C
  have hz : Y t = 0 := norm_le_zero_iff.mp (ge_of_tendsto' hlim hb)
  exact sub_eq_zero.mp hz

private theorem action_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    S.action (a + b) = (S.action a).comp (S.action b) := by
  simp only [Contraction.action, Real.toNNReal_add ha hb, S.add]

private theorem sum_restart {T M r s : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ q ∈ Set.Icc 0 T, ‖B q‖ ≤ M)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hsT : s ≤ T) (x : E) :
    ∀ t ∈ Set.Icc s T, sum S B t r x = S.action (t - s) (sum S B s r x) +
      ∫ q in s..t, S.action (t - q) (B q (sum S B q r x)) := by
  have hBr := hB.mono (Set.Icc_subset_Icc hr le_rfl)
  have hBMr : ∀ q ∈ Set.Icc r T, ‖B q‖ ≤ M := fun q hq => hBM q ⟨hr.trans hq.1, hq.2⟩
  have hSc := sum_continuous S B hT hB hM hBM hr x
  intro t ht
  have htr : t ∈ Set.Icc r T := ⟨hrs.trans ht.1, ht.2⟩
  have hsr : s ∈ Set.Icc r T := ⟨hrs, hsT⟩
  have hi : ∀ u ∈ Set.Icc r T, IntervalIntegrable
      (fun q => S.action (u - q) (B q (sum S B q r x))) volume r u :=
    fun u hu => (causal_integrand_continuous S B hBr hSc hu).intervalIntegrable_of_Icc hu.1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hi t htr).mono_set (by rw [Set.uIcc_of_le hrs, Set.uIcc_of_le htr.1];
      exact Set.Icc_subset_Icc le_rfl ht.1))
    ((hi t htr).mono_set (by rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le htr.1];
      exact Set.Icc_subset_Icc hrs le_rfl))
  have hfirst : (∫ q in r..s, S.action (t - q) (B q (sum S B q r x))) =
      S.action (t - s) (∫ q in r..s, S.action (s - q) (B q (sum S B q r x))) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hi s hsr)]
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hrs] at hq
    dsimp only
    rw [show t - q = (t - s) + (s - q) by ring,
      action_add S (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hq.2)]
    rfl
  rw [sum_mild S B (hrs.trans hsT) hBr hM hBMr htr x, ← hsplit, hfirst,
    sum_mild S B (hrs.trans hsT) hBr hM hBMr hsr x, map_add]
  rw [show t - r = (t - s) + (s - r) by ring,
    action_add S (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hrs)]
  rfl

private theorem sum_cocycle {T M r s t : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ q ∈ Set.Icc 0 T, ‖B q‖ ≤ M)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) (htT : t ≤ T) (x : E) :
    sum S B t r x = sum S B t s (sum S B s r x) := by
  exact sum_unique S B hT hB hM hBM ⟨hr.trans hrs, hst.trans htT⟩
    ((sum_continuous S B hT hB hM hBM hr x).mono (Set.Icc_subset_Icc hrs le_rfl))
    (sum S B s r x) (sum_restart S B hT hB hM hBM hr hrs (hst.trans htT) x) t ⟨hst, htT⟩

private theorem evolution_locality {B' : ℝ → E →L[ℂ] E} {r t : ℝ}
    (hrt : r ≤ t) (hB : ContinuousOn B (Set.Icc r t))
    (hBB : Set.EqOn B B' (Set.Icc r t)) :
    evolution S B t r = evolution S B' t r := by
  have hB' : ContinuousOn B' (Set.Icc r t) := hB.congr (fun s hs => (hBB hs).symm)
  ext x
  rw [evolution_apply S B ⟨hrt, hB⟩, evolution_apply S B' ⟨hrt, hB'⟩]
  exact tsum_congr fun n => term_locality S B hBB n ⟨hrt, le_rfl⟩ x

private theorem term_constant (Bzero : E →L[ℂ] E) (n : ℕ) (t r : ℝ) (x : E) :
    term S (fun _ => Bzero) n t r x =
      DysonPhillipsPerturbation.dysonTerm S.action Bzero n (t - r) x := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [term_succ]
    change (∫ s in r..t, S.action (t - s) (Bzero (term S (fun _ => Bzero) n s r x))) =
      ∫ s in 0..t-r, S.action (t-r-s)
        (Bzero (DysonPhillipsPerturbation.dysonTerm S.action Bzero n s x))
    have hshift := intervalIntegral.integral_comp_add_right
      (fun s => S.action (t - s) (Bzero (term S (fun _ => Bzero) n s r x)))
      (a := 0) (b := t-r) r
    simp only [zero_add, sub_add_cancel] at hshift
    rw [← hshift]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [ih, add_sub_cancel_right]
    congr 2
    ring

/-- The full finite-horizon evolution, with a single horizon-independent operator family. -/
theorem nonautonomous_bounded_perturbation {T M : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) :
    (∀ n t r, (t, r) ∈ triangle T → ∀ x : E,
      ‖term S B n t r x‖ ≤ M ^ n * (t - r) ^ n / n ! * ‖x‖) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      HasSum (fun n => term S B n t r x) (evolution S B t r x)) ∧
    (∀ x : E, ContinuousOn (fun p : ℝ × ℝ => evolution S B p.1 p.2 x) (triangle T)) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      evolution S B t r x = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (evolution S B s r x))) ∧
    (∀ r ∈ Set.Icc 0 T, evolution S B r r = 1) ∧
    (∀ r ∈ Set.Icc 0 T, ∀ (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc r T) →
      (∀ t ∈ Set.Icc r T, X t = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (X s))) →
      ∀ t ∈ Set.Icc r T, X t = evolution S B t r x) ∧
    (∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T →
      (evolution S B t s).comp (evolution S B s r) = evolution S B t r) ∧
    (∀ t r, (t, r) ∈ triangle T → ‖evolution S B t r‖ ≤ Real.exp (M * (t - r))) ∧
    (∀ n r x, term S B (n + 1) r r x = 0) ∧
    (∀ (B' : ℝ → E →L[ℂ] E) t r, (t, r) ∈ triangle T →
      Set.EqOn B B' (Set.Icc r t) → evolution S B t r = evolution S B' t r) ∧
    (∀ (Bzero : E →L[ℂ] E), Set.EqOn B (fun _ => Bzero) (Set.Icc 0 T) →
      ∀ t r, (t, r) ∈ triangle T → ∀ x : E, evolution S B t r x =
        DysonPhillipsPerturbation.dysonSum S.action Bzero (t - r) x) := by
  have hlocal : ∀ t r, (t, r) ∈ triangle T →
      r ≤ t ∧ ContinuousOn B (Set.Icc r t) := by
    intro t r h
    exact ⟨h.2.1, hB.mono (Set.Icc_subset_Icc h.1 h.2.2)⟩
  have happly : ∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      evolution S B t r x = sum S B t r x :=
    fun t r h x => evolution_apply S B (hlocal t r h) x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n t r h x
    simpa only [mul_pow] using term_bound S B (h.2.1.trans h.2.2)
      (hB.mono (Set.Icc_subset_Icc h.1 le_rfl)) hM
      (fun s hs => hBM s ⟨h.1.trans hs.1, hs.2⟩) n ⟨h.2.1, h.2.2⟩ x
  · intro t r h x
    rw [happly t r h x]
    exact (summable_norm_term S B (h.2.1.trans h.2.2)
      (hB.mono (Set.Icc_subset_Icc h.1 le_rfl)) hM
      (fun s hs => hBM s ⟨h.1.trans hs.1, hs.2⟩) ⟨h.2.1, h.2.2⟩ x).of_norm.hasSum
  · intro x
    apply (sum_joint_continuous S B hT hB hM hBM x).congr
    intro p hp
    exact happly p.1 p.2 hp x
  · intro t r h x
    rw [happly t r h x, sum_mild S B (h.2.1.trans h.2.2)
      (hB.mono (Set.Icc_subset_Icc h.1 le_rfl)) hM
      (fun s hs => hBM s ⟨h.1.trans hs.1, hs.2⟩) ⟨h.2.1, h.2.2⟩ x]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le h.2.1] at hs
    dsimp only
    rw [happly s r ⟨h.1, hs.1, hs.2.trans h.2.2⟩ x]
  · intro r hr
    ext x
    rw [happly r r ⟨hr.1, le_rfl, hr.2⟩ x, sum_diagonal]
    rfl
  · intro r hr X x hX heq t ht
    rw [happly t r ⟨hr.1, ht.1, ht.2⟩ x]
    exact sum_unique S B hT hB hM hBM hr hX x heq t ht
  · intro r s t hr hrs hst htT
    ext x
    change evolution S B t s (evolution S B s r x) = evolution S B t r x
    rw [happly s r ⟨hr, hrs, hst.trans htT⟩ x,
      happly t s ⟨hr.trans hrs, hst, htT⟩, happly t r ⟨hr, hrs.trans hst, htT⟩ x]
    exact (sum_cocycle S B hT hB hM hBM hr hrs hst htT x).symm
  · intro t r h
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    intro x
    rw [happly t r h x]
    exact sum_bound S B (h.2.1.trans h.2.2)
      (hB.mono (Set.Icc_subset_Icc h.1 le_rfl)) hM
      (fun s hs => hBM s ⟨h.1.trans hs.1, hs.2⟩) ⟨h.2.1, h.2.2⟩ x
  · intro n r x
    simp [term_succ]
  · intro B' t r h heq
    exact evolution_locality S B h.2.1 (hlocal t r h).2 heq
  · intro Bzero heq t r h x
    rw [happly t r h x]
    simp only [sum, DysonPhillipsPerturbation.dysonSum, max_eq_left (sub_nonneg.mpr h.2.1)]
    apply tsum_congr
    intro n
    exact (term_locality S B heq n ⟨h.2.1, h.2.2⟩ x).trans (term_constant S Bzero n t r x)

end D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
