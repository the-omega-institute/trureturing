/- GID: D5/S3/Quantum/Analysis/StrongNonautonomousDysonPhillips
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/StrongNonautonomousDysonPhillips
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strongly continuous coefficients in the original nonautonomous Bochner series. -/

/-
The Bochner-series and compact-residual method uses the Apache-2.0 source
by Zayn Blore cited in NonautonomousDysonPhillips.lean, retaining its original
causal integrals and Dyson terms. The classical strong-coefficient evolution
core is Engel–Nagel, Section VI.9, Theorem VI.9.19 and Corollary VI.9.20.
-/
import D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! # Strongly continuous nonautonomous coefficients

The space is an arbitrary complex Banach space, including the zero space.
Only vectorwise continuity of the coefficient is assumed on the stated interval.
-/

open scoped Nat Topology NNReal
open NormedSpace MeasureTheory intervalIntegral Filter
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips

namespace D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (S : Contraction E) (B : ℝ → E →L[ℂ] E)

private theorem strong_compact_uniform_bound {r H : ℝ}
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r H)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ M := by
  have hp : ∀ x : E, ∃ C : ℝ, ∀ s : Set.Icc r H, ‖B s.1 x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB x)
    exact ⟨C, fun s => hC s.1 s.2⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun s : Set.Icc r H => B s.1) hp
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs
  exact (hC ⟨s, hs⟩).trans (le_max_left _ _)

private theorem strong_joint_evaluation {r H : ℝ}
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r H)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ s ∈ Set.Icc r H, ‖B s‖ ≤ M) ∧
      ContinuousOn (fun p : ℝ × E => B p.1 p.2)
        (Set.Icc r H ×ˢ Set.univ) := by
  obtain ⟨M, hM, hBM⟩ := strong_compact_uniform_bound B hB
  refine ⟨M, hM, hBM, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith'
    (fun p : ℝ × E => B p.1 p.2) ⟨M, hM⟩
  · intro s hs
    exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le
      (show ‖B s‖ ≤ (⟨M, hM⟩ : ℝ≥0) from hBM s hs)).lipschitzOnWith
  · intro x hx
    exact hB x

private theorem strong_causal_integrand_continuous {r T t : ℝ}
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r T))
    {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r T)) (ht : t ∈ Set.Icc r T) :
    ContinuousOn (fun s => S.action (t - s) (B s (v s))) (Set.Icc r t) := by
  obtain ⟨M, hM, hBM, hjoint⟩ := strong_joint_evaluation B hB
  exact S.action_continuous.comp_continuousOn
    ((continuous_const.sub continuous_id).continuousOn.prodMk
      (hjoint.comp'
        (continuous_id.continuousOn.prodMk (hv.mono (Set.Icc_subset_Icc le_rfl ht.2)))
        (fun s hs => ⟨⟨hs.1, hs.2.trans ht.2⟩, Set.mem_univ _⟩)))

private theorem strong_causal_continuous {r T : ℝ} (hrT : r ≤ T)
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r T)) {v : ℝ → E}
    (hv : ContinuousOn v (Set.Icc r T)) :
    ContinuousOn (causal S B r v) (Set.Icc r T) := by
  let F : ℝ → E := causal S (extend B hrT) r (extend v hrT)
  obtain ⟨M, hM, hBM⟩ := strong_compact_uniform_bound B hB
  have hBext : ∀ x : E, Continuous (fun s => extend B hrT s x) :=
    fun x => continuous_extend hrT (hB x)
  have hBMext : ∀ s : ℝ, ‖extend B hrT s‖ ≤ M := by
    intro s
    exact hBM _ (Set.projIcc r T hrT s).property
  have hjoint : Continuous (fun p : ℝ × E => extend B hrT p.1 p.2) := by
    apply continuous_prod_of_continuous_lipschitzWith'
      (fun p : ℝ × E => extend B hrT p.1 p.2) ⟨M, hM⟩
    · intro s
      exact ContinuousLinearMap.lipschitzWith_of_opNorm_le
        (show ‖extend B hrT s‖ ≤ (⟨M, hM⟩ : ℝ≥0) from hBMext s)
    · intro x
      exact hBext x
  have hF : Continuous F := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun t s => S.action (t - s) (extend B hrT s (extend v hrT s)))
      _ continuous_id
    have hpair : Continuous (fun p : ℝ × ℝ =>
        (p.2, extend v hrT p.2)) :=
      continuous_snd.prodMk ((continuous_extend hrT hv).comp continuous_snd)
    exact S.action_continuous.comp
      ((continuous_fst.sub continuous_snd).prodMk (hjoint.comp hpair))
  apply hF.continuousOn.congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht.1] at hs
  have hsT : s ∈ Set.Icc r T := ⟨hs.1, hs.2.trans ht.2⟩
  simp only [F, extend_eq _ hrT hsT, extend_eq _ hrT hsT]

private theorem strong_iterate_continuous {r T : ℝ} (hrT : r ≤ T)
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r T)) {v : ℝ → E}
    (hv : ContinuousOn v (Set.Icc r T)) (n : ℕ) :
    ContinuousOn (causalIterate S B r v n) (Set.Icc r T) := by
  induction n with
  | zero => exact hv
  | succ n ih => exact strong_causal_continuous S B hrT hB ih

/-- Factorial control of the original causal iterates for a supplied operator bound. -/
theorem fixedWstrong {r H M C : ℝ} (hrH : r ≤ H)
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r H)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ M) {v : ℝ → E}
    (hv : ContinuousOn v (Set.Icc r H)) (hvC : ∀ s ∈ Set.Icc r H, ‖v s‖ ≤ C)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc r H) :
    ‖causalIterate S B r v n t‖ ≤ C * ((M * (t - r)) ^ n / n !) := by
  induction n generalizing t with
  | zero => simpa [causalIterate] using hvC t ht
  | succ n ih =>
    change ‖∫ s in r..t, S.action (t - s) (B s (causalIterate S B r v n s))‖ ≤ _
    have hint := strong_causal_integrand_continuous S B hB
      (strong_iterate_continuous S B hrH hB hv n) ht
    calc
      _ ≤ ∫ s in r..t, ‖S.action (t - s) (B s (causalIterate S B r v n s))‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in r..t, C * (M * ((M * (s - r)) ^ n / n !)) := by
        apply intervalIntegral.integral_mono_on ht.1
          (hint.norm.intervalIntegrable_of_Icc ht.1)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        intro s hs
        have hsT : s ∈ Set.Icc r H := ⟨hs.1, hs.2.trans ht.2⟩
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

private theorem strong_term_continuous {r T : ℝ}
    (hrT : r ≤ T) (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r T))
    (n : ℕ) (x : E) :
    ContinuousOn (fun t => term S B n t r x) (Set.Icc r T) :=
  strong_iterate_continuous S B hrT hB (orbit_continuous S r x).continuousOn n

private theorem strong_term_bound {r T M : ℝ} (hrT : r ≤ T)
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc r T) (x : E) :
    ‖term S B n t r x‖ ≤ (M * (t - r)) ^ n / n ! * ‖x‖ := by
  simpa only [term, mul_comm] using
    fixedWstrong (H := T) (C := ‖x‖) S B hrT hB hM hBM
      (v := fun s => S.action (s - r) x) (orbit_continuous S r x).continuousOn
      (fun s _ => S.action_bound (s - r) x) n ht

private theorem strong_summable_norm_term {r T M : ℝ} (hrT : r ≤ T)
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc r T) (x : E) :
    Summable fun n => ‖term S B n t r x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => strong_term_bound S B hrT hB hM hBM n ht x)
    ((Real.summable_pow_div_factorial (M * (t - r))).mul_right _)

private theorem strong_term_add {r T : ℝ} (hrT : r ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r T)) (n : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc r T) (x y : E) :
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
        ((strong_causal_integrand_continuous S B hB
          (strong_term_continuous S B hrT hB n x) ht).intervalIntegrable_of_Icc ht.1)
        ((strong_causal_integrand_continuous S B hB
          (strong_term_continuous S B hrT hB n y) ht).intervalIntegrable_of_Icc ht.1)

private noncomputable def strongSumLinear {t r : ℝ}
    (h : r ≤ t ∧ ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r t)) : E →ₗ[ℂ] E where
  toFun := sum S B t r
  map_add' x y := by
    obtain ⟨M, hM, hBM⟩ := strong_compact_uniform_bound B h.2
    simp only [sum, strong_term_add S B h.1 h.2 _ ⟨h.1, le_rfl⟩]
    exact (strong_summable_norm_term S B h.1 h.2 hM hBM ⟨h.1, le_rfl⟩ x).of_norm.tsum_add
      (strong_summable_norm_term S B h.1 h.2 hM hBM ⟨h.1, le_rfl⟩ y).of_norm
  map_smul' c x := by
    simp only [sum, term_smul]
    exact tsum_const_smul'' c

private theorem strong_sum_bound {r T M : ℝ} (hrT : r ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc r T) (x : E) :
    ‖sum S B t r x‖ ≤ Real.exp (M * (t - r)) * ‖x‖ := by
  have hn := strong_summable_norm_term S B hrT hB hM hBM ht x
  calc
    _ ≤ ∑' n, ‖term S B n t r x‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, (M * (t - r)) ^ n / n ! * ‖x‖ := hn.tsum_le_tsum
      (fun n => strong_term_bound S B hrT hB hM hBM n ht x)
      ((Real.summable_pow_div_factorial _).mul_right _)
    _ = _ := by
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ,
        ← (expSeries_div_hasSum_exp (M * (t - r))).tsum_eq]

/-- The coefficient determines one operator family before any horizon or majorant. -/
noncomputable def strongEvolution (t r : ℝ) : E →L[ℂ] E := by
  classical
  exact if h : r ≤ t ∧ ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r t) then
    (strongSumLinear S B h).mkContinuous
      (Real.exp ((strong_compact_uniform_bound B h.2).choose * (t - r)))
      (strong_sum_bound S B h.1 h.2
        (strong_compact_uniform_bound B h.2).choose_spec.1
        (strong_compact_uniform_bound B h.2).choose_spec.2 ⟨h.1, le_rfl⟩)
    else 0

private theorem strongEvolution_apply {t r : ℝ}
    (h : r ≤ t ∧ ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r t)) (x : E) :
    strongEvolution S B t r x = sum S B t r x := by
  classical
  simp only [strongEvolution, dite_eq_left h, LinearMap.mkContinuous_apply, strongSumLinear,
    LinearMap.coe_mk, AddHom.coe_mk]

private theorem strong_term_global_continuous
    (hB : ∀ x : E, Continuous (fun s => B s x))
    {M : ℝ} (hBM : ∀ s : ℝ, ‖B s‖ ≤ M) (n : ℕ) (x : E) :
    Continuous fun p : ℝ × ℝ => term S B n p.1 p.2 x := by
  induction n with
  | zero =>
    exact S.action_continuous.comp
      ((continuous_fst.sub continuous_snd).prodMk continuous_const)
  | succ n ih =>
    let f : (ℝ × ℝ) → ℝ → E :=
      fun p s => S.action (p.1 - s) (B s (term S B n s p.2 x))
    have hjoint : Continuous (fun p : ℝ × E => B p.1 p.2) := by
      apply continuous_prod_of_continuous_lipschitzWith'
        (fun p : ℝ × E => B p.1 p.2) ⟨M, le_trans (norm_nonneg _) (hBM 0)⟩
      · intro s
        exact ContinuousLinearMap.lipschitzWith_of_opNorm_le
          (show ‖B s‖ ≤ (⟨M, le_trans (norm_nonneg _) (hBM 0)⟩ : ℝ≥0) from hBM s)
      · intro y
        exact hB y
    have hf : Continuous f.uncurry := S.action_continuous.comp
      ((continuous_fst.fst.sub continuous_snd).prodMk
        (hjoint.comp
          (continuous_snd.prodMk
            (ih.comp (continuous_snd.prodMk continuous_fst.snd)))))
    have hleft := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0) hf continuous_fst
    have hright := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0) hf continuous_snd
    apply (hleft.sub hright).congr
    intro p
    exact intervalIntegral.integral_interval_sub_left (μ := volume) (f := f p)
      ((hf.uncurry_left p).intervalIntegrable 0 p.1)
      ((hf.uncurry_left p).intervalIntegrable 0 p.2)

private theorem strong_term_joint_continuous {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc 0 T)) (n : ℕ) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => term S B n p.1 p.2 x) (triangle T) := by
  obtain ⟨M, hM, hBM⟩ := strong_compact_uniform_bound B hB
  let Bext : ℝ → E →L[ℂ] E := extend B hT
  have hBext : ∀ y : E, Continuous (fun s => Bext s y) :=
    fun y => continuous_extend hT (hB y)
  have hBMext : ∀ s : ℝ, ‖Bext s‖ ≤ M := by
    intro s
    exact hBM _ (Set.projIcc 0 T hT s).property
  have hg := strong_term_global_continuous S Bext hBext
    (fun s => hBMext s) n x
  apply hg.continuousOn.congr
  intro p hp
  exact term_locality S B (fun s hs =>
    (extend_eq B hT ⟨hp.1.trans hs.1, hs.2⟩).symm)
    n ⟨hp.2.1, hp.2.2⟩ x

private theorem strong_sum_joint_continuous {T M : ℝ} (hT : 0 ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => sum S B p.1 p.2 x) (triangle T) := by
  apply continuousOn_tsum (u := fun n => (M * T) ^ n / n ! * ‖x‖)
    (fun n => strong_term_joint_continuous S B hT hB n x)
    ((Real.summable_pow_div_factorial _).mul_right _) _
  intro n p hp
  apply (strong_term_bound S B (hp.2.1.trans hp.2.2)
      (fun z => (hB z).mono (Set.Icc_subset_Icc hp.1 le_rfl)) hM
      (fun s hs => hBM s ⟨hp.1.trans hs.1, hs.2⟩)
      n ⟨hp.2.1, hp.2.2⟩ x).trans
  gcongr <;> nlinarith [hp.1, hp.2.1, hp.2.2]

private theorem strong_sum_continuous {T M r : ℝ} (hT : 0 ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) (hr : 0 ≤ r) (x : E) :
    ContinuousOn (fun t => sum S B t r x) (Set.Icc r T) :=
  (strong_sum_joint_continuous S B hT hB hM hBM x).comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨hr, ht.1, ht.2⟩)

private theorem strong_sum_mild {r T M : ℝ} (hrT : r ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc r T) (x : E) :
    sum S B t r x = S.action (t - r) x +
      ∫ s in r..t, S.action (t - s) (B s (sum S B s r x)) := by
  have hsum := (strong_summable_norm_term S B hrT hB hM hBM ht x).of_norm
  rw [sum, hsum.tsum_eq_zero_add, term_zero]
  congr 1
  have hi : HasSum (fun n => ∫ s in r..t,
      S.action (t - s) (B s (term S B n s r x)))
      (∫ s in r..t, S.action (t - s) (B s (sum S B s r x))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun n _ => M * ((M * (t - r)) ^ n / n ! * ‖x‖))
    · intro n
      exact ((strong_causal_integrand_continuous S B hB
        (strong_term_continuous S B hrT hB n x) ht)
          |>.intervalIntegrable_of_Icc ht.1).aestronglyMeasurable_restrict_uIoc
    · intro n
      exact Filter.Eventually.of_forall fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        have hsT : s ∈ Set.Icc r T := ⟨hs.1.le, hs.2.trans ht.2⟩
        calc
          _ ≤ ‖B s (term S B n s r x)‖ := S.action_bound _ _
          _ ≤ ‖B s‖ * ‖term S B n s r x‖ := (B s).le_opNorm _
          _ ≤ M * ((M * (s - r)) ^ n / n ! * ‖x‖) :=
            mul_le_mul (hBM s hsT) (strong_term_bound S B hrT hB hM hBM n hsT x)
              (norm_nonneg _) hM
          _ ≤ M * ((M * (t - r)) ^ n / n ! * ‖x‖) := by
            gcongr <;> nlinarith [hs.1, hs.2]
    · exact Filter.Eventually.of_forall fun _ _ =>
        ((Real.summable_pow_div_factorial _).mul_right _).mul_left _
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        exact ((S.action (t - s)).comp (B s)).hasSum
          (strong_summable_norm_term S B hrT hB hM hBM
            ⟨hs.1.le, hs.2.trans ht.2⟩ x).of_norm.hasSum
  simpa only [term_succ] using hi.tsum_eq

private theorem strong_sum_unique {T M r : ℝ} (hT : 0 ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) (hr : r ∈ Set.Icc 0 T)
    {X : ℝ → E} (hX : ContinuousOn X (Set.Icc r T)) (x : E)
    (hXeq : ∀ t ∈ Set.Icc r T, X t = S.action (t - r) x +
      ∫ s in r..t, S.action (t - s) (B s (X s))) :
    ∀ t ∈ Set.Icc r T, X t = sum S B t r x := by
  let Y : ℝ → E := fun t => X t - sum S B t r x
  have hBr : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r T) :=
    fun z => (hB z).mono (Set.Icc_subset_Icc hr.1 le_rfl)
  have hBMr : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M :=
    fun s hs => hBM s ⟨hr.1.trans hs.1, hs.2⟩
  have hSc := strong_sum_continuous S B hT hB hM hBM hr.1 x
  have hYc : ContinuousOn Y (Set.Icc r T) := hX.sub hSc
  have hYeq : ∀ t ∈ Set.Icc r T, Y t = causal S B r Y t := by
    intro t ht
    have hiX := (strong_causal_integrand_continuous S B hBr hX ht)
      |>.intervalIntegrable_of_Icc (μ := volume) ht.1
    have hiS := (strong_causal_integrand_continuous S B hBr hSc ht)
      |>.intervalIntegrable_of_Icc (μ := volume) ht.1
    change X t - sum S B t r x = ∫ s in r..t, S.action (t - s) (B s (Y s))
    rw [hXeq t ht, strong_sum_mild S B (hr.2) hBr hM hBMr ht x]
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
    exact fixedWstrong (H := T) (C := C) S B hr.2 hBr hM hBMr (v := Y) hYc hC n ht
  have hlim : Tendsto (fun n : ℕ => C * ((M * (t - r)) ^ n / n !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (M * (t - r))).const_mul C
  have hz : Y t = 0 := norm_le_zero_iff.mp (ge_of_tendsto' hlim hb)
  exact sub_eq_zero.mp hz

private theorem strong_sum_restart {T M r s : ℝ} (hT : 0 ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun q => B q z) (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ q ∈ Set.Icc 0 T, ‖B q‖ ≤ M) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hsT : s ≤ T) (x : E) :
    ∀ t ∈ Set.Icc s T, sum S B t r x = S.action (t - s) (sum S B s r x) +
      ∫ q in s..t, S.action (t - q) (B q (sum S B q r x)) := by
  have hBr : ∀ z : E, ContinuousOn (fun q => B q z) (Set.Icc r T) :=
    fun z => (hB z).mono (Set.Icc_subset_Icc hr le_rfl)
  have hBMr : ∀ q ∈ Set.Icc r T, ‖B q‖ ≤ M :=
    fun q hq => hBM q ⟨hr.trans hq.1, hq.2⟩
  have hSc := strong_sum_continuous S B hT hB hM hBM hr x
  intro t ht
  have htr : t ∈ Set.Icc r T := ⟨hrs.trans ht.1, ht.2⟩
  have hsr : s ∈ Set.Icc r T := ⟨hrs, hsT⟩
  have hi : ∀ u ∈ Set.Icc r T, IntervalIntegrable
      (fun q => S.action (u - q) (B q (sum S B q r x))) volume r u :=
    fun u hu => (strong_causal_integrand_continuous S B hBr hSc hu).intervalIntegrable_of_Icc hu.1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hi t htr).mono_set (by
      rw [Set.uIcc_of_le hrs, Set.uIcc_of_le htr.1]
      exact Set.Icc_subset_Icc le_rfl ht.1))
    ((hi t htr).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le htr.1]
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
  rw [strong_sum_mild S B (hrs.trans hsT) hBr hM hBMr htr x, ← hsplit, hfirst,
    strong_sum_mild S B (hrs.trans hsT) hBr hM hBMr hsr x, map_add]
  rw [show t - r = (t - s) + (s - r) by ring,
    action_add S (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hrs)]
  simp only [ContinuousLinearMap.comp_apply, add_assoc]

private theorem strong_sum_cocycle {T M r s t : ℝ} (hT : 0 ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun q => B q z) (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ q ∈ Set.Icc 0 T, ‖B q‖ ≤ M) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) (x : E) :
    sum S B t r x = sum S B t s (sum S B s r x) := by
  exact strong_sum_unique (r := s) (T := T) S B hT hB hM hBM
    ⟨hr.trans hrs, hst.trans htT⟩
    ((strong_sum_continuous S B hT hB hM hBM hr x).mono
      (Set.Icc_subset_Icc hrs le_rfl))
    (sum S B s r x)
    (strong_sum_restart (r := r) (s := s) (T := T) S B hT hB hM hBM hr hrs
      (hst.trans htT) x) t ⟨hst, htT⟩

private theorem strongEvolution_locality {B' : ℝ → E →L[ℂ] E} {r t : ℝ}
    (hrt : r ≤ t) (hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r t))
    (hB' : ∀ z : E, ContinuousOn (fun s => B' s z) (Set.Icc r t))
    (hBB : Set.EqOn B B' (Set.Icc r t)) :
    strongEvolution S B t r = strongEvolution S B' t r := by
  ext x
  rw [strongEvolution_apply S B ⟨hrt, hB⟩ x,
    strongEvolution_apply S B' ⟨hrt, hB'⟩ x]
  exact tsum_congr fun n => term_locality S B hBB n ⟨hrt, le_rfl⟩ x

/-- Full strong-coefficient Dyson--Phillips telescope.  The operator family is
chosen from the coefficient alone; finite horizons and majorants occur only in
the conclusions. -/
theorem fullstrongconstruction {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc 0 T)) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) ∧
    ∀ M : ℝ, 0 ≤ M → (∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) →
    (∀ n t r, (t, r) ∈ triangle T → ∀ x : E,
      ‖term S B n t r x‖ ≤ M ^ n * (t - r) ^ n / n ! * ‖x‖) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      HasSum (fun n => term S B n t r x) (strongEvolution S B t r x)) ∧
    (∀ x : E, ContinuousOn (fun p : ℝ × ℝ => strongEvolution S B p.1 p.2 x)
      (triangle T)) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      strongEvolution S B t r x = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (strongEvolution S B s r x))) ∧
    (∀ r ∈ Set.Icc 0 T, strongEvolution S B r r = 1) ∧
    (∀ r ∈ Set.Icc 0 T, ∀ (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc r T) →
      (∀ t ∈ Set.Icc r T, X t = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (X s))) →
      ∀ t ∈ Set.Icc r T, X t = strongEvolution S B t r x) ∧
    (∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T →
      (strongEvolution S B t s).comp (strongEvolution S B s r) =
        strongEvolution S B t r) ∧
    (∀ t r, (t, r) ∈ triangle T →
      ‖strongEvolution S B t r‖ ≤ Real.exp (M * (t - r))) ∧
    (∀ n r x, term S B (n + 1) r r x = 0) ∧
    (∀ (B' : ℝ → E →L[ℂ] E) t r, (t, r) ∈ triangle T →
      Set.EqOn B B' (Set.Icc r t) → strongEvolution S B t r = strongEvolution S B' t r) ∧
    (∀ (Bzero : E →L[ℂ] E), Set.EqOn B (fun _ => Bzero) (Set.Icc 0 T) →
      ∀ t r, (t, r) ∈ triangle T → ∀ x : E,
        strongEvolution S B t r x =
          DysonPhillipsPerturbation.dysonSum S.action Bzero (t - r) x) ∧
    (Set.EqOn B (fun _ => 0) (Set.Icc 0 T) → ∀ t r, (t, r) ∈ triangle T →
      strongEvolution S B t r = S.action (t - r)) := by
  refine ⟨strong_compact_uniform_bound B hB, ?_⟩
  intro M hM hBM
  have hlocal : ∀ t r, (t, r) ∈ triangle T →
      r ≤ t ∧ ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r t) := by
    intro t r h
    exact ⟨h.2.1, fun z => (hB z).mono (Set.Icc_subset_Icc h.1 h.2.2)⟩
  have happly : ∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      strongEvolution S B t r x = sum S B t r x :=
    fun t r h x => strongEvolution_apply S B (hlocal t r h) x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n t r h x
    simpa only [mul_pow] using strong_term_bound (r := r) (T := t) S B (h.2.1)
      (hlocal t r h).2 hM
      (fun s hs => hBM s ⟨h.1.trans hs.1, hs.2.trans h.2.2⟩) n ⟨h.2.1, le_rfl⟩ x
  · intro t r h x
    rw [happly t r h x]
    exact (strong_summable_norm_term (r := r) (T := t) S B (h.2.1)
      (hlocal t r h).2 hM
      (fun s hs => hBM s ⟨h.1.trans hs.1, hs.2.trans h.2.2⟩) ⟨h.2.1, le_rfl⟩ x).of_norm.hasSum
  · intro x
    apply (strong_sum_joint_continuous S B hT hB hM hBM x).congr
    intro p hp
    exact happly p.1 p.2 hp x
  · intro t r h x
    rw [happly t r h x, strong_sum_mild (r := r) (T := t) S B (h.2.1)
      (hlocal t r h).2 hM
      (fun s hs => hBM s ⟨h.1.trans hs.1, hs.2.trans h.2.2⟩) ⟨h.2.1, le_rfl⟩ x]
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
    exact strong_sum_unique S B hT hB hM hBM hr hX x heq t ht
  · intro r s t hr hrs hst htT
    ext x
    change strongEvolution S B t s (strongEvolution S B s r x) =
      strongEvolution S B t r x
    rw [happly s r ⟨hr, hrs, hst.trans htT⟩ x,
      happly t s ⟨hr.trans hrs, hst, htT⟩,
      happly t r ⟨hr, hrs.trans hst, htT⟩ x]
    exact (strong_sum_cocycle S B hT hB hM hBM hr hrs hst htT x).symm
  · intro t r h
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    intro x
    rw [happly t r h x]
    exact strong_sum_bound (r := r) (T := t) S B (h.2.1)
      (hlocal t r h).2 hM
      (fun s hs => hBM s ⟨h.1.trans hs.1, hs.2.trans h.2.2⟩) ⟨h.2.1, le_rfl⟩ x
  · intro n r x
    simp [term_succ]
  · intro B' t r h heq
    have hB' : ∀ z : E, ContinuousOn (fun s => B' s z) (Set.Icc r t) := by
      intro z
      exact ((hlocal t r h).2 z).congr (fun s hs =>
        congrArg (fun L : E →L[ℂ] E => L z) (heq hs).symm)
    exact strongEvolution_locality S B h.2.1 (hlocal t r h).2 hB' heq
  · intro Bzero heq t r h x
    rw [happly t r h x]
    simp only [sum, DysonPhillipsPerturbation.dysonSum,
      max_eq_left (sub_nonneg.mpr h.2.1)]
    apply tsum_congr
    intro n
    have hrt : Set.Icc r t ⊆ Set.Icc 0 T := fun s hs =>
      ⟨h.1.trans hs.1, hs.2.trans h.2.2⟩
    exact (term_locality S B (heq.mono hrt)
      n ⟨h.2.1, le_rfl⟩ x).trans (term_constant S Bzero n t r x)
  · intro heq t r h
    ext x
    rw [happly t r h x]
    have hrt : Set.Icc r t ⊆ Set.Icc 0 T := fun s hs =>
      ⟨h.1.trans hs.1, hs.2.trans h.2.2⟩
    calc
      _ = sum S (fun _ => 0) t r x := tsum_congr fun n =>
        term_locality S B (heq.mono hrt)
          n ⟨h.2.1, le_rfl⟩ x
      _ = _ := sum_zero_coefficient S t r x

end D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips
