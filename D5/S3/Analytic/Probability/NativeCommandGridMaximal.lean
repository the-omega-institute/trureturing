/- GID: D5/S3/Analytic/Probability/NativeCommandGridMaximal
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/NativeCommandGridMaximal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform fourth maximal estimates on the original normal command grid. -/

import Mathlib.Algebra.Order.Chebyshev
import D5.S3.Analytic.Probability.NativeCommandPathTightness
import D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
import D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption

/-! Fourth maximal bounds retain complete words and the chronological command area. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local instance] Classical.propDecidable

namespace D5.S3.Analytic.Probability.NativeCommandGridMaximal
open NativeCommandLifetime NativeCommandPathTightness
open D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption

private def endpointStep (B : Model) (δ : ℝ) (z : Triple) (e : SignPair) : Triple :=
  if Alive B z then next B δ z e else z

private def bias (B : Model) (δ : ℝ) (z : Triple) : Triple :=
  fun i => (1/4 : ℝ) * ∑ e : SignPair, (endpointStep B δ z e i-z i)

private def augmentedStep (B : Model) (δ : ℝ) (p : Triple × Triple)
    (e : SignPair) : Triple × Triple :=
  (endpointStep B δ p.1 e, p.2 + bias B δ p.1)

private def run (B : Model) (δ : ℝ) (w : List SignPair) : Triple × Triple :=
  w.foldl (augmentedStep B δ) (0,0)

private def innovationKernel (t : ℕ) (_ : Unit)
    (_ : History (fun _ => SignPair) t) (_ : SignPair) : ℝ := 1/4

private def law (N : ℕ) : Measure (Unit × (Fin N → SignPair)) :=
  historyLaw (fun _ : Unit => 1) innovationKernel N

private theorem kernel_normalized (t : ℕ) (j : Unit)
    (h : History (fun _ => SignPair) t) :
    (∀ e, 0 ≤ innovationKernel t j h e) ∧ ∑ e, innovationKernel t j h e = 1 := by
  norm_num [innovationKernel,Fintype.sum_prod_type,Fintype.sum_bool]

private theorem likelihood_uniform (t : ℕ) (w : History (fun _ => SignPair) t) :
    likelihood innovationKernel t () w = (1/4 : ℝ)^t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [likelihood,innovationKernel,ih,pow_succ]

private theorem law_probability (N : ℕ) : IsProbabilityMeasure (law N) :=
  (history_law_conditional_expectation (fun _ : Unit => 1)
    ⟨fun _ => zero_le_one,by simp⟩ innovationKernel N
    (fun t _ => ⟨fun j h e => (kernel_normalized t j h).1 e,
      fun j h => (kernel_normalized t j h).2⟩)).1

private theorem law_integral (N : ℕ) (f : (Fin N → SignPair) → ℝ) :
    (∫ ω, f ω.2 ∂law N) = (1/4 : ℝ)^N * ∑ w, f w := by
  have h := (history_law_conditional_expectation (fun _ : Unit => 1)
    ⟨fun _ => zero_le_one,by simp⟩ innovationKernel N
    (fun t _ => ⟨fun j h e => (kernel_normalized t j h).1 e,
      fun j h => (kernel_normalized t j h).2⟩)).2.1 N le_rfl (fun _ w => f w)
  have hr (w : Fin N → SignPair) :
      readPrefix (Z := fun _ => SignPair) le_rfl w = w := by funext i; rfl
  simp_rw [hr] at h
  simpa [law,likelihood_uniform,←Finset.mul_sum] using h

private theorem fresh_conditional (N t : ℕ) (ht : t < N)
    (f : (Fin (t + 1) → SignPair) → ℝ) :
    (law N)[(fun ω : Unit × (Fin N → SignPair) =>
      f (readPrefix (Z := fun _ => SignPair) (Nat.succ_le_of_lt ht) ω.2)) |
      historySigma (J := Unit) (Z := fun _ => SignPair) t (Nat.le_of_lt ht)] =ᵐ[law N]
      fun ω => (1/4 : ℝ) * ∑ e : SignPair,
        f (Fin.snoc (readPrefix (Z := fun _ => SignPair) (Nat.le_of_lt ht) ω.2) e) := by
  have h := (history_law_conditional_expectation (fun _ : Unit => 1)
    ⟨fun _ => zero_le_one,by simp⟩ innovationKernel N
    (fun t _ => ⟨fun j h e => (kernel_normalized t j h).1 e,
      fun j h => (kernel_normalized t j h).2⟩)).2.2 t ht f
  change (law N)[(fun ω : Unit × (Fin N → SignPair) =>
    f (readPrefix (Z := fun _ => SignPair) (Nat.succ_le_of_lt ht) ω.2)) |
    historySigma (J := Unit) (Z := fun _ => SignPair) t (Nat.le_of_lt ht)]
      =ᵐ[law N] _ at h
  refine h.trans (ae_of_all (law N) (fun ω => ?_))
  have hp : (1/4 : ℝ)^t ≠ 0 := by positivity
  simp only [historyMass,Fintype.sum_unique,one_mul,likelihood,
    Fin.init_snoc,innovationKernel]
  have hl (w : Fin t → SignPair) :
      likelihood innovationKernel t (default : Unit) w = (1/4 : ℝ)^t :=
    likelihood_uniform t w
  simp only [hl,mul_div_cancel_left₀ _ hp,←Finset.mul_sum]

private theorem prefix_list {N t : ℕ} (ht : t ≤ N) (w : Fin N → SignPair) :
    List.ofFn (readPrefix (Z := fun _ => SignPair) ht w) = (List.ofFn w).take t :=
  Fin.ofFn_take_eq_take_ofFn ht w

private theorem run_snoc (B : Model) (δ : ℝ) (t : ℕ)
    (w : Fin t → SignPair) (e : SignPair) :
    run B δ (List.ofFn (Fin.snoc w e)) = augmentedStep B δ (run B δ (List.ofFn w)) e := by
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc,Fin.snoc_last,run,List.concat_eq_append]
  exact List.foldl_concat _ _ _ _

private theorem centered_step (B : Model) (δ : ℝ) (p : Triple × Triple) (i : Fin 3) :
    (1/4 : ℝ) * ∑ e : SignPair,
      ((augmentedStep B δ p e).1 i-(augmentedStep B δ p e).2 i) = p.1 i-p.2 i := by
  simp only [augmentedStep,Pi.add_apply,bias]
  simp [Fintype.sum_prod_type]
  ring

private theorem increment_mean (B : Model) (δ : ℝ) (z : Triple) (i : Fin 2) :
    (1/4 : ℝ) * ∑ e : SignPair, increment B δ z e i =
      drift B (sourceMap B z) i*δ := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,increment]
  change (1/4 : ℝ)*((drift B (sourceMap B z) i*δ+
      Real.sqrt (2*δ)*(sigma B (sourceMap B z) i 0*1+sigma B (sourceMap B z) i 1*1))+
    (drift B (sourceMap B z) i*δ+
      Real.sqrt (2*δ)*(sigma B (sourceMap B z) i 0*1+sigma B (sourceMap B z) i 1*(-1)))+
    ((drift B (sourceMap B z) i*δ+
      Real.sqrt (2*δ)*(sigma B (sourceMap B z) i 0*(-1)+sigma B (sourceMap B z) i 1*1))+
    (drift B (sourceMap B z) i*δ+
      Real.sqrt (2*δ)*(sigma B (sourceMap B z) i 0*(-1)+sigma B (sourceMap B z) i 1*(-1))))) = _
  ring

private theorem source_bounds (B : Model) :
    ∃ D J : ℝ, 0 ≤ D ∧ 0 ≤ J ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ z : Triple, ‖bias B δ z‖ ≤ D*δ) ∧
      (∀ (z : Triple) (e : SignPair),
        ‖endpointStep B δ z e-z‖ ≤ J*Real.sqrt δ) ∧
      (∀ (z : Triple), Alive B z → ∀ (e : SignPair) (θ φ : ℝ),
        θ ∈ Icc (0:ℝ) 1 → φ ∈ Icc (0:ℝ) 1 →
        ‖chord z (increment B δ z e) θ-chord z (increment B δ z e) φ‖ ≤
          J*Real.sqrt δ*|θ-φ|) := by
  obtain ⟨M,hM,hraw⟩ := raw_coefficient_bounds B
  obtain ⟨L,hL,hinc⟩ := increment_sqrt_bound B
  let H := |B.source 0|+|B.l|+|B.u|
  let D := (H+1)*M+L^2
  let J := L*(H+L+1)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨D,J,hD,hJ,?_⟩
  intro δ hδ hδ1
  have hs : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.mpr hδ1
  have hLV : L*Real.sqrt δ ≤ L := by simpa using mul_le_mul_of_nonneg_left hs hL
  have hch (z : Triple) (hz : Alive B z) (e : SignPair) (θ φ : ℝ)
      (hθ : θ ∈ Icc (0:ℝ) 1) (hφ : φ ∈ Icc (0:ℝ) 1) :
      ‖chord z (increment B δ z e) θ-chord z (increment B δ z e) φ‖ ≤
        J*Real.sqrt δ*|θ-φ| := by
    have h := chord_dist_bound z (increment B δ z e) H (L*Real.sqrt δ)
      hH (by positivity) (alive_height_abs B z hz) (hinc δ hδ hδ1 z hz e) θ φ hθ hφ
    apply h.trans
    dsimp [J]
    have hm := mul_le_mul_of_nonneg_left (show H+L*Real.sqrt δ+1 ≤ H+L+1 by linarith)
      (show 0 ≤ L*Real.sqrt δ by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hm (abs_nonneg (θ-φ))]
  refine ⟨?_,?_,hch⟩
  · intro z
    by_cases hz : Alive B z
    · have hdrift (i : Fin 2) : |drift B (sourceMap B z) i| ≤ M :=
        (hraw _ ⟨hz.1.le,hz.2.le⟩ i).1
      have hprod (e : SignPair) :
          |increment B δ z e 0*increment B δ z e 1| ≤ L^2*δ := by
        rw [abs_mul]
        have h := mul_le_mul (hinc δ hδ hδ1 z hz e 0) (hinc δ hδ hδ1 z hz e 1)
          (abs_nonneg _) (by positivity)
        calc
          _ ≤ (L*Real.sqrt δ)*(L*Real.sqrt δ) := h
          _ = L^2*δ := by nlinarith [Real.sq_sqrt hδ.le]
      have hp : |(1/4 : ℝ)*∑ e : SignPair,
          increment B δ z e 0*increment B δ z e 1| ≤ L^2*δ := by
        rw [abs_mul,show |(1/4 : ℝ)| = 1/4 by norm_num]
        calc
          _ ≤ (1/4 : ℝ)*∑ e : SignPair,
              |increment B δ z e 0*increment B δ z e 1| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
          _ ≤ (1/4 : ℝ)*∑ _e : SignPair, L^2*δ :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e _ => hprod e)) (by norm_num)
          _ = L^2*δ := by simp
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hD hδ.le)).mpr
      intro i
      rw [Real.norm_eq_abs]
      fin_cases i
      · change |bias B δ z 0| ≤ _
        have he : bias B δ z 0 = drift B (sourceMap B z) 0*δ := by
          simpa [bias,endpointStep,hz,next,chord] using increment_mean B δ z 0
        rw [he,abs_mul,abs_of_pos hδ]
        have h := mul_le_mul_of_nonneg_right (hdrift 0) hδ.le
        dsimp [D]
        nlinarith [mul_nonneg hH hM]
      · change |bias B δ z 1| ≤ _
        have he : bias B δ z 1 = drift B (sourceMap B z) 1*δ := by
          simpa [bias,endpointStep,hz,next,chord] using increment_mean B δ z 1
        rw [he,abs_mul,abs_of_pos hδ]
        have h := mul_le_mul_of_nonneg_right (hdrift 1) hδ.le
        dsimp [D]
        nlinarith [mul_nonneg hH hM]
      · change |bias B δ z 2| ≤ _
        have he : bias B δ z 2 = z 0*(drift B (sourceMap B z) 1*δ)+
            (1/2 : ℝ)*((1/4 : ℝ)*∑ e : SignPair,
              increment B δ z e 0*increment B δ z e 1) := by
          have hm := increment_mean B δ z 1
          simp only [bias,endpointStep,ite_eq_left hz,next]
          change (1/4 : ℝ)*(∑ e : SignPair,
            (z 2+1*z 0*increment B δ z e 1+((1:ℝ)^2/2)*increment B δ z e 0*
              increment B δ z e 1-z 2)) = _
          simp only [one_mul,one_pow,Fintype.sum_prod_type,Fintype.sum_bool] at hm ⊢
          nlinarith only [congrArg (fun x : ℝ => z 0*x) hm]
        rw [he]
        have hfirst : |z 0*(drift B (sourceMap B z) 1*δ)| ≤ H*(M*δ) := by
          rw [abs_mul]
          exact mul_le_mul (alive_height_abs B z hz)
            (show |drift B (sourceMap B z) 1*δ| ≤ M*δ by
              rw [abs_mul,abs_of_pos hδ]; exact mul_le_mul_of_nonneg_right (hdrift 1) hδ.le)
            (abs_nonneg _) hH
        have hh := (abs_add_le _ _).trans (add_le_add hfirst
          (show |(1/2 : ℝ)*((1/4 : ℝ)*∑ e : SignPair,
            increment B δ z e 0*increment B δ z e 1)| ≤ (1/2 : ℝ)*(L^2*δ) by
            simpa only [abs_mul,show |(1/2 : ℝ)| = 1/2 by norm_num] using
              mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 1/2)))
        dsimp [D]
        nlinarith [mul_nonneg hM hδ.le,mul_nonneg (sq_nonneg L) hδ.le]
    · have hz0 : bias B δ z = 0 := by
        ext i
        simp [bias,endpointStep,hz]
      rw [hz0,norm_zero]
      exact mul_nonneg hD hδ.le
  · intro z e
    by_cases hz : Alive B z
    · have h := hch z hz e 1 0 (by norm_num) (by norm_num)
      have hz0 : chord z (increment B δ z e) 0 = z := by
        ext i
        fin_cases i <;> simp [chord]
      rw [hz0] at h
      simpa only [endpointStep,ite_eq_left hz,next,sub_zero,abs_one,mul_one] using h
    · simpa [endpointStep,hz] using mul_nonneg hJ (Real.sqrt_nonneg δ)

private def windowTime (k m j : ℕ) : ℕ := k + min j m

private theorem windowTime_le (N k m j : ℕ) (hkm : k + m ≤ N) :
    windowTime k m j ≤ N := (Nat.add_le_add_left (min_le_right j m) k).trans hkm

private def windowFiltration (N k m : ℕ) (hkm : k + m ≤ N) :
    Filtration ℕ (inferInstance : MeasurableSpace (Unit × (Fin N → SignPair))) where
  seq j := historyFiltration (J := Unit) (Z := fun _ => SignPair) N
    ⟨windowTime k m j,Nat.lt_succ_of_le (windowTime_le N k m j hkm)⟩
  mono' := by
    intro a b hab
    apply Filtration.mono
    exact Nat.add_le_add_left (min_le_min_right m hab) k
  le' j := (historyFiltration (J := Unit) (Z := fun _ => SignPair) N).le _

private def windowRun (B : Model) (δ : ℝ) (N k m : ℕ) (_hkm : k + m ≤ N)
    (j : ℕ) (ω : Unit × (Fin N → SignPair)) : Triple × Triple :=
  run B δ ((List.ofFn ω.2).take (windowTime k m j))

private def windowNoise (B : Model) (δ : ℝ) (N k m : ℕ) (hkm : k + m ≤ N)
    (i : Fin 3) (j : ℕ) (ω : Unit × (Fin N → SignPair)) : ℝ :=
  (windowRun B δ N k m hkm j ω).1 i-(windowRun B δ N k m hkm j ω).2 i-
    ((windowRun B δ N k m hkm 0 ω).1 i-(windowRun B δ N k m hkm 0 ω).2 i)

private theorem readPrefix_init (N t : ℕ) (ht : t < N) (w : Fin N → SignPair) :
    Fin.init (readPrefix (Z := fun _ => SignPair) (Nat.succ_le_of_lt ht) w) =
      readPrefix (Z := fun _ => SignPair) (Nat.le_of_lt ht) w := by
  funext i
  rfl

private theorem window_run_step (B : Model) (δ : ℝ) (N k m : ℕ) (hkm : k + m ≤ N)
    (j : ℕ) (hj : j < m) (ω : Unit × (Fin N → SignPair)) :
    windowRun B δ N k m hkm (j+1) ω = augmentedStep B δ
      (windowRun B δ N k m hkm j ω) (ω.2 ⟨k + j,by omega⟩) := by
  have ht : k + j < N := by omega
  have he : readPrefix (Z := fun _ => SignPair) (Nat.succ_le_of_lt ht) ω.2 =
      Fin.snoc (readPrefix (Z := fun _ => SignPair) (Nat.le_of_lt ht) ω.2) (ω.2 ⟨k + j,ht⟩) := by
    rw [←readPrefix_init N (k + j) ht ω.2]
    exact (Fin.snoc_init_self _).symm
  have hh := congrArg (fun v : Fin (k + j+1) → SignPair => run B δ (List.ofFn v)) he
  rw [run_snoc] at hh
  simp only [prefix_list] at hh
  simpa only [windowRun,prefix_list,windowTime,Nat.min_eq_left hj.le,
    Nat.min_eq_left (Nat.succ_le_of_lt hj),Nat.add_assoc] using hh

private theorem window_run_hold (B : Model) (δ : ℝ) (N k m : ℕ) (hkm : k + m ≤ N)
    (j : ℕ) (hj : m ≤ j) :
    windowRun B δ N k m hkm (j+1) = windowRun B δ N k m hkm j := by
  funext ω
  simp only [windowRun,windowTime,Nat.min_eq_right hj,Nat.min_eq_right (by omega : m ≤ j+1)]

private theorem window_noise_adapted (B : Model) (δ : ℝ) (N k m : ℕ)
    (hkm : k + m ≤ N) (i : Fin 3) :
    StronglyAdapted (windowFiltration N k m hkm) (windowNoise B δ N k m hkm i) := by
  have hY (j : ℕ) : StronglyMeasurable[windowFiltration N k m hkm j]
      (fun ω => (windowRun B δ N k m hkm j ω).1 i-
        (windowRun B δ N k m hkm j ω).2 i) := by
    have hp : @Measurable (Unit × (Fin N → SignPair))
        (Fin (windowTime k m j) → SignPair) (windowFiltration N k m hkm j) inferInstance
        (fun ω => readPrefix (Z := fun _ => SignPair) (windowTime_le N k m j hkm) ω.2) :=
      comap_measurable _
    simpa only [Function.comp_def,prefix_list,windowRun] using
      ((measurable_of_finite (fun w : Fin (windowTime k m j) → SignPair =>
        (run B δ (List.ofFn w)).1 i-(run B δ (List.ofFn w)).2 i)).comp
        hp).stronglyMeasurable
  intro j
  exact (hY j).sub ((hY 0).mono ((windowFiltration N k m hkm).mono (Nat.zero_le j)))

private theorem window_noise_martingale (B : Model) (δ : ℝ) (N k m : ℕ)
    (hkm : k + m ≤ N) (i : Fin 3) :
    Martingale (windowNoise B δ N k m hkm i) (windowFiltration N k m hkm) (law N) := by
  let _ := law_probability N
  have ha := window_noise_adapted B δ N k m hkm i
  have hint (j : ℕ) : Integrable (windowNoise B δ N k m hkm i j) (law N) :=
    Integrable.of_finite
  apply martingale_nat ha hint
  intro j
  let f := windowNoise B δ N k m hkm i
  let Y (t : ℕ) (ω : Unit × (Fin N → SignPair)) :=
    (windowRun B δ N k m hkm t ω).1 i-(windowRun B δ N k m hkm t ω).2 i
  have haY (t : ℕ) : StronglyMeasurable[windowFiltration N k m hkm t] (Y t) := by
    have hp : @Measurable (Unit × (Fin N → SignPair))
        (Fin (windowTime k m t) → SignPair) (windowFiltration N k m hkm t) inferInstance
        (fun ω => readPrefix (Z := fun _ => SignPair) (windowTime_le N k m t hkm) ω.2) :=
      comap_measurable _
    simpa only [Function.comp_def,prefix_list,Y,windowRun] using
      ((measurable_of_finite (fun w : Fin (windowTime k m t) → SignPair =>
      (run B δ (List.ofFn w)).1 i-(run B δ (List.ofFn w)).2 i)).comp
        hp).stronglyMeasurable
  by_cases hj : j < m
  · have ht : k + j < N := by omega
    have hce := fresh_conditional N (k + j) ht (fun w =>
      (run B δ (List.ofFn w)).1 i-(run B δ (List.ofFn w)).2 i)
    have hmean : (law N)[Y (j+1) | windowFiltration N k m hkm j] =ᵐ[law N] Y j := by
      have hy : Y (j+1) = (fun ω : Unit × (Fin N → SignPair) =>
          (run B δ (List.ofFn (readPrefix (Z := fun _ => SignPair)
            (Nat.succ_le_of_lt ht) ω.2))).1 i-
          (run B δ (List.ofFn (readPrefix (Z := fun _ => SignPair)
            (Nat.succ_le_of_lt ht) ω.2))).2 i) := by
        funext ω
        simp only [Y,windowRun,prefix_list,windowTime,
          Nat.min_eq_left (Nat.succ_le_of_lt hj),Nat.add_succ]
      have hfil : windowFiltration N k m hkm j =
          historySigma (J := Unit) (Z := fun _ => SignPair) (k + j) (Nat.le_of_lt ht) := by
        simp only [windowFiltration,historyFiltration,windowTime,Nat.min_eq_left hj.le]
      rw [hy,hfil]
      refine hce.trans (ae_of_all (law N) (fun ω => ?_))
      simp only [run_snoc]
      simpa only [Y,windowRun,prefix_list,windowTime,Nat.min_eq_left hj.le] using
        centered_step B δ (run B δ
          (List.ofFn (readPrefix (Z := fun _ => SignPair) (Nat.le_of_lt ht) ω.2))) i
    have he : f (j+1) = Y (j+1)-Y 0 := rfl
    change f j =ᵐ[law N] (law N)[f (j+1) | windowFiltration N k m hkm j]
    rw [he]
    have h0 : StronglyMeasurable[windowFiltration N k m hkm j] (Y 0) :=
      (haY 0).mono ((windowFiltration N k m hkm).mono (Nat.zero_le j))
    have hsub := condExp_sub (show Integrable (Y (j+1)) (law N) from Integrable.of_finite)
      (show Integrable (Y 0) (law N) from Integrable.of_finite)
      (windowFiltration N k m hkm j)
    rw [condExp_of_stronglyMeasurable ((windowFiltration N k m hkm).le j) h0
      (show Integrable (Y 0) (law N) from Integrable.of_finite)] at hsub
    filter_upwards [hmean,hsub] with ω hm hs
    change Y j ω-Y 0 ω = _
    rw [hs,Pi.sub_apply,hm]
  · have he : f (j+1) = f j := by
      funext ω
      simp only [f,windowNoise,window_run_hold B δ N k m hkm j (by omega)]
    change f j =ᵐ[law N] (law N)[f (j+1) | windowFiltration N k m hkm j]
    rw [he,condExp_of_stronglyMeasurable ((windowFiltration N k m hkm).le j)
      (ha j) (hint j)]

private theorem window_noise_jumps (B : Model) (δ D J : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hD : 0 ≤ D) (hJ : 0 ≤ J)
    (hb : ∀ z : Triple, ‖bias B δ z‖ ≤ D*δ)
    (hs : ∀ (z : Triple) (e : SignPair), ‖endpointStep B δ z e-z‖ ≤ J*Real.sqrt δ)
    (N k m : ℕ) (hkm : k + m ≤ N) (i : Fin 3) (j : ℕ)
    (ω : Unit × (Fin N → SignPair)) :
    |windowNoise B δ N k m hkm i (j+1) ω-windowNoise B δ N k m hkm i j ω| ≤
      (J+D)*Real.sqrt δ := by
  by_cases hj : j < m
  · let z := (windowRun B δ N k m hkm j ω).1
    let e := ω.2 ⟨k + j,by omega⟩
    have he : windowNoise B δ N k m hkm i (j+1) ω-
        windowNoise B δ N k m hkm i j ω =
        (endpointStep B δ z e-z) i-bias B δ z i := by
      rw [windowNoise,window_run_step B δ N k m hkm j hj ω]
      simp only [windowNoise,augmentedStep,Pi.add_apply,Pi.sub_apply,z,e]
      ring
    rw [he]
    have hp : |(endpointStep B δ z e-z) i| ≤ J*Real.sqrt δ := by
      exact (norm_le_pi_norm _ i).trans (hs z e)
    have hq : |bias B δ z i| ≤ D*δ := (norm_le_pi_norm _ i).trans (hb z)
    have hδs : δ ≤ Real.sqrt δ := by
      nlinarith only [Real.sq_sqrt hδ.le,Real.sqrt_nonneg δ,hδ,hδ1]
    have h := (abs_sub _ _).trans (add_le_add hp hq)
    nlinarith only [h,mul_le_mul_of_nonneg_left hδs hD]
  · simp only [windowNoise,window_run_hold B δ N k m hkm j (by omega)]
    simpa using mul_nonneg (add_nonneg hJ hD) (Real.sqrt_nonneg δ)

private theorem window_bias_bound (B : Model) (δ D : ℝ)
    (hb : ∀ z : Triple, ‖bias B δ z‖ ≤ D*δ)
    (N k m : ℕ) (hkm : k + m ≤ N) (j : ℕ) (hj : j ≤ m)
    (ω : Unit × (Fin N → SignPair)) :
    ‖(windowRun B δ N k m hkm j ω).2-(windowRun B δ N k m hkm 0 ω).2‖ ≤
      D*(j:ℝ)*δ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjm : j < m := by omega
    have h := ih hjm.le
    calc
      _ ≤ ‖(windowRun B δ N k m hkm (j+1) ω).2-
          (windowRun B δ N k m hkm j ω).2‖+
          ‖(windowRun B δ N k m hkm j ω).2-
            (windowRun B δ N k m hkm 0 ω).2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖bias B δ (windowRun B δ N k m hkm j ω).1‖+
          ‖(windowRun B δ N k m hkm j ω).2-
            (windowRun B δ N k m hkm 0 ω).2‖ := by
        rw [window_run_step B δ N k m hkm j hjm ω]
        simp [augmentedStep]
      _ ≤ D*δ+D*(j:ℝ)*δ := add_le_add (hb _) h
      _ = _ := by push_cast; ring

private def noiseMaximum (B : Model) (δ : ℝ) (N k m : ℕ) (hkm : k + m ≤ N)
    (i : Fin 3) (ω : Unit × (Fin N → SignPair)) : ℝ :=
  (Finset.range (m+1)).sup' Finset.nonempty_range_add_one
    (fun j => |windowNoise B δ N k m hkm i j ω|)

private theorem noise_maximal_estimate (B : Model) (δ D J : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hD : 0 ≤ D) (hJ : 0 ≤ J)
    (hb : ∀ z : Triple, ‖bias B δ z‖ ≤ D*δ)
    (hs : ∀ (z : Triple) (e : SignPair), ‖endpointStep B δ z e-z‖ ≤ J*Real.sqrt δ)
    (N k m : ℕ) (hkm : k + m ≤ N) (i : Fin 3) :
    (∫ ω, noiseMaximum B δ N k m hkm i ω^4 ∂law N) ≤
      262144*(J+D)^4*((m:ℝ)*δ)^2 := by
  let _ := law_probability N
  let f := windowNoise B δ N k m hkm i
  have hf := window_noise_martingale B δ N k m hkm i
  have hf0 (ω : Unit × (Fin N → SignPair)) : f 0 ω = 0 := by simp [f,windowNoise]
  let R := ∑ a : Fin (m+1), ∑ ω : Unit × (Fin N → SignPair), |f a ω|
  have hR : 0 ≤ R := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun ω _ => abs_nonneg _))
  have hfbdd (j : ℕ) (ω : Unit × (Fin N → SignPair)) : |f j ω| ≤ R := by
    have he : f j ω = f (min j m) ω := by
      simp [f,windowNoise,windowRun,windowTime]
    rw [he]
    let a : Fin (m+1) := ⟨min j m,Nat.lt_succ_of_le (min_le_right j m)⟩
    have h1 : |f a ω| ≤ ∑ v : Unit × (Fin N → SignPair), |f a v| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun v => |f a v|)
        (fun v _ => abs_nonneg _) (Finset.mem_univ ω)
    have h2 : (∑ v : Unit × (Fin N → SignPair), |f a v|) ≤ R :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun b : Fin (m+1) => ∑ v : Unit × (Fin N → SignPair), |f b v|)
        (fun b _ => Finset.sum_nonneg (fun v _ => abs_nonneg _)) (Finset.mem_univ a)
    exact h1.trans h2
  have hmax := finite_even_maximal_integral
    hf hf0 hR hfbdd (m := 2) (by norm_num) m
  have hquad (ω : Unit × (Fin N → SignPair)) :
      (∑ a ∈ Finset.range m, (f (a+1) ω-f a ω)^2) ≤ (m:ℝ)*(J+D)^2*δ := by
    calc
      _ ≤ ∑ _a ∈ Finset.range m, ((J+D)*Real.sqrt δ)^2 :=
        Finset.sum_le_sum (fun a _ => by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
            (window_noise_jumps B δ D J hδ hδ1 hD hJ hb hs N k m hkm i a ω) 2)
      _ = _ := by simp [mul_pow,Real.sq_sqrt hδ.le,mul_assoc]
  have hq2 : (∫ ω, (∑ a ∈ Finset.range m, (f (a+1) ω-f a ω)^2)^2 ∂law N) ≤
      ((m:ℝ)*(J+D)^2*δ)^2 := by
    calc
      _ ≤ ∫ _ω : Unit × (Fin N → SignPair), ((m:ℝ)*(J+D)^2*δ)^2 ∂law N :=
        integral_mono Integrable.of_finite Integrable.of_finite (fun ω =>
          pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => sq_nonneg _)) (hquad ω) 2)
      _ = _ := by simp
  have hmax' : (∫ ω, noiseMaximum B δ N k m hkm i ω^4 ∂law N) ≤
      262144*(∫ ω, (∑ a ∈ Finset.range m, (f (a+1) ω-f a ω)^2)^2 ∂law N) := by
    norm_num [noiseMaximum,f] at hmax ⊢
    exact hmax
  exact hmax'.trans ((mul_le_mul_of_nonneg_left hq2 (by norm_num)).trans_eq (by ring))

private theorem run_first (B : Model) (δ : ℝ) (w : List SignPair)
    (p : Triple × Triple) :
    (w.foldl (augmentedStep B δ) p).1 = w.foldl (endpointStep B δ) p.1 := by
  induction w generalizing p with
  | nil => rfl
  | cons e w ih => exact ih (augmentedStep B δ p e)

private theorem endpoint_dead (B : Model) (δ : ℝ) (w : List SignPair)
    (z : Triple) (hz : ¬Alive B z) : w.foldl (endpointStep B δ) z = z := by
  induction w with
  | nil => rfl
  | cons e w ih => simpa [List.foldl,endpointStep,hz] using ih

private theorem trajectory_grid_comparison (B : Model) (δ J : ℝ)
    (hδ : 0 < δ) (hJ : 0 ≤ J)
    (hch : ∀ z : Triple, Alive B z → ∀ (e : SignPair) (θ φ : ℝ),
      θ ∈ Icc (0:ℝ) 1 → φ ∈ Icc (0:ℝ) 1 →
      ‖chord z (increment B δ z e) θ-chord z (increment B δ z e) φ‖ ≤
        J*Real.sqrt δ*|θ-φ|)
    (j : ℕ) (w : List SignPair) (z : Triple) (hz : Alive B z) (hj : j ≤ w.length) :
    ‖trajectory B δ z w ((j:ℝ)*δ)-(w.take j).foldl (endpointStep B δ) z‖ ≤
      J*Real.sqrt δ := by
  induction j generalizing w z with
  | zero =>
    simp only [Nat.cast_zero,zero_mul,List.take_zero,List.foldl_nil]
    rw [trajectory_zero B δ hδ w z hz,sub_self,norm_zero]
    positivity
  | succ j ih =>
    cases w with
    | nil => simp at hj
    | cons e w =>
      have hjw : j ≤ w.length := by simpa using hj
      by_cases hn : Alive B (next B δ z e)
      · have he : trajectory B δ z (e::w) (((j+1:ℕ):ℝ)*δ) =
            trajectory B δ (next B δ z e) w ((j:ℝ)*δ) := by
          by_cases hj0 : j = 0
          · subst j
            simp only [Nat.cast_zero,Nat.cast_one,zero_add,one_mul,zero_mul]
            rw [trajectory_zero B δ hδ w _ hn]
            simp only [trajectory,hn,ite_true,le_refl,div_self (ne_of_gt hδ),
              max_eq_left (by norm_num : (0:ℝ) ≤ 1)]
            rfl
          · have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
            have ht : ¬ (((j+1:ℕ):ℝ)*δ) ≤ δ := by push_cast; nlinarith
            simp only [trajectory,hn,ite_true,ht,ite_false]
            congr 1
            push_cast
            ring
        rw [he]
        simpa only [List.take_succ_cons,List.foldl,endpointStep,ite_eq_left hz] using
          ih w (next B δ z e) hn hjw
      · have hf := fraction_bounds B z (increment B δ z e) hz
        have hparam : min (max ((((j+1:ℕ):ℝ)*δ)/δ) 0)
            (hitFraction B z (increment B δ z e)) =
            hitFraction B z (increment B δ z e) := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hδ)]
          apply min_eq_right
          apply hf.2.trans
          apply le_trans _ (le_max_left _ _)
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
        simp only [trajectory,hn,ite_false,hparam,List.take_succ_cons,List.foldl,
          endpointStep,ite_eq_left hz]
        rw [endpoint_dead B δ _ _ hn]
        have hh := hch z hz e (hitFraction B z (increment B δ z e)) 1
          ⟨hf.1.le,hf.2⟩ (by norm_num)
        have hp : |hitFraction B z (increment B δ z e)-1| ≤ 1 := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        exact hh.trans (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ J*Real.sqrt δ))

private theorem command_grid_comparison (B : Model) (n : ℕ) (J : ℝ)
    (hδ : 0 < mesh n) (hJ : 0 ≤ J)
    (hch : ∀ z : Triple, Alive B z → ∀ (e : SignPair) (θ φ : ℝ),
      θ ∈ Icc (0:ℝ) 1 → φ ∈ Icc (0:ℝ) 1 →
      ‖chord z (increment B (mesh n) z e) θ-chord z (increment B (mesh n) z e) φ‖ ≤
        J*Real.sqrt (mesh n)*|θ-φ|)
    (j : ℕ) (hj : j ≤ n ^ 3) (w : Fin (n ^ 3) → SignPair) :
    ‖command B n w ((j:ℝ)*mesh n)-
      (run B (mesh n) ((List.ofFn w).take j)).1‖ ≤ J*Real.sqrt (mesh n) := by
  rw [run,run_first]
  exact trajectory_grid_comparison B (mesh n) J hδ hJ hch j (List.ofFn w) 0
    (by simpa [Alive,sourceMap] using B.source_height) (by simpa using hj)

/-- The nonempty grid maximum includes the zero increment at its anchor. -/
def gridFourthMaximum (B : Model) (n : ℕ) (w : Fin (n ^ 3) → SignPair) (k m : ℕ) : ℝ :=
  (Finset.range (m+1)).sup' Finset.nonempty_range_add_one
    (fun j => ‖command B n w (((k + j:ℕ):ℝ)*mesh n)-
      command B n w ((k:ℝ)*mesh n)‖^4)

/-- The complete original word law assigns the same mass to all unused suffixes. -/
def gridFourthExpectation (B : Model) (n k m : ℕ) : ℝ :=
  (1/4 : ℝ)^(n ^ 3)*∑ w : Fin (n ^ 3) → SignPair, gridFourthMaximum B n w k m

private theorem grid_maximum_bound (B : Model) (n k m : ℕ) (hkm : k + m ≤ n ^ 3)
    (D J : ℝ) (hδ : 0 < mesh n) (hD : 0 ≤ D) (hJ : 0 ≤ J)
    (hb : ∀ z : Triple, ‖bias B (mesh n) z‖ ≤ D*mesh n)
    (hch : ∀ z : Triple, Alive B z → ∀ (e : SignPair) (θ φ : ℝ),
      θ ∈ Icc (0:ℝ) 1 → φ ∈ Icc (0:ℝ) 1 →
      ‖chord z (increment B (mesh n) z e) θ-chord z (increment B (mesh n) z e) φ‖ ≤
        J*Real.sqrt (mesh n)*|θ-φ|)
    (ω : Unit × (Fin (n ^ 3) → SignPair)) :
    gridFourthMaximum B n ω.2 k m ≤
      125*((∑ i : Fin 3, noiseMaximum B (mesh n) (n ^ 3) k m hkm i ω^4)+
        (3*D*((m:ℝ)*mesh n))^4+(2*J*Real.sqrt (mesh n))^4) := by
  let S := noiseMaximum B (mesh n) (n ^ 3) k m hkm
  let T := (m:ℝ)*mesh n
  have hS (i : Fin 3) : 0 ≤ S i ω := by
    exact (abs_nonneg (windowNoise B (mesh n) (n ^ 3) k m hkm i 0 ω)).trans
      (Finset.le_sup' (fun a => |windowNoise B (mesh n) (n ^ 3) k m hkm i a ω|)
        (Finset.mem_range.mpr (Nat.zero_lt_succ m)))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS0 := hS 0
  have hS1 := hS 1
  have hS2 := hS 2
  have hsumpow : ((∑ i : Fin 3, S i ω)+3*D*T+2*J*Real.sqrt (mesh n))^4 ≤
      125*((∑ i : Fin 3, S i ω^4)+(3*D*T)^4+(2*J*Real.sqrt (mesh n))^4) := by
    have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
      (f := ![S 0 ω,S 1 ω,S 2 ω,3*D*T,2*J*Real.sqrt (mesh n)])
      (by
        intro i _
        fin_cases i
        · exact hS0
        · exact hS1
        · exact hS2
        · exact mul_nonneg (mul_nonneg (by norm_num) hD) hT
        · exact mul_nonneg (mul_nonneg (by norm_num) hJ) (Real.sqrt_nonneg _)) 3
    convert h using 1 <;> norm_num [Fin.sum_univ_succ,add_assoc]
  apply Finset.sup'_le
  intro j hj
  have hjm : j ≤ m := by simpa using Finset.mem_range.mp hj
  let P := windowRun B (mesh n) (n ^ 3) k m hkm
  have he (a : ℕ) (ha : a ≤ m) :
      ‖command B n ω.2 (((k+a:ℕ):ℝ)*mesh n)-(P a ω).1‖ ≤ J*Real.sqrt (mesh n) := by
    have hh := command_grid_comparison B n J hδ hJ hch (k+a) (by omega) ω.2
    simpa only [P,windowRun,prefix_list,windowTime,Nat.min_eq_left ha] using hh
  have hA := window_bias_bound B (mesh n) D hb (n ^ 3) k m hkm j hjm ω
  have hA' : ‖(P j ω).2-(P 0 ω).2‖ ≤ D*T := hA.trans (by
    dsimp [T]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hjm : (j:ℝ) ≤ m) hD) hδ.le)
  have hp : ‖(P j ω).1-(P 0 ω).1‖ ≤ (∑ i : Fin 3, S i ω)+3*D*T := by
    calc
      _ ≤ ∑ i : Fin 3, |((P j ω).1-(P 0 ω).1) i| := by
        apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr
        intro i
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun a : Fin 3 => |((P j ω).1-(P 0 ω).1) a|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ i : Fin 3, (S i ω+D*T) := by
        apply Finset.sum_le_sum
        intro i _
        have hf : |windowNoise B (mesh n) (n ^ 3) k m hkm i j ω| ≤ S i ω :=
          Finset.le_sup' (fun a => |windowNoise B (mesh n) (n ^ 3) k m hkm i a ω|) hj
        have ha : |((P j ω).2-(P 0 ω).2) i| ≤ D*T :=
          (norm_le_pi_norm _ i).trans hA'
        have heq : ((P j ω).1-(P 0 ω).1) i =
            windowNoise B (mesh n) (n ^ 3) k m hkm i j ω+
              ((P j ω).2-(P 0 ω).2) i := by
          simp only [windowNoise,P,Pi.sub_apply]
          ring
        rw [heq]
        exact (abs_add_le _ _).trans (add_le_add hf ha)
      _ = _ := by simp [Finset.sum_add_distrib]; ring
  have hn : ‖command B n ω.2 (((k + j:ℕ):ℝ)*mesh n)-
      command B n ω.2 ((k:ℝ)*mesh n)‖ ≤ (∑ i : Fin 3, S i ω)+3*D*T+
        2*J*Real.sqrt (mesh n) := by
    have h0 := he 0 (Nat.zero_le m)
    simp only [Nat.add_zero] at h0
    have htri := (norm_sub_le_norm_sub_add_norm_sub (command B n ω.2 (((k + j:ℕ):ℝ)*mesh n))
      (P j ω).1 (command B n ω.2 ((k:ℝ)*mesh n))).trans
      (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub (P j ω).1 (P 0 ω).1
        (command B n ω.2 ((k:ℝ)*mesh n))) _)
    rw [norm_sub_rev (P 0 ω).1] at htri
    linarith only [htri,he j hjm,h0,hp]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 4).trans hsumpow

/-- Every normal grid window of duration at most two obeys one model-dependent fourth bound. -/
theorem actual_grid_maximal_estimate (B : Model) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ k m : ℕ,
      k + m ≤ n ^ 3 → (m:ℝ)*mesh n ≤ 2 →
      gridFourthExpectation B n k m ≤ C*((m:ℝ)*mesh n)^2 := by
  obtain ⟨D,J,hD,hJ,hbounds⟩ := source_bounds B
  let C := 125*(3*262144*(J+D)^4+324*D^4+16*J^4)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro n hn k m hkm hT2
  have hnc : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hδ : 0 < mesh n := by dsimp [mesh]; positivity
  have hδ1 : mesh n ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hnc)).mpr
    nlinarith only [hn1]
  obtain ⟨hb,hs,hch⟩ := hbounds (mesh n) hδ hδ1
  by_cases hm : m = 0
  · subst m
    simp [gridFourthExpectation,gridFourthMaximum]
  let _ := law_probability (n ^ 3)
  let S := noiseMaximum B (mesh n) (n ^ 3) k m hkm
  let T := (m:ℝ)*mesh n
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hdT : mesh n ≤ T := by
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    dsimp [T]
    nlinarith only [mul_le_mul_of_nonneg_right hm1 hδ.le]
  have hTle : T ≤ 2 := hT2
  have hT4 : T^4 ≤ 4*T^2 := by
    have hs : T^2 ≤ 4 := by nlinarith only [hT,hTle]
    nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg T)]
  have hδ2 : (mesh n)^2 ≤ T^2 := pow_le_pow_left₀ hδ.le hdT 2
  have hsum : (∑ i : Fin 3, ∫ ω, S i ω^4 ∂law (n ^ 3)) ≤
      3*262144*(J+D)^4*T^2 := by
    calc
      _ ≤ ∑ _i : Fin 3, 262144*(J+D)^4*T^2 :=
        Finset.sum_le_sum (fun i _ => noise_maximal_estimate B (mesh n) D J hδ hδ1
          hD hJ hb hs (n ^ 3) k m hkm i)
      _ = _ := by simp; ring
  unfold gridFourthExpectation
  rw [←law_integral (n ^ 3) (fun w => gridFourthMaximum B n w k m)]
  have hi : (∫ ω, gridFourthMaximum B n ω.2 k m ∂law (n ^ 3)) ≤
      ∫ ω, 125*((∑ i : Fin 3, S i ω^4)+(3*D*T)^4+
        (2*J*Real.sqrt (mesh n))^4) ∂law (n ^ 3) :=
    integral_mono Integrable.of_finite Integrable.of_finite
      (fun ω => grid_maximum_bound B n k m hkm D J hδ hD hJ hb hch ω)
  have he : (∫ ω, 125*((∑ i : Fin 3, S i ω^4)+(3*D*T)^4+
      (2*J*Real.sqrt (mesh n))^4) ∂law (n ^ 3)) =
      125*((∑ i : Fin 3, ∫ ω, S i ω^4 ∂law (n ^ 3))+(3*D*T)^4+
        (2*J*Real.sqrt (mesh n))^4) := by
    rw [integral_const_mul,integral_add Integrable.of_finite Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite,
      integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    simp
  rw [he] at hi
  have hsqrt : (Real.sqrt (mesh n))^4 = (mesh n)^2 := by
    rw [show 4 = 2*2 by norm_num,pow_mul,Real.sq_sqrt hδ.le]
  have hterm : (3*D*T)^4 ≤ 324*D^4*T^2 := by
    have h := mul_le_mul_of_nonneg_left hT4 (show 0 ≤ 81*D^4 by positivity)
    nlinarith only [h]
  have herr : (2*J*Real.sqrt (mesh n))^4 ≤ 16*J^4*T^2 := by
    rw [mul_pow,mul_pow,hsqrt]
    simpa only [show (2:ℝ)^4 = 16 by norm_num] using
      mul_le_mul_of_nonneg_left hδ2 (show 0 ≤ 16*J^4 by positivity)
  dsimp [C]
  nlinarith only [hi,hsum,hterm,herr]

end D5.S3.Analytic.Probability.NativeCommandGridMaximal
