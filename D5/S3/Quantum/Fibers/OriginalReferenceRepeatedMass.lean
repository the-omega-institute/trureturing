/- GID: D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalReferenceRepeatedMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native mode mass balance and repeated reference-output completeness. -/

import D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure

/-! Native mode balance retains arbitrary positive joint reference inputs. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators Matrix
open Set Filter Topology MeasureTheory intervalIntegral TraceClassFiniteBlocks
namespace D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass
open OriginalControlMarkedJump OriginalReferenceKraus OriginalReferenceOutputMeasure
open OriginalRepeatedPrefix OriginalControlComposition OriginalMarkedConcatenation

private theorem native_bounds (c T : ℝ) (k : ℝ → ℝ)
    (hk : OriginalControl (c, c, 1 - 2*c) T k (fun _ => (0 : ℝ)))
    (t : ℝ) (ht : t ∈ uIcc 0 T) : k t ∈ Ioo 0 c := by
  have hl : FiniteRectangleTransport.lower (c, c, 1 - 2*c)=0 := by
    dsimp [FiniteRectangleTransport.lower]; ring_nf; simp
  simpa [hl,FiniteRectangleTransport.upper] using hk.2.2.2.1 t ht

private theorem survival_ac (c T : ℝ) (k : ℝ → ℝ)
    (hk : OriginalControl (c, c, 1 - 2*c) T k (fun _ => (0 : ℝ))) :
    AbsolutelyContinuousOnInterval (survival c k) 0 T := by
  let A : ℝ → ℝ := fun t => -(∫ u in (0 : ℝ)..t, hazard c k u)
  have ha : AbsolutelyContinuousOnInterval A 0 T :=
    ((hazard_integrable c T 0 k hk).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)).neg
  obtain ⟨C,hC⟩ := ha.exists_bound
  obtain ⟨K,hK⟩ := (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ 1 Real.exp (Icc (-C) C)).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc
  have hm : MapsTo A (uIcc 0 T) (Icc (-C) C) := by
    intro t ht
    have hb := hC t ht
    simpa only [Real.norm_eq_abs,abs_le,mem_Icc] using hb
  exact hK.comp_absolutelyContinuousOnInterval hm ha

private theorem probability_ac (c T : ℝ) (k : ℝ → ℝ)
    (hk : AbsolutelyContinuousOnInterval k 0 T) (i : Fin 5) :
    AbsolutelyContinuousOnInterval (fun t => p c (k t) i) 0 T := by
  have hc (x : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => x) 0 T :=
    (LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval
  simp only [p_explicit]
  fin_cases i
  · simpa using hk
  · exact (hc c).sub hk
  · exact hc _
  · exact (hc c).sub hk
  · simpa using hk

private theorem probability_deriv (c : ℝ) (k : ℝ → ℝ) (t : ℝ)
    (hd : DifferentiableAt ℝ k t) (i : Fin 5) :
    HasDerivAt (fun u => p c (k u) i)
      (![1,-1,0,-1,1] i * deriv k t) t := by
  simp only [p_explicit]
  fin_cases i
  · simpa using hd.hasDerivAt
  · simpa using hd.hasDerivAt.const_sub c
  · simpa using hasDerivAt_const t (1 - 2*c)
  · simpa using hd.hasDerivAt.const_sub c
  · simpa using hd.hasDerivAt

private theorem rate_nonneg (c : ℝ) (k : ℝ → ℝ) (t : ℝ)
    (hc : c < 1 / 2) (hb : k t ∈ Ioo 0 c) (hd : DifferentiableAt ℝ k t)
    (i : Fin 5) : 0 ≤ jumpRate c k t i := by
  have hp := probability_deriv c k t hd i
  rw [jumpRate,(hp.log (p_pos c (k t) hc hb i).ne').deriv]
  have h0 : 0 ≤ max (deriv k t) 0 := le_max_right _ _
  have h1 : 0 ≤ max (-deriv k t) 0 := le_max_right _ _
  have h2 : deriv k t ≤ max (deriv k t) 0 := le_max_left _ _
  have h3 : -deriv k t ≤ max (-deriv k t) 0 := le_max_left _ _
  have hc0 : 0 < c-k t := sub_pos.mpr hb.2
  have hu : deriv k t / k t ≤ hazard c k t :=
    (div_le_div_of_nonneg_right h2 hb.1.le).trans
      (le_add_of_nonneg_right (div_nonneg h1 hc0.le))
  have hv : -deriv k t / (c-k t) ≤ hazard c k t :=
    (div_le_div_of_nonneg_right h3 hc0.le).trans
      (le_add_of_nonneg_left (div_nonneg h0 hb.1.le))
  have hz : 0 ≤ hazard c k t := add_nonneg (div_nonneg h0 hb.1.le)
    (div_nonneg h1 hc0.le)
  simp only [p_explicit]
  fin_cases i <;> simp_all

private theorem native_coefficient_deriv (c a T : ℝ) (k : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2*c) T k (fun _ => (0 : ℝ))) (i : Fin 5) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
      modeCoefficient c a k i t =
        -deriv (fun u => survival c k u * p c (k u) i) t / p c a i := by
  have hi := hazard_integrable c T 0 k hk
  filter_upwards [(original_ac _ _ _ _ hk).1.ae_differentiableAt,
    hi.ae_hasDerivAt_integral] with t hkt hIt ht
  have hb := native_bounds c T k hk t ht
  have hd := hkt ht
  have hp := probability_deriv c k t hd i
  have hS : HasDerivAt (survival c k)
      (survival c k t * (-hazard c k t)) t :=
    (hIt ht 0 (by simp)).neg.exp
  have hprod := hS.mul hp
  change HasDerivAt (fun u => survival c k u * p c (k u) i) _ t at hprod
  have hg := rate_nonneg c k t hc hb hd i
  have hSn : 0 ≤ survival c k t := (Real.exp_pos _).le
  have hp0 := p_pos c a hc ha i
  have hpt := p_pos c (k t) hc hb i
  rw [modeCoefficient,amplitude,Complex.normSq_mul,Complex.normSq_mul,
    Complex.normSq_ofReal,Complex.normSq_ofReal,Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt hg,Real.mul_self_sqrt hSn,
    Real.mul_self_sqrt (div_nonneg hpt.le hp0.le),hprod.deriv]
  rw [jumpRate,(hp.log hpt.ne').deriv]
  field_simp [hpt.ne',hp0.ne']
  <;> ring

/-- Every native mode loses exactly the decrease in its surviving diagonal
weight, on every subinterval of an original absolutely continuous control. -/
theorem native_mode_balance (c a T : ℝ) (k : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2*c) T k (fun _ => (0 : ℝ)))
    (i : Fin 5) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    IntegrableOn (modeCoefficient c a k i) (Ioc s t) ∧
    (∫ u in Ioc s t, modeCoefficient c a k i u) =
      (survival c k s * p c (k s) i - survival c k t * p c (k t) i) / p c a i := by
  let v : ℝ → ℝ := fun u => survival c k u * p c (k u) i
  have hv : AbsolutelyContinuousOnInterval v 0 T :=
    (survival_ac c T k hk).mul (probability_ac c T k (original_ac _ _ _ _ hk).1 i)
  have hsub : uIcc s t ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hst,uIcc_of_le hk.1]
    exact Icc_subset_Icc hs.1 ht.2
  have hvst := hv.mono hsub
  have he : ∀ᵐ u : ℝ, u ∈ uIoc s t →
      modeCoefficient c a k i u = -deriv v u / p c a i := by
    filter_upwards [native_coefficient_deriv c a T k hc ha hk i] with u hu hum
    exact hu (hsub (uIoc_subset_uIcc hum))
  have hi : IntervalIntegrable (modeCoefficient c a k i) volume s t :=
    (hvst.intervalIntegrable_deriv.neg.div_const _).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (he.mono (fun u hu hum => (hu hum).symm)))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mp hi,?_⟩
  rw [← intervalIntegral.integral_of_le hst, intervalIntegral.integral_congr_ae he,
    intervalIntegral.integral_div,intervalIntegral.integral_neg,hvst.integral_deriv_eq_sub]
  dsimp [v]
  ring


private theorem repeated_endpoints (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool) :
    let k := if e then B.early n hn else B.late n hn
    OriginalControl (B.c,B.c,1-2*B.c) 2 k (fun _ => (0 : ℝ)) ∧
    k 0 = B.a ∧ k 1 = B.a ∧ k 2 = B.a ∧
    survival B.c k 0 = 1 ∧ survival B.c k 1 = B.q^n ∧
    survival B.c k 2 = B.q^(n+1) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have htime : 2*(n:ℝ)*Band.halfStep n=1 := by
    dsimp [Band.halfStep]; field_simp
  obtain ⟨hp,hp0,hp1,hps⟩ := B.prefix_facts (Band.halfStep n) 0 (Band.halfStep_pos n hn) n
  rw [htime] at hp1 hps
  have h := early_late_native_survival B n hn 0
  have hk : OriginalControl (B.c,B.c,1-2*B.c) 2
      (if e then B.early n hn else B.late n hn) (fun _ => (0 : ℝ)) := by
    cases e
    · exact h.2.2.2.1
    · exact h.2.2.1
  have h0 : (if e then B.early n hn else B.late n hn) 0 = B.a := by
    cases e <;> simpa [Band.early,Band.late,concatenate] using hp0
  have h1 : (if e then B.early n hn else B.late n hn) 1 = B.a := by
    cases e <;> simpa [Band.early,Band.late,concatenate] using hp1
  have hs1 : survival B.c (if e then B.early n hn else B.late n hn) 1 = B.q^n := by
    cases e <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [Band.late,survival_before B.c 1 1 _ _ zero_le_one le_rfl,hps]
    · rw [Band.early,survival_before B.c 1 1 _ _ zero_le_one le_rfl,hps]
  refine ⟨hk,h0,h1,?_,by simp [OriginalControlSurvivalInstability.survival],hs1,?_⟩
  · cases e
    · exact h.2.2.2.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.2.1
  · cases e
    · exact h.2.2.2.2.2.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.2.2.2.1

private theorem suffix_coefficient_scaling (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (e : Bool) (i : Fin 5) (t : ℝ) (ht : t ∈ Ioc (1 : ℝ) 2) :
    let k := if e then B.early n hn else B.late n hn
    let K := if e then B.earlySuffix else B.lateSuffix
    modeCoefficient B.c B.a k i t = B.q^n * modeCoefficient B.c B.a K i (t-1) := by
  have h := ((OriginalRepeatedMarkedLaw.early_late_marked_probability B n hn
    0 0 (fun _ => 0) e).2.2.1 t ht (fun _ => 1)).2 i
  have hp := p_pos B.c B.a B.c_lt ⟨B.a_pos,B.ab.trans B.bc⟩ i
  have he := congrArg (fun z => Complex.normSq (z 0)) h
  simp only [jump_action,successful_action,jump,live,div_self hp.ne',Real.sqrt_one,
    Complex.ofReal_one,mul_one,Complex.normSq_mul,Complex.normSq_ofReal,
    Real.mul_self_sqrt (pow_nonneg (early_late_native_survival B n hn 0).1.le n)] at he
  dsimp only
  simp only [modeCoefficient,amplitude,Complex.normSq_mul,Complex.normSq_ofReal]
  nlinarith only [he]

private theorem repeated_coefficient_masses (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (e : Bool) (i : Fin 5) :
    let k := if e then B.early n hn else B.late n hn
    (∫ t in Ioc (0 : ℝ) 1, modeCoefficient B.c B.a k i t) = 1-B.q^n ∧
    (∫ t in Ioc (1 : ℝ) 2, modeCoefficient B.c B.a k i t) = B.q^n*(1-B.q) ∧
    (∫ t in Ioc (0 : ℝ) 2, modeCoefficient B.c B.a k i t) = 1-B.q^(n+1) := by
  obtain ⟨hk,h0,h1,h2,hS0,hS1,hS2⟩ := repeated_endpoints B n hn e
  have hb := native_mode_balance B.c B.a 2 _ B.c_lt ⟨B.a_pos,B.ab.trans B.bc⟩ hk i
  have hp := p_pos B.c B.a B.c_lt ⟨B.a_pos,B.ab.trans B.bc⟩ i
  have h01 := (hb 0 1 (by norm_num) (by norm_num) (by norm_num)).2
  have h12 := (hb 1 2 (by norm_num) (by norm_num) (by norm_num)).2
  have h02 := (hb 0 2 (by norm_num) (by norm_num) (by norm_num)).2
  rw [h0,h1,hS0,hS1] at h01
  rw [h1,h2,hS1,hS2] at h12
  rw [h0,h2,hS0,hS2] at h02
  refine ⟨?_,?_,?_⟩
  · rw [h01]; field_simp [hp.ne']
  · rw [h12,pow_succ]; field_simp [hp.ne']
  · rw [h02]; field_simp [hp.ne']

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Modewise prefix and suffix outputs retain the same arbitrary positive joint
input. Their total trace norms obey exact suffix scaling and mass completeness. -/
theorem repeated_reference_completeness (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    let k := if e then B.early n hn else B.late n hn
    (∀ i : Fin 5,
      (∀ t ∈ Ioc (1 : ℝ) 2,
        modeOutput B.c B.a k i rho hpos t =
          ((B.q^n : ℝ) : ℂ) • modeOutput B.c B.a
            (if e then B.earlySuffix else B.lateSuffix) i rho hpos (t-1)) ∧
      (∫ t in Ioc (0 : ℝ) 1, modeCoefficient B.c B.a k i t) = 1-B.q^n ∧
      (∫ t in Ioc (1 : ℝ) 2, modeCoefficient B.c B.a k i t) = B.q^n*(1-B.q) ∧
      (∫ t in Ioc (0 : ℝ) 2, modeCoefficient B.c B.a k i t) = 1-B.q^(n+1) ∧
      (∫ t in Ioc (1 : ℝ) 2, modeOutput B.c B.a k i rho hpos t) =
        ((B.q^n*(1-B.q) : ℝ) : ℂ) •
          TraceClass.ofOperator (compression rho.1 i)
            (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)) ∧
    (∑ i : Fin 5, ‖∫ t in Ioc (1 : ℝ) 2, modeOutput B.c B.a k i rho hpos t‖) =
      B.q^n*(1-B.q)*‖rho‖ ∧
    (∑ i : Fin 5, ‖∫ t in Ioc (0 : ℝ) 2, modeOutput B.c B.a k i rho hpos t‖) +
      ‖((B.q^(n+1) : ℝ) : ℂ) • rho‖ = ‖rho‖ := by
  dsimp only
  let k := if e then B.early n hn else B.late n hn
  let A (i : Fin 5) : TraceClass H := TraceClass.ofOperator (compression rho.1 i)
    (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
  have hq := early_late_native_survival B n hn 0
  have hnq : 0 ≤ B.q^n*(1-B.q) := mul_nonneg (pow_nonneg hq.1.le n) (by linarith [hq.2.1])
  have hqn : B.q^(n+1) ≤ 1 := pow_le_one₀ hq.1.le hq.2.1.le
  have hint (i : Fin 5) (D : Set ℝ) :
      (∫ t in D, modeOutput B.c B.a k i rho hpos t) =
      ((∫ t in D, modeCoefficient B.c B.a k i t : ℝ) : ℂ) • A i := by
    change (∫ t in D, (modeCoefficient B.c B.a k i t : ℂ) • A i) = _
    rw [_root_.integral_smul_const,integral_complex_ofReal]
  have hmass (i : Fin 5) := repeated_coefficient_masses B n hn e i
  have hsuffix (i : Fin 5) :
      ‖∫ t in Ioc (1 : ℝ) 2, modeOutput B.c B.a k i rho hpos t‖ =
        B.q^n*(1-B.q)*‖A i‖ := by
    rw [hint, (hmass i).2.1, norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnq]
  have htotal (i : Fin 5) :
      ‖∫ t in Ioc (0 : ℝ) 2, modeOutput B.c B.a k i rho hpos t‖ =
        (1-B.q^(n+1))*‖A i‖ := by
    rw [hint,(hmass i).2.2,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hqn)]
  refine ⟨?_,?_,?_⟩
  · intro i
    refine ⟨?_,(hmass i).1,(hmass i).2.1,(hmass i).2.2,by rw [hint,(hmass i).2.1]⟩
    intro t ht
    change (modeCoefficient B.c B.a k i t : ℂ) • A i = _
    rw [suffix_coefficient_scaling B n hn e i t ht,Complex.ofReal_mul,mul_smul]
    rfl
  · change (∑ i : Fin 5, ‖∫ t in Ioc (1 : ℝ) 2, modeOutput B.c B.a k i rho hpos t‖) = _
    simp_rw [hsuffix]
    rw [← Finset.mul_sum,actual_output_mass_partition rho hpos]
  · change (∑ i : Fin 5, ‖∫ t in Ioc (0 : ℝ) 2, modeOutput B.c B.a k i rho hpos t‖) + _ = _
    simp_rw [htotal]
    rw [← Finset.mul_sum,actual_output_mass_partition rho hpos,norm_smul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq.1.le _)]
    ring


private theorem prefix_output_eq (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin 5) (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    modeOutput B.c B.a (B.early n hn) i rho hpos t =
      modeOutput B.c B.a (B.late n hn) i rho hpos t := by
  unfold modeOutput modeCoefficient
  simp only [Band.early,Band.late,
    survival_before B.c 1 t _ _ ht.1.le ht.2.le,
    rate_before B.c 1 _ _ t ht.2]
  simp [concatenate,ht.2.le]

private theorem constant_coefficient_zero (c a v : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (t : ℝ) (he : k =ᶠ[𝓝 t] (fun _ => v)) : modeCoefficient c a k i t = 0 := by
  have hd : deriv k t = 0 := by rw [he.deriv_eq]; simp
  have hl : deriv (fun u => Real.log (p c (k u) i)) t = 0 := by
    have hlog : (fun u => Real.log (p c (k u) i)) =ᶠ[𝓝 t]
        (fun _ => Real.log (p c v i)) := by
      simpa only [Function.comp_def] using he.fun_comp (fun x : ℝ => Real.log (p c x i))
    rw [hlog.deriv_eq]; simp
  simp [modeCoefficient,amplitude,jumpRate,OriginalControlSurvivalInstability.hazard,hd,hl]

private theorem suffix_wait_zero (B : Band) (e : Bool) (i : Fin 5) (t : ℝ)
    (ht : if e then (1 / 2:ℝ) < t else t < 1 / 2) :
    modeCoefficient B.c B.a (if e then B.earlySuffix else B.lateSuffix) i t = 0 := by
  apply constant_coefficient_zero B.c B.a B.a
  cases e <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢
  · filter_upwards [eventually_lt_nhds ht] with u hu
    simp only [Band.lateSuffix,concatenate,ite_eq_left hu.le]
    simp [Band.wait,Leg.height,Leg.speed]
  · have hl := B.loop_end (1/4) (by norm_num)
    norm_num only at hl
    filter_upwards [eventually_gt_nhds ht] with u hu
    simp only [Band.earlySuffix,concatenate,ite_eq_right (not_le.mpr hu)]
    rw [hl]
    simp [Band.wait,Leg.height,Leg.speed]

/-- The common prefix cancels on every Borel event. The two disjoint suffix
windows give the exact integrated trace norm on the same arbitrary joint input. -/
theorem repeated_reference_distance (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    (∀ (i : Fin 5) (E : Set ℝ), MeasurableSet E →
      (∫ t in (Ioc (0 : ℝ) 1) ∩ E, modeOutput B.c B.a (B.early n hn) i rho hpos t) =
      ∫ t in (Ioc (0 : ℝ) 1) ∩ E, modeOutput B.c B.a (B.late n hn) i rho hpos t) ∧
    (∑ i : Fin 5, ∫ t in Ioc (0 : ℝ) 2,
      ‖modeOutput B.c B.a (B.early n hn) i rho hpos t -
        modeOutput B.c B.a (B.late n hn) i rho hpos t‖) =
      2*(B.q^n*(1-B.q))*‖rho‖ := by
  let FE (i : Fin 5) := modeOutput B.c B.a (B.early n hn) i rho hpos
  let FL (i : Fin 5) := modeOutput B.c B.a (B.late n hn) i rho hpos
  have hpref (i : Fin 5) : FE i =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] FL i := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.ae_ne (1 : ℝ)).filter_mono (ae_mono Measure.restrict_le_self)] with t ht hne
    exact prefix_output_eq B n hn i rho hpos t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  have hintE (i : Fin 5) : IntegrableOn (FE i) (Ioc (0 : ℝ) 2) :=
    (repeated_failure_event B n hn true i rho hpos).2.1
  have hintL (i : Fin 5) : IntegrableOn (FL i) (Ioc (0 : ℝ) 2) :=
    (repeated_failure_event B n hn false i rho hpos).2.1
  have hsub0 : Ioc (0 : ℝ) 1 ⊆ Ioc (0 : ℝ) 2 := Ioc_subset_Ioc le_rfl (by norm_num)
  have hsub1 : Ioc (1 : ℝ) 2 ⊆ Ioc (0 : ℝ) 2 := Ioc_subset_Ioc (by norm_num) le_rfl
  have hdis (i : Fin 5) :
      (fun t => ‖FE i t - FL i t‖) =ᵐ[volume.restrict (Ioc (1 : ℝ) 2)]
        (fun t => ‖FE i t‖ + ‖FL i t‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.ae_ne (3 / 2:ℝ)).filter_mono (ae_mono Measure.restrict_le_self)] with t ht hne
    by_cases he : t < 3 / 2
    · have hz : FL i t = 0 := by
        have hc := suffix_coefficient_scaling B n hn false i t ht
        have hw := suffix_wait_zero B false i (t-1) (by simp only [Bool.false_eq_true, ↓reduceIte]; linarith)
        simp only [Bool.false_eq_true, ↓reduceIte] at hc hw
        rw [hw,mul_zero] at hc
        simp [FL,modeOutput,hc]
      simp [hz]
    · have hz : FE i t = 0 := by
        have hc := suffix_coefficient_scaling B n hn true i t ht
        have hgt : (3 / 2:ℝ) < t := lt_of_le_of_ne (le_of_not_gt he) (Ne.symm hne)
        have hw := suffix_wait_zero B true i (t-1) (by
          simp only [↓reduceIte]
          linarith)
        simp only [Bool.false_eq_true, ↓reduceIte] at hc hw
        rw [hw,mul_zero] at hc
        simp [FE,modeOutput,hc]
      simp [hz]
  have hmode (i : Fin 5) :
      (∫ t in Ioc (0 : ℝ) 2, ‖FE i t-FL i t‖) =
      (∫ t in Ioc (1 : ℝ) 2, ‖FE i t‖) + (∫ t in Ioc (1 : ℝ) 2, ‖FL i t‖) := by
    have hi : IntegrableOn (fun t => ‖FE i t - FL i t‖) (Ioc (0 : ℝ) 2) :=
      ((hintE i).sub (hintL i)).norm
    rw [← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2),
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hi.mono_set hsub0) (hi.mono_set hsub1)]
    have hz : (∫ t in Ioc (0 : ℝ) 1, ‖FE i t-FL i t‖) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hpref i] with t ht
      simp [ht]
    rw [hz,zero_add,integral_congr_ae (hdis i), integral_add
      ((hintE i).mono_set hsub1).norm ((hintL i).mono_set hsub1).norm]
  refine ⟨?_,?_⟩
  · intro i E hE
    exact integral_congr_ae ((hpref i).filter_mono
      (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)))
  · change (∑ i : Fin 5, ∫ t in Ioc (0 : ℝ) 2, ‖FE i t-FL i t‖) = _
    simp_rw [hmode]
    rw [Finset.sum_add_distrib]
    have hnorm (e : Bool) (i : Fin 5) :
        (∫ t in Ioc (1 : ℝ) 2, ‖modeOutput B.c B.a
          (if e then B.early n hn else B.late n hn) i rho hpos t‖) =
        ‖∫ t in Ioc (1 : ℝ) 2, modeOutput B.c B.a
          (if e then B.early n hn else B.late n hn) i rho hpos t‖ := by
      have hh := ((repeated_failure_event B n hn e i rho hpos).2.2
        (Ioc (1 : ℝ) 2) measurableSet_Ioc).2.2.2
      rw [inter_eq_right.mpr hsub1] at hh
      exact hh.symm
    have hE := (repeated_reference_completeness B n hn true rho hpos).2.1
    have hL := (repeated_reference_completeness B n hn false rho hpos).2.1
    have hEE : (∑ i : Fin 5, ∫ t in Ioc (1 : ℝ) 2, ‖FE i t‖) = B.q^n*(1-B.q)*‖rho‖ := by
      change (∑ i : Fin 5, ∫ t in Ioc (1 : ℝ) 2, ‖modeOutput B.c B.a (B.early n hn) i rho hpos t‖) = _
      calc
        _ = ∑ i : Fin 5, ‖∫ t in Ioc (1 : ℝ) 2, FE i t‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa only [↓reduceIte] using hnorm true i
        _ = _ := by simpa only [↓reduceIte] using hE
    have hLL : (∑ i : Fin 5, ∫ t in Ioc (1 : ℝ) 2, ‖FL i t‖) = B.q^n*(1-B.q)*‖rho‖ := by
      change (∑ i : Fin 5, ∫ t in Ioc (1 : ℝ) 2, ‖modeOutput B.c B.a (B.late n hn) i rho hpos t‖) = _
      calc
        _ = ∑ i : Fin 5, ‖∫ t in Ioc (1 : ℝ) 2, FL i t‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa only [Bool.false_eq_true, ↓reduceIte] using hnorm false i
        _ = _ := by simpa only [Bool.false_eq_true, ↓reduceIte] using hL
    rw [hEE,hLL]
    ring

end D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass
