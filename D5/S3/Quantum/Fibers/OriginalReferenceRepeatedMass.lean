/- GID: D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalReferenceRepeatedMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native balance and the complete arbitrary-reference operational distance. -/

import D5.S3.Quantum.Fibers.OriginalReferenceOutputMeasure

/-! Native mode balance retains arbitrary positive joint reference inputs. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators Matrix TensorProduct
open Set Filter Topology MeasureTheory intervalIntegral TraceClassFiniteBlocks
namespace D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass
open OriginalControlMarkedJump OriginalReferenceKraus OriginalReferenceOutputMeasure
open OriginalRepeatedPrefix OriginalControlComposition OriginalMarkedConcatenation

theorem survival_ac (c T : ℝ) (k : ℝ → ℝ)
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

theorem probability_ac (c T : ℝ) (k : ℝ → ℝ)
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

theorem rate_nonneg (c : ℝ) (k : ℝ → ℝ) (t : ℝ)
    (hc : c < 1 / 2) (hb : k t ∈ Ioo 0 c) (hd : DifferentiableAt ℝ k t)
    (i : Fin 5) : 0 ≤ jumpRate c k t i := by
  have hp : HasDerivAt (fun u => p c (k u) i)
      (![1,-1,0,-1,1] i * deriv k t) t := by
    simpa [p, FiniteRectangleTransport.direction] using
      (FiniteRectangleTransport.probability_derivative
        (c, c, 1 - 2*c) k (deriv k t) t hd.hasDerivAt i)
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

theorem native_coefficient_deriv (c a T : ℝ) (k : ℝ → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c, c, 1 - 2*c) T k (fun _ => (0 : ℝ))) (i : Fin 5) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
      modeCoefficient c a k i t =
        -deriv (fun u => survival c k u * p c (k u) i) t / p c a i := by
  have hi := hazard_integrable c T 0 k hk
  filter_upwards [(original_ac _ _ _ _ hk).1.ae_differentiableAt,
    hi.ae_hasDerivAt_integral] with t hkt hIt ht
  have ht' : t ∈ Icc 0 T := by
    simpa only [uIcc_of_le hk.1] using ht
  have hb := OriginalRepeatedMarkedLaw.native_bounds c T 0 k hk t ht'
  have hd := hkt ht
  have hp : HasDerivAt (fun u => p c (k u) i)
      (![1,-1,0,-1,1] i * deriv k t) t := by
    simpa [p, FiniteRectangleTransport.direction] using
      (FiniteRectangleTransport.probability_derivative
        (c, c, 1 - 2*c) k (deriv k t) t hd.hasDerivAt i)
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

/-! The complete classical--quantum output uses the literal Kraus success
branch as well as every retained mode/time failure density. -/

def diagonalAction {m : ℕ} (d : Fin m → ℂ) :
    Blocks (Fin m) H →L[ℂ] Blocks (Fin m) H :=
  ∑ i, d i • embedding (ContinuousLinearMap.id ℂ H) i

theorem diagonalAction_apply {m : ℕ} (d : Fin m → ℂ)
    (x : Blocks (Fin m) H) (i : Fin m) : diagonalAction d x i = d i • x i := by
  change coordinate i (diagonalAction d x) = _
  simp [diagonalAction, embedding, ContinuousLinearMap.comp_apply, coordinate, PiLp.single_apply]

/-- The original constant-phase successful Kraus, amplified by the unchanged reference. -/
def referenceSuccess (c a k S : ℝ) : Blocks (Fin 5) H →L[ℂ] Blocks (Fin 5) H :=
  diagonalAction (fun i => (Real.sqrt S : ℂ) * (Real.sqrt (p c k i / p c a i) : ℂ))

/-- The actual successful trace-class output; no normalization or dephasing. -/
def successOutput (c a k S : ℝ) (rho : TraceClass (Blocks (Fin 5) H)) :
    TraceClass (Blocks (Fin 5) H) :=
  TraceClass.ofOperator
    (referenceSuccess c a k S * rho.1 * (referenceSuccess c a k S).adjoint)
    (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))

theorem tensor_diagonal {m : ℕ} (d : Fin m → ℂ)
    (z : EuclideanSpace ℂ (Fin m) ⊗[ℂ] H) :
    diagonalAction d (tensorCoordinates z) = tensorCoordinates
      (TensorProduct.map (diagonalAction (H := ℂ) d).toLinearMap
        (LinearMap.id : H →ₗ[ℂ] H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    apply PiLp.ext
    intro i
    simp [diagonalAction_apply, tensorCoordinates_tmul, TensorProduct.map_tmul,
      smul_smul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem terminal_success (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool) :
    let k := if e then B.early n hn else B.late n hn
    referenceSuccess (H := H) B.c B.a (k 2) (survival B.c k 2) =
      (Real.sqrt (B.q^(n+1)) : ℂ) • ContinuousLinearMap.id ℂ _ := by
  have hf := early_late_native_survival B n hn 0
  have he : (if e then B.early n hn else B.late n hn) 2 = B.a := by
    cases e <;> simp_all
  have hs : survival B.c (if e then B.early n hn else B.late n hn) 2 = B.q^(n+1) := by
    cases e <;> simp_all
  dsimp only
  rw [he, hs]
  ext x i
  simp [referenceSuccess, diagonalAction_apply, div_self (p_pos B.c B.a B.c_lt
    ⟨B.a_pos, B.ab.trans B.bc⟩ i).ne']

/-- The fixed absorbing successor and the unchanged reference, with exact time and mode. -/
def liveFailure (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    TraceClass (Blocks (Fin 6) H) :=
  (modeCoefficient c a k i t : ℂ) • TraceClass.ofOperator
    (embedding (compression rho.1 i) (5 : Fin 6))
    (embedding_traceClass (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
      (compression_nonneg hpos i) (5 : Fin 6))

theorem liveFailure_diff_norm (c a : ℝ) (k l : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    ‖liveFailure c a k i rho hpos t - liveFailure c a l i rho hpos t‖ =
      ‖modeOutput c a k i rho hpos t - modeOutput c a l i rho hpos t‖ := by
  simp only [liveFailure, modeOutput, ← sub_smul, norm_smul, TraceClass.norm_eq_traceNorm]
  congr 1
  exact (embedding_trace_norm (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
    (compression_nonneg hpos i) (5 : Fin 6)).2

theorem liveFailure_actual (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    (liveFailure c a k i rho hpos t).1 =
      (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
        (rho.1.comp (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint) := by
  have he := congrArg (fun A : H →L[ℂ] H =>
    (insertion (5 : Fin 6)).comp (A.comp (coordinate (5 : Fin 6))))
    (actual_raw_jump_operator c a (k t) (survival c k t) (jumpRate c k t) i rho.1)
  change (modeCoefficient c a k i t : ℂ) • embedding (compression rho.1 i) (5 : Fin 6) = _
  simpa only [modeCoefficient, absorbingJump,
    ContinuousLinearMap.adjoint_comp, insertion, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc, embedding, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul] using he.symm

/-- IS.7 on the complete five-live-mode output, including the absorbing successor. -/
def liveDistance (c a T : ℝ) (k l : ℝ → ℝ)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) : ℝ :=
  (‖successOutput c a (k T) (survival c k T) rho -
      successOutput c a (l T) (survival c l T) rho‖ +
    ∑ i : Fin 5, ∫ t in Ioc (0 : ℝ) T,
      ‖liveFailure c a k i rho hpos t - liveFailure c a l i rho hpos t‖) / 2

/-- The successful tensor Kraus is common, and the complete IS.7 distance
has the asserted value for every positive joint input, without normalization. -/
theorem repeated_live_operational (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    (∀ (c a k S : ℝ) (z : EuclideanSpace ℂ (Fin 5) ⊗[ℂ] H),
      referenceSuccess c a k S (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (referenceSuccess (H := ℂ) c a k S).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a k S : ℝ) (x : EuclideanSpace ℂ (Fin 5)) (i : Fin 5),
      referenceSuccess (H := ℂ) c a k S x i =
        (successfulKraus c a k S *ᵥ x) i) ∧
    (∀ (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5) (t : ℝ),
      (liveFailure c a k i rho hpos t).1 =
        (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
          (rho.1.comp (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint)) ∧
    (∀ e : Bool, let k := if e then B.early n hn else B.late n hn
      referenceSuccess (H := H) B.c B.a (k 2) (survival B.c k 2) =
        (Real.sqrt (B.q^(n+1)) : ℂ) • ContinuousLinearMap.id ℂ _) ∧
    liveDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos =
      B.q^n*(1-B.q)*‖rho‖ := by
  refine ⟨fun c a k S z => tensor_diagonal _ z, ?_,
    fun c a k i t => liveFailure_actual c a k i rho hpos t,
    terminal_success B n hn, ?_⟩
  · intro c a k S x i
    simp [referenceSuccess, diagonalAction_apply, successfulKraus, Matrix.mulVec]
  have he : successOutput B.c B.a (B.early n hn 2)
      (survival B.c (B.early n hn) 2) rho =
      successOutput B.c B.a (B.late n hn 2)
        (survival B.c (B.late n hn) 2) rho := by
    apply Subtype.ext
    change _ * rho.1 * _ = _ * rho.1 * _
    have hs : referenceSuccess (H := H) B.c B.a (B.early n hn 2)
        (survival B.c (B.early n hn) 2) = referenceSuccess B.c B.a (B.late n hn 2)
          (survival B.c (B.late n hn) 2) :=
      by
        have hE := terminal_success (H := H) B n hn true
        have hL := terminal_success (H := H) B n hn false
        dsimp only at hE hL
        exact hE.trans hL.symm
    exact congrArg (fun K : Blocks (Fin 5) H →L[ℂ] Blocks (Fin 5) H => K * rho.1 * K.adjoint) hs
  simp_rw [liveDistance, liveFailure_diff_norm]
  rw [he, sub_self, norm_zero, zero_add,
    (repeated_reference_distance B n hn rho hpos).2]
  ring

private def sixBlock (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1)
    (i : Fin 6) : TraceClass H :=
  TraceClass.ofOperator (compression rho.1 i)
    (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)

/-- Initial live weight, with all six-coordinate coherences still present in the input. -/
def liveWeight (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) : ℝ :=
  ∑ i : Fin 5, ‖sixBlock rho hpos i.castSucc‖

private def diagonalLive (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    TraceClass (Blocks (Fin 5) H) :=
  ∑ i : Fin 5, TraceClass.ofOperator (embedding (sixBlock rho hpos i.castSucc).1 i)
    (embedding_traceClass (TraceClass.isTraceClass_coe _) (compression_nonneg hpos _) i)

private theorem diagonalLive_pos (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    0 ≤ (diagonalLive rho hpos).1 := by
  change 0 ≤ ∑ i : Fin 5, embedding (compression rho.1 i.castSucc) i
  apply Finset.sum_nonneg
  intro i _
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  simpa only [embedding, insertion, ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (compression_nonneg hpos i.castSucc)).adjoint_conj
      (coordinate i)

private theorem diagonalLive_compression (rho : TraceClass (Blocks (Fin 6) H))
    (hpos : 0 ≤ rho.1) (i : Fin 5) :
    compression (diagonalLive rho hpos).1 i = compression rho.1 i.castSucc := by
  ext x
  change coordinate i ((∑ j : Fin 5, embedding (compression rho.1 j.castSucc) j)
    (insertion i x)) = _
  simp [embedding, ContinuousLinearMap.comp_apply, coordinate, PiLp.single_apply]

private theorem diagonalLive_mass (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    ‖diagonalLive rho hpos‖ = liveWeight rho hpos := by
  rw [← actual_output_mass_partition _ (diagonalLive_pos rho hpos)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Subtype.ext
  exact diagonalLive_compression rho hpos i

private theorem liveWeight_partition (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    liveWeight rho hpos + ‖sixBlock rho hpos 5‖ = ‖rho‖ := by
  have ht := congrArg (Complex.reCLM : ℂ → ℝ)
    (trace_compression_sum (TraceClass.isTraceClass_coe rho) hpos)
  have hi (i : Fin 6) : ‖sixBlock rho hpos i‖ =
      (trace (compression rho.1 i) (compression_traceClass
        (TraceClass.isTraceClass_coe rho) hpos i)).re :=
    QuantumLogEnergy.traceNorm_eq_re_trace _ (compression_nonneg hpos i)
  have hn : ‖rho‖ = (trace rho.1 (TraceClass.isTraceClass_coe rho)).re :=
    QuantumLogEnergy.traceNorm_eq_re_trace _ hpos
  have ht' : (∑ i : Fin 6, (trace (compression rho.1 i)
      (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)).re) =
      (trace rho.1 (TraceClass.isTraceClass_coe rho)).re := by
    simpa only [map_sum, Complex.reCLM_apply] using ht
  rw [hn, ← ht']
  simp_rw [← hi]
  rw [Fin.sum_univ_castSucc]
  rfl

/-- OC.19a/OC.28: the no-new-failure Kraus is K direct-sum the stopped identity. -/
def stoppedSuccess (c a k S : ℝ) : Blocks (Fin 6) H →L[ℂ] Blocks (Fin 6) H :=
  diagonalAction (Fin.lastCases 1
    (fun i => (Real.sqrt S : ℂ) * (Real.sqrt (p c k i / p c a i) : ℂ)))

def stoppedSuccessOutput (c a k S : ℝ) (rho : TraceClass (Blocks (Fin 6) H)) :
    TraceClass (Blocks (Fin 6) H) :=
  TraceClass.ofOperator (stoppedSuccess c a k S * rho.1 * (stoppedSuccess c a k S).adjoint)
    (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho))

/-- OC.19b extended by zero on the already stopped input. -/
def stoppedJump (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    Blocks (Fin 6) H →L[ℂ] Blocks (Fin 6) H :=
  (insertion (5 : Fin 6)).comp (amplitude c a k S g i • coordinate i.castSucc)

private theorem tensor_stoppedJump (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (z : EuclideanSpace ℂ (Fin 6) ⊗[ℂ] H) :
    stoppedJump c a k S g i (tensorCoordinates z) = tensorCoordinates
      (TensorProduct.map (stoppedJump (H := ℂ) c a k S g i).toLinearMap
        (LinearMap.id : H →ₗ[ℂ] H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    apply PiLp.ext
    intro j
    change coordinate j (stoppedJump c a k S g i (tensorCoordinates (u ⊗ₜ[ℂ] x))) = _
    by_cases hj : j = (5 : Fin 6) <;>
      simp [stoppedJump, ContinuousLinearMap.comp_apply, tensorCoordinates_tmul,
        TensorProduct.map_tmul, coordinate, PiLp.single_apply, apply_ite, smul_smul, hj, eq_comm]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

def stoppedFailure (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    TraceClass (Blocks (Fin 6) H) :=
  (modeCoefficient c a k i t : ℂ) • TraceClass.ofOperator
    (embedding (compression rho.1 i.castSucc) (5 : Fin 6))
    (embedding_traceClass (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos _)
      (compression_nonneg hpos _) (5 : Fin 6))

/-- IS.7 for the supplier's six-dimensional carrier, on the original input. -/
def stoppedDistance (c a T : ℝ) (k l : ℝ → ℝ)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) : ℝ :=
  (‖stoppedSuccessOutput c a (k T) (survival c k T) rho -
      stoppedSuccessOutput c a (l T) (survival c l T) rho‖ +
    ∑ i : Fin 5, ∫ t in Ioc (0 : ℝ) T,
      ‖stoppedFailure c a k i rho hpos t - stoppedFailure c a l i rho hpos t‖) / 2

private theorem stoppedFailure_live (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    stoppedFailure c a k i rho hpos t =
      liveFailure c a k i (diagonalLive rho hpos) (diagonalLive_pos rho hpos) t := by
  apply Subtype.ext
  change _ • embedding _ _ = _ • embedding _ _
  rw [diagonalLive_compression]

private theorem stoppedFailure_actual (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) (t : ℝ) :
    (stoppedFailure c a k i rho hpos t).1 =
      (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
        (rho.1.comp (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint) := by
  change (modeCoefficient c a k i t : ℂ) •
    embedding (compression rho.1 i.castSucc) (5 : Fin 6) = _
  ext x : 1
  simp only [stoppedJump, modeCoefficient, embedding, compression,
    ContinuousLinearMap.adjoint_comp, map_smulₛₗ, insertion,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply,
    smul_apply, map_smul, smul_smul, RingHom.id_apply]
  change (Complex.normSq (amplitude c a (k t) (survival c k t) (jumpRate c k t) i) : ℂ) • _ =
    (star (amplitude c a (k t) (survival c k t) (jumpRate c k t) i) *
      amplitude c a (k t) (survival c k t) (jumpRate c k t) i) • _
  rw [mul_comm (star _) _, Complex.star_def, Complex.mul_conj]

private theorem stopped_terminal (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool) :
    let k := if e then B.early n hn else B.late n hn
    stoppedSuccess (H := H) B.c B.a (k 2) (survival B.c k 2) =
      diagonalAction (Fin.lastCases 1 (fun _ : Fin 5 => (Real.sqrt (B.q^(n+1)) : ℂ))) := by
  have hf := early_late_native_survival B n hn 0
  have he : (if e then B.early n hn else B.late n hn) 2 = B.a := by
    cases e <;> simp_all
  have hs : survival B.c (if e then B.early n hn else B.late n hn) 2 = B.q^(n+1) := by
    cases e <;> simp_all
  dsimp only
  rw [he, hs]
  unfold stoppedSuccess
  apply congrArg (diagonalAction (H := H))
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rfl
  · simp [div_self (p_pos B.c B.a B.c_lt ⟨B.a_pos, B.ab.trans B.bc⟩ i).ne']

private theorem stoppedFailure_integrable (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool)
    (i : Fin 5) (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    IntegrableOn (stoppedFailure B.c B.a (if e then B.early n hn else B.late n hn) i rho hpos)
      (Ioc (0 : ℝ) 2) := by
  obtain ⟨_, _, hE, hL, _⟩ := early_late_native_survival B n hn 0
  let k := if e then B.early n hn else B.late n hn
  have hk : OriginalControl (B.c, B.c, 1-2*B.c) 2 k (fun _ => (0 : ℝ)) := by
    cases e <;> assumption
  have hi := (native_mode_balance B.c B.a 2 k B.c_lt ⟨B.a_pos, B.ab.trans B.bc⟩
    hk i 0 2 (by norm_num) (by norm_num) (by norm_num)).1
  exact hi.ofReal.smul_const _

/-- Arbitrary initially stopped mass and live/stopped coherences are retained.
The complete output distance equals the live weight times the original scalar. -/
theorem repeated_stopped_operational (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1) :
    (∀ (c a k S : ℝ) (z : EuclideanSpace ℂ (Fin 6) ⊗[ℂ] H),
      stoppedSuccess c a k S (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (stoppedSuccess (H := ℂ) c a k S).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5) (t : ℝ),
      (stoppedFailure c a k i rho hpos t).1 =
        (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
          (rho.1.comp (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint)) ∧
    (∀ (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) (x : H),
      stoppedJump c a k S g i (insertion (5 : Fin 6) x) = 0) ∧
    stoppedSuccessOutput B.c B.a (B.early n hn 2) (survival B.c (B.early n hn) 2) rho =
      stoppedSuccessOutput B.c B.a (B.late n hn 2) (survival B.c (B.late n hn) 2) rho ∧
    stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos =
      B.q^n*(1-B.q)*liveWeight rho hpos ∧
    (‖rho‖ = 1 → stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos ≤
      B.q^n*(1-B.q)) ∧
    (∀ (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
      (z : EuclideanSpace ℂ (Fin 6) ⊗[ℂ] H),
      stoppedJump c a k S g i (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (stoppedJump (H := ℂ) c a k S g i).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a k S : ℝ) (x : Blocks (Fin 6) H),
      (∀ i : Fin 5, stoppedSuccess c a k S x i.castSucc =
        ((Real.sqrt S : ℂ) * (Real.sqrt (p c k i / p c a i) : ℂ)) • x i.castSucc) ∧
      stoppedSuccess c a k S x 5 = x 5) ∧
    (∀ (e : Bool) (i : Fin 5) (E : Set ℝ), MeasurableSet E →
      IntegrableOn (stoppedFailure B.c B.a
        (if e then B.early n hn else B.late n hn) i rho hpos) ((Ioc (0 : ℝ) 2) ∩ E)) := by
  have he : stoppedSuccessOutput B.c B.a (B.early n hn 2)
      (survival B.c (B.early n hn) 2) rho =
      stoppedSuccessOutput B.c B.a (B.late n hn 2)
        (survival B.c (B.late n hn) 2) rho := by
    apply Subtype.ext
    change _ * rho.1 * _ = _ * rho.1 * _
    have hE := stopped_terminal (H := H) B n hn true
    have hL := stopped_terminal (H := H) B n hn false
    dsimp only at hE hL
    exact congrArg (fun K : Blocks (Fin 6) H →L[ℂ] Blocks (Fin 6) H => K * rho.1 * K.adjoint) (hE.trans hL.symm)
  have hd : stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos =
      B.q^n*(1-B.q)*liveWeight rho hpos := by
    have hl := (repeated_live_operational B n hn (diagonalLive rho hpos)
      (diagonalLive_pos rho hpos)).2.2.2.2
    rw [diagonalLive_mass] at hl
    rw [stoppedDistance, he, sub_self, norm_zero, zero_add]
    simp_rw [stoppedFailure_live]
    rw [liveDistance] at hl
    have hE := terminal_success (H := H) B n hn true
    have hL := terminal_success (H := H) B n hn false
    dsimp only at hE hL
    have hs := hE.trans hL.symm
    have ho : successOutput B.c B.a (B.early n hn 2) (survival B.c (B.early n hn) 2)
        (diagonalLive rho hpos) = successOutput B.c B.a (B.late n hn 2)
          (survival B.c (B.late n hn) 2) (diagonalLive rho hpos) := by
      apply Subtype.ext
      change _ * _ * _ = _ * _ * _
      exact congrArg (fun K : Blocks (Fin 5) H →L[ℂ] Blocks (Fin 5) H =>
        K * (diagonalLive rho hpos).1 * K.adjoint) hs
    simpa only [ho, sub_self, norm_zero, zero_add] using hl
  refine ⟨fun c a k S z => tensor_diagonal _ z,
    fun c a k i t => stoppedFailure_actual c a k i rho hpos t, ?_, he, hd, ?_,
    tensor_stoppedJump, ?_, ?_⟩
  · intro c a k S g i x
    have hi : i.castSucc ≠ (5 : Fin 6) := i.castSucc_ne_last
    simp [stoppedJump, ContinuousLinearMap.comp_apply, coordinate, PiLp.single_apply, hi]
  · intro hnorm
    rw [hd]
    have hw : liveWeight rho hpos ≤ 1 := by
      have hp := liveWeight_partition rho hpos
      rw [hnorm] at hp
      linarith [norm_nonneg (sixBlock rho hpos 5)]
    have hq := early_late_native_survival B n hn 0
    exact (mul_le_mul_of_nonneg_left hw
      (mul_nonneg (pow_nonneg hq.1.le _) (sub_nonneg.mpr hq.2.1.le))).trans_eq (mul_one _)
  · intro c a k S x
    constructor
    · intro i
      simp [stoppedSuccess, diagonalAction_apply]
    · rw [stoppedSuccess, diagonalAction_apply]
      change (1 : ℂ) • x 5 = x 5
      exact one_smul _ _
  · intro e i E _
    exact (stoppedFailure_integrable B n hn e i rho hpos).mono_set inter_subset_left

universe v

/-- A normalized joint input with a reference in any fixed universe. -/
structure JointState (m : ℕ) where
  Ref : Type v
  [normed : NormedAddCommGroup Ref]
  [inner : InnerProductSpace ℂ Ref]
  [complete : CompleteSpace Ref]
  rho : TraceClass (Blocks (Fin m) Ref)
  positive : 0 ≤ rho.1
  normalized : ‖rho‖ = 1

attribute [instance] JointState.normed JointState.inner JointState.complete

/-- The genuine IS.7 supremum, indexed by all normalized inputs and references
in the chosen universe; its definition contains no proposed scalar value. -/
def operationalDistance (c a T : ℝ) (k l : ℝ → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ s : JointState.{v} 6,
    x = stoppedDistance c a T k l s.rho s.positive}

abbrev witnessReference := EuclideanSpace ℂ (ULift.{v} Unit)

def witnessBase : TraceClass witnessReference.{v} :=
  TraceClass.ofOperator (ContinuousLinearMap.id ℂ _)
    (isTraceClass_of_finiteDimensional _)

theorem witnessBase_pos : 0 ≤ witnessBase.{v}.1 := by
  change (0 : witnessReference.{v} →L[ℂ] witnessReference.{v}) ≤ 1
  exact zero_le_one

theorem witnessBase_norm : ‖witnessBase.{v}‖ = 1 := by
  rw [TraceClass.norm_eq_traceNorm, QuantumLogEnergy.traceNorm_eq_re_trace _ witnessBase_pos]
  have ht : trace witnessBase.{v}.1 (TraceClass.isTraceClass_coe _) = 1 := by
    have hf : HasFiniteMultiplicity (1 : witnessReference.{v} →L[ℂ] witnessReference.{v}) :=
      ⟨.one _, isTraceClass_of_finiteDimensional _⟩
    have hv := hf.trace_eq_finrank_range
    have hr : LinearMap.range (1 : witnessReference.{v} →L[ℂ] witnessReference.{v}).toLinearMap = ⊤ := by
      ext x
      simp
    rw [hr] at hv
    change trace (1 : witnessReference.{v} →L[ℂ] witnessReference.{v}) _ = 1
    simpa using hv
  exact congrArg Complex.re ht

private def fullyLive : TraceClass (Blocks (Fin 6) witnessReference.{v}) :=
  TraceClass.ofOperator (embedding witnessBase.{v}.1 (0 : Fin 6))
    (embedding_traceClass (TraceClass.isTraceClass_coe _) witnessBase_pos _)

private theorem fullyLive_pos : 0 ≤ fullyLive.{v}.1 := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  simpa only [fullyLive, TraceClass.ofOperator_coe, embedding, insertion,
    ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp witnessBase_pos).adjoint_conj
      (coordinate (0 : Fin 6))

private theorem fullyLive_norm : ‖fullyLive.{v}‖ = 1 :=
  (embedding_trace_norm (TraceClass.isTraceClass_coe _) witnessBase_pos (0 : Fin 6)).2.trans
    witnessBase_norm

private theorem fullyLive_weight : liveWeight fullyLive.{v} fullyLive_pos = 1 := by
  have hp := liveWeight_partition fullyLive.{v} fullyLive_pos
  have hz : sixBlock fullyLive.{v} fullyLive_pos 5 = 0 := by
    apply Subtype.ext
    ext x : 1
    change coordinate (5 : Fin 6)
      (embedding witnessBase.{v}.1 (0 : Fin 6) (insertion 5 x)) = 0
    simp [embedding, ContinuousLinearMap.comp_apply, coordinate, PiLp.single_apply]
  simpa [hz, fullyLive_norm] using hp

/-- Every universe admits a fully live attaining state. The independently
defined supremum equals the original complete marked-law supplier. -/
theorem repeated_operational_supremum (B : Band) (n : ℕ) (hn : 1 ≤ n) :
    (∀ (s : JointState.{v} 5),
      liveDistance B.c B.a 2 (B.early n hn) (B.late n hn) s.rho s.positive =
        B.q^n*(1-B.q)) ∧
    (∃ s : JointState.{v} 6, liveWeight s.rho s.positive = 1 ∧
      stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) s.rho s.positive =
        B.q^n*(1-B.q)) ∧
    operationalDistance.{v} B.c B.a 2 (B.early n hn) (B.late n hn) = B.q^n*(1-B.q) ∧
    (∀ (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ),
      OriginalRepeatedMarkedLaw.eventTV
        (markedLaw B.c B.a beta 2 m theta (B.early n hn))
        (markedLaw B.c B.a beta 2 m theta (B.late n hn)) =
      operationalDistance.{v} B.c B.a 2 (B.early n hn) (B.late n hn)) := by
  have hbound (s : JointState.{v} 6) :
      stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) s.rho s.positive ≤
        B.q^n*(1-B.q) :=
    (repeated_stopped_operational B n hn s.rho s.positive).2.2.2.2.2.1 s.normalized
  let witness : JointState.{v} 6 :=
    ⟨witnessReference.{v}, fullyLive.{v}, fullyLive_pos, fullyLive_norm⟩
  have hw : liveWeight witness.rho witness.positive = 1 := fullyLive_weight
  have ha : stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn)
      witness.rho witness.positive = B.q^n*(1-B.q) := by
    rw [(repeated_stopped_operational B n hn witness.rho witness.positive).2.2.2.2.1, hw, mul_one]
  have hop : operationalDistance.{v} B.c B.a 2 (B.early n hn) (B.late n hn) =
      B.q^n*(1-B.q) := by
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, witness, rfl⟩
      · rintro x ⟨s, rfl⟩
        exact hbound s
    · apply le_csSup
      · exact ⟨_, by rintro x ⟨s, rfl⟩; exact hbound s⟩
      · exact ⟨witness, ha.symm⟩
  refine ⟨?_, ⟨witness, hw, ha⟩, hop, ?_⟩
  · intro s
    simpa only [s.normalized, mul_one] using
      (repeated_live_operational B n hn s.rho s.positive).2.2.2.2
  · intro beta m theta
    rw [hop]
    exact (OriginalRepeatedMarkedLaw.native_marked_tv B n hn beta m theta).2.2.2


end D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass
