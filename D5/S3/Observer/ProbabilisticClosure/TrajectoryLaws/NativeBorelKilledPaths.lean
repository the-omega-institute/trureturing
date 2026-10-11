/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lawful killed Doob rows and finite-step conjugacy for the original boxed Borel flow. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal Topology
attribute [local instance] Classical.propDecidable
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelEndpointIdentification
open NativeBorelRepresentation NativeBorelNativeLaws NativeBorelStationaryLocalization

/-- The same Doob row on the conull carrier, killed immediately off that carrier. -/
def doob (F : CommonFlow) (G : Set PDescriptor) : Kernel PDescriptor PDescriptor :=
  F.L.withDensity (fun Q R => if Q ∈ G then
    endpointRate⁻¹ * (threeStepAverage F Q)⁻¹ * threeStepAverage F R else 0)

private theorem doob_density_measurable (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) :
    Measurable (Function.uncurry (fun Q R => if Q ∈ G then
      endpointRate⁻¹ * (threeStepAverage F Q)⁻¹ * threeStepAverage F R else 0)) := by
  exact ((measurable_const.mul ((h_measurable F).comp measurable_fst).inv).mul
    ((h_measurable F).comp measurable_snd)).ite
      (hmG.preimage measurable_fst) measurable_const

private theorem core_h_positive (F : CommonFlow) (Q : PDescriptor) (hQ : CoreAt F Q) :
    threeStepAverage F Q ≠ 0 := by
  intro hz
  have hh := hQ.2.1
  simp only [h, hz, ENNReal.toReal_zero] at hh
  norm_num at hh

private theorem doob_integral (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (Q : PDescriptor) (hQ : Q ∈ G)
    (f : PDescriptor → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ R, f R ∂doob F G Q) =
      (threeStepAverage F Q)⁻¹ *
        normalizedAction F (fun R => threeStepAverage F R * f R) Q := by
  rw [doob, Kernel.lintegral_withDensity _ (doob_density_measurable F G hmG) _ hf]
  simp only [hQ, if_true]
  simp_rw [mul_assoc]
  have hp : Measurable (fun R => threeStepAverage F R * f R) := (h_measurable F).mul hf
  have hp' : Measurable (fun R => (threeStepAverage F Q)⁻¹ * (threeStepAverage F R * f R)) :=
    measurable_const.mul hp
  calc
    _ = endpointRate⁻¹ * ∫⁻ R, (threeStepAverage F Q)⁻¹ * (threeStepAverage F R * f R) ∂F.L Q :=
      lintegral_const_mul _ hp'
    _ = endpointRate⁻¹ * ((threeStepAverage F Q)⁻¹ *
        ∫⁻ R, threeStepAverage F R * f R ∂F.L Q) :=
      congrArg (fun x => endpointRate⁻¹ * x) (lintegral_const_mul _ hp)
    _ = _ := by unfold normalizedAction; ring

private theorem doob_null (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (Q : PDescriptor) (hQ : Q ∉ G) : doob F G Q = 0 := by
  rw [doob, Kernel.withDensity_apply _ (doob_density_measurable F G hmG)]
  simp only [hQ, if_false]
  change (F.L Q).withDensity 0 = 0
  exact withDensity_zero

private theorem doob_subprobability (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (hG : ∀ Q ∈ G, CoreAt F Q) (Q : PDescriptor) :
    doob F G Q Set.univ ≤ 1 := by
  by_cases hQ : Q ∈ G
  · have hi := doob_integral F G hmG Q hQ (fun _ => 1) measurable_const
    simp only [lintegral_one, mul_one] at hi
    rw [hi]
    have hpos := core_h_positive F Q (hG Q hQ)
    calc
      _ ≤ (threeStepAverage F Q)⁻¹ * threeStepAverage F Q :=
        mul_le_mul_of_nonneg_left (hG Q hQ).2.2.1 bot_le
      _ = 1 := ENNReal.inv_mul_cancel hpos (h_finite F Q)
  · rw [doob_null F G hmG Q hQ]
    simp

private theorem doob_conjugacy (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G)
    (hG : ∀ Q ∈ G, CoreAt F Q ∧ ∀ᵐ R ∂F.C Q, R ∈ G)
    (f : PDescriptor → ℝ≥0∞) (hf : Measurable f) :
    ∀ n Q, Q ∈ G →
      normalizedIterate F (fun R => threeStepAverage F R * f R) n Q =
        threeStepAverage F Q * iterate (doob F G) f n Q := by
  have hM : IsFiniteKernel (doob F G) :=
    ⟨⟨1, by simp, doob_subprobability F G hmG (fun Q hQ => (hG Q hQ).1)⟩⟩
  letI := hM
  have hmi : ∀ n, Measurable (iterate (doob F G) f n) := by
    intro n
    induction n with
    | zero => exact hf
    | succ n ih =>
      change Measurable (fun Q => ∫⁻ R, iterate (doob F G) f n R ∂doob F G Q)
      exact ih.lintegral_kernel
  intro n
  induction n with
  | zero => intro Q hQ; simp only [normalizedIterate, pow_zero, iterate, one_mul]
  | succ n ih =>
    intro Q hQ
    rw [normalizedIterate_succ F (fun R => threeStepAverage F R * f R)
      (show Measurable (fun R => threeStepAverage F R * f R) from (h_measurable F).mul hf) n Q]
    unfold normalizedAction
    have hcL : ∀ᵐ R ∂F.L Q, R ∈ G :=
      (L_le_C F Q).absolutelyContinuous.ae_le (hG Q hQ).2
    rw [lintegral_congr_ae (hcL.mono (fun R hR => ih R hR))]
    rw [show iterate (doob F G) f (n + 1) Q =
      ∫⁻ R, iterate (doob F G) f n R ∂doob F G Q from rfl,
      doob_integral F G hmG Q hQ _ (hmi n)]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (core_h_positive F Q (hG Q hQ).1)
      (h_finite F Q), one_mul]
    rfl

abbrev Cemetery := PDescriptor ⊕ Unit

private instance cemetery_singletons : MeasurableSingletonClass Cemetery where
  measurableSet_singleton x := by
    cases x with
    | inl Q => simpa only [Set.image_singleton] using
        (measurableSet_singleton Q).inl_image (β := Unit)
    | inr u => simpa only [Set.image_singleton] using
        (measurableSet_singleton u).inr_image (α := PDescriptor)

/-- The lost row mass is sent to an absorbing cemetery state. -/
def cemetery (M : Kernel PDescriptor PDescriptor) : Kernel Cemetery Cemetery :=
  let live : Kernel PDescriptor Cemetery := M.map Sum.inl +
    ⟨fun Q => (1 - M Q Set.univ) • Measure.dirac (Sum.inr ()),
      (measurable_const.sub (M.measurable_coe MeasurableSet.univ)).smul_measure _⟩
  ⟨Sum.elim live (fun _ => Measure.dirac (Sum.inr ())),
    live.measurable.sumElim measurable_const⟩

private theorem cemetery_markov (M : Kernel PDescriptor PDescriptor)
    (hsub : ∀ Q, M Q Set.univ ≤ 1) : IsMarkovKernel (cemetery M) := by
  refine ⟨fun x => ⟨?_⟩⟩
  cases x with
  | inr x => simp [cemetery]
  | inl Q =>
    change (((M.map (Sum.inl : PDescriptor → Cemetery)) Q +
      (1 - M Q Set.univ) • Measure.dirac (Sum.inr ()) : Measure Cemetery) Set.univ) = 1
    rw [Measure.add_apply, Kernel.map_apply _ measurable_inl _]
    rw [Measure.map_apply measurable_inl MeasurableSet.univ]
    simp only [Set.preimage_univ, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact add_tsub_cancel_of_le (hsub Q)

/-- The full Ionescu-Tulcea law uses the Markov extension and the original initial margin. -/
def killedTrajectory (F : CommonFlow) (M : Kernel PDescriptor PDescriptor)
    (hsub : ∀ Q, M Q Set.univ ≤ 1) : Measure (ℕ → Cemetery) :=
  letI := cemetery_markov M hsub
  Kernel.trajMeasure (F.nuP.map Sum.inl) (fun n =>
    (cemetery M).comap
      (fun x : (i : Finset.Iic n) → Cemetery => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _))


private theorem doob_killing_bound (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (haG : ∀ᵐ Q ∂F.nuP, Q ∈ G)
    (hsub : ∀ Q, doob F G Q Set.univ ≤ 1) :
    ∀ᵐ Q ∂F.nuP,
      (1 - doob F G Q Set.univ).toReal = delta F Q / h F Q ∧
      (2 / 3 : ℝ) * excess Q ≤ (1 - doob F G Q Set.univ).toReal := by
  filter_upwards [haG, (common_flow_signed_h F).2] with Q hQ hh
  have hhpos : 0 < h F Q := lt_of_lt_of_le (by norm_num) hh.1
  have hi := doob_integral F G hmG Q hQ (fun _ => 1) measurable_const
  simp only [lintegral_one, mul_one] at hi
  have hir := congrArg ENNReal.toReal hi
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv] at hir
  have hk : (1 - doob F G Q Set.univ).toReal = delta F Q / h F Q := by
    rw [ENNReal.toReal_sub_of_le (hsub Q) (by simp), ENNReal.toReal_one, hir]
    change 1 - (h F Q)⁻¹ * (normalizedAction F (threeStepAverage F) Q).toReal =
      (h F Q - (normalizedAction F (threeStepAverage F) Q).toReal) / h F Q
    field_simp [ne_of_gt hhpos]
  refine ⟨hk, ?_⟩
  rw [hk]
  apply (le_div_iff₀ hhpos).mpr
  have hm := mul_le_mul_of_nonneg_left hh.2.1 hh.2.2.1
  nlinarith [hh.2.2.2.2.1]

private theorem doob_row_positive (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G)
    (hG : ∀ Q ∈ G, CoreAt F Q ∧ ∀ᵐ R ∂F.C Q, R ∈ G)
    (Q : PDescriptor) (hQ : Q ∈ G) : 0 < doob F G Q Set.univ := by
  have hlower : ∀ᵐ R ∂F.L Q, (3 / 25 : ℝ≥0∞) ≤ threeStepAverage F R := by
    filter_upwards [(L_le_C F Q).absolutelyContinuous.ae_le (hG Q hQ).2] with R hR
    apply (ENNReal.toReal_le_toReal (by finiteness) (h_finite F R)).mp
    simpa only [h, ENNReal.toReal_div, ENNReal.toReal_ofNat] using (hG R hR).1.2.1
  have hm : (1 / 5 : ℝ≥0∞) ≤ F.L Q Set.univ := by
    have hb := (common_flow_operator_bounds F).1 Q
    have hs := Measure.le_iff.mp hb.1 Set.univ MeasurableSet.univ
    simpa only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hs
  have hi : (3 / 25 : ℝ≥0∞) * (1 / 5 : ℝ≥0∞) ≤
      ∫⁻ R, threeStepAverage F R ∂F.L Q := by
    calc
      _ ≤ (3 / 25 : ℝ≥0∞) * F.L Q Set.univ := mul_le_mul_of_nonneg_left hm bot_le
      _ = ∫⁻ _ : PDescriptor, (3 / 25 : ℝ≥0∞) ∂F.L Q := by rw [lintegral_const]
      _ ≤ _ := lintegral_mono_ae hlower
  have hip : (∫⁻ R, threeStepAverage F R ∂F.L Q) ≠ 0 := by
    intro hz
    rw [hz] at hi
    have hh := nonpos_iff_eq_zero.mp hi
    exact (mul_ne_zero (by norm_num : (3 / 25 : ℝ≥0∞) ≠ 0)
      (by norm_num : (1 / 5 : ℝ≥0∞) ≠ 0)) hh
  have he := doob_integral F G hmG Q hQ (fun _ => 1) measurable_const
  simp only [lintegral_one, mul_one] at he
  rw [he, normalizedAction]
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ENNReal.inv_ne_zero.mpr (h_finite F Q))
    (mul_ne_zero (ENNReal.inv_ne_zero.mpr (by unfold endpointRate; finiteness)) hip))

/-- A genuine substochastic Doob kernel, finite conjugacy and the original survival limit. -/
theorem common_flow_doob_survival (F : CommonFlow) :
    ∃ (G : Set PDescriptor) (hsub : ∀ Q, doob F G Q Set.univ ≤ 1),
      MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
      IsMarkovKernel (cemetery (doob F G)) ∧
      IsProbabilityMeasure (killedTrajectory F (doob F G) hsub) ∧
      (∀ Q, doob F G Q ≪ F.C Q) ∧
      (∀ Q ∈ G, CoreAt F Q ∧ (∀ᵐ R ∂F.C Q, R ∈ G)) ∧
      (∀ (f : PDescriptor → ℝ≥0∞), Measurable f → ∀ n Q, Q ∈ G →
        normalizedIterate F (fun R => threeStepAverage F R * f R) n Q =
          threeStepAverage F Q * iterate (doob F G) f n Q) ∧
      (∀ᵐ Q ∂F.nuP, Antitone (fun n => iterate (doob F G) (fun _ => 1) n Q) ∧
        Tendsto (fun n => iterate (doob F G) (fun _ => 1) n Q) atTop
          (𝓝 (q F Q / threeStepAverage F Q))) ∧
      (∀ Q ∈ G, 0 < doob F G Q Set.univ) ∧
      (∀ᵐ Q ∂F.nuP,
        (1 - doob F G Q Set.univ).toReal = delta F Q / h F Q ∧
        (2 / 3 : ℝ) * excess Q ≤ (1 - doob F G Q Set.univ).toReal) ∧
      (∀ᵐ Q ∂F.nuP, endpointRate⁻¹ • F.L Q ≤
        ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q) := by
  obtain ⟨G, hmG, haG, hG⟩ := common_flow_absorbing_core F
  have hc : ∀ Q ∈ G, CoreAt F Q ∧ ∀ᵐ R ∂F.C Q, R ∈ G :=
    fun Q hQ => ⟨(hG Q hQ).1, ((hG Q hQ).2).mono (fun R hR => hR.1)⟩
  have hsub := doob_subprobability F G hmG (fun Q hQ => (hc Q hQ).1)
  have hpath : IsProbabilityMeasure (killedTrajectory F (doob F G) hsub) := by
    letI := cemetery_markov (doob F G) hsub
    haveI : IsProbabilityMeasure (F.nuP.map (Sum.inl : PDescriptor → Cemetery)) :=
      Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
    unfold killedTrajectory
    infer_instance
  refine ⟨G, hsub, hmG, haG, cemetery_markov (doob F G) hsub, hpath,
    ?_, hc, doob_conjugacy F G hmG hc, ?_, doob_row_positive F G hmG hc,
    doob_killing_bound F G hmG haG hsub, completion_distortion F⟩
  · intro Q
    exact (Kernel.withDensity_absolutelyContinuous (κ := F.L) _ Q).trans
      (L_le_C F Q).absolutelyContinuous
  · filter_upwards [haG, (common_flow_q_limit F).2] with Q hQ hlim
    have he (n : ℕ) : iterate (doob F G) (fun _ => 1) n Q =
        (threeStepAverage F Q)⁻¹ * qIterate F n Q := by
      have hi := doob_conjugacy F G hmG hc (fun _ => 1) measurable_const n Q hQ
      simp only [mul_one] at hi
      change qIterate F n Q = threeStepAverage F Q * iterate (doob F G) (fun _ => 1) n Q at hi
      rw [hi, ENNReal.inv_mul_cancel_left (core_h_positive F Q (hc Q hQ).1)
        (h_finite F Q)]
    refine ⟨?_, ?_⟩
    · intro m n hmn
      change iterate (doob F G) (fun _ => 1) n Q ≤ iterate (doob F G) (fun _ => 1) m Q
      rw [he m, he n]
      exact mul_le_mul_of_nonneg_left (hlim.1 hmn) bot_le
    simp only [he]
    have ht := ENNReal.Tendsto.const_mul hlim.2.1
      (Or.inr (ENNReal.inv_ne_top.mpr (core_h_positive F Q (hc Q hQ).1)))
    simpa only [div_eq_mul_inv, mul_comm] using ht

private def homogeneousStep {S : Type*} [MeasurableSpace S] (K : Kernel S S) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → S) S :=
  K.comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

private instance homogeneousStep_markov {S : Type*} [MeasurableSpace S]
    (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) : IsMarkovKernel (homogeneousStep K n) := by
  unfold homogeneousStep
  infer_instance

private def homogeneousLaw {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (K : Kernel S S) [IsMarkovKernel K] : Measure (ℕ → S) :=
  Kernel.trajMeasure μ (homogeneousStep K)

private instance homogeneousLaw_probability {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K] :
    IsProbabilityMeasure (homogeneousLaw μ K) := by
  unfold homogeneousLaw
  infer_instance

private def actionIterate {S : Type*} [MeasurableSpace S] (K : Kernel S S)
    (f : S → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0 => f
  | n + 1 => fun x => ∫⁻ y, actionIterate K f n y ∂K x

private theorem actionIterate_measurable {S : Type*} [MeasurableSpace S]
    (K : Kernel S S) [IsSFiniteKernel K] (f : S → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    Measurable (actionIterate K f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.lintegral_kernel

private theorem actionIterate_eq_iterate (K : Kernel PDescriptor PDescriptor)
    (f : PDescriptor → ℝ≥0∞) (n : ℕ) : actionIterate K f n = iterate K f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [actionIterate, iterate, ih]

private theorem actionIterate_commute {S : Type*} [MeasurableSpace S]
    (K : Kernel S S) [IsSFiniteKernel K] (f : S → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    actionIterate K (fun x => ∫⁻ y, f y ∂K x) n = actionIterate K f (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [actionIterate, ih]

private theorem homogeneous_initial {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (K : Kernel S S) [IsMarkovKernel K] :
    (homogeneousLaw μ K).map (fun x => x 0) = μ := by
  have hp : (homogeneousLaw μ K).map (frestrictLe 0) =
      μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => S)).symm := by
    unfold homogeneousLaw Kernel.trajMeasure
    rw [Measure.map_comp _ _ (measurable_frestrictLe _), Kernel.traj_map_frestrictLe,
      Kernel.partialTraj_self, Measure.id_comp]
  have he : (fun x : ℕ → S => x 0) =
      (fun u : (i : Finset.Iic (0 : ℕ)) → S => u ⟨0, by simp⟩) ∘ frestrictLe 0 := rfl
  rw [he, ← Measure.map_map (μ := homogeneousLaw μ K) (f := frestrictLe 0)
    (g := fun u : (i : Finset.Iic (0 : ℕ)) → S => u ⟨0, by simp⟩)
    (by fun_prop) (measurable_frestrictLe 0), hp,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  have hid : (fun u : (i : Finset.Iic (0 : ℕ)) → S => u ⟨0, by simp⟩) ∘
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => S)).symm = id := by
    funext x
    simp [MeasurableEquiv.piUnique, Equiv.piUnique, uniqueElim_const]
  rw [hid, Measure.map_id]

private theorem homogeneous_integral {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K]
    (n : ℕ) (f : S → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (x n) ∂homogeneousLaw μ K) = ∫⁻ x, actionIterate K f n x ∂μ := by
  induction n generalizing f with
  | zero =>
    rw [← lintegral_map hf (measurable_pi_apply 0), homogeneous_initial]
    rfl
  | succ n ih =>
    have hk := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => S) (μ₀ := μ) (κ := homogeneousStep K) (a := n)
    have hm : Measurable (fun x : ((i : Finset.Iic n) → S) × S => f x.2) :=
      hf.comp measurable_snd
    calc
      _ = ∫⁻ x, f x.2 ∂((homogeneousLaw μ K).map
          (fun x => (frestrictLe n x, x (n + 1)))) :=
        (lintegral_map hm (by fun_prop)).symm
      _ = ∫⁻ x, f x.2 ∂((homogeneousLaw μ K).map (frestrictLe n) ⊗ₘ homogeneousStep K n) := by
        rw [homogeneousLaw, ← hk]
      _ = ∫⁻ x, ∫⁻ y, f y ∂K (x ⟨n, by simp⟩)
          ∂(homogeneousLaw μ K).map (frestrictLe n) := by
        rw [Measure.lintegral_compProd hm]
        rfl
      _ = ∫⁻ x, ∫⁻ y, f y ∂K (x n) ∂homogeneousLaw μ K :=
        lintegral_map (hf.lintegral_kernel.comp (measurable_pi_apply _))
          (measurable_frestrictLe n)
      _ = ∫⁻ x, actionIterate K (fun x => ∫⁻ y, f y ∂K x) n x ∂μ :=
        ih _ hf.lintegral_kernel
      _ = _ := by rw [actionIterate_commute K f hf n]

/-- The path remains live at every finite time. -/
def immortal : Set (ℕ → Cemetery) := {x | ∀ n, x n ≠ Sum.inr ()}

private def liveTest : Cemetery → ℝ≥0∞ := Sum.elim (fun _ => 1) (fun _ => 0)

private theorem liveTest_measurable : Measurable liveTest :=
  measurable_const.sumElim measurable_const

private theorem cemetery_iterate_lift (M : Kernel PDescriptor PDescriptor)
    (hsub : ∀ Q, M Q Set.univ ≤ 1) (f : PDescriptor → ℝ≥0∞)
    (hf : Measurable f) (n : ℕ) :
    actionIterate (cemetery M) (Sum.elim f (fun _ => 0)) n =
      Sum.elim (iterate M f n) (fun _ => 0) := by
  letI := cemetery_markov M hsub
  haveI : IsFiniteKernel M := ⟨⟨1, by simp, hsub⟩⟩
  have hm (n : ℕ) : Measurable (iterate M f n) := by
    induction n with
    | zero => exact hf
    | succ n ih => exact ih.lintegral_kernel
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    cases x with
    | inr x =>
      rw [actionIterate, ih]
      change (∫⁻ y, Sum.elim (iterate M f n) (fun _ => 0) y
        ∂Measure.dirac (Sum.inr ())) = 0
      rw [lintegral_dirac]
      rfl
    | inl Q =>
      rw [actionIterate, ih]
      change (∫⁻ y, Sum.elim (iterate M f n) (fun _ => 0) y
        ∂((M.map (Sum.inl : PDescriptor → Cemetery)) Q +
          (1 - M Q Set.univ) • Measure.dirac (Sum.inr ()))) = _
      rw [lintegral_add_measure, lintegral_smul_measure,
        lintegral_dirac]
      simp only [Sum.elim_inr, mul_zero, add_zero]
      rw [Kernel.map_apply _ measurable_inl, lintegral_map
        ((hm n).sumElim measurable_const) measurable_inl]
      simp only [Sum.elim_inl, smul_eq_mul, mul_zero, add_zero]
      rfl

private theorem cemetery_iterate_live (M : Kernel PDescriptor PDescriptor)
    (hsub : ∀ Q, M Q Set.univ ≤ 1) (n : ℕ) :
    actionIterate (cemetery M) liveTest n =
      Sum.elim (iterate M (fun _ => 1) n) (fun _ => 0) :=
  cemetery_iterate_lift M hsub _ measurable_const n

private def cemeteryLaw (μ : Measure Cemetery) (M : Kernel PDescriptor PDescriptor)
    (hsub : ∀ Q, M Q Set.univ ≤ 1) : Measure (ℕ → Cemetery) :=
  letI := cemetery_markov M hsub
  homogeneousLaw μ (cemetery M)

set_option maxHeartbeats 800000 in
private theorem cemetery_path_antitone (μ : Measure Cemetery) [IsProbabilityMeasure μ]
    (M : Kernel PDescriptor PDescriptor) (hsub : ∀ Q, M Q Set.univ ≤ 1) :
    ∀ᵐ x ∂cemeteryLaw μ M hsub, Antitone (fun n => x n ≠ Sum.inr ()) := by
  letI := cemetery_markov M hsub
  change ∀ᵐ x ∂homogeneousLaw μ (cemetery M), Antitone (fun n => x n ≠ Sum.inr ())
  have hs (n : ℕ) : ∀ᵐ x ∂homogeneousLaw μ (cemetery M),
      x n = Sum.inr () → x (n + 1) = Sum.inr () := by
    have hk := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => Cemetery) (μ₀ := μ) (κ := homogeneousStep (cemetery M)) (a := n)
    have hp : MeasurableSet {x : ((i : Finset.Iic n) → Cemetery) × Cemetery |
        x.1 ⟨n, by simp⟩ = Sum.inr () → x.2 = Sum.inr ()} := by
      have hm : Measurable (fun x : ((i : Finset.Iic n) → Cemetery) × Cemetery =>
          x.1 ⟨n, by simp⟩) := (measurable_pi_apply _).comp measurable_fst
      convert (hm.eq_const (Sum.inr () : Cemetery)).setOf.compl.union
        (measurable_snd.eq_const (Sum.inr () : Cemetery)).setOf using 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
    have ha : ∀ᵐ x ∂((homogeneousLaw μ (cemetery M)).map (frestrictLe n) ⊗ₘ
        homogeneousStep (cemetery M) n),
        x.1 ⟨n, by simp⟩ = Sum.inr () → x.2 = Sum.inr () := by
      apply Measure.ae_compProd_of_ae_ae hp
      filter_upwards [] with w
      by_cases hw : w ⟨n, by simp⟩ = Sum.inr ()
      · change ∀ᵐ y ∂cemetery M (w ⟨n, by simp⟩),
          w ⟨n, by simp⟩ = Sum.inr () → y = Sum.inr ()
        rw [hw]
        simp only [cemetery, Sum.elim_inr]
        filter_upwards [ae_eq_dirac (fun y : Cemetery => y)] with y hy
        exact fun _ => hy
      · exact Filter.Eventually.of_forall (fun _ h => (hw h).elim)
    change ∀ᵐ x ∂((Kernel.trajMeasure (X := fun _ => Cemetery) μ
      (homogeneousStep (cemetery M))).map
      (frestrictLe n) ⊗ₘ homogeneousStep (cemetery M) n), _ at ha
    rw [hk] at ha
    exact (ae_map_iff (by fun_prop) hp).mp ha
  filter_upwards [ae_all_iff.mpr hs] with x hx
  apply antitone_nat_of_succ_le
  intro n hn hdead
  exact hn (hx n hdead)

set_option maxHeartbeats 800000 in
private theorem cemetery_survival (μ : Measure PDescriptor) [IsProbabilityMeasure μ]
    (M : Kernel PDescriptor PDescriptor) (hsub : ∀ Q, M Q Set.univ ≤ 1) :
    cemeteryLaw (μ.map Sum.inl) M hsub immortal =
      ⨅ n, ∫⁻ Q, iterate M (fun _ => 1) n Q ∂μ := by
  letI := cemetery_markov M hsub
  change homogeneousLaw (μ.map Sum.inl) (cemetery M) immortal = _
  haveI : IsProbabilityMeasure (μ.map (Sum.inl : PDescriptor → Cemetery)) :=
    Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  have he (n : ℕ) : homogeneousLaw (μ.map Sum.inl) (cemetery M)
      {x | x n ≠ Sum.inr ()} = ∫⁻ Q, iterate M (fun _ => 1) n Q ∂μ := by
    have hset : MeasurableSet {x : ℕ → Cemetery | x n ≠ Sum.inr ()} :=
      ((measurableSet_singleton (Sum.inr () : Cemetery)).preimage
        (measurable_pi_apply n)).compl
    have ht : (fun x : ℕ → Cemetery => liveTest (x n)) =
        Set.indicator {x | x n ≠ Sum.inr ()} (fun _ => (1 : ℝ≥0∞)) := by
      funext x
      cases hx : x n with
      | inl Q => simp [liveTest, hx]
      | inr u => cases u; simp [liveTest, hx]
    rw [← setLIntegral_one]
    rw [← lintegral_indicator hset, ← ht,
      homogeneous_integral _ _ n liveTest liveTest_measurable,
      cemetery_iterate_live M hsub]
    haveI : IsFiniteKernel M := ⟨⟨1, by simp, hsub⟩⟩
    have hm : Measurable (iterate M (fun _ => 1) n) := by
      rw [← actionIterate_eq_iterate]
      exact actionIterate_measurable M (fun _ => 1) measurable_const n
    rw [lintegral_map (hm.sumElim measurable_const) measurable_inl]
    rfl
  have hi : immortal = ⋂ n, {x : ℕ → Cemetery | x n ≠ Sum.inr ()} := by
    ext x
    simp only [immortal, Set.mem_setOf_eq, Set.mem_iInter]
  have hanti : ∀ᵐ x ∂homogeneousLaw (μ.map Sum.inl) (cemetery M),
      Antitone (fun n => x n ≠ Sum.inr ()) :=
    cemetery_path_antitone (μ.map Sum.inl) M hsub
  have hfin : homogeneousLaw (μ.map Sum.inl) (cemetery M)
      {x | x 0 ≠ Sum.inr ()} ≠ ∞ := measure_ne_top _ _
  rw [hi]
  calc
    _ = ⨅ n, homogeneousLaw (μ.map Sum.inl) (cemetery M)
        {x | x n ≠ Sum.inr ()} :=
      measure_iInter_of_ae_antitone (s := fun n => {x : ℕ → Cemetery | x n ≠ Sum.inr ()})
        hanti (fun n => (((measurableSet_singleton (Sum.inr () : Cemetery)).preimage
          (measurable_pi_apply n)).compl).nullMeasurableSet) ⟨0, hfin⟩
    _ = _ := by simp_rw [he]

/-- The lawful cemetery trajectory from a specified original descriptor. -/
def startedTrajectory (M : Kernel PDescriptor PDescriptor)
    (hsub : ∀ Q, M Q Set.univ ≤ 1) (Q : PDescriptor) : Measure (ℕ → Cemetery) :=
  cemeteryLaw (Measure.dirac (Sum.inl Q)) M hsub

private theorem doob_finite_positive (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (hsub : ∀ Q, doob F G Q Set.univ ≤ 1)
    (hc : ∀ Q ∈ G, CoreAt F Q ∧ ∀ᵐ R ∂F.C Q, R ∈ G) :
    ∀ n Q, Q ∈ G → 0 < iterate (doob F G) (fun _ => 1) n Q := by
  haveI : IsFiniteKernel (doob F G) := ⟨⟨1, by simp, hsub⟩⟩
  have hm (n : ℕ) : Measurable (iterate (doob F G) (fun _ => 1) n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih => exact ih.lintegral_kernel
  intro n
  induction n with
  | zero => intro Q hQ; simp [iterate]
  | succ n ih =>
    intro Q hQ
    apply pos_iff_ne_zero.mpr
    intro hz
    change (∫⁻ R, iterate (doob F G) (fun _ => 1) n R ∂doob F G Q) = 0 at hz
    have hzero := (lintegral_eq_zero_iff (hm n)).mp hz
    have hAC : doob F G Q ≪ F.C Q :=
      (Kernel.withDensity_absolutelyContinuous (κ := F.L) _ Q).trans
        (L_le_C F Q).absolutelyContinuous
    have hfalse : ∀ᵐ R ∂doob F G Q, False := by
      filter_upwards [hAC.ae_le (hc Q hQ).2, hzero] with R hR hz
      exact (ne_of_gt (ih R hR)) hz
    have hm0 : doob F G Q Set.univ = 0 := by simpa using ae_iff.mp hfalse
    exact (ne_of_gt (doob_row_positive F G hmG hc Q hQ)) hm0

/-- Infinite survival is the earned q/h, and its original-margin mass is the native atom. -/
theorem common_flow_immortal_survival (F : CommonFlow) :
    ∃ (G : Set PDescriptor) (hsub : ∀ Q, doob F G Q Set.univ ≤ 1),
      MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
      (∀ Q ∈ G, ∀ n, 0 < iterate (doob F G) (fun _ => 1) n Q) ∧
      (∀ᵐ Q ∂F.nuP,
        startedTrajectory (doob F G) hsub Q immortal = q F Q / threeStepAverage F Q ∧
        startedTrajectory (doob F G) hsub Q immortal =
          (if Q = nativeEndpoint .p true then 1 else 0)) ∧
      killedTrajectory F (doob F G) hsub immortal = F.nuP {nativeEndpoint .p true} := by
  obtain ⟨G, hsub, hmG, haG, hm, hp, hac, hc, hconj, hlim, hpos, hk, hdist⟩ :=
    common_flow_doob_survival F
  haveI : IsFiniteKernel (doob F G) := ⟨⟨1, by simp, hsub⟩⟩
  have hmeas (n : ℕ) : Measurable (iterate (doob F G) (fun _ => 1) n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih => exact ih.lintegral_kernel
  have hrow (Q : PDescriptor) : startedTrajectory (doob F G) hsub Q immortal =
      ⨅ n, iterate (doob F G) (fun _ => 1) n Q := by
    have hs := cemetery_survival (Measure.dirac Q) (doob F G) hsub
    rw [Measure.map_dirac] at hs
    simp_rw [lintegral_dirac] at hs
    exact hs
  have hd := (common_flow_upper_endpoint_limits F).1
  refine ⟨G, hsub, hmG, haG,
    (fun Q hQ n => doob_finite_positive F G hmG hsub hc n Q hQ), ?_, ?_⟩
  · filter_upwards [hlim, hd] with Q hl hd
    have he := iInf_eq_of_tendsto hl.1 hl.2
    rw [hrow Q, he]
    exact ⟨rfl, hd.2⟩
  · have he : killedTrajectory F (doob F G) hsub immortal =
        ⨅ n, ∫⁻ Q, iterate (doob F G) (fun _ => 1) n Q ∂F.nuP :=
      cemetery_survival F.nuP (doob F G) hsub
    have hant : Antitone (fun n => ∫⁻ Q, iterate (doob F G) (fun _ => 1) n Q ∂F.nuP) := by
      intro m n hmn
      exact lintegral_mono_ae (hlim.mono (fun Q hQ => hQ.1 hmn))
    have hdom (n : ℕ) : ∀ᵐ Q ∂F.nuP,
        iterate (doob F G) (fun _ => 1) n Q ≤ 1 :=
      hlim.mono (fun Q hQ => hQ.1 (Nat.zero_le n))
    have ht := tendsto_lintegral_of_dominated_convergence (fun _ : PDescriptor => 1)
      hmeas hdom (by simp) (hlim.mono (fun Q hQ => hQ.2))
    have hi : (∫⁻ Q, q F Q / threeStepAverage F Q ∂F.nuP) =
        F.nuP {nativeEndpoint .p true} := by
      rw [lintegral_congr_ae (hd.mono (fun Q hQ => hQ.2))]
      simpa only [Set.indicator, Set.mem_singleton_iff, one_mul] using
        lintegral_indicator_const (μ := F.nuP)
          (measurableSet_singleton (nativeEndpoint .p true)) 1
    rw [hi] at ht
    exact he.trans (iInf_eq_of_tendsto hant ht)

private theorem at_positive_atom {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (a : S) {p : S → Prop} (hp : ∀ᵐ x ∂μ, p x) (ha : μ {a} ≠ 0) : p a := by
  by_contra h
  have hsub : {a} ⊆ {x | ¬ p x} := by
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact h
  exact ha (le_antisymm ((measure_mono hsub).trans_eq (ae_iff.mp hp)) bot_le)

private theorem measure_dirac_of_support {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (a : S) (ha : ∀ᵐ x ∂μ, x = a) :
    μ = Measure.dirac a := by
  have hm : μ.map (id : S → S) = μ.map (fun _ => a) := Measure.map_congr ha
  rw [Measure.map_id, Measure.map_const, measure_univ, one_smul] at hm
  exact hm

private theorem homogeneous_constant_mass {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsProbabilityMeasure μ]
    (K : Kernel S S) [IsMarkovKernel K] (a : S) (ha : K a = Measure.dirac a) :
    homogeneousLaw μ K {fun _ => a} = μ {a} := by
  let E (n : ℕ) : Set (ℕ → S) :=
    (fun x (i : Fin (n + 1)) => x i.1) ⁻¹' {fun _ => a}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_singleton _).preimage (by fun_prop)
  have he (n : ℕ) : homogeneousLaw μ K (E n) = μ {a} := by
    rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    change ((Kernel.trajMeasure (X := fun _ => S) μ
      (fun n => K.comap (fun u : Finset.Iic n → S =>
        u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _))).map
      (fun x (i : Fin (n + 1)) => x i.1)) {fun _ => a} = _
    have hp := MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton μ K n
      (fun _ => a)
    simpa [ha] using hp
  have hant : Antitone E := by
    intro m n hmn x hx
    change (fun i : Fin (n + 1) => x i.1) = (fun _ => a) at hx
    change (fun i : Fin (m + 1) => x i.1) = (fun _ => a)
    funext i
    exact congrFun hx ⟨i.1, lt_of_lt_of_le i.2 (Nat.succ_le_succ hmn)⟩
  have hi : {fun _ : ℕ => a} = ⋂ n, E n := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_singleton_iff.mp hx]
      exact Set.mem_iInter.mpr (fun _ => rfl)
    · intro hx
      apply Set.mem_singleton_iff.mpr
      funext n
      exact congrFun (Set.mem_iInter.mp hx n) (Fin.last n)
  rw [hi, hant.measure_iInter (fun n => (hE n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  simp_rw [he, iInf_const]

private theorem native_absorption (F : CommonFlow)
    (ha : F.nuP {nativeEndpoint .p true} ≠ 0) :
    F.C (nativeEndpoint .p true) = Measure.dirac (nativeEndpoint .p true) ∧
    F.L (nativeEndpoint .p true) = endpointRate • Measure.dirac (nativeEndpoint .p true) := by
  let a := nativeEndpoint .p true
  have hd := at_positive_atom F.nuP a (common_flow_upper_endpoint_limits F).1 ha
  have hq : q F a ≠ 0 := by
    rw [hd.1, if_pos rfl]
    norm_num [endpointCompletion]
  have ht := (at_positive_atom F.nuP a (common_flow_surviving_transitions F) ha) hq
  have hc : ∀ᵐ R ∂F.C a, R = a :=
    Kernel.ae_comp_of_ae_ae (measurableSet_singleton a)
      (ht.2.2.mono (fun _ hW => hW.2))
  have he := measure_dirac_of_support (F.C a) a hc
  exact ⟨he, ht.2.1.trans (congrArg (fun μ => endpointRate • μ) he)⟩

private theorem doob_native_absorption (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (haG : ∀ᵐ Q ∂F.nuP, Q ∈ G)
    (ha : F.nuP {nativeEndpoint .p true} ≠ 0) :
    doob F G (nativeEndpoint .p true) = Measure.dirac (nativeEndpoint .p true) := by
  let a := nativeEndpoint .p true
  have hGa := at_positive_atom F.nuP a haG ha
  have habs := native_absorption F ha
  have hpos : threeStepAverage F a ≠ 0 := by
    intro hz
    have hh := (at_positive_atom F.nuP a (common_flow_signed_h F).2 ha).1
    simp only [h, hz, ENNReal.toReal_zero] at hh
    norm_num at hh
  have he := doob_integral F G hmG a hGa (fun _ => 1) measurable_const
  simp only [lintegral_one, mul_one] at he
  rw [normalizedAction, habs.2, lintegral_smul_measure, lintegral_dirac] at he
  have hz : endpointRate⁻¹ * endpointRate = 1 :=
    ENNReal.inv_mul_cancel (by norm_num [endpointRate]) (by unfold endpointRate; finiteness)
  change doob F G a Set.univ = (threeStepAverage F a)⁻¹ *
    (endpointRate⁻¹ * (endpointRate * threeStepAverage F a)) at he
  rw [← mul_assoc endpointRate⁻¹ endpointRate (threeStepAverage F a), hz, one_mul,
    ENNReal.inv_mul_cancel hpos (h_finite F a)] at he
  haveI : IsProbabilityMeasure (doob F G a) := ⟨he⟩
  have hAC : doob F G a ≪ F.C a :=
    (Kernel.withDensity_absolutelyContinuous (κ := F.L) _ a).trans
      (L_le_C F a).absolutelyContinuous
  rw [habs.1] at hAC
  exact measure_dirac_of_support (doob F G a) a
    (hAC.ae_le (ae_eq_dirac (fun R : PDescriptor => R)))

/-- The original stationary unweighted return trajectory. -/
def originalTrajectory (F : CommonFlow) : Measure (ℕ → PDescriptor) :=
  homogeneousLaw F.nuP F.C

/-- Inclusion of a complete original trajectory into the cemetery path space. -/
def includePath (x : ℕ → PDescriptor) : ℕ → Cemetery := fun n => Sum.inl (x n)

/-- The original nonnegative defect series, with zero defect at the cemetery. -/
def pathDefect (x : ℕ → Cemetery) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (Sum.elim excess (fun _ => 0) (x n))

private theorem doob_survival_fixed (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (haG : ∀ᵐ Q ∂F.nuP, Q ∈ G)
    (hsub : ∀ Q, doob F G Q Set.univ ≤ 1) :
    ∀ n, ∀ᵐ Q ∂F.nuP,
      iterate (doob F G) (fun R => q F R / threeStepAverage F R) n Q =
        q F Q / threeStepAverage F Q := by
  haveI : IsFiniteKernel (doob F G) := ⟨⟨1, by simp, hsub⟩⟩
  have hs : Measurable (fun R => q F R / threeStepAverage F R) :=
    (common_flow_q_limit F).1.div (h_measurable F)
  have hpos : ∀ᵐ Q ∂F.nuP, threeStepAverage F Q ≠ 0 := by
    filter_upwards [(common_flow_signed_h F).2] with Q hQ
    intro hz
    have hh := hQ.1
    simp only [h, hz, ENNReal.toReal_zero] at hh
    norm_num at hh
  have hr := Measure.ae_ae_of_ae_comp (κ := F.C)
    ((common_flow_word_iteration F).1.symm ▸ hpos)
  have hfixed : ∀ᵐ Q ∂F.nuP,
      (∫⁻ R, q F R / threeStepAverage F R ∂doob F G Q) =
        q F Q / threeStepAverage F Q := by
    filter_upwards [haG, hr, (common_flow_q_limit F).2] with Q hQ hr hq
    rw [doob_integral F G hmG Q hQ _ hs]
    have he : normalizedAction F
        (fun R => threeStepAverage F R * (q F R / threeStepAverage F R)) Q =
        normalizedAction F (q F) Q := by
      unfold normalizedAction
      congr 1
      apply lintegral_congr_ae
      have hr' : ∀ᵐ R ∂F.L Q, threeStepAverage F R ≠ 0 :=
        (L_le_C F Q).absolutelyContinuous.ae_le hr
      exact hr'.mono (fun R hR => ENNReal.mul_div_cancel hR (h_finite F R))
    rw [he, hq.2.2.2, div_eq_mul_inv, mul_comm]
  intro n
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    have hi := Measure.ae_ae_of_ae_comp (κ := F.C)
      ((common_flow_word_iteration F).1.symm ▸ ih)
    filter_upwards [hi, hfixed] with Q hi hQ
    change (∫⁻ R, iterate (doob F G) _ n R ∂doob F G Q) = _
    have hAC : doob F G Q ≪ F.C Q :=
      (Kernel.withDensity_absolutelyContinuous (κ := F.L) _ Q).trans
        (L_le_C F Q).absolutelyContinuous
    exact (lintegral_congr_ae (hAC.ae_le hi)).trans hQ

private theorem terminal_survival_mass (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (haG : ∀ᵐ Q ∂F.nuP, Q ∈ G)
    (hsub : ∀ Q, doob F G Q Set.univ ≤ 1) (n : ℕ) :
    (∫⁻ x, Sum.elim (fun Q => q F Q / threeStepAverage F Q) (fun _ => 0) (x n)
      ∂killedTrajectory F (doob F G) hsub) = F.nuP {nativeEndpoint .p true} := by
  letI := cemetery_markov (doob F G) hsub
  haveI : IsFiniteKernel (doob F G) := ⟨⟨1, by simp, hsub⟩⟩
  haveI : IsProbabilityMeasure (F.nuP.map (Sum.inl : PDescriptor → Cemetery)) :=
    Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  have hs : Measurable (fun Q => q F Q / threeStepAverage F Q) :=
    (common_flow_q_limit F).1.div (h_measurable F)
  have hm : Measurable (iterate (doob F G)
      (fun Q => q F Q / threeStepAverage F Q) n) := by
    rw [← actionIterate_eq_iterate]
    exact actionIterate_measurable _ _ hs n
  rw [show killedTrajectory F (doob F G) hsub =
    homogeneousLaw (F.nuP.map Sum.inl) (cemetery (doob F G)) from rfl,
    homogeneous_integral _ _ n _ (hs.sumElim measurable_const),
    cemetery_iterate_lift _ hsub _ hs n,
    lintegral_map (hm.sumElim measurable_const) measurable_inl]
  simp only [Sum.elim_inl]
  rw [lintegral_congr_ae (doob_survival_fixed F G hmG haG hsub n),
    lintegral_congr_ae ((common_flow_upper_endpoint_limits F).1.mono (fun Q hQ => hQ.2))]
  simpa only [Set.indicator, Set.mem_singleton_iff, one_mul] using
    lintegral_indicator_const (μ := F.nuP)
      (measurableSet_singleton (nativeEndpoint .p true)) 1

private theorem map_terminal_density {S U : Type*} [MeasurableSpace S]
    [MeasurableSpace U] (μ : Measure S) (f : S → U) (hf : Measurable f)
    (w : U → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun x => w (f x))).map f = (μ.map f).withDensity w := by
  ext E hE
  rw [Measure.map_apply hf hE, withDensity_apply _ (hE.preimage hf),
    withDensity_apply _ hE, ← lintegral_indicator hE,
    lintegral_map (hw.indicator hE) hf, ← lintegral_indicator (hE.preimage hf)]
  apply lintegral_congr
  intro x
  simp only [Set.indicator, Set.mem_preimage]

/-- The immortal measure equals the actual stationary C law restricted to the upper native start. -/
theorem common_flow_immortal_identity (F : CommonFlow) :
    ∃ (G : Set PDescriptor) (hsub : ∀ Q, doob F G Q Set.univ ≤ 1),
      MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
      (∀ Q ∈ G, ∀ n, 0 < iterate (doob F G) (fun _ => 1) n Q) ∧
      (killedTrajectory F (doob F G) hsub).restrict immortal =
        F.nuP {nativeEndpoint .p true} • Measure.dirac (fun _ => Sum.inl (nativeEndpoint .p true)) ∧
      (killedTrajectory F (doob F G) hsub).restrict immortal =
        ((originalTrajectory F).restrict {x | x 0 = nativeEndpoint .p true}).map includePath ∧
      (killedTrajectory F (doob F G) hsub).restrict immortal ≤
        (originalTrajectory F).map includePath ∧
      (killedTrajectory F (doob F G) hsub).restrict immortal ≪
        (originalTrajectory F).map includePath ∧
      (∀ᵐ x ∂(killedTrajectory F (doob F G) hsub).restrict immortal, pathDefect x = 0) ∧
      (∀ R : ℝ, 0 ≤ R →
        ((killedTrajectory F (doob F G) hsub).restrict immortal).restrict
          {x | pathDefect x ≤ ENNReal.ofReal R} ≤
        ((25 / 6 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (25 * R / 9))) •
          (originalTrajectory F).map includePath) ∧
      (∀ n : ℕ,
        (killedTrajectory F (doob F G) hsub).withDensity
          (fun x => Sum.elim (fun Q => q F Q / threeStepAverage F Q) (fun _ => 0) (x n)) =
          (killedTrajectory F (doob F G) hsub).restrict immortal ∧
        ((killedTrajectory F (doob F G) hsub).map (frestrictLe n)).withDensity
          (fun x => Sum.elim (fun Q => q F Q / threeStepAverage F Q) (fun _ => 0)
            (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) =
          ((killedTrajectory F (doob F G) hsub).restrict immortal).map (frestrictLe n)) := by
  obtain ⟨G, hsub, hmG, haG, hfinite, hsrow, hmass⟩ := common_flow_immortal_survival F
  let a := nativeEndpoint .p true
  let μ := killedTrajectory F (doob F G) hsub
  let κ := cemetery (doob F G)
  letI := cemetery_markov (doob F G) hsub
  haveI : IsProbabilityMeasure (F.nuP.map (Sum.inl : PDescriptor → Cemetery)) :=
    Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  haveI : IsProbabilityMeasure μ :=
    inferInstanceAs (IsProbabilityMeasure (homogeneousLaw (F.nuP.map Sum.inl) κ))
  haveI : IsProbabilityMeasure (originalTrajectory F) :=
    inferInstanceAs (IsProbabilityMeasure (homogeneousLaw F.nuP F.C))
  have him : MeasurableSet immortal := by
    have he : immortal = ⋂ n, {x : ℕ → Cemetery | x n ≠ Sum.inr ()} := by
      ext x; simp only [immortal, Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact MeasurableSet.iInter (fun n =>
      ((measurableSet_singleton (Sum.inr () : Cemetery)).preimage
        (measurable_pi_apply n)).compl)
  have hin : Measurable includePath := by unfold includePath; fun_prop
  have hstart : originalTrajectory F {x | x 0 = a} = F.nuP {a} := by
    have hinit := homogeneous_initial F.nuP F.C
    rw [← hinit, Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton a)]
    rfl
  have hsubconst : {fun _ : ℕ => Sum.inl a} ⊆ immortal := by
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact fun _ => Sum.inl_ne_inr
  have hs : μ {fun _ => Sum.inl a} = F.nuP {a} := by
    by_cases ha : F.nuP {a} = 0
    · apply le_antisymm
      · rw [ha]
        exact (measure_mono hsubconst).trans_eq (hmass.trans ha)
      · rw [ha]; exact bot_le
    · have hM := doob_native_absorption F G hmG haG ha
      have hk : κ (Sum.inl a) = Measure.dirac (Sum.inl a) := by
        change (doob F G).map Sum.inl a +
          (1 - (doob F G a) Set.univ) • Measure.dirac (Sum.inr ()) = _
        rw [Kernel.map_apply _ measurable_inl, hM, Measure.map_dirac]
        simp [a]
      have hp := homogeneous_constant_mass (F.nuP.map Sum.inl) κ (Sum.inl a) hk
      have hpre : (Sum.inl : PDescriptor → Cemetery) ⁻¹' {Sum.inl a} = {a} := by
        ext Q; simp
      rw [Measure.map_apply measurable_inl (measurableSet_singleton _), hpre] at hp
      exact hp
  have hx : μ.restrict immortal = F.nuP {a} • Measure.dirac (fun _ => Sum.inl a) := by
    have he := ae_eq_of_subset_of_measure_ge hsubconst (hmass.trans hs.symm).le
      (measurableSet_singleton _).nullMeasurableSet (measure_ne_top _ _)
    rw [← Measure.restrict_congr_set he, Measure.restrict_singleton, hs]
  have hcs : originalTrajectory F {fun _ => a} = F.nuP {a} := by
    by_cases ha : F.nuP {a} = 0
    · apply le_antisymm
      · rw [ha]
        exact (measure_mono (by intro x hx; rw [Set.mem_singleton_iff.mp hx]; rfl :
          {fun _ : ℕ => a} ⊆ {x | x 0 = a})).trans_eq (hstart.trans ha)
      · rw [ha]; exact bot_le
    · exact homogeneous_constant_mass F.nuP F.C a (native_absorption F ha).1
  have hcr : (originalTrajectory F).restrict {x | x 0 = a} =
      F.nuP {a} • Measure.dirac (fun _ => a) := by
    have he := ae_eq_of_subset_of_measure_ge
      (by intro x hx; rw [Set.mem_singleton_iff.mp hx]; rfl :
        {fun _ : ℕ => a} ⊆ {x | x 0 = a})
      (hstart.trans hcs.symm).le (measurableSet_singleton _).nullMeasurableSet
      (measure_ne_top _ _)
    rw [← Measure.restrict_congr_set he, Measure.restrict_singleton, hcs]
  have hid : μ.restrict immortal =
      ((originalTrajectory F).restrict {x | x 0 = a}).map includePath := by
    rw [hx, hcr, Measure.map_smul, Measure.map_dirac]
    rfl
  have hle : μ.restrict immortal ≤ (originalTrajectory F).map includePath := by
    rw [hid]
    exact Measure.map_mono Measure.restrict_le_self hin
  have hdef : ∀ᵐ x ∂μ.restrict immortal, pathDefect x = 0 := by
    by_cases ha : F.nuP {a} = 0
    · rw [hx, ha, zero_smul]
      simp
    · have hd := at_positive_atom F.nuP a (common_flow_upper_endpoint_limits F).1 ha
      have hq : q F a ≠ 0 := by
        rw [hd.1, if_pos rfl]
        norm_num [endpointCompletion]
      have hz := (at_positive_atom F.nuP a (common_flow_stationary_localization F) ha).2.2 hq
      have hd0 : pathDefect (fun _ => Sum.inl a) = 0 := by simp [pathDefect, hz]
      rw [hx]
      exact Measure.ae_smul_measure
        ((ae_eq_dirac pathDefect).mono (fun x h => h.trans hd0)) _
  have hterminal (n : ℕ) : μ.withDensity
      (fun x => Sum.elim (fun Q => q F Q / threeStepAverage F Q) (fun _ => 0) (x n)) =
      μ.restrict immortal := by
    let w : (ℕ → Cemetery) → ℝ≥0∞ :=
      fun x => Sum.elim (fun Q => q F Q / threeStepAverage F Q) (fun _ => 0) (x n)
    have htotal : μ.withDensity w Set.univ = F.nuP {a} := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact terminal_survival_mass F G hmG haG hsub n
    by_cases ha : F.nuP {a} = 0
    · rw [ha] at htotal
      rw [Measure.measure_univ_eq_zero.mp htotal, hx, ha, zero_smul]
    · have hw : w (fun _ => Sum.inl a) = 1 := by
        have hd := at_positive_atom F.nuP a (common_flow_upper_endpoint_limits F).1 ha
        simpa [w, a] using hd.2
      have hsingle : (μ.withDensity w).restrict {fun _ => Sum.inl a} =
          μ.restrict immortal := by
        rw [restrict_withDensity (measurableSet_singleton _),
          Measure.restrict_singleton, hs, withDensity_smul_measure,
          dirac_withDensity, hw, one_smul, hx]
      have hl : μ.restrict immortal ≤ μ.withDensity w := by
        rw [← hsingle]
        exact Measure.restrict_le_self
      have he : μ.restrict immortal Set.univ = μ.withDensity w Set.univ := by
        rw [htotal, hx]
        simp
      exact (Measure.eq_of_le_of_measure_univ_eq hl he).symm
  refine ⟨G, hsub, hmG, haG, hfinite, hx, hid, hle, hle.absolutelyContinuous, hdef, ?_, ?_⟩
  · intro R hR
    have hexp : 1 ≤ ENNReal.ofReal (Real.exp (25 * R / 9)) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
    have hscalar : (1 : ℝ≥0∞) ≤
        (25 / 6 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (25 * R / 9)) := by
      calc
        1 ≤ 25 / 6 := by
          apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
          norm_num
        _ = (25 / 6 : ℝ≥0∞) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp bot_le
    apply (Measure.restrict_le_self.trans hle).trans
    apply Measure.le_iff.mpr
    intro E hE
    rw [Measure.smul_apply, smul_eq_mul]
    exact (mul_one ((originalTrajectory F).map includePath E)).symm.trans_le
      (mul_le_mul_of_nonneg_left hscalar bot_le |>.trans_eq (mul_comm _ _))
  · intro n
    refine ⟨hterminal n, ?_⟩
    have hs : Measurable (fun Q => q F Q / threeStepAverage F Q) :=
      (common_flow_q_limit F).1.div (h_measurable F)
    have hm := map_terminal_density μ (frestrictLe n) (measurable_frestrictLe n)
      (fun x => Sum.elim (fun Q => q F Q / threeStepAverage F Q) (fun _ => 0)
        (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
      ((hs.sumElim measurable_const).comp (measurable_pi_apply _))
    exact hm.symm.trans (congrArg (fun ν => ν.map (frestrictLe n)) (hterminal n))

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
