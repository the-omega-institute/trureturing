/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual started return trajectory and its summable-excess event. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
import Mathlib.Probability.Kernel.CondDistrib

/- This instance layer retains the native descriptor and paid-history dependency family.
   The I classification does not enlarge its original endpoint boxes or mathematical quantifiers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal Topology
open NativeBorelCommonFlow NativeBorelTVTopology NativeBorelEndpointIdentification
open NativeBorelSuperharmonic NativeBorelStationaryLocalization NativeBorelKilledPaths
open NativeBorelFiniteProducts

/-- The original C trajectory started at its actual input descriptor. -/
def startedC (F : CommonFlow) : Kernel PDescriptor (ℕ → PDescriptor) :=
  (Kernel.traj (homogeneousStep F.C) 0).comap (fun Q _ => Q) (by fun_prop)

instance startedC_markov (F : CommonFlow) : IsMarkovKernel (startedC F) := by
  unfold startedC
  infer_instance

/-- Removal of the first state, preserving every subsequent state. -/
def shift (x : ℕ → PDescriptor) : ℕ → PDescriptor := fun n => x (n + 1)

/-- The original nonnegative series, equal to the real excess series on the conull carrier. -/
def excessSeries (x : ℕ → PDescriptor) : ℝ≥0∞ := pathDefect (includePath x)

/-- The event of a finite total excess on the original return history. -/
def summableExcess : Set (ℕ → PDescriptor) := {x | excessSeries x < ∞}

/-- The probability of that event under the actual started C row. -/
def eventProbability (F : CommonFlow) (Q : PDescriptor) : ℝ≥0∞ :=
  startedC F Q summableExcess


private theorem map_comap_pair {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) [IsFiniteMeasure μ] (K : Kernel Y Z) [IsMarkovKernel K]
    (f : X → Y) (hf : Measurable f) :
    (μ ⊗ₘ K.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ K := by
  ext E hE
  rw [Measure.map_apply (hf.prodMap measurable_id) hE,
    Measure.compProd_apply (hE.preimage (hf.prodMap measurable_id)),
    Measure.compProd_apply hE,
    lintegral_map (K.measurable_kernel_prodMk_left hE) hf]
  rfl

private def drop {S : Type*} (n : ℕ) (w : Fin (n + 2) → S) : Fin (n + 1) → S :=
  fun i => w i.succ

private theorem drop_measurable {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (drop (S := S) n) := by fun_prop [drop]

private theorem finiteProduct_drop {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K] :
    ∀ n, (finiteProduct μ K (n + 1)).map (drop n) = finiteProduct (K ∘ₘ μ) K n := by
  intro n
  induction n with
  | zero =>
    have hlast : (finiteProduct μ K 0).map (fun w => w (Fin.last 0)) = μ := by
      rw [finiteProduct, Measure.map_map (by fun_prop) (by fun_prop)]
      exact Measure.map_id
    have hpair := map_comap_pair (finiteProduct μ K 0) K
      (fun w => w (Fin.last 0)) (measurable_pi_apply _)
    have hsnd := congrArg (fun ν => ν.map Prod.snd) hpair
    rw [Measure.map_map (by fun_prop) (by fun_prop), hlast] at hsnd
    have hb : (finiteProduct μ K 0 ⊗ₘ
        K.comap (fun w => w (Fin.last 0)) (measurable_pi_apply _)).map Prod.snd = K ∘ₘ μ := by
      change _ = (μ ⊗ₘ K).snd at hsnd
      rwa [Measure.snd_compProd] at hsnd
    change ((finiteProduct μ K 0 ⊗ₘ
      K.comap (fun w => w (Fin.last 0)) (measurable_pi_apply _)).map
        (fun p => Fin.snoc p.1 p.2)).map (drop 0) = (K ∘ₘ μ).map (fun x _ => x)
    rw [Measure.map_map (drop_measurable 0) (snoc_measurable 0)]
    have he : (drop 0) ∘ (fun p : (Fin 1 → S) × S => Fin.snoc p.1 p.2) =
        (fun x : S => fun _ : Fin 1 => x) ∘ Prod.snd := by
      funext p i
      rw [Fin.eq_zero i]
      change (Fin.snoc p.1 p.2 : Fin 2 → S) (Fin.last 1) = p.2
      rw [Fin.snoc_last]
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), hb]
  | succ n ih =>
    let J := K.comap (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _)
    have hK : K.comap (fun w : Fin (n + 2) → S => w (Fin.last (n + 1)))
        (measurable_pi_apply _) = J.comap (drop n) (drop_measurable n) := by
      ext w E hE
      rfl
    have hp := map_comap_pair (finiteProduct μ K (n + 1)) J (drop n) (drop_measurable n)
    rw [ih] at hp
    rw [finiteProduct, hK, Measure.map_map (drop_measurable (n + 1)) (snoc_measurable (n + 1))]
    have he : (drop (n + 1)) ∘ (fun p : (Fin (n + 2) → S) × S => Fin.snoc p.1 p.2) =
        (fun p : (Fin (n + 1) → S) × S => Fin.snoc p.1 p.2) ∘ Prod.map (drop n) id := by
      funext p i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [drop, Function.comp_def]
      · simp only [Function.comp_def, Prod.map_apply, id_eq, drop,
          show j.castSucc.succ = j.succ.castSucc from rfl, Fin.snoc_castSucc]
        rfl
    rw [he, ← Measure.map_map (snoc_measurable n) ((drop_measurable n).prodMap measurable_id), hp]
    rfl

theorem measure_eq_of_prefix {S : Type*} [MeasurableSpace S]
    (μ ν : Measure (ℕ → S)) [IsFiniteMeasure ν]
    (hp : ∀ n, μ.map (fun x (i : Fin (n + 1)) => x i.1) =
      ν.map (fun x (i : Fin (n + 1)) => x i.1)) : μ = ν := by
  let P := fun I : Finset ℕ => ν.map I.restrict
  haveI : ∀ I, IsFiniteMeasure (P I) := fun I => Measure.isFiniteMeasure_map _ _
  apply IsProjectiveLimit.unique (P := P) ?_ (fun I => rfl)
  intro I
  let n := I.sup id
  let f : (Fin (n + 1) → S) → ((i : I) → S) := fun w i =>
    w ⟨i.1, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.2)⟩
  have hf : Measurable f := by fun_prop
  have he : I.restrict = f ∘ (fun x : ℕ → S => fun i : Fin (n + 1) => x i.1) := rfl
  rw [he, ← Measure.map_map hf (by fun_prop), hp n, Measure.map_map hf (by fun_prop)]
  rfl

private theorem homogeneous_shift {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K] :
    (homogeneousLaw μ K).map (fun x n => x (n + 1)) = homogeneousLaw (K ∘ₘ μ) K := by
  apply measure_eq_of_prefix
  intro n
  rw [Measure.map_map (by fun_prop) (by fun_prop), homogeneous_prefix_product]
  have he : (fun x : ℕ → S => fun i : Fin (n + 1) => x (i.1 + 1)) =
      (drop n) ∘ (fun x : ℕ → S => fun i : Fin (n + 2) => x i.1) := rfl
  change (homogeneousLaw μ K).map (fun x (i : Fin (n + 1)) => x (i.1 + 1)) = _
  rw [he, ← Measure.map_map (drop_measurable n) (by fun_prop),
    homogeneous_prefix_product, finiteProduct_drop]

private theorem startedC_row (F : CommonFlow) (Q : PDescriptor) :
    startedC F Q = homogeneousLaw (Measure.dirac Q) F.C := by
  let T := Kernel.traj (X := fun _ => PDescriptor) (homogeneousStep F.C) 0
  have hi : (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => PDescriptor)).symm Q =
      (fun _ => Q) := rfl
  rw [homogeneousLaw, Kernel.trajMeasure, Measure.map_dirac, hi]
  change T (fun _ => Q) = (Measure.dirac (fun _ => Q)).bind T
  exact (Measure.dirac_bind T.measurable (fun _ => Q)).symm

private theorem original_started (F : CommonFlow) :
    originalTrajectory F = startedC F ∘ₘ F.nuP := by
  rw [originalTrajectory, homogeneousLaw, Kernel.trajMeasure]
  ext E hE
  rw [Measure.bind_apply hE (Kernel.aemeasurable _),
    Measure.bind_apply hE (Kernel.aemeasurable _),
    lintegral_map ((Kernel.traj (homogeneousStep F.C) 0).measurable_coe hE) (by fun_prop)]
  rfl

private theorem startedC_shift (F : CommonFlow) (Q : PDescriptor) :
    (startedC F Q).map shift = startedC F ∘ₘ F.C Q := by
  rw [startedC_row]
  change (homogeneousLaw (Measure.dirac Q) F.C).map (fun x n => x (n + 1)) = _
  rw [homogeneous_shift, Measure.dirac_bind F.C.measurable]
  unfold homogeneousLaw Kernel.trajMeasure startedC
  ext E hE
  rw [Measure.bind_apply hE (Kernel.aemeasurable _),
    Measure.bind_apply hE (Kernel.aemeasurable _),
    lintegral_map ((Kernel.traj (homogeneousStep F.C) 0).measurable_coe hE) (by fun_prop)]
  rfl

private theorem original_shift (F : CommonFlow) :
    (originalTrajectory F).map shift = originalTrajectory F := by
  unfold originalTrajectory shift
  rw [homogeneous_shift, (common_flow_word_iteration F).1]

private theorem excessSeries_measurable : Measurable excessSeries := by
  unfold excessSeries pathDefect includePath
  simp only [Sum.elim_inl]
  have he : Measurable excess := measurable_g.ennreal_toReal.sub measurable_const
  exact Measurable.tsum (fun n => (he.comp (measurable_pi_apply n)).ennreal_ofReal)

private theorem event_measurable : MeasurableSet summableExcess :=
  measurableSet_lt excessSeries_measurable measurable_const

private theorem series_shift (x : ℕ → PDescriptor) :
    excessSeries x = ENNReal.ofReal (excess (x 0)) + excessSeries (shift x) := by
  unfold excessSeries pathDefect includePath shift
  simp only [Sum.elim_inl]
  exact tsum_eq_zero_add' ENNReal.summable

private theorem event_shift : shift ⁻¹' summableExcess = summableExcess := by
  ext x
  change excessSeries (shift x) < ∞ ↔ excessSeries x < ∞
  rw [series_shift x]
  simp [ENNReal.add_lt_top]

private theorem eventProbability_measurable (F : CommonFlow) : Measurable (eventProbability F) :=
  (startedC F).measurable_coe event_measurable

/-- The actual event probability is harmonic for the original return kernel. -/
theorem common_flow_event_harmonic (F : CommonFlow) :
    (originalTrajectory F).map shift = originalTrajectory F ∧
    shift ⁻¹' summableExcess = summableExcess ∧
    ∀ Q, (∫⁻ R, eventProbability F R ∂F.C Q) = eventProbability F Q := by
  refine ⟨original_shift F, event_shift, fun Q => ?_⟩
  have hs := congrArg (fun μ => μ summableExcess) (startedC_shift F Q)
  rw [Measure.map_apply (by fun_prop [shift]) event_measurable, event_shift,
    Measure.bind_apply event_measurable (Kernel.aemeasurable _)] at hs
  exact hs.symm


private def reciprocalSeries (x : ℕ → PDescriptor) : ℝ≥0∞ := (1 + excessSeries x)⁻¹

private theorem reciprocal_measurable : Measurable reciprocalSeries :=
  (measurable_const.add excessSeries_measurable).inv

private theorem reciprocal_le_one (x : ℕ → PDescriptor) : reciprocalSeries x ≤ 1 :=
  ENNReal.inv_le_one.mpr le_self_add

private theorem event_zero_initial (F : CommonFlow) :
    ∀ᵐ x ∂originalTrajectory F, x ∈ summableExcess → ENNReal.ofReal (excess (x 0)) = 0 := by
  have hle : ∀ x, reciprocalSeries x ≤ reciprocalSeries (shift x) := by
    intro x
    apply ENNReal.inv_le_inv.mpr
    change 1 + excessSeries (shift x) ≤ 1 + excessSeries x
    rw [series_shift x]
    exact add_le_add_right le_add_self 1
  have hi : (∫⁻ x, reciprocalSeries x ∂originalTrajectory F) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      _ ≤ ∫⁻ _ : ℕ → PDescriptor, 1 ∂originalTrajectory F := lintegral_mono reciprocal_le_one
      _ = 1 := by simp [originalTrajectory]
  have heq : (∫⁻ x, reciprocalSeries (shift x) ∂originalTrajectory F) =
      ∫⁻ x, reciprocalSeries x ∂originalTrajectory F := by
    rw [← lintegral_map reciprocal_measurable (by fun_prop [shift]), original_shift]
  have hae := ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ hle) hi
    (reciprocal_measurable.comp (by fun_prop [shift])).aemeasurable heq.le
  filter_upwards [hae] with x hx hE
  have he := congrArg (fun a : ℝ≥0∞ => a⁻¹) hx
  change ((1 + excessSeries x)⁻¹)⁻¹ = ((1 + excessSeries (shift x))⁻¹)⁻¹ at he
  simp only [inv_inv] at he
  have hs : excessSeries x = excessSeries (shift x) :=
    (ENNReal.add_right_inj ENNReal.one_ne_top).mp he
  have ht : excessSeries (shift x) ≠ ∞ :=
    (lt_of_le_of_lt (by rw [series_shift x]; exact le_add_self) hE).ne
  rw [series_shift] at hs
  have he0 : ENNReal.ofReal (excess (x 0)) + excessSeries (shift x) =
      0 + excessSeries (shift x) := by simpa using hs
  exact (ENNReal.add_left_inj ht).mp he0

private theorem started_initial (F : CommonFlow) (Q : PDescriptor) :
    ∀ᵐ x ∂startedC F Q, x 0 = Q := by
  have hm : (startedC F Q).map (fun x => x 0) = Measure.dirac Q := by
    rw [startedC_row, homogeneous_initial]
  have ha : ∀ᵐ R ∂(startedC F Q).map (fun x => x 0), R = Q := by
    rw [hm]
    simp
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable ha

private theorem original_coordinate (F : CommonFlow) :
    ∀ n, (originalTrajectory F).map (fun x => x n) = F.nuP := by
  intro n
  induction n with
  | zero => exact homogeneous_initial F.nuP F.C
  | succ n ih =>
    have he : (fun x : ℕ → PDescriptor => x (n + 1)) =
        (fun x : ℕ → PDescriptor => x n) ∘ shift := rfl
    rw [he, ← Measure.map_map (measurable_pi_apply n) (by fun_prop [shift]), original_shift, ih]

private instance pDescriptor_nonempty : Nonempty PDescriptor := ⟨nativeEndpoint .p true⟩

private instance original_probability (F : CommonFlow) : IsProbabilityMeasure (originalTrajectory F) := by
  unfold originalTrajectory
  infer_instance

/-- The exhibited started kernel is the conditional distribution of the full original history. -/
theorem common_flow_event_conditional (F : CommonFlow) :
    condDistrib (id : (ℕ → PDescriptor) → (ℕ → PDescriptor)) (fun x => x 0) (originalTrajectory F)
      =ᵐ[F.nuP] startedC F := by
  letI : Nonempty PDescriptor := ⟨nativeEndpoint .p true⟩
  have hj : (originalTrajectory F).map (fun x => (x 0, x)) = F.nuP ⊗ₘ startedC F := by
    have hi' : ∀ᵐ p ∂(F.nuP ⊗ₘ startedC F), p.2 0 = p.1 := by
      apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))
      exact ae_of_all _ (started_initial F)
    have hmap : (F.nuP ⊗ₘ startedC F).map (fun p => (p.2 0, p.2)) = F.nuP ⊗ₘ startedC F := by
      have he : (fun p : PDescriptor × (ℕ → PDescriptor) => (p.2 0, p.2)) =ᵐ[F.nuP ⊗ₘ startedC F] id := by
        filter_upwards [hi'] with p hp
        simp only [hp, id_eq]
      rw [Measure.map_congr he, Measure.map_id]
    rw [original_started, ← Measure.snd_compProd]
    change ((F.nuP ⊗ₘ startedC F).map Prod.snd).map (fun x => (x 0, x)) = _
    rw [Measure.map_map (by fun_prop) measurable_snd]
    exact hmap
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := originalTrajectory F) (measurable_pi_apply 0) measurable_id
    (by rw [original_coordinate F 0]; exact hj)
  simpa only [original_coordinate F 0] using h


/-- Summability on the stationary original law localizes its actual event probability. -/
theorem common_flow_event_localization (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, ENNReal.ofReal (excess Q) * eventProbability F Q = 0 ∧
      (eventProbability F Q ≠ 0 → excess Q = 0) := by
  have hz := event_zero_initial F
  let D := condDistrib (id : (ℕ → PDescriptor) → (ℕ → PDescriptor))
    (fun x => x 0) (originalTrajectory F)
  have hmix : D ∘ₘ F.nuP = originalTrajectory F := by
    have hd := condDistrib_comp_map (μ := originalTrajectory F)
      (measurable_pi_apply 0).aemeasurable measurable_id.aemeasurable
    simpa only [original_coordinate F 0, Measure.map_id] using hd
  have hzr : ∀ᵐ x ∂(D ∘ₘ F.nuP),
      x ∈ summableExcess → ENNReal.ofReal (excess (x 0)) = 0 := by
    rw [hmix]
    exact hz
  have hr' := Measure.ae_ae_of_ae_comp hzr
  have hr : ∀ᵐ Q ∂F.nuP, ∀ᵐ x ∂startedC F Q,
      x ∈ summableExcess → ENNReal.ofReal (excess (x 0)) = 0 := by
    filter_upwards [hr', common_flow_event_conditional F] with Q hQ he
    change D Q = startedC F Q at he
    rwa [he] at hQ
  filter_upwards [hr, (common_flow_signed_h F).2] with Q hQ hsign
  have hrow : ∀ᵐ x ∂startedC F Q, x ∈ summableExcess → ENNReal.ofReal (excess Q) = 0 := by
    filter_upwards [hQ, started_initial F Q] with x hx hi
    simpa only [hi] using hx
  by_cases he : ENNReal.ofReal (excess Q) = 0
  · refine ⟨by rw [he, zero_mul], fun _ => ?_⟩
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp he) hsign.2.2.1
  · have hf : eventProbability F Q = 0 := by
      apply (measure_eq_zero_iff_ae_notMem).mpr
      filter_upwards [hrow] with x hx
      exact fun hE => he (hx hE)
    exact ⟨by rw [hf, mul_zero], fun hn => (hn hf).elim⟩


private theorem event_second_moment (F : CommonFlow) (Q : PDescriptor) :
    (∫⁻ R, eventProbability F R ∂F.C Q) ^ 2 ≤
      ∫⁻ R, eventProbability F R ^ 2 ∂F.C Q := by
  have hm := eventProbability_measurable F
  have hp := ENNReal.lintegral_mul_norm_pow_le (μ := F.C Q)
    (f := fun R => eventProbability F R ^ 2) (g := fun _ => 1)
    (hm.pow_const 2).aemeasurable measurable_const.aemeasurable
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he (R : PDescriptor) : (eventProbability F R ^ 2) ^ (1 / 2 : ℝ) =
      eventProbability F R := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [ENNReal.one_rpow, mul_one, he, lintegral_one, measure_univ] at hp
  have hs := ENNReal.rpow_le_rpow hp (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul] at hs
  norm_num at hs
  exact hs

/-- The actual summable-excess probability is constant on stationary C edges. -/
theorem common_flow_event_edges (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, ∀ᵐ R ∂F.C Q, eventProbability F R = eventProbability F Q := by
  have hm := eventProbability_measurable F
  have hb (Q : PDescriptor) : eventProbability F Q ≤ 1 := prob_le_one
  have hf (Q : PDescriptor) : eventProbability F Q ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hb Q)
  have hm2 := hm.pow_const 2
  have hi : (∫⁻ Q, eventProbability F Q ^ 2 ∂F.nuP) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      _ ≤ ∫⁻ _ : PDescriptor, (1 : ℝ≥0∞) ∂F.nuP :=
        lintegral_mono (fun Q => by simpa using pow_le_pow_left' (hb Q) 2)
      _ = 1 := by simp
  have hs := (common_flow_word_iteration F).1
  change F.nuP.bind F.C = F.nuP at hs
  have heq : (∫⁻ Q, ∫⁻ R, eventProbability F R ^ 2 ∂F.C Q ∂F.nuP) =
      ∫⁻ Q, eventProbability F Q ^ 2 ∂F.nuP := by
    rw [← Measure.lintegral_bind F.C.aemeasurable hm2.aemeasurable, hs]
  have hh := (common_flow_event_harmonic F).2.2
  have hle : ∀ᵐ Q ∂F.nuP, eventProbability F Q ^ 2 ≤
      ∫⁻ R, eventProbability F R ^ 2 ∂F.C Q := by
    exact ae_of_all _ (fun Q => by simpa only [hh Q] using event_second_moment F Q)
  have he := ae_eq_of_ae_le_of_lintegral_le hle hi hm2.lintegral_kernel.aemeasurable heq.le
  filter_upwards [he] with Q hQ2
  have hmR : Measurable (fun R => (eventProbability F R).toReal) := hm.ennreal_toReal
  have hmem : MemLp (fun R => (eventProbability F R).toReal) 2 (F.C Q) :=
    memLp_of_bounded (ae_of_all _ (fun R =>
      ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hb R)⟩))
      hmR.aestronglyMeasurable 2
  have hr1 : (∫ R, (eventProbability F R).toReal ∂F.C Q) =
      (eventProbability F Q).toReal := by
    rw [integral_toReal hm.aemeasurable (ae_of_all _ (fun R => (hf R).lt_top)), hh Q]
  have hr2 : (∫ R, (eventProbability F R).toReal ^ 2 ∂F.C Q) =
      (eventProbability F Q).toReal ^ 2 := by
    have hi2 := integral_toReal (μ := F.C Q) hm2.aemeasurable
      (ae_of_all _ (fun R => (ENNReal.pow_ne_top (hf R)).lt_top))
    simpa only [ENNReal.toReal_pow, ← hQ2] using hi2
  have hv : variance (fun R => (eventProbability F R).toReal) (F.C Q) = 0 := by
    rw [variance_eq_sub hmem]
    change (∫ R, (eventProbability F R).toReal ^ 2 ∂F.C Q) -
      (∫ R, (eventProbability F R).toReal ∂F.C Q) ^ 2 = 0
    rw [hr1, hr2, sub_self]
  filter_upwards [ae_eq_integral_of_variance_eq_zero hmem hv] with R hR
  apply (ENNReal.toReal_eq_toReal_iff' (hf R) (hf Q)).mp
  exact hR.trans hr1



end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent
