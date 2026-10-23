/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unweighted all-live cemetery prefixes and actual same-flow Radon-Nikodym products. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
import Mathlib.Probability.Kernel.CompProdEqIff

/- This instance layer retains the native descriptor and paid-history dependency family.
   The I classification does not enlarge its original endpoint boxes or mathematical quantifiers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal Topology
attribute [local instance] Classical.propDecidable
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelEndpointIdentification
open NativeBorelTVTopology NativeBorelEndpointIdentification NativeBorelStationaryLocalization NativeBorelKilledPaths

/-- The actual unnormalized iterated kernel product through time n. -/
def finiteProduct {S : Type*} [MeasurableSpace S] (μ : Measure S) (K : Kernel S S) :
    (n : ℕ) → Measure (Fin (n + 1) → S)
  | 0 => μ.map (fun x _ => x)
  | n + 1 => ((finiteProduct μ K n) ⊗ₘ
      K.comap (fun w => w (Fin.last n)) (measurable_pi_apply _)).map
        (fun p => Fin.snoc p.1 p.2)

theorem snoc_measurable {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (fun p : (Fin (n + 1) → S) × S =>
      (Fin.snoc p.1 p.2 : Fin (n + 2) → S)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (Prod.snd :
      (Fin (n + 1) → S) × S → S))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply j (X := fun _ : Fin (n + 1) => S)).comp
        (measurable_fst : Measurable (Prod.fst : (Fin (n + 1) → S) × S → (Fin (n + 1) → S)))

instance finiteProduct_finite {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (K : Kernel S S) [IsFiniteKernel K] (n : ℕ) :
    IsFiniteMeasure (finiteProduct μ K n) := by
  induction n with
  | zero => unfold finiteProduct; exact Measure.isFiniteMeasure_map _ _
  | succ n ih =>
    letI := ih
    unfold finiteProduct
    exact Measure.isFiniteMeasure_map _ _

/-- Each factor is the Radon-Nikodym derivative of the actual same-flow row. -/
def finiteDensity (F : CommonFlow) (M : Kernel PDescriptor PDescriptor) (n : ℕ)
    (w : Fin (n + 1) → PDescriptor) : ℝ≥0∞ :=
  ∏ i : Fin n, M.rnDeriv F.C (w i.castSucc) (w i.succ)

private theorem finiteDensity_measurable (F : CommonFlow)
    (M : Kernel PDescriptor PDescriptor) (n : ℕ) : Measurable (finiteDensity F M n) := by
  unfold finiteDensity
  apply Finset.measurable_prod
  intro i hi
  have hm : Measurable (fun w : Fin (n + 1) → PDescriptor => (w i.castSucc, w i.succ)) := by fun_prop
  exact (Kernel.measurable_rnDeriv M F.C).comp hm

private theorem finiteDensity_snoc (F : CommonFlow) (M : Kernel PDescriptor PDescriptor)
    (n : ℕ) (w : Fin (n + 1) → PDescriptor) (R : PDescriptor) :
    finiteDensity F M (n + 1) (Fin.snoc w R) =
      finiteDensity F M n w * M.rnDeriv F.C (w (Fin.last n)) R := by
  unfold finiteDensity
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [show i.castSucc.succ = i.succ.castSucc from rfl, Fin.snoc_castSucc]
  · simp

private theorem finiteProduct_terminal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Kernel X X) [IsMarkovKernel K]
    (hstat : K ∘ₘ μ = μ) (n : ℕ) :
    (finiteProduct μ K n).map (fun w => w (Fin.last n)) = μ := by
  induction n with
  | zero =>
    rw [finiteProduct, Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def]
    exact Measure.map_id
  | succ n ih =>
    let K' := K.comap (fun w : Fin (n + 1) → X => w (Fin.last n))
      (measurable_pi_apply _)
    have hmap : (finiteProduct μ K n ⊗ₘ K').map Prod.snd = K ∘ₘ μ := by
      change (finiteProduct μ K n ⊗ₘ K').snd = K ∘ₘ μ
      rw [Measure.snd_compProd]
      have hcomp : (⇑K') ∘ₘ finiteProduct μ K n =
          (⇑K) ∘ₘ Measure.map (fun w : Fin (n + 1) → X => w (Fin.last n))
            (finiteProduct μ K n) := by
        ext s hs
        rw [Measure.bind_apply hs (Kernel.aemeasurable _),
          Measure.bind_apply hs (Kernel.aemeasurable _),
          lintegral_map (K.measurable_coe hs) (measurable_pi_apply _)]
        apply lintegral_congr
        intro w
        simp [K', Kernel.comap_apply]
      rw [hcomp, ih]
    rw [finiteProduct, Measure.map_map (by fun_prop) (snoc_measurable n)]
    have hsnoc : (fun w : Fin (n + 2) → X => w (Fin.last (n + 1))) ∘
        (fun p : (Fin (n + 1) → X) × X => Fin.snoc p.1 p.2) = Prod.snd := by
      funext p
      simp
    rw [hsnoc, hmap, hstat]

private theorem finiteProduct_pair_last {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Kernel X X) [IsMarkovKernel K]
    (hstat : K ∘ₘ μ = μ) (n : ℕ) :
    (finiteProduct μ K n ⊗ₘ
      K.comap (fun w : Fin (n + 1) → X => w (Fin.last n)) (measurable_pi_apply _)).map
        (fun p => (p.1 (Fin.last n), p.2)) = μ ⊗ₘ K := by
  let P := finiteProduct μ K n
  let K' := K.comap (fun w : Fin (n + 1) → X => w (Fin.last n))
    (measurable_pi_apply _)
  have hterm := finiteProduct_terminal μ K hstat n
  ext E hE
  rw [Measure.map_apply (by fun_prop) hE,
    Measure.compProd_apply (hE.preimage (by fun_prop)),
    Measure.compProd_apply hE]
  have hfun : Measurable (fun Q : X =>
      K Q ((fun r => (Q, r)) ⁻¹' E)) := by
    change Measurable (fun Q : X => K Q (Prod.mk Q ⁻¹' E))
    exact K.measurable_kernel_prodMk_left hE
  have hR : (∫⁻ Q, K Q ((fun r => (Q, r)) ⁻¹' E) ∂μ) =
      ∫⁻ w, K (w (Fin.last n)) ((fun r => (w (Fin.last n), r)) ⁻¹' E)
        ∂finiteProduct μ K n := by
    have hm := (lintegral_map (μ := finiteProduct μ K n) hfun
      (measurable_pi_apply (X := fun _ : Fin (n + 1) => X) (Fin.last n))).symm
    simpa only [hterm] using hm.symm
  rw [hR]
  apply lintegral_congr
  intro w
  congr 1

private def rowBound (F : CommonFlow) (M : Kernel PDescriptor PDescriptor)
    (Q R : PDescriptor) : Prop :=
  M.rnDeriv F.C Q R ≤
    (threeStepAverage F Q)⁻¹ * threeStepAverage F R *
      ENNReal.ofReal (1 + 25 * excess Q / 9)

/- The exact h-ratio and original excess product on a finite C history. -/
private def finiteDistortion (F : CommonFlow) (n : ℕ)
    (w : Fin (n + 1) → PDescriptor) : ℝ≥0∞ :=
  (threeStepAverage F (w 0))⁻¹ * threeStepAverage F (w (Fin.last n)) *
    ∏ i : Fin n, ENNReal.ofReal (1 + 25 * excess (w i.castSucc) / 9)

private theorem rowBound_measurable (F : CommonFlow)
    (M : Kernel PDescriptor PDescriptor) :
    MeasurableSet {p : PDescriptor × PDescriptor | rowBound F M p.1 p.2} := by
  have hm : Measurable (fun p : PDescriptor × PDescriptor =>
      M.rnDeriv F.C p.1 p.2) := by
    exact (Kernel.measurable_rnDeriv M F.C).comp (by fun_prop)
  have he : Measurable excess := measurable_g.ennreal_toReal.sub measurable_const
  have hfactor : Measurable (fun p : PDescriptor × PDescriptor =>
      ENNReal.ofReal ((1 : ℝ) + 25 * excess p.1 / 9)) := by
    exact ((measurable_const.add
      ((measurable_const.mul (he.comp measurable_fst)).div measurable_const)).ennreal_ofReal)
  have hf : Measurable (fun p : PDescriptor × PDescriptor =>
      (threeStepAverage F p.1)⁻¹ * threeStepAverage F p.2 *
        ENNReal.ofReal (1 + 25 * excess p.1 / 9)) := by
    exact ((h_measurable F).comp measurable_fst).inv.mul
      ((h_measurable F).comp measurable_snd) |>.mul
        hfactor
  exact measurableSet_le hm hf

private theorem finiteDistortion_measurable (F : CommonFlow) (n : ℕ) :
    Measurable (finiteDistortion F n) := by
  unfold finiteDistortion
  have he : Measurable excess := measurable_g.ennreal_toReal.sub measurable_const
  have hfactor (i : Fin n) : Measurable (fun w : Fin (n + 1) → PDescriptor =>
      ENNReal.ofReal ((1 : ℝ) + 25 * excess (w i.castSucc) / 9)) := by
    exact ((measurable_const.add
      ((measurable_const.mul (he.comp (measurable_pi_apply i.castSucc))).div
        measurable_const)).ennreal_ofReal)
  apply ((h_measurable F).comp (measurable_pi_apply 0)).inv.mul
    ((h_measurable F).comp (measurable_pi_apply (Fin.last n))) |>.mul
  apply Finset.measurable_prod
  intro i hi
  exact hfactor i

private theorem finiteProduct_ae_terminal_positive (F : CommonFlow) (n : ℕ) :
    ∀ᵐ w ∂finiteProduct F.nuP F.C n,
      threeStepAverage F (w (Fin.last n)) ≠ 0 := by
  have hposNu : ∀ᵐ Q ∂F.nuP, threeStepAverage F Q ≠ 0 := by
    filter_upwards [(common_flow_signed_h F).2] with Q hQ
    intro hz
    have hh := hQ.1
    simp only [h, hz, ENNReal.toReal_zero] at hh
    norm_num at hh
  have hterm := finiteProduct_terminal F.nuP F.C
    (common_flow_word_iteration F).1 n
  have hs : MeasurableSet {Q : PDescriptor | threeStepAverage F Q ≠ 0} :=
    (measurableSet_singleton (0 : ℝ≥0∞)).preimage (h_measurable F) |>.compl
  have hmap : ∀ᵐ Q ∂(finiteProduct F.nuP F.C n).map
      (fun w => w (Fin.last n)), threeStepAverage F Q ≠ 0 := by
    simpa only [hterm] using hposNu
  exact ae_of_ae_map (measurable_pi_apply _).aemeasurable hmap

private theorem finiteDistortion_snoc (F : CommonFlow) (n : ℕ)
    (w : Fin (n + 1) → PDescriptor) (R : PDescriptor)
    (hh : threeStepAverage F (w (Fin.last n)) ≠ 0)
    (ht : threeStepAverage F (w (Fin.last n)) ≠ ∞) :
    finiteDistortion F (n + 1) (Fin.snoc w R) =
      finiteDistortion F n w *
        (threeStepAverage F (w (Fin.last n)))⁻¹ * threeStepAverage F R *
          ENNReal.ofReal (1 + 25 * excess (w (Fin.last n)) / 9) := by
  unfold finiteDistortion
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  have h0 : (Fin.snoc w R : Fin (n + 2) → PDescriptor) (0 : Fin (n + 2)) = w 0 := by
    simpa only [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl] using
      (@Fin.snoc_castSucc (n + 1) (fun _ : Fin (n + 2) => PDescriptor)
        R (fun i => w i) (0 : Fin (n + 1)))
  rw [h0]
  have hc := ENNReal.mul_inv_cancel hh ht
  symm
  calc
    ((threeStepAverage F (w 0))⁻¹ * threeStepAverage F (w (Fin.last n)) *
        ∏ x : Fin n, ENNReal.ofReal (1 + 25 * excess (w x.castSucc) / 9)) *
        (threeStepAverage F (w (Fin.last n)))⁻¹ * threeStepAverage F R *
          ENNReal.ofReal (1 + 25 * excess (w (Fin.last n)) / 9) =
      (threeStepAverage F (w 0))⁻¹ *
        (threeStepAverage F (w (Fin.last n)) *
          (threeStepAverage F (w (Fin.last n)))⁻¹) *
          (∏ x : Fin n, ENNReal.ofReal (1 + 25 * excess (w x.castSucc) / 9)) *
            threeStepAverage F R *
              ENNReal.ofReal (1 + 25 * excess (w (Fin.last n)) / 9) := by
                ac_rfl
    _ = (threeStepAverage F (w 0))⁻¹ * threeStepAverage F R *
        (∏ x : Fin n, ENNReal.ofReal (1 + 25 * excess (w x.castSucc) / 9)) *
          ENNReal.ofReal (1 + 25 * excess (w (Fin.last n)) / 9) := by
      rw [hc]
      ac_rfl
    _ = (threeStepAverage F (w 0))⁻¹ * threeStepAverage F R *
        ((∏ x : Fin n, ENNReal.ofReal (1 + 25 * excess (w x.castSucc) / 9)) *
          ENNReal.ofReal (1 + 25 * excess (w (Fin.last n)) / 9)) := by
      ac_rfl

set_option maxHeartbeats 800000 in
private theorem finiteDensity_le_distortion (F : CommonFlow)
    (M : Kernel PDescriptor PDescriptor)
    (hrow : ∀ᵐ Q ∂F.nuP, ∀ᵐ R ∂F.C Q, rowBound F M Q R) :
    ∀ n, ∀ᵐ w ∂finiteProduct F.nuP F.C n,
      finiteDensity F M n w ≤ finiteDistortion F n w := by
  have hrowc : ∀ᵐ p ∂(F.nuP ⊗ₘ F.C), rowBound F M p.1 p.2 :=
    Measure.ae_compProd_of_ae_ae (rowBound_measurable F M) hrow
  intro n
  induction n with
  | zero =>
      filter_upwards [finiteProduct_ae_terminal_positive F 0] with w hw
      have hw0 : threeStepAverage F (w 0) ≠ 0 := by simpa using hw
      have hone : (1 : ℝ≥0∞) ≤
          (threeStepAverage F (w 0))⁻¹ * threeStepAverage F (w 0) := by
        rw [ENNReal.inv_mul_cancel hw0 (h_finite F _)]
      simpa [finiteDensity, finiteDistortion] using hone
  | succ n ih =>
      let K := F.C.comap (fun w : Fin (n + 1) → PDescriptor => w (Fin.last n))
        (measurable_pi_apply _)
      have hpair_last := finiteProduct_pair_last F.nuP F.C
        (common_flow_word_iteration F).1 n
      have hrow_pair : ∀ᵐ p ∂(finiteProduct F.nuP F.C n ⊗ₘ K),
          rowBound F M (p.1 (Fin.last n)) p.2 := by
        have hmaprow : ∀ᵐ z ∂Measure.map
            (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
              (p.1 (Fin.last n), p.2)) (finiteProduct F.nuP F.C n ⊗ₘ K),
            rowBound F M z.1 z.2 := by
          rw [show Measure.map
              (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
                (p.1 (Fin.last n), p.2)) (finiteProduct F.nuP F.C n ⊗ₘ K) =
              F.nuP ⊗ₘ F.C by exact hpair_last]
          exact hrowc
        have hpair_meas : Measurable (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
            (p.1 (Fin.last n), p.2)) := by fun_prop
        exact (ae_map_iff hpair_meas.aemeasurable
          (rowBound_measurable F M)).mp hmaprow
      have hih_pair : ∀ᵐ p ∂(finiteProduct F.nuP F.C n ⊗ₘ K),
          finiteDensity F M n p.1 ≤ finiteDistortion F n p.1 := by
        apply Measure.ae_compProd_of_ae_fst K
          (measurableSet_le (finiteDensity_measurable F M n)
            (finiteDistortion_measurable F n))
        exact ih
      have hterm_pair : ∀ᵐ p ∂(finiteProduct F.nuP F.C n ⊗ₘ K),
          threeStepAverage F (p.1 (Fin.last n)) ≠ 0 := by
        have hterm_meas : MeasurableSet {w : Fin (n + 1) → PDescriptor |
            threeStepAverage F (w (Fin.last n)) ≠ 0} :=
          ((measurableSet_singleton (0 : ℝ≥0∞)).preimage
            ((h_measurable F).comp
              (measurable_pi_apply (X := fun _ : Fin (n + 1) => PDescriptor)
                (Fin.last n)))).compl
        apply Measure.ae_compProd_of_ae_fst K
          hterm_meas
        exact finiteProduct_ae_terminal_positive F n
      rw [show finiteProduct F.nuP F.C (n + 1) =
          (finiteProduct F.nuP F.C n ⊗ₘ K).map
            (fun p => Fin.snoc p.1 p.2) by rfl]
      apply (ae_map_iff (snoc_measurable n).aemeasurable
        (measurableSet_le (finiteDensity_measurable F M (n + 1))
          (finiteDistortion_measurable F (n + 1)))).mpr
      filter_upwards [hih_pair, hrow_pair, hterm_pair] with p hi hr ht
      rw [finiteDensity_snoc]
      change M.rnDeriv F.C (p.1 (Fin.last n)) p.2 ≤
        (threeStepAverage F (p.1 (Fin.last n)))⁻¹ * threeStepAverage F p.2 *
          ENNReal.ofReal (1 + 25 * excess (p.1 (Fin.last n)) / 9) at hr
      have hmul : finiteDensity F M n p.1 *
          M.rnDeriv F.C (p.1 (Fin.last n)) p.2 ≤
          finiteDistortion F n p.1 *
            (threeStepAverage F (p.1 (Fin.last n)))⁻¹ *
              threeStepAverage F p.2 *
                ENNReal.ofReal (1 + 25 * excess (p.1 (Fin.last n)) / 9) := by
        calc
          finiteDensity F M n p.1 *
              M.rnDeriv F.C (p.1 (Fin.last n)) p.2 ≤
              finiteDistortion F n p.1 *
                M.rnDeriv F.C (p.1 (Fin.last n)) p.2 :=
            mul_le_mul_left hi _
          _ ≤ finiteDistortion F n p.1 *
              ((threeStepAverage F (p.1 (Fin.last n)))⁻¹ *
                threeStepAverage F p.2 *
                  ENNReal.ofReal (1 + 25 * excess (p.1 (Fin.last n)) / 9)) :=
            mul_le_mul_right hr _
          _ = finiteDistortion F n p.1 *
              (threeStepAverage F (p.1 (Fin.last n)))⁻¹ *
                threeStepAverage F p.2 *
                  ENNReal.ofReal (1 + 25 * excess (p.1 (Fin.last n)) / 9) := by
            ring
      rw [finiteDistortion_snoc F n p.1 p.2 ht (h_finite F _)]
      exact hmul


private theorem compProd_density {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    (K J : Kernel X Y) [IsFiniteKernel K] [IsFiniteKernel J]
    (d : X → ℝ≥0∞) (hd : Measurable d)
    (a : X → Y → ℝ≥0∞) (ha : Measurable (Function.uncurry a))
    (hμ : μ = ν.withDensity d) (hK : ∀ x, K x = (J x).withDensity (a x)) :
    μ ⊗ₘ K = (ν ⊗ₘ J).withDensity (fun p => d p.1 * a p.1 p.2) := by
  ext E hE
  rw [Measure.compProd_apply hE, hμ,
    lintegral_withDensity_eq_lintegral_mul _ hd (K.measurable_kernel_prodMk_left hE),
    withDensity_apply _ hE, ← lintegral_indicator hE,
    Measure.lintegral_compProd (show Measurable (E.indicator
      (fun p : X × Y => d p.1 * a p.1 p.2)) from
      ((hd.comp measurable_fst).mul ha).indicator hE)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  rw [hK x, withDensity_apply _ (measurable_prodMk_left hE),
    ← lintegral_indicator (measurable_prodMk_left hE)]
  rw [← lintegral_const_mul _ (show Measurable ((Prod.mk x ⁻¹' E).indicator (a x)) from
    (ha.comp measurable_prodMk_left).indicator (measurable_prodMk_left hE))]
  apply lintegral_congr
  intro y
  by_cases hy : (x,y) ∈ E <;> simp [Set.indicator, hy]

private theorem finiteProduct_density (F : CommonFlow)
    (M : Kernel PDescriptor PDescriptor) [IsFiniteKernel M]
    (hAC : ∀ Q, M Q ≪ F.C Q) (n : ℕ) :
    finiteProduct F.nuP M n = (finiteProduct F.nuP F.C n).withDensity (finiteDensity F M n) := by
  induction n with
  | zero =>
    rw [show finiteDensity F M 0 = (fun _ => 1) by funext w; simp [finiteDensity],
      show ((finiteProduct F.nuP F.C 0).withDensity (fun _ => 1)) =
        finiteProduct F.nuP F.C 0 from withDensity_one]
    rfl
  | succ n ih =>
    let K := M.comap (fun w : Fin (n + 1) → PDescriptor => w (Fin.last n))
      (measurable_pi_apply _)
    let J := F.C.comap (fun w : Fin (n + 1) → PDescriptor => w (Fin.last n))
      (measurable_pi_apply _)
    let a := fun w : Fin (n + 1) → PDescriptor => M.rnDeriv F.C (w (Fin.last n))
    have ha : Measurable (Function.uncurry a) := by
      have hm : Measurable (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
          (p.1 (Fin.last n), p.2)) := by fun_prop
      exact (Kernel.measurable_rnDeriv M F.C).comp hm
    have hrow (w : Fin (n + 1) → PDescriptor) : K w = (J w).withDensity (a w) := by
      exact (Kernel.withDensity_rnDeriv_eq (hAC (w (Fin.last n)))).symm.trans
        (Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv M F.C) _)
    have hp := compProd_density (finiteProduct F.nuP M n) (finiteProduct F.nuP F.C n)
      K J (finiteDensity F M n) (finiteDensity_measurable F M n) a ha ih hrow
    change ((finiteProduct F.nuP M n) ⊗ₘ K).map _ = _
    rw [hp]
    have he : (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
        finiteDensity F M n p.1 * a p.1 p.2) =
        (fun p => finiteDensity F M (n + 1) (Fin.snoc p.1 p.2)) := by
      funext p
      exact (finiteDensity_snoc F M n p.1 p.2).symm
    rw [he, map_terminal_density _ _ (snoc_measurable n) _
      (finiteDensity_measurable F M (n + 1))]
    rfl

private theorem withDensity_mono_measure {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hμν : μ ≤ ν) (f : X → ℝ≥0∞) :
    μ.withDensity f ≤ ν.withDensity f := by
  refine Measure.le_iff.mpr (fun s hs => ?_)
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  exact lintegral_mono' (Measure.restrict_mono_measure hμν s) le_rfl

set_option maxHeartbeats 800000 in
private theorem rnDeriv_le_of_density {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hAC : μ ≪ ν)
    (f : X → ℝ≥0∞) (hμ : μ ≤ ν.withDensity f) :
    μ.rnDeriv ν ≤ᵐ[ν] f := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
  intro s hs hst
  calc
    (∫⁻ x in s, (Measure.rnDeriv μ ν) x ∂ν) = μ s :=
      Measure.setLIntegral_rnDeriv hAC s
    _ ≤ (ν.withDensity f) s := hμ s
    _ = ∫⁻ x in s, f x ∂ν := withDensity_apply (μ := ν) f hs

set_option maxHeartbeats 800000 in
private theorem doob_row_rn_bound (F : CommonFlow) (G : Set PDescriptor)
    (hmG : MeasurableSet G) (haG : ∀ᵐ Q ∂F.nuP, Q ∈ G)
    (hsub : ∀ Q, doob F G Q Set.univ ≤ 1)
    (hc : ∀ Q, Q ∈ G → CoreAt F Q ∧ (∀ᵐ Q' ∂F.C Q, Q' ∈ G))
    (hdist : ∀ᵐ Q ∂F.nuP, endpointRate⁻¹ • F.L Q ≤
      ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q) :
    ∀ᵐ Q ∂F.nuP, ∀ᵐ R ∂F.C Q,
      (doob F G).rnDeriv F.C Q R ≤
        (threeStepAverage F Q)⁻¹ * threeStepAverage F R *
          ENNReal.ofReal (1 + 25 * excess Q / 9) := by
  filter_upwards [haG, hdist] with Q hQ hd
  have hq : CoreAt F Q := (hc Q hQ).1
  have hpos : threeStepAverage F Q ≠ 0 := by
    intro hz
    have hh := hq.2.1
    simp only [h, hz, ENNReal.toReal_zero] at hh
    norm_num at hh
  have hM : doob F G Q =
      (endpointRate⁻¹ • F.L Q).withDensity
        (fun R => (threeStepAverage F Q)⁻¹ * threeStepAverage F R) := by
    have hm : Measurable (Function.uncurry (fun Q R => if Q ∈ G then
        endpointRate⁻¹ * (threeStepAverage F Q)⁻¹ * threeStepAverage F R else 0)) := by
      exact ((measurable_const.mul ((h_measurable F).comp measurable_fst).inv).mul
        ((h_measurable F).comp measurable_snd)).ite
          (hmG.preimage measurable_fst) measurable_const
    rw [doob, Kernel.withDensity_apply _ hm]
    simp only [hQ, if_true]
    ext E hE
    rw [withDensity_apply _ hE, withDensity_apply _ hE, Measure.restrict_smul,
      lintegral_smul_measure]
    simp only [smul_eq_mul]
    have hf : Measurable (fun R : PDescriptor =>
        (threeStepAverage F Q)⁻¹ * threeStepAverage F R) :=
      measurable_const.mul (h_measurable F)
    rw [← lintegral_const_mul _ hf]
    apply lintegral_congr
    intro R
    ring
  have hscaled := withDensity_mono_measure hd
      (fun R => (threeStepAverage F Q)⁻¹ * threeStepAverage F R)
  have hright :
      ((ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q).withDensity
        (fun R => (threeStepAverage F Q)⁻¹ * threeStepAverage F R)) =
        (F.C Q).withDensity (fun R =>
          (threeStepAverage F Q)⁻¹ * threeStepAverage F R *
            ENNReal.ofReal (1 + 25 * excess Q / 9)) := by
    ext E hE
    rw [withDensity_apply _ hE, withDensity_apply _ hE, Measure.restrict_smul,
      lintegral_smul_measure]
    simp only [smul_eq_mul]
    have hf : Measurable (fun R : PDescriptor =>
        (threeStepAverage F Q)⁻¹ * threeStepAverage F R) :=
      measurable_const.mul (h_measurable F)
    rw [← lintegral_const_mul _ hf]
    apply lintegral_congr
    intro R
    ring
  have hle : doob F G Q ≤ (F.C Q).withDensity (fun R =>
      (threeStepAverage F Q)⁻¹ * threeStepAverage F R *
        ENNReal.ofReal (1 + 25 * excess Q / 9)) := by
    rw [hM]
    exact hscaled.trans_eq hright
  letI : IsFiniteMeasure (doob F G Q) := ⟨lt_of_le_of_lt (hsub Q) ENNReal.one_lt_top⟩
  letI : IsFiniteMeasure (F.C Q) := ⟨by finiteness⟩
  letI : IsFiniteKernel (doob F G) := ⟨⟨1, by simp, hsub⟩⟩
  have hacQ : doob F G Q ≪ F.C Q :=
    (Kernel.withDensity_absolutelyContinuous (κ := F.L) _ Q).trans
      (L_le_C F Q).absolutelyContinuous
  have hbound := rnDeriv_le_of_density (μ := doob F G Q) (ν := F.C Q) hacQ _ hle
  filter_upwards [(doob F G).rnDeriv_eq_rnDeriv_measure (η := F.C) (a := Q), hbound]
    with R hR hRbound
  rw [hR]
  exact hRbound

private theorem homogeneous_prefix_pair {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) :
    (homogeneousLaw μ K).map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) =
      ((homogeneousLaw μ K).map (fun x (i : Fin (n + 1)) => x i.1)) ⊗ₘ
        K.comap (fun w => w (Fin.last n)) (measurable_pi_apply _) := by
  let e : ((i : Finset.Iic n) → S) → (Fin (n + 1) → S) :=
    fun w i => w ⟨i.1, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩
  have he : Measurable e := by fun_prop
  have hk := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => S) (μ₀ := μ) (κ := homogeneousStep K) (a := n)
  have hmap : ( ((homogeneousLaw μ K).map (frestrictLe n)) ⊗ₘ homogeneousStep K n).map
      (Prod.map e id) =
      ((homogeneousLaw μ K).map (fun x (i : Fin (n + 1)) => x i.1)) ⊗ₘ
        K.comap (fun w => w (Fin.last n)) (measurable_pi_apply _) := by
    ext E hE
    rw [Measure.map_apply (he.prodMap measurable_id) hE,
      Measure.compProd_apply (hE.preimage (he.prodMap measurable_id)),
      Measure.compProd_apply hE, lintegral_map
        ((K.comap (fun w : Fin (n + 1) → S => w (Fin.last n))
          (measurable_pi_apply _)).measurable_kernel_prodMk_left hE) (by fun_prop),
      lintegral_map ((homogeneousStep K n).measurable_kernel_prodMk_left
        (hE.preimage (he.prodMap measurable_id))) (measurable_frestrictLe n)]
    rfl
  rw [show (homogeneousLaw μ K).map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) =
    ((homogeneousLaw μ K).map (fun x => (frestrictLe n x, x (n + 1)))).map (Prod.map e id) by
      rw [Measure.map_map (he.prodMap measurable_id) (by fun_prop)]; rfl,
    homogeneousLaw, ← hk]
  exact hmap

theorem homogeneous_prefix_product {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) :
    (homogeneousLaw μ K).map (fun x (i : Fin (n + 1)) => x i.1) = finiteProduct μ K n := by
  induction n with
  | zero =>
    rw [show (fun x : ℕ → S => fun i : Fin 1 => x i.1) =
      (fun Q _ => Q) ∘ (fun x : ℕ → S => x 0) by funext x i; rw [Fin.eq_zero i]; rfl,
      ← Measure.map_map (f := fun x : ℕ → S => x 0)
        (g := fun Q : S => fun _ : Fin 1 => Q) (by fun_prop) (measurable_pi_apply 0),
      homogeneous_initial]
    rfl
  | succ n ih =>
    rw [show (fun x : ℕ → S => fun i : Fin (n + 2) => x i.1) =
      (fun p => Fin.snoc p.1 p.2) ∘
        (fun x : ℕ → S => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) by
          funext x i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp,
      ← Measure.map_map
        (f := fun x : ℕ → S => ((fun i : Fin (n + 1) => x i.1), x (n + 1)))
        (g := fun p : (Fin (n + 1) → S) × S => (Fin.snoc p.1 p.2 : Fin (n + 2) → S))
        (snoc_measurable n) (by fun_prop), homogeneous_prefix_pair, ih]
    rfl


/-- All coordinates through the specified finite time are live. -/
def allLive (n : ℕ) : Set (Fin (n + 1) → Cemetery) := {w | ∀ i, w i ≠ Sum.inr ()}

private theorem allLive_measurable (n : ℕ) : MeasurableSet (allLive n) := by
  have he : allLive n = ⋂ i : Fin (n + 1), {w : Fin (n + 1) → Cemetery | w i ≠ Sum.inr ()} := by
    ext w; simp only [allLive, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun i => ((measurableSet_singleton (Sum.inr () : Cemetery)).preimage
    (measurable_pi_apply i)).compl)

private theorem allLive_snoc (n : ℕ) (w : Fin (n + 1) → Cemetery) (y : Cemetery) :
    Fin.snoc w y ∈ allLive (n + 1) ↔ w ∈ allLive n ∧ y ≠ Sum.inr () := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.snoc_castSucc] using h i.castSucc,
      by simpa only [Fin.snoc_last] using h (Fin.last (n + 1))⟩
  · rintro ⟨hw, hy⟩ i
    exact Fin.lastCases (by simpa only [Fin.snoc_last] using hy)
      (fun j => by simpa only [Fin.snoc_castSucc] using hw j) i

private theorem cemetery_live_integral (M : Kernel PDescriptor PDescriptor)
    (hsub : ∀ Q, M Q Set.univ ≤ 1) (Q : PDescriptor)
    (f : Cemetery → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, {y : Cemetery | y ≠ Sum.inr ()}.indicator f y ∂cemetery M (Sum.inl Q)) =
      ∫⁻ R, f (Sum.inl R) ∂M Q := by
  letI := cemetery_markov M hsub
  haveI : IsFiniteKernel M := ⟨⟨1, by simp, hsub⟩⟩
  have hset : MeasurableSet {y : Cemetery | y ≠ Sum.inr ()} :=
    (measurableSet_singleton (Sum.inr () : Cemetery)).compl
  change (∫⁻ y, _ ∂((M.map (Sum.inl : PDescriptor → Cemetery)) Q +
      (1 - M Q Set.univ) • Measure.dirac (Sum.inr ()))) = _
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  simp only [Set.indicator_of_notMem (show Sum.inr () ∉ {y : Cemetery | y ≠ Sum.inr ()} by simp),
    smul_eq_mul, mul_zero, add_zero]
  rw [Kernel.map_apply _ measurable_inl, lintegral_map (hf.indicator hset) measurable_inl]
  apply lintegral_congr
  intro R
  exact Set.indicator_of_mem Sum.inl_ne_inr f

private theorem finiteProduct_live_integral (μ : Measure PDescriptor) [IsProbabilityMeasure μ]
    (M : Kernel PDescriptor PDescriptor) (hsub : ∀ Q, M Q Set.univ ≤ 1)
    (n : ℕ) (f : (Fin (n + 1) → Cemetery) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, (allLive n).indicator f w ∂finiteProduct (μ.map Sum.inl) (cemetery M) n) =
      ∫⁻ w, f (fun i => Sum.inl (w i)) ∂finiteProduct μ M n := by
  letI := cemetery_markov M hsub
  haveI : IsFiniteKernel M := ⟨⟨1, by simp, hsub⟩⟩
  induction n with
  | zero =>
    rw [finiteProduct, lintegral_map ((hf.indicator (allLive_measurable 0))) (by fun_prop),
      lintegral_map (show Measurable (fun y : Cemetery =>
        (allLive 0).indicator f (fun _ : Fin 1 => y)) from
        (hf.indicator (allLive_measurable 0)).comp (by fun_prop)) measurable_inl,
      finiteProduct, lintegral_map
        (show Measurable (fun w : Fin 1 → PDescriptor => f (fun i => Sum.inl (w i))) from
          hf.comp (by fun_prop))
        (show Measurable (fun Q : PDescriptor => fun _ : Fin 1 => Q) by fun_prop)]
    apply lintegral_congr
    intro Q
    exact Set.indicator_of_mem
      (show (fun _ : Fin 1 => (Sum.inl Q : Cemetery)) ∈ allLive 0 from fun _ => Sum.inl_ne_inr) f
  | succ n ih =>
    have hs := snoc_measurable (S := Cemetery) n
    let t : (Fin (n + 1) → Cemetery) × Cemetery → ℝ≥0∞ :=
      fun p => (allLive (n + 1)).indicator f (Fin.snoc p.1 p.2)
    have ht : Measurable t := (hf.indicator (allLive_measurable (n + 1))).comp hs
    let K := (cemetery M).comap (fun w : Fin (n + 1) → Cemetery => w (Fin.last n))
      (measurable_pi_apply _)
    let g : (Fin (n + 1) → Cemetery) → ℝ≥0∞ := fun w => ∫⁻ y, t (w,y) ∂K w
    have hg : Measurable g := Measurable.lintegral_kernel_prod_right ht
    have hgmask : g = (allLive n).indicator g := by
      funext w
      by_cases hw : w ∈ allLive n
      · exact (Set.indicator_of_mem hw g).symm
      · rw [Set.indicator_of_notMem hw]
        change (∫⁻ y, t (w,y) ∂K w) = 0
        have he : (fun y => t (w,y)) = 0 := by
          funext y
          exact Set.indicator_of_notMem (fun h => hw ((allLive_snoc n w y).mp h).1) f
        rw [he]
        exact lintegral_zero
    rw [finiteProduct, lintegral_map (hf.indicator (allLive_measurable (n + 1))) hs,
      Measure.lintegral_compProd ht]
    change (∫⁻ w, g w ∂finiteProduct (μ.map Sum.inl) (cemetery M) n) = _
    rw [hgmask, ih g hg, finiteProduct,
      lintegral_map
        (show Measurable (fun w : Fin (n + 2) → PDescriptor => f (fun i => Sum.inl (w i))) from
          hf.comp (by fun_prop)) (snoc_measurable (S := PDescriptor) n),
      Measure.lintegral_compProd
        (show Measurable (fun p : (Fin (n + 1) → PDescriptor) × PDescriptor =>
          f (fun i => Sum.inl ((Fin.snoc p.1 p.2 : Fin (n + 2) → PDescriptor) i))) from
          (hf.comp (show Measurable (fun w : Fin (n + 2) → PDescriptor =>
            fun i => (Sum.inl (w i) : Cemetery)) by fun_prop)).comp
              (snoc_measurable (S := PDescriptor) n))]
    apply lintegral_congr
    intro w
    change (∫⁻ y, t ((fun i => Sum.inl (w i)),y)
      ∂cemetery M (Sum.inl (w (Fin.last n)))) = _
    have he : (fun y => t ((fun i => Sum.inl (w i)),y)) =
      {y : Cemetery | y ≠ Sum.inr ()}.indicator (fun y => f (Fin.snoc (fun i => Sum.inl (w i)) y)) := by
      funext y
      have hw : (fun i => Sum.inl (w i)) ∈ allLive n := fun _ => Sum.inl_ne_inr
      by_cases hy : y ≠ Sum.inr ()
      · rw [Set.indicator_of_mem hy]
        exact Set.indicator_of_mem ((allLive_snoc n _ y).mpr ⟨hw,hy⟩) f
      · rw [Set.indicator_of_notMem hy]
        exact Set.indicator_of_notMem (fun h => hy ((allLive_snoc n _ y).mp h).2) f
    have hfc : Measurable (fun y : Cemetery =>
        f (Fin.snoc (fun i => (Sum.inl (w i) : Cemetery)) y)) :=
      by
      have hm : Measurable (fun y : Cemetery =>
          ((fun i : Fin (n + 1) => (Sum.inl (w i) : Cemetery)), y)) := by fun_prop
      have hh := (snoc_measurable (S := Cemetery) n).comp hm
      exact hf.comp hh
    rw [he, cemetery_live_integral M hsub (w (Fin.last n))
      (fun y => f (Fin.snoc (fun i => (Sum.inl (w i) : Cemetery)) y)) hfc]
    apply lintegral_congr
    intro R
    congr 1
    funext i
    exact Fin.lastCases (by simp) (fun j => by simp) i

/-- The unweighted surviving prefix is the actual substochastic product law;
its density relative to the original finite C history is the product of the
same-row Radon-Nikodym derivatives. -/
theorem common_flow_finite_product (F : CommonFlow) :
    ∃ (G : Set PDescriptor) (hsub : ∀ Q, doob F G Q Set.univ ≤ 1),
      MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
      (∀ᵐ Q ∂F.nuP, ∀ᵐ R ∂F.C Q,
        (doob F G).rnDeriv F.C Q R ≤
          (threeStepAverage F Q)⁻¹ * threeStepAverage F R *
            ENNReal.ofReal (1 + 25 * excess Q / 9)) ∧
      ∀ n : ℕ,
        ((killedTrajectory F (doob F G) hsub).map
          (fun x (i : Fin (n + 1)) => x i.1)).restrict (allLive n) =
          (finiteProduct F.nuP (doob F G) n).map (fun w i => Sum.inl (w i)) ∧
        finiteProduct F.nuP (doob F G) n =
          ((originalTrajectory F).map (fun x (i : Fin (n + 1)) => x i.1)).withDensity
            (finiteDensity F (doob F G) n) ∧
        finiteProduct F.nuP (doob F G) n ≪
          (originalTrajectory F).map (fun x (i : Fin (n + 1)) => x i.1) := by
  obtain ⟨G, hsub, hmG, haG, hm, hp, hac, hc, hconj, hlim, hpos, hk, hdist⟩ :=
    common_flow_doob_survival F
  letI := cemetery_markov (doob F G) hsub
  haveI : IsFiniteKernel (doob F G) := ⟨⟨1, by simp, hsub⟩⟩
  haveI : IsProbabilityMeasure (F.nuP.map (Sum.inl : PDescriptor → Cemetery)) :=
    inferInstance
  refine ⟨G, hsub, hmG, haG, doob_row_rn_bound F G hmG haG hsub hc hdist,
    fun n => ⟨?_, ?_, ?_⟩⟩
  · change ((homogeneousLaw (F.nuP.map Sum.inl) (cemetery (doob F G))).map _).restrict _ = _
    rw [homogeneous_prefix_product]
    ext E hE
    rw [Measure.restrict_apply hE, Measure.map_apply (by fun_prop) hE]
    have hf := finiteProduct_live_integral F.nuP (doob F G) hsub n
      (E.indicator (fun _ => 1)) (measurable_const.indicator hE)
    rw [show (fun w : Fin (n + 1) → Cemetery =>
        (allLive n).indicator (E.indicator (fun _ => (1 : ℝ≥0∞))) w) =
        (E ∩ allLive n).indicator (fun _ => 1) by
          funext w; by_cases hw : w ∈ allLive n <;> by_cases he : w ∈ E <;>
            simp [Set.indicator, hw, he], show (∫⁻ w, (E ∩ allLive n).indicator (fun _ => (1 : ℝ≥0∞)) w
        ∂finiteProduct (F.nuP.map Sum.inl) (cemetery (doob F G)) n) =
        finiteProduct (F.nuP.map Sum.inl) (cemetery (doob F G)) n (E ∩ allLive n) from
          lintegral_indicator_one (hE.inter (allLive_measurable n)),
      show (fun w : Fin (n + 1) → PDescriptor => E.indicator (fun _ => (1 : ℝ≥0∞))
          (fun i => Sum.inl (w i))) =
        ((fun w i => Sum.inl (w i)) ⁻¹' E).indicator (fun _ => 1) by rfl,
      show (∫⁻ w, ((fun w : Fin (n + 1) → PDescriptor => fun i => (Sum.inl (w i) : Cemetery)) ⁻¹' E).indicator
        (fun _ => (1 : ℝ≥0∞)) w ∂finiteProduct F.nuP (doob F G) n) =
        finiteProduct F.nuP (doob F G) n
          ((fun w : Fin (n + 1) → PDescriptor => fun i => (Sum.inl (w i) : Cemetery)) ⁻¹' E) from
          lintegral_indicator_one (hE.preimage (by fun_prop))] at hf
    exact hf
  · rw [originalTrajectory, homogeneous_prefix_product]
    exact finiteProduct_density F (doob F G) hac n
  · rw [originalTrajectory, homogeneous_prefix_product,
      finiteProduct_density F (doob F G) hac n]
    exact withDensity_absolutelyContinuous _ _

/-- The original finite C-history RN derivative obeys the h-ratio/excess bound. -/
theorem common_flow_finite_history_rn_bound (F : CommonFlow) :
    ∃ (G : Set PDescriptor) (hsub : ∀ Q, doob F G Q Set.univ ≤ 1),
      MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
      (∀ᵐ Q ∂F.nuP, ∀ᵐ R ∂F.C Q,
        (doob F G).rnDeriv F.C Q R ≤
          (threeStepAverage F Q)⁻¹ * threeStepAverage F R *
            ENNReal.ofReal (1 + 25 * excess Q / 9)) ∧
      ∀ n : ℕ, (finiteProduct F.nuP (doob F G) n).rnDeriv
          (finiteProduct F.nuP F.C n) ≤ᵐ[finiteProduct F.nuP F.C n]
        (fun w =>
          (threeStepAverage F (w 0))⁻¹ *
            threeStepAverage F (w (Fin.last n)) *
              ∏ i : Fin n, ENNReal.ofReal
                (1 + 25 * excess (w i.castSucc) / 9)) := by
  obtain ⟨G, hsub, hmG, haG, _hmarkov, _hprob, hac, hc, _hconj, _hlim,
      _hpos, _hk, hdist⟩ := common_flow_doob_survival F
  letI := cemetery_markov (doob F G) hsub
  haveI : IsFiniteKernel (doob F G) := ⟨⟨1, by simp, hsub⟩⟩
  have hrow := doob_row_rn_bound F G hmG haG hsub hc hdist
  have hdistortion : ∀ n, ∀ᵐ w ∂finiteProduct F.nuP F.C n,
      finiteDensity F (doob F G) n w ≤ finiteDistortion F n w :=
    finiteDensity_le_distortion F (doob F G) hrow
  refine ⟨G, hsub, hmG, haG, hrow, ?_⟩
  intro n
  have hdensity := finiteProduct_density F (doob F G) hac n
  have hrn : (finiteProduct F.nuP (doob F G) n).rnDeriv
      (finiteProduct F.nuP F.C n) =ᵐ[finiteProduct F.nuP F.C n]
        finiteDensity F (doob F G) n := by
    rw [hdensity]
    exact Measure.rnDeriv_withDensity _ (finiteDensity_measurable F (doob F G) n)
  filter_upwards [hrn, hdistortion n] with w hw hd
  rw [hw]
  simpa [finiteDistortion] using hd

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
