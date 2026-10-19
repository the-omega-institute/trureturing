/- GID: D5/S3/Estimation/DataProcessing/BorelIidStrictPeakLower
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/BorelIidStrictPeakLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite rational-cut sources converge to the actual Borel iid strict-peak law. -/

import D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
import Mathlib.Topology.Sequences
import Mathlib.Data.Rat.Encodable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false
namespace D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
open IidStrictPeakSource FiniteIidStrictPeakLower
open MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- A fixed exhaustive list of rational cuts. -/
def cut (n : ℕ) : ℝ := ((Encodable.decode (α := ℚ) n).getD 0 : ℚ)

/-- The rank among the first n rational cuts has a genuinely finite ordered range. -/
def quantize (n : ℕ) (x : ℝ) : Fin (n+1) :=
  ⟨((Finset.range n).filter (fun k => cut k < x)).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans_eq (Finset.card_range n))⟩

private theorem quantize_mono (n : ℕ) : Monotone (quantize n) := by
  intro x y hxy
  change ((Finset.range n).filter (fun k => cut k < x)).card ≤
    ((Finset.range n).filter (fun k => cut k < y)).card
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1,lt_of_lt_of_le hk.2 hxy⟩

private theorem quantize_strict_eventually (x y : ℝ) (hxy : x < y) :
    ∀ᶠ n in atTop, quantize n x < quantize n y := by
  obtain ⟨r,hxr,hry⟩ := exists_rat_btwn hxy
  have hcut : cut (Encodable.encode r) = (r : ℝ) := by simp [cut]
  filter_upwards [eventually_ge_atTop (Encodable.encode r+1)] with n hn
  change ((Finset.range n).filter (fun k => cut k < x)).card <
    ((Finset.range n).filter (fun k => cut k < y)).card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1,lt_trans hk.2 hxy⟩
  · intro he
    have hrmem : Encodable.encode r ∈ (Finset.range n).filter (fun k => cut k < y) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [hcut]⟩
    rw [← he] at hrmem
    have : (r:ℝ) < x := by simpa [hcut] using (Finset.mem_filter.mp hrmem).2
    exact (not_lt_of_ge hxr.le) this

private theorem quantize_comparison (x y : ℝ) :
    ∀ᶠ n in atTop, (quantize n x < quantize n y ↔ x < y) := by
  by_cases hxy : x < y
  · filter_upwards [quantize_strict_eventually x y hxy] with n hn
    exact iff_of_true hn hxy
  · filter_upwards [] with n
    have hle := quantize_mono n (le_of_not_gt hxy)
    exact iff_of_false (not_lt_of_ge hle) hxy

private theorem quantize_mode_eventually (v : Fin 5 → ℝ) :
    ∀ᶠ n in atTop,
      mode (quantize n (v 0)) (quantize n (v 1)) (quantize n (v 2))
        (quantize n (v 3)) (quantize n (v 4)) = mode (v 0) (v 1) (v 2) (v 3) (v 4) := by
  filter_upwards [quantize_comparison (v 0) (v 1),quantize_comparison (v 2) (v 1),
    quantize_comparison (v 1) (v 2),quantize_comparison (v 3) (v 2),
    quantize_comparison (v 2) (v 3),quantize_comparison (v 4) (v 3)]
    with n h01 h21 h12 h32 h23 h43
  have hz : peak (quantize n (v 1)) (quantize n (v 2)) (quantize n (v 3)) ↔
      peak (v 1) (v 2) (v 3) := and_congr h12 h32
  have hx : peak (quantize n (v 0)) (quantize n (v 1)) (quantize n (v 2)) ↔
      peak (v 0) (v 1) (v 2) := and_congr h01 h21
  have hy : peak (quantize n (v 2)) (quantize n (v 3)) (quantize n (v 4)) ↔
      peak (v 2) (v 3) (v 4) := and_congr h23 h43
  unfold mode
  apply ite_congr (propext hz) (fun _ => rfl)
  intro _
  apply ite_congr (propext hx)
  · intro _
    exact ite_cond_congr (propext hy)
  · intro _
    exact ite_cond_congr (propext hy)

private theorem measurable_quantize (n : ℕ) : Measurable (quantize n) := by
  have hm : Measurable (fun x : ℝ => ((Finset.range n).filter (fun k => cut k < x)).card) := by
    have he : (fun x : ℝ => ((Finset.range n).filter (fun k => cut k < x)).card) =
        fun x => ∑ k ∈ Finset.range n, if cut k < x then (1 : ℕ) else 0 := by
      funext x
      simp
    rw [he]
    exact Finset.measurable_sum _ fun k _ =>
      Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hc : Measurable (fun k : ℕ => Fin.ofNat (n+1) k) := measurable_of_countable _
  convert hc.comp hm using 1
  funext x
  apply Fin.ext
  simp [quantize,Fin.val_ofNat,Nat.mod_eq_of_lt
    (Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans_eq (Finset.card_range n)))]

/-- Borel strict-peak probabilities are pushforward masses of the original samples. -/
def modeMass (μ : Measure ℝ) (s : Fin 5) : ℝ :=
  ∫ v, if mode (v 0) (v 1) (v 2) (v 3) (v 4) = s then (1 : ℝ) else 0 ∂(Measure.pi (fun _ : Fin 5 => μ))

/-- The approximating law is induced from the same samples by finite quantization. -/
def quantizedMass (μ : Measure ℝ) (n : ℕ) (s : Fin 5) : ℝ :=
  ∫ v, if mode (quantize n (v 0)) (quantize n (v 1)) (quantize n (v 2))
    (quantize n (v 3)) (quantize n (v 4)) = s then (1 : ℝ) else 0 ∂(Measure.pi (fun _ : Fin 5 => μ))

private theorem measurable_real_mode :
    Measurable (fun v : Fin 5 → ℝ => mode (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  have hp (i j k : Fin 5) : MeasurableSet {v : Fin 5 → ℝ | peak (v i) (v j) (v k)} :=
    (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)).inter
      (measurableSet_lt (measurable_pi_apply k) (measurable_pi_apply j))
  exact Measurable.ite (hp 1 2 3) measurable_const
    (Measurable.ite (hp 0 1 2)
      (Measurable.ite (hp 2 3 4) measurable_const measurable_const)
      (Measurable.ite (hp 2 3 4) measurable_const measurable_const))

private theorem measurable_quantized_mode (n : ℕ) :
    Measurable (fun v : Fin 5 → ℝ =>
      mode (quantize n (v 0)) (quantize n (v 1)) (quantize n (v 2))
        (quantize n (v 3)) (quantize n (v 4))) := by
  have hf : Measurable (fun v : Fin 5 → Fin (n+1) =>
      mode (v 0) (v 1) (v 2) (v 3) (v 4)) := measurable_of_finite _
  exact hf.comp (Measurable.of_eval fun i =>
    (measurable_quantize n).comp (measurable_pi_apply i))

private theorem quantized_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Fin 5) :
    Tendsto (fun n => quantizedMass μ n s) atTop (𝓝 (modeMass μ s)) := by
  letI : IsProbabilityMeasure ((Measure.pi (fun _ : Fin 5 => μ))) := by infer_instance
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact (Measurable.ite ((measurable_quantized_mode n) (measurableSet_singleton s))
      measurable_const measurable_const).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    filter_upwards [] with v
    split_ifs <;> norm_num
  · filter_upwards [] with v
    apply tendsto_const_nhds.congr'
    filter_upwards [quantize_mode_eventually v] with n hn
    simp only [hn]

private theorem sum_cons {A : Type*} [Fintype A] (n : ℕ)
    (f : (Fin (n+1) → A) → ℝ) :
    (∑ v, f v) = ∑ a, ∑ v : Fin n → A, f (Fin.cons a v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f,Fintype.sum_prod_type]
  rfl

private theorem finite_integral {A : Type*} [Fintype A] [LinearOrder A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure A) [IsProbabilityMeasure ν] (s : Fin 5) :
    (∫ v : Fin 5 → A, if mode (v 0) (v 1) (v 2) (v 3) (v 4) = s then (1 : ℝ) else 0
      ∂Measure.pi (fun _ => ν)) = modeLaw (fun a => ν.real {a}) s := by
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def,Measure.pi_singleton,ENNReal.toReal_prod,smul_eq_mul]
  simp_rw [sum_cons]
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Fintype.sum_unique,
    Fin.prod_univ_zero,mul_one]
  dsimp only [Fin.cons,Fin.cases,Fin.induction]
  simp only [modeLaw,productAverage,IidStrictPeakSource.average,Finset.mul_sum,mul_assoc,measureReal_def]
  try rfl

private theorem quantized_mode_finite (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Fin 5) :
    quantizedMass μ n s = modeLaw (fun a : Fin (n+1) =>
      (μ.map (quantize n)).real {a}) s := by
  let ν := μ.map (quantize n)
  have hmap : ((Measure.pi (fun _ : Fin 5 => μ))).map (fun v i => quantize n (v i)) =
      Measure.pi (fun _ : Fin 5 => ν) :=
    Measure.pi_map_pi (fun _ => (measurable_quantize n).aemeasurable)
  have hmeas : Measurable (fun v : Fin 5 → ℝ => fun i => quantize n (v i)) :=
    Measurable.of_eval fun i => (measurable_quantize n).comp (measurable_pi_apply i)
  have hm : Measurable (fun v : Fin 5 → Fin (n+1) =>
      if mode (v 0) (v 1) (v 2) (v 3) (v 4) = s then (1 : ℝ) else 0) :=
    measurable_of_finite _
  have ht := integral_map (μ := (Measure.pi (fun _ : Fin 5 => μ))) hmeas.aemeasurable hm.aestronglyMeasurable
  rw [hmap,finite_integral] at ht
  exact ht.symm

private theorem quantized_is_finite (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    ∃ p : Fin (n+1) → ℝ, (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1) ∧
      (∀ s, quantizedMass μ n s = modeLaw p s) ∧
      ∀ c : ℝ, μ.real {c} ≤ p (quantize n c) := by
  let ν := μ.map (quantize n)
  have hν : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  refine ⟨fun a => ν.real {a},fun _ => measureReal_nonneg,?_,?_,?_⟩
  · have ht := integral_fintype (μ := ν) (integrable_const (1 : ℝ))
    simpa using ht.symm
  · intro s
    exact quantized_mode_finite μ n s
  · intro c
    have hsub : {c} ⊆ (quantize n) ⁻¹' {quantize n c} := by
      intro x hx
      have he : x = c := mem_singleton_iff.mp hx
      subst x
      exact rfl
    have hm := measureReal_mono (μ := μ) hsub
    simpa only [ν,measureReal_def,Measure.map_apply (measurable_quantize n)
      (measurableSet_singleton (quantize n c))] using hm

private def quantizedCdf (μ : Measure ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  μ.real {w | quantize n w < quantize n v}

private theorem quantizedCdf_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (v : ℝ) : 0 ≤ quantizedCdf μ n v ∧ quantizedCdf μ n v ≤ 1 := by
  refine ⟨measureReal_nonneg,?_⟩
  have hm := measureReal_mono (μ := μ)
    (subset_univ {w | quantize n w < quantize n v})
  simpa [quantizedCdf] using hm

private theorem measurable_quantizedCdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) : Measurable (quantizedCdf μ n) := by
  have hm : Monotone (quantizedCdf μ n) := by
    intro x y hxy
    exact measureReal_mono (μ := μ) (fun w hw =>
      lt_of_lt_of_le hw (quantize_mono n hxy))
  exact hm.measurable

private theorem quantizedCdf_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    Tendsto (fun n => quantizedCdf μ n v) atTop (𝓝 (μ.real (Iio v))) := by
  have hmeas (n : ℕ) : MeasurableSet {w | quantize n w < quantize n v} :=
    (measurable_quantize n) (measurableSet_Iio)
  have he (n : ℕ) :
      (∫ w, if quantize n w < quantize n v then (1 : ℝ) else 0 ∂μ) =
        quantizedCdf μ n v := by
    simpa only [quantizedCdf,indicator_apply,mem_setOf_eq,Pi.one_apply] using
      (integral_indicator_one (μ := μ) (hmeas n))
  have he' : (∫ w, if w<v then (1 : ℝ) else 0 ∂μ) = μ.real (Iio v) :=
    integral_indicator_one measurableSet_Iio
  have ht : Tendsto (fun n => ∫ w, if quantize n w < quantize n v then (1 : ℝ) else 0 ∂μ)
      atTop (𝓝 (∫ w, if w<v then (1 : ℝ) else 0 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact (Measurable.ite (hmeas n) measurable_const measurable_const).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [] with w
      split_ifs <;> norm_num
    · filter_upwards [] with w
      apply tendsto_const_nhds.congr'
      filter_upwards [quantize_comparison w v] with n hn
      simp only [hn]
  simpa only [he,he'] using ht

private theorem quantized_cdf_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    quantizedMass μ n 1+quantizedMass μ n 3 =
      ∫ v, quantizedCdf μ n v^2 ∂μ := by
  let ν := μ.map (quantize n)
  let p := fun a : Fin (n+1) => ν.real {a}
  have hp : ∀ a, 0 ≤ p a := fun _ => measureReal_nonneg
  have hs : ∑ a, p a = 1 := by
    have ht := integral_fintype (μ := ν) (integrable_const (1 : ℝ))
    simpa [p] using ht.symm
  have hq (s : Fin 5) : quantizedMass μ n s = modeLaw p s :=
    quantized_mode_finite μ n s
  have hl (a : Fin (n+1)) : lowerMass p a = ν.real (Iio a) := by
    have ht := integral_fintype (μ := ν)
      (f := fun b => if b<a then (1 : ℝ) else 0) Integrable.of_finite
    have he : (∫ b, if b<a then (1 : ℝ) else 0 ∂ν) = ν.real (Iio a) :=
      by simpa only [indicator_apply,mem_Iio,Pi.one_apply] using
        (integral_indicator_one (μ := ν) (measurableSet_Iio (a := a)))
    rw [he] at ht
    simpa [lowerMass,p,mul_ite] using ht.symm
  have hc (v : ℝ) : lowerMass p (quantize n v) = quantizedCdf μ n v := by
    rw [hl]
    simp only [ν,measureReal_def,Measure.map_apply (measurable_quantize n) measurableSet_Iio]
    rfl
  rw [hq 1,hq 3,(iid_peak_source p hp hs).2.2.2.1]
  have hm : Measurable (fun a : Fin (n+1) => lowerMass p a^2) := measurable_of_finite _
  have ht := integral_map (μ := μ) (measurable_quantize n).aemeasurable hm.aestronglyMeasurable
  rw [integral_fintype Integrable.of_finite] at ht
  simp only [smul_eq_mul] at ht
  simpa only [hc,p] using ht

private theorem borel_cdf_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    modeMass μ 1+modeMass μ 3 = ∫ v, (μ.real (Iio v))^2 ∂μ := by
  have ht : Tendsto (fun n => ∫ v, quantizedCdf μ n v^2 ∂μ) atTop
      (𝓝 (∫ v, (μ.real (Iio v))^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact ((measurable_quantizedCdf μ n).pow_const 2).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [] with v
      obtain ⟨h0,h1⟩ := quantizedCdf_bounds μ n v
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (1-quantizedCdf μ n v)]
    · filter_upwards [] with v
      exact (quantizedCdf_tendsto μ v).pow 2
  simp_rw [← quantized_cdf_moment μ] at ht
  exact tendsto_nhds_unique ((quantized_tendsto μ 1).add (quantized_tendsto μ 3)) ht

private theorem borel_zero_iff_dirac (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    modeMass μ 1+modeMass μ 3 = 0 ↔ ∃ c : ℝ, μ = Measure.dirac c := by
  have hm : Measurable (fun v : ℝ => μ.real (Iio v)) :=
    (show Monotone (fun v : ℝ => μ.real (Iio v)) from
      fun _ _ h => measureReal_mono (fun _ hw => lt_of_lt_of_le hw h)).measurable
  constructor
  · intro hx
    have hint : Integrable (fun v : ℝ => (μ.real (Iio v))^2) μ := by
      apply Integrable.of_mem_Icc 0 1 (hm.pow_const 2).aemeasurable
      filter_upwards [] with v
      have h0 : 0 ≤ μ.real (Iio v) := measureReal_nonneg
      have h1 : μ.real (Iio v) ≤ 1 := by
        simpa using (measureReal_mono (μ := μ) (subset_univ (Iio v)))
      exact ⟨sq_nonneg _,by nlinarith [sq_nonneg (1-μ.real (Iio v))]⟩
    have hz : (fun v : ℝ => (μ.real (Iio v))^2) =ᵐ[μ] 0 := by
      apply (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint).mp
      rw [← borel_cdf_moment μ,hx]
    have horder : ∀ᵐ v ∂μ, ∀ᵐ w ∂μ, v ≤ w := by
      filter_upwards [hz] with v hv
      have ha : μ.real (Iio v) = 0 := eq_zero_of_pow_eq_zero hv
      have ha' : μ (Iio v) = 0 := (measureReal_eq_zero_iff).mp ha
      rw [ae_iff]
      simpa only [not_le,Iio] using ha'
    have hswap : ∀ᵐ w ∂μ, ∀ᵐ v ∂μ, v ≤ w :=
      (Measure.ae_ae_comm (measurableSet_le measurable_fst measurable_snd)).mp horder
    have hconst : ∀ᵐ v ∂μ, ∀ᵐ w ∂μ, w = v := by
      filter_upwards [horder,hswap] with v hv hw
      filter_upwards [hv,hw] with w hvw hwv
      exact le_antisymm hwv hvw
    obtain ⟨c,hc⟩ := hconst.exists
    refine ⟨c,?_⟩
    have he : μ.map (id : ℝ → ℝ) = μ.map (fun _ : ℝ => c) := Measure.map_congr hc
    simpa only [Measure.map_id,Measure.map_const,measure_univ,one_smul] using he
  · rintro ⟨c,rfl⟩
    rw [borel_cdf_moment]
    simp [measureReal_def]

private theorem quantized_facts (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (∀ s, 0 ≤ quantizedMass μ n s) ∧ (∑ s, quantizedMass μ n s) = 1 ∧
    quantizedMass μ n 2+quantizedMass μ n 3 = quantizedMass μ n 1+quantizedMass μ n 3 ∧
    quantizedMass μ n 4 = quantizedMass μ n 1+quantizedMass μ n 3 ∧
    0 ≤ quantizedMass μ n 1+quantizedMass μ n 3 ∧
    quantizedMass μ n 1+quantizedMass μ n 3 ≤ 1/3 ∧
    -(quantizedMass μ n 1+quantizedMass μ n 3)/15 ≤
      quantizedMass μ n 0*quantizedMass μ n 3-quantizedMass μ n 1*quantizedMass μ n 2 := by
  obtain ⟨p,hp,hs,he,_⟩ := quantized_is_finite μ n
  simp_rw [he]
  obtain ⟨_,hn,hm,hx,hy,hz,_,_,_⟩ := iid_peak_source p hp hs
  have hb := finite_iid_lower_surface p hp hs
  exact ⟨hn,hm,hy.trans hx.symm,hz.trans hx.symm,hb.1,hb.2.1.le,hb.2.2.2.2.1⟩

private theorem finite_atom_deficit {A : Type*} [Fintype A] [LinearOrder A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (d : A) :
    3*(∑ b, p b*lowerMass p b^2)+(p d)^3 ≤ 1 := by
  let w := fun a b c => p a*p b*p c
  let T := fun (f : A → A → A → ℝ) => ∑ a, ∑ b, ∑ c, f a b c
  have hpoint (a b c : A) :
      (if peak a b c then w a b c else 0)+
      (if peak b a c then w a b c else 0)+
      (if peak a c b then w a b c else 0)+
      (if a=d ∧ b=d ∧ c=d then w a b c else 0) ≤ w a b c := by
    have hw : 0 ≤ w a b c := mul_nonneg (mul_nonneg (hp a) (hp b)) (hp c)
    by_cases hd : a=d ∧ b=d ∧ c=d
    · obtain ⟨rfl,rfl,rfl⟩ := hd
      simp [peak]
    · rw [if_neg hd,add_zero]
      by_cases h1 : peak a b c
      · have h2 : ¬ peak b a c := fun h => lt_asymm h1.1 h.1
        have h3 : ¬ peak a c b := fun h => lt_asymm h1.2 h.2
        simp [h1,h2,h3]
      · by_cases h2 : peak b a c
        · have h3 : ¬ peak a c b := fun h => lt_asymm h2.2 h.1
          simp [h1,h2,h3]
        · by_cases h3 : peak a c b <;> simp [h1,h2,h3,hw]
  have hm : T (fun a b c => if peak a b c then w a b c else 0) =
      ∑ b, p b*lowerMass p b^2 := by
    dsimp [T,w]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    simp only [peak,lowerMass,pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    by_cases ha : a<b <;> by_cases hc : c<b <;> simp [ha,hc] <;> ring
  have hm2 : T (fun a b c => if peak b a c then w a b c else 0) =
      ∑ b, p b*lowerMass p b^2 := by
    rw [← hm]
    dsimp [T,w]
    rw [Finset.sum_comm]
    congr 1
    funext a
    congr 1
    funext b
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> ring
  have hm3 : T (fun a b c => if peak a c b then w a b c else 0) =
      ∑ b, p b*lowerMass p b^2 := by
    rw [← hm]
    dsimp [T,w]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> ring
  have hd : T (fun a b c => if a=d ∧ b=d ∧ c=d then w a b c else 0) = (p d)^3 := by
    dsimp [T,w]
    simp only [ite_and]
    simp
    ring
  have ht : T w = 1 := by
    dsimp [T,w]
    simp [← Finset.mul_sum,hs]
  have hle : T (fun a b c =>
      (if peak a b c then w a b c else 0)+(if peak b a c then w a b c else 0)+
      (if peak a c b then w a b c else 0)+
      (if a=d ∧ b=d ∧ c=d then w a b c else 0)) ≤ T w := by
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      Finset.sum_le_sum fun c _ => hpoint a b c
  change _ ≤ _ at hle
  simp only [T,Finset.sum_add_distrib] at hle
  change T _+T _+T _+T _ ≤ T w at hle
  rw [hm,hm2,hm3,hd,ht] at hle
  linarith

private theorem quantized_atom_deficit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (c : ℝ) :
    3*(quantizedMass μ n 1+quantizedMass μ n 3)+(μ.real {c})^3 ≤ 1 := by
  obtain ⟨p,hp,hs,he,hmono⟩ := quantized_is_finite μ n
  rw [he 1,he 3,(iid_peak_source p hp hs).2.2.2.1]
  have hm := finite_atom_deficit p hp hs (quantize n c)
  have hp3 : (μ.real {c})^3 ≤ (p (quantize n c))^3 :=
    pow_le_pow_left₀ measureReal_nonneg (hmono c) 3
  linarith

private theorem borel_atom_deficit (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    3*(modeMass μ 1+modeMass μ 3)+(μ.real {c})^3 ≤ 1 := by
  exact le_of_tendsto
    ((((quantized_tendsto μ 1).add (quantized_tendsto μ 3)).const_mul 3).add_const _)
    (Eventually.of_forall fun n => quantized_atom_deficit μ n c)

private theorem borel_saturation (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    modeMass μ 3 ≤ 2/15 ∧ modeMass μ 1+modeMass μ 3-1/5 ≤ modeMass μ 3 := by
  have hn (n : ℕ) : quantizedMass μ n 3 ≤ 2/15 ∧
      quantizedMass μ n 1+quantizedMass μ n 3-1/5 ≤ quantizedMass μ n 3 := by
    obtain ⟨p,hp,hs,he,_⟩ := quantized_is_finite μ n
    simp_rw [he]
    exact (finite_iid_lower_surface p hp hs).2.2.2.2.2.2.2
  refine ⟨le_of_tendsto (quantized_tendsto μ 3)
    (Eventually.of_forall fun n => (hn n).1),?_⟩
  exact le_of_tendsto_of_tendsto
    (((quantized_tendsto μ 1).add (quantized_tendsto μ 3)).sub_const (1/5))
    (quantized_tendsto μ 3) (Eventually.of_forall fun n => (hn n).2)

private theorem quantized_correction (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    ∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*(quantizedMass μ n 1+quantizedMass μ n 3) ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤
        quantizedMass μ n 0*quantizedMass μ n 3-quantizedMass μ n 1*quantizedMass μ n 2+
          (quantizedMass μ n 1+quantizedMass μ n 3)/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) := by
  obtain ⟨p,hp,hs,he,_⟩ := quantized_is_finite μ n
  simp_rw [he]
  exact (finite_iid_lower_surface p hp hs).2.2.2.1

private theorem borel_correction (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*(modeMass μ 1+modeMass μ 3) ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤
        modeMass μ 0*modeMass μ 3-modeMass μ 1*modeMass μ 2+
          (modeMass μ 1+modeMass μ 3)/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) := by
  let sn := fun n => Classical.choose (quantized_correction μ n)
  have hsn (n : ℕ) := Classical.choose_spec (quantized_correction μ n)
  change ∀ n, sn n ∈ Icc (0 : ℝ) 1 ∧ _ at hsn
  obtain ⟨s,hs,φ,hφ,hst⟩ := isCompact_Icc.tendsto_subseq (fun n => (hsn n).1)
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hx : Tendsto (fun n => quantizedMass μ (φ n) 1+quantizedMass μ (φ n) 3) atTop
      (𝓝 (modeMass μ 1+modeMass μ 3)) := by
    simpa only [Function.comp_def] using
      ((quantized_tendsto μ 1).add (quantized_tendsto μ 3)).comp hφt
  have hd : Tendsto (fun n => quantizedMass μ (φ n) 0*quantizedMass μ (φ n) 3-
      quantizedMass μ (φ n) 1*quantizedMass μ (φ n) 2) atTop
      (𝓝 (modeMass μ 0*modeMass μ 3-modeMass μ 1*modeMass μ 2)) := by
    simpa only [Function.comp_def] using
      (((quantized_tendsto μ 0).mul (quantized_tendsto μ 3)).sub
        ((quantized_tendsto μ 1).mul (quantized_tendsto μ 2))).comp hφt
  have hcube : s^3 = 1-3*(modeMass μ 1+modeMass μ 3) := by
    have ht : Tendsto (fun n => (sn (φ n))^3) atTop
        (𝓝 (1-3*(modeMass μ 1+modeMass μ 3))) :=
      (tendsto_const_nhds.sub (hx.const_mul 3)).congr'
        (Eventually.of_forall fun n => (hsn (φ n)).2.1.symm)
    exact tendsto_nhds_unique (by simpa only [Function.comp_def] using hst.pow 3) ht
  let C := fun t : ℝ => t^3/45*(1-t)*(1+t+7*t^2-3*t^3-3*t^4)
  have hc : Continuous C := by dsimp [C]; fun_prop
  have hct : Tendsto (fun n => C (sn (φ n))) atTop (𝓝 (C s)) := by
    simpa only [Function.comp_def] using hc.continuousAt.tendsto.comp hst
  refine ⟨s,hs,hcube,?_,?_⟩
  · exact le_of_tendsto_of_tendsto hct (hd.add (hx.div_const 15))
      (Eventually.of_forall fun n => (hsn (φ n)).2.2.1)
  · exact ge_of_tendsto hct (Eventually.of_forall fun n => (hsn (φ n)).2.2.2)

private theorem atomless_cdf_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : (∫ v, (μ.real (Iio v))^2 ∂μ) = 1/3 := by
  let f : ℝ → ℝ → ℝ → ℝ := fun a b c => if b<a ∧ c<a then 1 else 0
  have hf : Measurable (fun p : (ℝ × ℝ) × ℝ => f p.1.1 p.1.2 p.2) := by
    exact Measurable.ite
      ((measurableSet_lt measurable_fst.snd measurable_fst.fst).inter
        (measurableSet_lt measurable_snd measurable_fst.fst))
      measurable_const measurable_const
  have hbound (a b c : ℝ) : ‖f a b c‖ ≤ 1 := by
    dsimp [f]
    split_ifs <;> norm_num
  have hint : Integrable (fun p : (ℝ × ℝ) × ℝ => f p.1.1 p.1.2 p.2)
      ((μ.prod μ).prod μ) :=
    (integrable_const 1).mono' hf.aestronglyMeasurable
      (Eventually.of_forall fun p => hbound p.1.1 p.1.2 p.2)
  have hswap12 : (∫ a, ∫ b, ∫ c, f a b c ∂μ ∂μ ∂μ) =
      ∫ b, ∫ a, ∫ c, f a b c ∂μ ∂μ ∂μ :=
    integral_integral_swap hint.integral_prod_left
  have hswap23 (a : ℝ) : (∫ b, ∫ c, f a b c ∂μ ∂μ) =
      ∫ c, ∫ b, f a b c ∂μ ∂μ := by
    apply integral_integral_swap
    apply (integrable_const 1).mono'
    · exact (Measurable.ite
        ((measurableSet_lt measurable_fst measurable_const).inter
          (measurableSet_lt measurable_snd measurable_const))
        measurable_const measurable_const).aestronglyMeasurable
    · exact Eventually.of_forall fun p => hbound a p.1 p.2
  have hinner (a : ℝ) : (∫ b, ∫ c, f a b c ∂μ ∂μ) = (μ.real (Iio a))^2 := by
    have hc (b : ℝ) : (∫ c, f a b c ∂μ) =
        if b<a then μ.real (Iio a) else 0 := by
      by_cases h : b<a
      · simp only [f,h,true_and]
        exact integral_indicator_one measurableSet_Iio
      · simp [f,h]
    simp_rw [hc]
    have he : (fun b : ℝ => if b<a then μ.real (Iio a) else 0) =
        fun b => (if b<a then (1 : ℝ) else 0)*μ.real (Iio a) := by
      funext b
      split_ifs <;> simp
    rw [he,integral_mul_const]
    rw [show (∫ b, if b<a then (1 : ℝ) else 0 ∂μ) = μ.real (Iio a) from
      integral_indicator_one measurableSet_Iio]
    ring
  have hmass : (∫ a, ∫ b, ∫ c, f a b c ∂μ ∂μ ∂μ) =
      ∫ v, (μ.real (Iio v))^2 ∂μ := by simp_rw [hinner]
  have hperm2 : (∫ a, ∫ b, ∫ c, f b a c ∂μ ∂μ ∂μ) =
      ∫ v, (μ.real (Iio v))^2 ∂μ := hswap12.symm.trans hmass
  have hperm3 : (∫ a, ∫ b, ∫ c, f c a b ∂μ ∂μ ∂μ) =
      ∫ v, (μ.real (Iio v))^2 ∂μ := by
    have hs (a : ℝ) : (∫ b, ∫ c, f c a b ∂μ ∂μ) =
        ∫ c, ∫ b, f c a b ∂μ ∂μ := by
      apply integral_integral_swap
      apply (integrable_const 1).mono'
      · exact (Measurable.ite
          ((measurableSet_lt measurable_const measurable_snd).inter
            (measurableSet_lt measurable_fst measurable_snd))
          measurable_const measurable_const).aestronglyMeasurable
      · filter_upwards [] with p
        exact hbound p.2 a p.1
    simp_rw [hs]
    exact hperm2
  have hpartition : ∀ᵐ a ∂μ, ∀ᵐ b ∂μ, ∀ᵐ c ∂μ,
      f a b c+f b a c+f c a b = 1 := by
    filter_upwards [] with a
    filter_upwards [μ.ae_ne a] with b hba
    filter_upwards [μ.ae_ne a,μ.ae_ne b] with c hca hcb
    dsimp [f]
    split_ifs <;> push_neg at * <;> linarith
  have htotal : (∫ a, ∫ b, ∫ c, f a b c+f b a c+f c a b ∂μ ∂μ ∂μ) = 1 := by
    calc
      _ = ∫ a, ∫ b, ∫ c, (1 : ℝ) ∂μ ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hpartition] with a ha
        apply integral_congr_ae
        filter_upwards [ha] with b hb
        exact integral_congr_ae hb
      _ = 1 := by simp
  have hi (a b : ℝ) : Integrable (fun c => f a b c) μ := by
    apply (integrable_const 1).mono'
    · exact (Measurable.ite
        ((measurableSet_lt measurable_const measurable_const).inter
          (measurableSet_lt measurable_id measurable_const))
        measurable_const measurable_const).aestronglyMeasurable
    · exact Eventually.of_forall fun c => hbound a b c
  have hi2 (a b : ℝ) : Integrable (fun c => f c a b) μ := by
    apply (integrable_const 1).mono'
    · exact (Measurable.ite
        ((measurableSet_lt measurable_const measurable_id).inter
          (measurableSet_lt measurable_const measurable_id))
        measurable_const measurable_const).aestronglyMeasurable
    · exact Eventually.of_forall fun c => hbound c a b
  have hab (a : ℝ) : Integrable (fun b => ∫ c, f a b c ∂μ) μ := by
    apply (integrable_const 1).mono'
    · exact (show Measurable (fun p : ℝ × ℝ => f a p.1 p.2) from
        Measurable.ite
          ((measurableSet_lt measurable_fst measurable_const).inter
            (measurableSet_lt measurable_snd measurable_const))
          measurable_const measurable_const).stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    · filter_upwards [] with b
      exact norm_integral_le_of_norm_le_const (hbound a b)
  have hba (a : ℝ) : Integrable (fun b => ∫ c, f b a c ∂μ) μ := by
    apply (integrable_const 1).mono'
    · exact (show Measurable (fun p : ℝ × ℝ => f p.1 a p.2) from
        Measurable.ite
          ((measurableSet_lt measurable_const measurable_fst).inter
            (measurableSet_lt measurable_snd measurable_fst))
          measurable_const measurable_const).stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    · filter_upwards [] with b
      exact norm_integral_le_of_norm_le_const (hbound b a)
  have hca (a : ℝ) : Integrable (fun b => ∫ c, f c a b ∂μ) μ := by
    apply (integrable_const 1).mono'
    · exact (show Measurable (fun p : ℝ × ℝ => f p.2 a p.1) from
        Measurable.ite
          ((measurableSet_lt measurable_const measurable_snd).inter
            (measurableSet_lt measurable_fst measurable_snd))
          measurable_const measurable_const).stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    · filter_upwards [] with b
      exact norm_integral_le_of_norm_le_const (hbound · a b)
  have hout1 : Integrable (fun a => ∫ b, ∫ c, f a b c ∂μ ∂μ) μ := by
    simpa only [hinner] using (show Integrable (fun a => (μ.real (Iio a))^2) μ from ?_)
    apply Integrable.of_mem_Icc 0 1
    · exact ((show Monotone (fun a : ℝ => μ.real (Iio a)) from
        fun _ _ h => measureReal_mono (Iio_subset_Iio.mpr h)).measurable.pow_const 2).aemeasurable
    · filter_upwards [] with a
      have hlo : 0 ≤ μ.real (Iio a) := measureReal_nonneg
      have hhi : μ.real (Iio a) ≤ 1 := by
        simpa using measureReal_mono (μ := μ) (subset_univ (Iio a))
      exact ⟨sq_nonneg _,by nlinarith [sq_nonneg (1-μ.real (Iio a))]⟩
  have hout2 : Integrable (fun a => ∫ b, ∫ c, f b a c ∂μ ∂μ) μ :=
    hint.integral_prod_left.integral_prod_right
  have hout3 : Integrable (fun a => ∫ b, ∫ c, f c a b ∂μ ∂μ) μ := by
    have hf3 : Integrable (fun p : (ℝ × ℝ) × ℝ => f p.2 p.1.1 p.1.2)
        ((μ.prod μ).prod μ) := by
      apply (integrable_const 1).mono'
      · exact (Measurable.ite
          ((measurableSet_lt measurable_fst.fst measurable_snd).inter
            (measurableSet_lt measurable_fst.snd measurable_snd))
          measurable_const measurable_const).aestronglyMeasurable
      · exact Eventually.of_forall fun p => hbound p.2 p.1.1 p.1.2
    exact hf3.integral_prod_left.integral_prod_left
  simp_rw [integral_add ((hi _ _).add (hi _ _)) (hi2 _ _),
    integral_add (hi _ _) (hi _ _),
    integral_add ((hab _).add (hba _)) (hca _),
    integral_add (hab _) (hba _)] at htotal
  rw [integral_add (hout1.add hout2) hout3,integral_add hout1 hout2,
    hmass,hperm2,hperm3] at htotal
  linarith

/-- Actual Borel product laws are limits of finite iid sources, so the universal
linear determinant lower surface persists without assumptions on atoms. -/
theorem borel_iid_lower_surface (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    let X := modeMass μ 1+modeMass μ 3
    let D := modeMass μ 0*modeMass μ 3-modeMass μ 1*modeMass μ 2
    (∀ s, Tendsto (fun n => quantizedMass μ n s) atTop (𝓝 (modeMass μ s))) ∧
    (∀ s, 0 ≤ modeMass μ s) ∧ (∑ s, modeMass μ s) = 1 ∧
    modeMass μ 2+modeMass μ 3 = X ∧ modeMass μ 4 = X ∧
    0 ≤ X ∧ X ≤ 1/3 ∧ -X/15 ≤ D ∧ -1/45 ≤ D ∧
    (∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*X ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤ D+X/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4)) ∧
    (0 < X → X < 1/3 → -X/15 < D) ∧
    (∀ c : ℝ, 3*X+(μ.real {c})^3 ≤ 1 ∧
      (μ.real {c})^3/45 ≤ D+1/45 ∧
      (0 < μ.real {c} → -1/45 < D)) ∧
    X = ∫ v, (μ.real (Iio v))^2 ∂μ ∧
    (X = 0 ↔ ∃ c : ℝ, μ = Measure.dirac c) ∧
    modeMass μ 3 ≤ 2/15 ∧ X-1/5 ≤ modeMass μ 3 ∧
    (X = 1/3 ↔ D = -1/45) ∧ (X = 1/3 → NullSingletonClass μ) := by
  dsimp only
  have ht := quantized_tendsto μ
  have hx := (ht 1).add (ht 3)
  have hd := ((ht 0).mul (ht 3)).sub ((ht 1).mul (ht 2))
  have hn (s : Fin 5) : 0 ≤ modeMass μ s :=
    ge_of_tendsto (ht s) (Eventually.of_forall fun n => (quantized_facts μ n).1 s)
  have hm : (∑ s, modeMass μ s) = 1 := by
    rw [Fin.sum_univ_five]
    have hl := ((((ht 0).add (ht 1)).add (ht 2)).add (ht 3)).add (ht 4)
    have he : (fun n => quantizedMass μ n 0+quantizedMass μ n 1+quantizedMass μ n 2+
        quantizedMass μ n 3+quantizedMass μ n 4) = fun _ : ℕ => (1 : ℝ) := by
      funext n
      exact (Fin.sum_univ_five (quantizedMass μ n)).symm.trans (quantized_facts μ n).2.1
    rw [he] at hl
    exact tendsto_nhds_unique hl tendsto_const_nhds
  have hy : modeMass μ 2+modeMass μ 3 = modeMass μ 1+modeMass μ 3 := by
    have hy' : Tendsto (fun n => quantizedMass μ n 2+quantizedMass μ n 3) atTop
        (𝓝 (modeMass μ 1+modeMass μ 3)) :=
      hx.congr' (Eventually.of_forall fun n => (quantized_facts μ n).2.2.1.symm)
    exact tendsto_nhds_unique ((ht 2).add (ht 3)) hy'
  have hz : modeMass μ 4 = modeMass μ 1+modeMass μ 3 := by
    have hz' : Tendsto (fun n => quantizedMass μ n 4) atTop
        (𝓝 (modeMass μ 1+modeMass μ 3)) :=
      hx.congr' (Eventually.of_forall fun n => (quantized_facts μ n).2.2.2.1.symm)
    exact tendsto_nhds_unique (ht 4) hz'
  have hx0 : 0 ≤ modeMass μ 1+modeMass μ 3 := add_nonneg (hn 1) (hn 3)
  have hx1 : modeMass μ 1+modeMass μ 3 ≤ 1/3 :=
    le_of_tendsto hx (Eventually.of_forall fun n => (quantized_facts μ n).2.2.2.2.2.1)
  have hl : -(modeMass μ 1+modeMass μ 3)/15 ≤
      modeMass μ 0*modeMass μ 3-modeMass μ 1*modeMass μ 2 := by
    exact le_of_tendsto_of_tendsto (hx.neg.div_const 15) hd
      (Eventually.of_forall fun n => (quantized_facts μ n).2.2.2.2.2.2)
  have hcor := borel_correction μ
  have hsat := borel_saturation μ
  have hdet : modeMass μ 0*modeMass μ 3-modeMass μ 1*modeMass μ 2 =
      (1-(modeMass μ 1+modeMass μ 3))*modeMass μ 3-(modeMass μ 1+modeMass μ 3)^2 := by
    have hp2 : modeMass μ 2 = modeMass μ 1 := by linarith
    have hp0 : modeMass μ 0 = 1-3*modeMass μ 1-2*modeMass μ 3 := by
      rw [Fin.sum_univ_five] at hm
      linarith
    rw [hp0,hp2]
    ring
  refine ⟨ht,hn,hm,hy,hz,hx0,hx1,hl,by linarith,hcor,?_,?_,borel_cdf_moment μ,
    borel_zero_iff_dirac μ,hsat.1,hsat.2,?_,?_⟩
  · intro hXpos hXlt
    obtain ⟨s,hs,hs3,hcorr,_⟩ := hcor
    have hs0 : 0 < s := by
      by_contra h
      have he : s = 0 := le_antisymm (not_lt.mp h) hs.1
      rw [he] at hs3
      norm_num at hs3
      linarith
    have hs1 : s < 1 := by
      by_contra h
      have he : s = 1 := le_antisymm hs.2 (not_lt.mp h)
      rw [he] at hs3
      norm_num at hs3
      linarith
    have hs2 : s^2 ≤ 1 := by nlinarith [sq_nonneg (1-s)]
    have h3 : s^3 ≤ s^2 := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs.2)]
    have h4 : s^4 ≤ s^2 := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs2)]
    have hpoly : 0 < 1+s+7*s^2-3*s^3-3*s^4 := by nlinarith [sq_nonneg s,hs.1]
    have hpos := mul_pos (mul_pos (div_pos (pow_pos hs0 3) (by norm_num : (0 : ℝ) < 45))
      (sub_pos.mpr hs1)) hpoly
    linarith
  · intro c
    have hdef := borel_atom_deficit μ c
    refine ⟨hdef,by linarith,?_⟩
    intro hc
    have hp3 : 0 < (μ.real {c})^3 := pow_pos hc 3
    linarith

  · constructor
    · intro hX
      have hk : modeMass μ 3 = 2/15 := by linarith [hsat.1,hsat.2]
      rw [hdet,hX,hk]
      norm_num
    · intro hD
      linarith
  · intro hX
    constructor
    intro c
    have hd := borel_atom_deficit μ c
    rw [hX] at hd
    have hz3 : (μ.real {c})^3 = 0 := by
      have hnonneg := pow_nonneg (measureReal_nonneg (μ := μ) (s := {c})) 3
      linarith
    exact (measureReal_eq_zero_iff).mp (eq_zero_of_pow_eq_zero hz3)

#print axioms borel_iid_lower_surface

end
end D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
