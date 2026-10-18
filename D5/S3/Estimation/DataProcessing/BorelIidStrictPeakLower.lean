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

/-- The actual five-fold product measure is specified before the mode readout. -/
def source (μ : Measure ℝ) : Measure (Fin 5 → ℝ) := Measure.pi (fun _ => μ)

/-- Borel strict-peak probabilities are pushforward masses of the original samples. -/
def modeMass (μ : Measure ℝ) (s : Fin 5) : ℝ :=
  ∫ v, if mode (v 0) (v 1) (v 2) (v 3) (v 4) = s then (1 : ℝ) else 0 ∂source μ

/-- The approximating law is induced from the same samples by finite quantization. -/
def quantizedMass (μ : Measure ℝ) (n : ℕ) (s : Fin 5) : ℝ :=
  ∫ v, if mode (quantize n (v 0)) (quantize n (v 1)) (quantize n (v 2))
    (quantize n (v 3)) (quantize n (v 4)) = s then (1 : ℝ) else 0 ∂source μ

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
  letI : IsProbabilityMeasure (source μ) := by unfold source; infer_instance
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

private theorem quantized_is_finite (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    ∃ p : Fin (n+1) → ℝ, (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1) ∧
      ∀ s, quantizedMass μ n s = modeLaw p s := by
  let ν := μ.map (quantize n)
  have hν : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  refine ⟨fun a => ν.real {a},fun _ => measureReal_nonneg,?_,?_⟩
  · have ht := integral_fintype (μ := ν) (integrable_const (1 : ℝ))
    simpa using ht.symm
  · intro s
    have hmap : (source μ).map (fun v i => quantize n (v i)) =
        Measure.pi (fun _ : Fin 5 => ν) :=
      Measure.pi_map_pi (fun _ => (measurable_quantize n).aemeasurable)
    have hmeas : Measurable (fun v : Fin 5 → ℝ => fun i => quantize n (v i)) :=
      Measurable.of_eval fun i => (measurable_quantize n).comp (measurable_pi_apply i)
    have hm : Measurable (fun v : Fin 5 → Fin (n+1) =>
        if mode (v 0) (v 1) (v 2) (v 3) (v 4) = s then (1 : ℝ) else 0) :=
      measurable_of_finite _
    have ht := integral_map (μ := source μ) hmeas.aemeasurable hm.aestronglyMeasurable
    rw [hmap,finite_integral] at ht
    exact ht.symm

private theorem quantized_facts (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (∀ s, 0 ≤ quantizedMass μ n s) ∧ (∑ s, quantizedMass μ n s) = 1 ∧
    quantizedMass μ n 2+quantizedMass μ n 3 = quantizedMass μ n 1+quantizedMass μ n 3 ∧
    quantizedMass μ n 4 = quantizedMass μ n 1+quantizedMass μ n 3 ∧
    0 ≤ quantizedMass μ n 1+quantizedMass μ n 3 ∧
    quantizedMass μ n 1+quantizedMass μ n 3 ≤ 1/3 ∧
    -(quantizedMass μ n 1+quantizedMass μ n 3)/15 ≤
      quantizedMass μ n 0*quantizedMass μ n 3-quantizedMass μ n 1*quantizedMass μ n 2 := by
  obtain ⟨p,hp,hs,he⟩ := quantized_is_finite μ n
  simp_rw [he]
  obtain ⟨_,hn,hm,hx,hy,hz,_,_,_⟩ := iid_peak_source p hp hs
  have hb := finite_iid_lower_surface p hp hs
  exact ⟨hn,hm,hy.trans hx.symm,hz.trans hx.symm,hb.1,hb.2.1.le,hb.2.2.2.2.1⟩

private theorem quantized_correction (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    ∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*(quantizedMass μ n 1+quantizedMass μ n 3) ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤
        quantizedMass μ n 0*quantizedMass μ n 3-quantizedMass μ n 1*quantizedMass μ n 2+
          (quantizedMass μ n 1+quantizedMass μ n 3)/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) := by
  obtain ⟨p,hp,hs,he⟩ := quantized_is_finite μ n
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
    (0 < X → X < 1/3 → -X/15 < D) := by
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
  refine ⟨ht,hn,hm,hy,hz,hx0,hx1,hl,by linarith,hcor,?_⟩
  intro hXpos hXlt
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

#print axioms borel_iid_lower_surface

end
end D5.S3.Estimation.DataProcessing.BorelIidStrictPeakLower
