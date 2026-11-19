/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: BV weighted discrepancy and polynomial logarithmic variation bounds. -/

import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! Real-cut BV discrepancy, and polynomial logarithmic weights. -/

open scoped BigOperators Topology ENNReal NNReal
open Set MeasureTheory Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def meshCut (a q i : ℕ) : ℝ := a + (i : ℝ) / q

private def meshStep (a b q : ℕ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  w b - ∑ i ∈ Finset.range ((b - a) * q),
    (w (meshCut a q (i + 1)) - w (meshCut a q i)) *
      (Ioc (a : ℝ) (meshCut a q i)).indicator (fun _ => (1 : ℝ)) x

private lemma meshCut_mem {a b q i : ℕ} (hab : a ≤ b) (hq : 0 < q)
    (hi : i ≤ (b - a) * q) : meshCut a q i ∈ Icc (a : ℝ) b := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hi' : (i : ℝ) ≤ (b - a : ℕ) * q := by exact_mod_cast hi
  rw [Nat.cast_sub hab] at hi'
  dsimp [meshCut]
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · have := (div_le_iff₀ hq').mpr hi'
    linarith

private lemma meshStep_eq {a b q : ℕ} (hab : a ≤ b) (hq : 0 < q)
    (w : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (a : ℝ) b) :
    meshStep a b q w x = w (meshCut a q ⌈(x - a) * q⌉₊) := by
  let j := ⌈(x - a) * q⌉₊
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hj : j ≤ (b - a) * q := by
    rw [Nat.ceil_le]
    push_cast [Nat.cast_sub hab]
    nlinarith [hx.2]
  have hiff (i : ℕ) : x ≤ meshCut a q i ↔ j ≤ i := by
    rw [Nat.ceil_le]
    dsimp [meshCut]
    rw [← le_div_iff₀ hq']
    constructor <;> intro h <;> linarith
  have hs : (∑ i ∈ Finset.range ((b - a) * q),
      (w (meshCut a q (i + 1)) - w (meshCut a q i)) *
        (Ioc (a : ℝ) (meshCut a q i)).indicator (fun _ => (1 : ℝ)) x) =
      ∑ i ∈ Finset.Ico j ((b - a) * q),
        (w (meshCut a q (i + 1)) - w (meshCut a q i)) := by
    simp only [indicator_apply, mem_Ioc, hx.1, true_and, hiff,
      mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  unfold meshStep
  rw [hs, Finset.sum_Ico_sub (fun i => w (meshCut a q i)) hj]
  have hb : meshCut a q ((b - a) * q) = b := by
    dsimp [meshCut]
    push_cast [Nat.cast_sub hab]
    field_simp
    ring
  rw [hb]
  ring

private lemma meshStep_nat {a b q n : ℕ} (hab : a ≤ b) (hq : 0 < q)
    (w : ℝ → ℝ) (hn : n ∈ Finset.Ioc a b) : meshStep a b q w n = w n := by
  have hn' := Finset.mem_Ioc.mp hn
  rw [meshStep_eq hab hq w ⟨by exact_mod_cast hn'.1, by exact_mod_cast hn'.2⟩]
  have h : ((n : ℝ) - a) * q = ((n - a) * q : ℕ) := by
    push_cast [Nat.cast_sub hn'.1.le]
    rfl
  rw [h, Nat.ceil_natCast]
  congr 1
  dsimp [meshCut]
  push_cast [Nat.cast_sub hn'.1.le]
  field_simp
  ring

private lemma mesh_variation {a b q : ℕ} (_hab : a ≤ b) (hq : 0 < q)
    (w : ℝ → ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hv : eVariationOn w univ ≤ ENNReal.ofReal V) :
    (∑ i ∈ Finset.range ((b - a) * q),
      |w (meshCut a q (i + 1)) - w (meshCut a q i)|) ≤ V := by
  apply (ENNReal.ofReal_le_ofReal_iff hV).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  simp_rw [← Real.dist_eq, ← edist_dist]
  apply (eVariationOn.sum_le (s := univ) ?_ (fun _ => mem_univ _)).trans hv
  intro i j hij
  dsimp [meshCut]
  gcongr


private lemma meshStep_bound {a b q : ℕ} (hab : a ≤ b) (hq : 0 < q)
    {w : ℝ → ℝ} {U : ℝ} (hw : ∀ x ∈ Icc (a : ℝ) b, |w x| ≤ U)
    {x : ℝ} (hx : x ∈ Ioc (a : ℝ) b) : |meshStep a b q w x| ≤ U := by
  rw [meshStep_eq hab hq w hx]
  apply hw
  apply meshCut_mem hab hq
  rw [Nat.ceil_le]
  push_cast [Nat.cast_sub hab]
  nlinarith [hx.2]

private lemma meshCut_tendsto {a : ℕ} {x : ℝ} (hx : (a : ℝ) ≤ x) :
    Tendsto (fun n : ℕ => meshCut a (n + 1) ⌈(x - a) * (n + 1)⌉₊) atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝 x) by
      simpa using (tendsto_const_nhds (x := x)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0)))
  · intro n
    have h := Nat.le_ceil ((x - a) * (n + 1))
    dsimp [meshCut]
    push_cast
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr h
    linarith
  · intro n
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (x - a) * (n + 1) by positivity)
    dsimp [meshCut]
    push_cast
    have he : (⌈(x - a) * (n + 1)⌉₊ : ℝ) / ((n : ℝ) + 1) < x - a + 1 / ((n : ℝ) + 1) := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
      calc
        _ < (x - a) * ((n : ℝ) + 1) + 1 := h
        _ = _ := by field_simp
    linarith

private lemma meshStep_integral {a b q : ℕ} (hab : a ≤ b) (hq : 0 < q)
    (w ρ : ℝ → ℝ) (hρ : IntegrableOn ρ (Ioc (a : ℝ) b)) :
    (∫ x in Ioc (a : ℝ) b, meshStep a b q w x * ρ x) =
      w b * (∫ x in Ioc (a : ℝ) b, ρ x) -
      ∑ i ∈ Finset.range ((b - a) * q),
        (w (meshCut a q (i + 1)) - w (meshCut a q i)) *
          ∫ x in Ioc (a : ℝ) (meshCut a q i), ρ x := by
  have hint (i : ℕ) : IntegrableOn
      ((Ioc (a : ℝ) (meshCut a q i)).indicator ρ) (Ioc (a : ℝ) b) :=
    hρ.indicator measurableSet_Ioc
  have heq (x : ℝ) : meshStep a b q w x * ρ x = w b * ρ x -
      ∑ i ∈ Finset.range ((b - a) * q),
        (w (meshCut a q (i + 1)) - w (meshCut a q i)) *
          ((Ioc (a : ℝ) (meshCut a q i)).indicator ρ) x := by
    unfold meshStep
    rw [sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x ∈ Ioc (a : ℝ) (meshCut a q i) <;> simp [hx]
  simp_rw [heq]
  rw [integral_sub (hρ.const_mul _) (integrable_finsetSum _ (fun i _ => (hint i).const_mul _)),
    integral_const_mul, integral_finsetSum _ (fun i _ => (hint i).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, setIntegral_indicator measurableSet_Ioc]
  rw [inter_eq_right.mpr (Ioc_subset_Ioc_right
    (meshCut_mem hab hq (by have := Finset.mem_range.mp hi; omega)).2)]


private lemma atomic_prefix_indicator {a b : ℕ} (c : ℕ → ℝ) {t : ℝ}
    (ht : t ∈ Icc (a : ℝ) b) :
    (∑ n ∈ Finset.Ioc a b, (Ioc (a : ℝ) t).indicator (fun _ => (1 : ℝ)) n * c n) =
      ∑ n ∈ Finset.Ioc a ⌊t⌋₊, c n := by
  have ht0 : 0 ≤ t := (Nat.cast_nonneg a).trans ht.1
  have hs : (Finset.Ioc a b).filter (fun n : ℕ => (n : ℝ) ≤ t) = Finset.Ioc a ⌊t⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff ht0]
    constructor
    · tauto
    · rintro ⟨ha, hn⟩
      exact ⟨⟨ha, by exact_mod_cast hn.trans ht.2⟩, hn⟩
  rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have ha : (a : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  simp [indicator_apply, mem_Ioc, ha]

private lemma meshStep_discrepancy {a b q : ℕ} (hab : a ≤ b) (hq : 0 < q)
    (w ρ : ℝ → ℝ) (c : ℕ → ℝ) (hρ : IntegrableOn ρ (Ioc (a : ℝ) b)) :
    (∑ n ∈ Finset.Ioc a b, meshStep a b q w n * c n) -
        (∫ x in Ioc (a : ℝ) b, meshStep a b q w x * ρ x) =
      w b * ((∑ n ∈ Finset.Ioc a b, c n) - ∫ x in Ioc (a : ℝ) b, ρ x) -
      ∑ i ∈ Finset.range ((b - a) * q),
        (w (meshCut a q (i + 1)) - w (meshCut a q i)) *
          ((∑ n ∈ Finset.Ioc a ⌊meshCut a q i⌋₊, c n) -
            ∫ x in Ioc (a : ℝ) (meshCut a q i), ρ x) := by
  rw [meshStep_integral hab hq w ρ hρ]
  have hs : (∑ n ∈ Finset.Ioc a b, meshStep a b q w n * c n) =
      w b * (∑ n ∈ Finset.Ioc a b, c n) -
      ∑ i ∈ Finset.range ((b - a) * q),
        (w (meshCut a q (i + 1)) - w (meshCut a q i)) *
          (∑ n ∈ Finset.Ioc a ⌊meshCut a q i⌋₊, c n) := by
    have he (n : ℕ) : meshStep a b q w n * c n = w b * c n -
        ∑ i ∈ Finset.range ((b - a) * q),
          (w (meshCut a q (i + 1)) - w (meshCut a q i)) *
            ((Ioc (a : ℝ) (meshCut a q i)).indicator (fun _ => (1 : ℝ)) n * c n) := by
      unfold meshStep
      rw [sub_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum, atomic_prefix_indicator c
      (meshCut_mem hab hq (by have := Finset.mem_range.mp hi; omega))]
  rw [hs]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

private lemma meshStep_error {a b q : ℕ} (hab : a ≤ b) (hq : 0 < q)
    (w ρ : ℝ → ℝ) (c : ℕ → ℝ) {E U V : ℝ}
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hρ : IntegrableOn ρ (Ioc (a : ℝ) b))
    (hv : eVariationOn w univ ≤ ENNReal.ofReal V)
    (hw : ∀ x ∈ Icc (a : ℝ) b, |w x| ≤ U)
    (hc : ∀ y ∈ Icc (a : ℝ) b,
      |(∑ n ∈ Finset.Ioc a ⌊y⌋₊, c n) - ∫ x in Ioc (a : ℝ) y, ρ x| ≤ E) :
    |(∑ n ∈ Finset.Ioc a b, w n * c n) -
        (∫ x in Ioc (a : ℝ) b, meshStep a b q w x * ρ x)| ≤ E * (U + V) := by
  have heq : (∑ n ∈ Finset.Ioc a b, w n * c n) =
      ∑ n ∈ Finset.Ioc a b, meshStep a b q w n * c n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [meshStep_nat hab hq w hn]
  rw [heq, meshStep_discrepancy hab hq w ρ c hρ]
  calc
    _ ≤ |w b * ((∑ n ∈ Finset.Ioc a b, c n) - ∫ x in Ioc (a : ℝ) b, ρ x)| +
        ∑ i ∈ Finset.range ((b - a) * q),
          |(w (meshCut a q (i + 1)) - w (meshCut a q i)) *
            ((∑ n ∈ Finset.Ioc a ⌊meshCut a q i⌋₊, c n) -
              ∫ x in Ioc (a : ℝ) (meshCut a q i), ρ x)| :=
      (abs_sub _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ U * E + (∑ i ∈ Finset.range ((b - a) * q),
        |w (meshCut a q (i + 1)) - w (meshCut a q i)|) * E := by
      rw [Finset.sum_mul]
      apply add_le_add
      · rw [abs_mul]
        apply mul_le_mul (hw b ⟨by exact_mod_cast hab, le_rfl⟩) _ (abs_nonneg _) hU
        simpa only [Nat.floor_natCast] using hc b ⟨by exact_mod_cast hab, le_rfl⟩
      · apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact hc _ (meshCut_mem hab hq (by have := Finset.mem_range.mp hi; omega))
    _ ≤ U * E + V * E := by gcongr; exact mesh_variation hab hq w hV hv
    _ = _ := by ring


/-- An integrable density and an atomic sum with uniformly bounded real-cut discrepancy obey the
BV weighted bound. -/
theorem bv_discrepancy_bound (a b : ℕ) (c : ℕ → ℝ) (ρ w : ℝ → ℝ)
    (E U V : ℝ) (hab : a ≤ b) (hE : 0 ≤ E) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hρ : IntegrableOn ρ (Ioc (a : ℝ) b)) (hw : BoundedVariationOn w univ)
    (hv : eVariationOn w univ ≤ ENNReal.ofReal V)
    (hbound : ∀ x ∈ Icc (a : ℝ) b, |w x| ≤ U)
    (hc : ∀ y ∈ Icc (a : ℝ) b,
      |(∑ n ∈ Finset.Ioc a ⌊y⌋₊, c n) - ∫ x in Ioc (a : ℝ) y, ρ x| ≤ E) :
    |(∑ n ∈ Finset.Ioc a b, w n * c n) -
      ∫ x in Ioc (a : ℝ) b, w x * ρ x| ≤ E * (U + V) := by
  have hmeas (n : ℕ) : Measurable (meshStep a b (n + 1) w) := by
    unfold meshStep
    exact measurable_const.sub (Finset.measurable_sum _ (fun i _ =>
      measurable_const.mul (measurable_const.indicator measurableSet_Ioc)))
  have hcont : ∀ᵐ x : ℝ, ContinuousAt w x := by
    exact ae_iff.mpr (hw.countable_not_continuousAt.measure_zero volume)
  have hlim : Tendsto (fun n : ℕ =>
      ∫ x in Ioc (a : ℝ) b, meshStep a b (n + 1) w x * ρ x) atTop
        (𝓝 (∫ x in Ioc (a : ℝ) b, w x * ρ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => U * |ρ x|)
    · intro n
      exact (hmeas n).aestronglyMeasurable.mul hρ.aestronglyMeasurable
    · exact hρ.norm.const_mul U
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (meshStep_bound hab (by omega) hbound hx) (abs_nonneg _)
    · filter_upwards [ae_restrict_of_ae hcont, ae_restrict_mem measurableSet_Ioc] with x hx hxi
      have hm : Tendsto (fun n : ℕ => meshStep a b (n + 1) w x) atTop (𝓝 (w x)) := by
        simp_rw [meshStep_eq hab (Nat.succ_pos _) w hxi]
        simpa only [Function.comp_def, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
          hx.tendsto.comp (meshCut_tendsto (a := a) (x := x) hxi.1.le)
      exact hm.mul_const (ρ x)
  apply le_of_tendsto ((tendsto_const_nhds.sub hlim).abs)
  exact Filter.Eventually.of_forall (fun n => meshStep_error hab (Nat.succ_pos n)
    w ρ c hE hU hV hρ hv hbound hc)


/-- Real-cut discrepancy bounds on a dyadic interval control every BV-weighted correlation,
including arbitrary values at integer atoms. -/
theorem bv_correlation_discrepancy (N c E U : ℝ) (f : ℕ → ℝ) (v : ℝ → ℝ)
    (hN : 2 ≤ N) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hv : BoundedVariationOn v (Icc N (2 * N)))
    (hbound : ∀ x ∈ Icc N (2 * N), |v x| ≤ U)
    (hc : ∀ y ∈ Icc N (2 * N),
      |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊y⌋₊, f n) - c * (y - N)| ≤ E) :
    |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, v n * f n) -
      c * (∫ x in N..2 * N, v x)| ≤ E * (U + (eVariationOn v (Icc N (2 * N))).toReal) := by
  let a := ⌊N⌋₊
  let b := ⌈2 * N⌉₊
  let φ : ℝ → ℝ := fun x => max N (min (2 * N) x)
  let w := v ∘ φ
  let ρ := (Ioc N (2 * N)).indicator (fun _ => c)
  let g : ℕ → ℝ := fun n => if n ≤ ⌊2 * N⌋₊ then f n else 0
  have hN0 : 0 ≤ N := by linarith
  have ha : (a : ℝ) ≤ N := Nat.floor_le hN0
  have hb : 2 * N ≤ (b : ℝ) := Nat.le_ceil _
  have hab : a ≤ b := by exact_mod_cast (ha.trans (by linarith : N ≤ (b : ℝ)))
  have hφ : MapsTo φ univ (Icc N (2 * N)) := by
    intro x _
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hvar : eVariationOn w univ ≤ eVariationOn v (Icc N (2 * N)) :=
    eVariationOn.comp_le_of_monotoneOn v φ
      (fun x _ y _ h => max_le_max_left _ (min_le_min_left _ h)) hφ
  have hw : BoundedVariationOn w univ := ne_top_of_le_ne_top hv hvar
  have hwbound (x : ℝ) : |w x| ≤ U := hbound _ (hφ (mem_univ x))
  have hρ : IntegrableOn ρ (Ioc (a : ℝ) b) :=
    (integrableOn_const (s := Ioc (a : ℝ) b) (C := c)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).indicator measurableSet_Ioc
  have hsum (y : ℝ) (hy : (a : ℝ) ≤ y) :
      (∑ n ∈ Finset.Ioc a ⌊y⌋₊, g n) = ∑ n ∈ Finset.Ioc a ⌊φ y⌋₊, f n := by
    have hy' : a ≤ ⌊y⌋₊ := (Nat.le_floor_iff ((Nat.cast_nonneg a).trans hy)).mpr hy
    have hN' : a ≤ ⌊2 * N⌋₊ := Nat.floor_le_floor (by linarith)
    have hflo : ⌊φ y⌋₊ = min ⌊2 * N⌋₊ ⌊y⌋₊ := by
      dsimp [φ]
      rw [Nat.floor_mono.map_max, Nat.floor_mono.map_min, max_eq_right (le_min hN' hy')]
    rw [hflo]
    change (∑ n ∈ Finset.Ioc a ⌊y⌋₊, if n ≤ ⌊2 * N⌋₊ then f n else 0) = _
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, le_min_iff]
    tauto
  have hint (y : ℝ) : (∫ x in Ioc (a : ℝ) y, ρ x) = c * (φ y - N) := by
    dsimp [ρ]
    rw [setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc, max_eq_right ha,
      setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
    dsimp [φ]
    rw [min_comm y (2 * N)]
    by_cases hy : N ≤ min (2 * N) y
    · rw [max_eq_left (sub_nonneg.mpr hy), max_eq_right hy]
      ring
    · have hle := (not_le.mp hy).le
      rw [max_eq_right (sub_nonpos.mpr hle), max_eq_left hle]
      ring
  have hcuts (y : ℝ) (hy : y ∈ Icc (a : ℝ) b) :
      |(∑ n ∈ Finset.Ioc a ⌊y⌋₊, g n) - ∫ x in Ioc (a : ℝ) y, ρ x| ≤ E := by
    rw [hsum y hy.1, hint y]
    exact hc _ (hφ (mem_univ y))
  have hmain := bv_discrepancy_bound a b g ρ w E U
    (eVariationOn v (Icc N (2 * N))).toReal hab hE hU ENNReal.toReal_nonneg hρ hw
    (hvar.trans_eq (ENNReal.ofReal_toReal hv).symm)
    (fun x _ => hwbound x) hcuts
  have hphi (x : ℝ) (hx : x ∈ Icc N (2 * N)) : w x = v x := by
    dsimp [w, φ]
    rw [min_eq_right hx.2, max_eq_right hx.1]
  have hsum' : (∑ n ∈ Finset.Ioc a b, w n * g n) =
      ∑ n ∈ Finset.Ioc a ⌊2 * N⌋₊, v n * f n := by
    have hfb : ⌊2 * N⌋₊ ≤ b := (Nat.floor_le_floor hb).trans_eq (Nat.floor_natCast b)
    symm
    calc
      _ = ∑ n ∈ Finset.Ioc a ⌊2 * N⌋₊, w n * g n := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' := Finset.mem_Ioc.mp hn
        have hx : (n : ℝ) ∈ Icc N (2 * N) :=
          ⟨((Nat.floor_lt hN0).mp hn'.1).le, (Nat.le_floor_iff (by positivity)).mp hn'.2⟩
        simp only [g, ite_eq_left hn'.2, hphi _ hx]
      _ = _ := by
        apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right hfb)
        intro n hn hnot
        have hn' := Finset.mem_Ioc.mp hn
        have hn2 : ¬n ≤ ⌊2 * N⌋₊ := by simpa [Finset.mem_Ioc, hn'.1] using hnot
        simp [g, hn2]
  have hint' : (∫ x in Ioc (a : ℝ) b, w x * ρ x) = c * (∫ x in N..2 * N, v x) := by
    have heq : (fun x => w x * ρ x) = (Ioc N (2 * N)).indicator (fun x => c * w x) := by
      funext x
      dsimp only [ρ]
      simp only [indicator_apply]
      split_ifs <;> ring
    rw [heq, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (Ioc_subset_Ioc ha hb), integral_const_mul]
    rw [intervalIntegral.integral_of_le (by linarith : N ≤ 2 * N)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact hphi x ⟨hx.1.le, hx.2⟩
  rwa [hsum', hint'] at hmain


private lemma polynomial_size_and_lipschitz (p : Polynomial ℝ) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ T : ℝ, 1 ≤ T →
      (∀ x ∈ Icc (0 : ℝ) T, |p.eval x| ≤ A * T ^ p.natDegree) ∧
      LipschitzOnWith (D * T ^ p.natDegree).toNNReal p.eval (Icc (0 : ℝ) T) := by
  let A := ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|
  let D := ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * (i : ℝ)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨A, D, hA, hD, ?_⟩
  intro T hT
  have hp (i : ℕ) (hi : i ∈ Finset.range (p.natDegree + 1)) {x : ℝ}
      (hx : x ∈ Icc (0 : ℝ) T) : |x| ^ i ≤ T ^ p.natDegree := by
    apply (pow_le_pow_left₀ (b := T) (abs_nonneg x)
      (by simpa only [abs_of_nonneg hx.1] using hx.2) i).trans
    exact pow_le_pow_right₀ (m := i) (n := p.natDegree) hT
      (by have := Finset.mem_range.mp hi; omega)
  constructor
  · intro x hx
    rw [Polynomial.eval_eq_sum_range]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    dsimp [A]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hp i hi hx) (abs_nonneg _)
  · apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, Polynomial.eval_eq_sum_range,
      Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    change _ ≤ (D * T ^ p.natDegree) * |x - y|
    dsimp [D]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [← mul_sub, abs_mul]
    have hpow : max |x| |y| ^ (i - 1) ≤ T ^ p.natDegree := by
      have hmax : max |x| |y| ≤ T := max_le
        (by simpa only [abs_of_nonneg hx.1] using hx.2)
        (by simpa only [abs_of_nonneg hy.1] using hy.2)
      apply (pow_le_pow_left₀ (b := T) (by positivity) hmax (i - 1)).trans
      exact pow_le_pow_right₀ (m := i - 1) (n := p.natDegree) hT
        (by have := Finset.mem_range.mp hi; omega)
    calc
      _ ≤ |p.coeff i| * (|x - y| * (i : ℝ) * max |x| |y| ^ (i - 1)) :=
        mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le x y i) (abs_nonneg _)
      _ ≤ |p.coeff i| * (|x - y| * (i : ℝ) * T ^ p.natDegree) := by gcongr
      _ = _ := by ring

/-- Multiplying a macroscopic BV weight by a fixed polynomial in log x costs at most its degree
in log N. -/
theorem polynomial_log_bv_bound (p : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N U V : ℝ) (w : ℝ → ℝ),
      2 ≤ N → 0 ≤ U → 0 ≤ V → BoundedVariationOn w univ →
      (∀ t, |w t| ≤ U) → eVariationOn w univ ≤ ENNReal.ofReal V →
      BoundedVariationOn (fun x => w (x / N) * p.eval (Real.log x)) (Icc N (2 * N)) ∧
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ x ∈ Icc N (2 * N), |w (x / N) * p.eval (Real.log x)| ≤ K) ∧
        K + (eVariationOn (fun x => w (x / N) * p.eval (Real.log x)) (Icc N (2 * N))).toReal ≤
          C * (U + V) * (1 + Real.log N) ^ p.natDegree := by
  obtain ⟨A, D, hA, hD, hp⟩ := polynomial_size_and_lipschitz p
  refine ⟨A + D, by positivity, ?_⟩
  intro N U V w hN hU hV _hw hw hvar
  have hN0 : 0 < N := by linarith
  let T := 1 + Real.log N
  have hT : 1 ≤ T := by dsimp [T]; linarith [Real.log_nonneg (by linarith : 1 ≤ N)]
  have hTd : 0 ≤ T ^ p.natDegree := by positivity
  have hlog (x : ℝ) (hx : x ∈ Icc N (2 * N)) : Real.log x ∈ Icc (0 : ℝ) T := by
    refine ⟨Real.log_nonneg (by linarith [hx.1]), ?_⟩
    have h := Real.log_le_log (hN0.trans_le hx.1) hx.2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at h
    dsimp [T]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlvar : eVariationOn Real.log (Icc N (2 * N)) ≤ ENNReal.ofReal 1 := by
    have h := eVariationOn.comp_le_of_monotoneOn id Real.log
      (Real.strictMonoOn_log.monotoneOn.mono (fun x hx => hN0.trans_le hx.1))
      (show MapsTo Real.log (Icc N (2 * N)) (Icc (Real.log N) (Real.log (2 * N))) from
        fun x hx => ⟨Real.log_le_log hN0 hx.1,
          Real.log_le_log (hN0.trans_le hx.1) hx.2⟩)
    simp only [Function.id_comp, eVariationOn_id_Icc] at h
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne']
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpvar : eVariationOn (fun x => p.eval (Real.log x)) (Icc N (2 * N)) ≤
      ENNReal.ofReal (D * T ^ p.natDegree) := by
    have h0 := (hp T hT).2.comp_eVariationOn_le hlog
    have h : eVariationOn (p.eval ∘ Real.log) (Icc N (2 * N)) ≤
        ((D * T ^ p.natDegree).toNNReal : ℝ≥0∞) * ENNReal.ofReal 1 := by
      apply h0.trans
      gcongr
    simpa only [ENNReal.coe_nnreal_eq,
      Real.coe_toNNReal _ (by positivity : 0 ≤ D * T ^ p.natDegree),
      ENNReal.ofReal_one, mul_one,
      Function.comp_def] using h
  have hwvar : eVariationOn (fun x => w (x / N)) (Icc N (2 * N)) ≤ ENNReal.ofReal V :=
    (eVariationOn.comp_le_of_monotoneOn w (fun x : ℝ => x / N)
      (fun x _ y _ h => div_le_div_of_nonneg_right h hN0.le)
      (fun _ _ => mem_univ _)).trans hvar
  have hmul := eVariation_mul_le (f := fun x : ℝ => w (x / N))
    (g := fun x => p.eval (Real.log x))
    (s := Icc N (2 * N))
    (C := ENNReal.ofReal U) (D := ENNReal.ofReal (A * T ^ p.natDegree))
    (fun x _ => by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hw _))
    (fun x hx => by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal ((hp T hT).1 _ (hlog x hx)))
  have hprod : eVariationOn (fun x => w (x / N) * p.eval (Real.log x)) (Icc N (2 * N)) ≤
      ENNReal.ofReal ((U * D + A * V) * T ^ p.natDegree) := by
    apply hmul.trans
    calc
      _ ≤ ENNReal.ofReal U * ENNReal.ofReal (D * T ^ p.natDegree) +
          ENNReal.ofReal (A * T ^ p.natDegree) * ENNReal.ofReal V := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul hU, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hbv : BoundedVariationOn (fun x => w (x / N) * p.eval (Real.log x)) (Icc N (2 * N)) :=
    ne_top_of_le_ne_top (by finiteness) hprod
  refine ⟨hbv, U * A * T ^ p.natDegree, by positivity, ?_, ?_⟩
  · intro x hx
    rw [abs_mul]
    calc
      _ ≤ U * (A * T ^ p.natDegree) := mul_le_mul (hw _) ((hp T hT).1 _ (hlog x hx))
        (abs_nonneg _) hU
      _ = _ := by ring
  · have ht := ENNReal.toReal_mono (by finiteness) hprod
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    change _ ≤ (A + D) * (U + V) * T ^ p.natDegree
    nlinarith [mul_nonneg (mul_nonneg hD hV) hTd]


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
