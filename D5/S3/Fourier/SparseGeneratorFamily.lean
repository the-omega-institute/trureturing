/- GID: D5/S3/Fourier/SparseGeneratorFamily
   generality: G
   mirror-B: D5/B/S3/Fourier/SparseGeneratorFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform cyclic sampling yields sparse symmetric generating families with positive gap. -/

import D5.S3.Fourier.GeneratorRowStability
import D5.S3.Fourier.FinitePoisson
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.UniformOn
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Sym.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace D5.S3.Fourier.SparseGeneratorGapObstruction

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate
open FullBispectrumStability (cyclic_parseval dft_translation unit_mul_conj)

noncomputable section

def logOrder (N : ℕ) : ℝ := Real.log N
def sampleSize (N : ℕ) : ℕ := Nat.ceil (16 * logOrder N)
def radius (N : ℕ) : ℕ := Nat.floor (logOrder N / 16)
def familyDomain (N : ℕ) : Prop := Nat.ceil (Real.exp 128) ≤ N

def chordAverage {N : ℕ} [NeZero N] (S : Finset (ZMod N)) (a : ZMod N) : ℝ :=
  (∑ s ∈ S, ‖ZMod.stdAddChar (a * s) - 1‖ ^ 2) / S.card

/-- The empty frequency domain has gap zero. -/
def ordinaryGap {N : ℕ} [NeZero N] (S : Finset (ZMod N)) : ℝ :=
  if h : ((univ : Finset (ZMod N)).erase 0).Nonempty then
    ((univ : Finset (ZMod N)).erase 0).inf' h (chordAverage S)
  else 0

def generating {N : ℕ} [NeZero N] (S : Finset (ZMod N)) : Prop :=
  AddSubgroup.closure (S : Set (ZMod N)) = ⊤

def goodSet (N : ℕ) [NeZero N] (S : Finset (ZMod N)) : Prop :=
  0 ∉ S ∧ (∀ s, s ∈ S ↔ -s ∈ S) ∧ S.card = 2 * sampleSize N ∧
    1 ≤ ordinaryGap S

/-- A fixed choice by order, with the empty set outside the existence domain. -/
def familySet (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  by
    classical
    exact if h : ∃ S : Finset (ZMod N), goodSet N S then Classical.choose h else ∅

def observationTolerance (N : ℕ) : ℝ := Real.pi / (2 * (radius N : ℝ))

def bispectrum {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (k l : ZMod N) : ℂ :=
  F k * F l * conj (F (k + l))

def countingError {N : ℕ} (f g : ZMod N → ℂ) (t : ZMod N) : ℝ :=
  if h : N = 0 then 0 else
    letI : NeZero N := ⟨h⟩
    ∑ x, ‖g x - f (x - t)‖ ^ 2

lemma char_sum {N : ℕ} [NeZero N] (a : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (a * k) =
      if a = 0 then (N : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, ZMod.card]
  · rw [if_neg ha]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ha)

lemma large_log {N : ℕ} (hN : familyDomain N) : 128 ≤ logOrder N := by
  have hexp : Real.exp 128 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hn : 0 < (N : ℝ) := (Real.exp_pos 128).trans_le hexp
  exact (Real.le_log_iff_exp_le hn).2 hexp

lemma large_order_pos {N : ℕ} (hN : familyDomain N) : 0 < N := by
  have hexp : Real.exp 128 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  exact_mod_cast (Real.exp_pos 128).trans_le hexp

private lemma log_two_lt : Real.log 2 < 3 / 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 4 by norm_num)
  norm_num at h
  linarith

lemma parameters_bounds {N : ℕ} (hN : familyDomain N) :
    16 * logOrder N ≤ (sampleSize N : ℝ) ∧
    (sampleSize N : ℝ) + 1 ≤ 17 * logOrder N ∧
    8 ≤ radius N ∧
    (radius N : ℝ) ≤ logOrder N / 16 ∧
    logOrder N / 32 ≤ (radius N : ℝ) := by
  have hL := large_log hN
  have hL0 : 0 ≤ logOrder N := by linarith
  have hceil := Nat.le_ceil (16 * logOrder N)
  have hceil' := Nat.ceil_le_floor_add_one (16 * logOrder N)
  have hfloor := Nat.floor_le (show 0 ≤ 16 * logOrder N by positivity)
  have hfloor' := Nat.lt_floor_add_one (logOrder N / 16)
  have hr8 : 8 ≤ radius N := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ logOrder N / 16)).2
    norm_num
    linarith
  have hq : (sampleSize N : ℝ) ≤ 16 * logOrder N + 1 := by
    have h : (Nat.ceil (16 * logOrder N) : ℝ) ≤
        (Nat.floor (16 * logOrder N) : ℝ) + 1 := by exact_mod_cast hceil'
    dsimp [sampleSize]
    linarith
  exact ⟨hceil, by linarith, hr8,
    Nat.floor_le (by positivity : 0 ≤ logOrder N / 16), by
      change logOrder N / 32 ≤ (Nat.floor (logOrder N / 16) : ℝ)
      linarith⟩

lemma tolerance_bounds {N : ℕ} (hN : familyDomain N) :
    0 < observationTolerance N ∧ observationTolerance N ≤ Real.pi / 16 ∧
    Real.pi / 16 < 1 / 4 := by
  have hr : (8 : ℝ) ≤ radius N := by exact_mod_cast (parameters_bounds hN).2.2.1
  dsimp [observationTolerance]
  refine ⟨by positivity, ?_, by linarith [Real.pi_lt_four]⟩
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)

private lemma binomial_weighted_bound (p r : ℕ) :
    ((p + r).choose r : ℝ) ≤
      Real.exp ((r : ℝ) * Real.log 512 + ((p : ℝ) + r) / 512) := by
  have hterm : ((p + r).choose r : ℝ) * (1 / 512 : ℝ) ^ r ≤
      (1 / 512 + 1 : ℝ) ^ (p + r) := by
    rw [add_pow]
    have h := Finset.single_le_sum
      (s := range (p + r + 1))
      (f := fun i => (1 / 512 : ℝ) ^ i * 1 ^ (p + r - i) *
        ((p + r).choose i : ℝ))
      (fun i _ => by positivity) (show r ∈ range (p + r + 1) by simp)
    simpa [mul_comm] using h
  have hexp : (1 / 512 + 1 : ℝ) ^ (p + r) ≤
      Real.exp (((p : ℝ) + r) / 512) := by
    calc
      _ ≤ (Real.exp (1 / 512)) ^ (p + r) :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _ ) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hpow : (512 : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log 512) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc
    ((p + r).choose r : ℝ) =
        (((p + r).choose r : ℝ) * (1 / 512 : ℝ) ^ r) * 512 ^ r := by
          rw [mul_assoc, ← mul_pow]
          norm_num
    _ ≤ Real.exp (((p : ℝ) + r) / 512) * 512 ^ r :=
      mul_le_mul_of_nonneg_right (hterm.trans hexp) (by positivity)
    _ = _ := by rw [hpow, ← Real.exp_add]; congr 1; ring

lemma volume_numeric_bound {N : ℕ} (hN : familyDomain N) (p : ℕ)
    (hp : (p : ℝ) ≤ 34 * logOrder N) :
    ((p + radius N).choose (radius N) : ℝ) ≤ Real.sqrt N := by
  have hL := large_log hN
  have hr := (parameters_bounds hN).2.2.2.1
  have hlog : Real.log 512 < 27 / 4 := by
    have he : (512 : ℝ) = 2 ^ 9 := by norm_num
    rw [he, Real.log_pow]
    nlinarith [log_two_lt]
  have hbound : (radius N : ℝ) * Real.log 512 +
      ((p : ℝ) + radius N) / 512 ≤ logOrder N / 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg (radius N))
    nlinarith
  have hn := large_order_pos hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hn
  have hsqrt : Real.exp (logOrder N / 2) = Real.sqrt N := by
    rw [logOrder, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  exact (binomial_weighted_bound p (radius N)).trans
    ((Real.exp_le_exp.mpr hbound).trans_eq hsqrt)

private instance cyclicMeasurable (N : ℕ) : MeasurableSpace (ZMod N) := ⊤

private def cyclicMeasure (N : ℕ) [NeZero N] : Measure (ZMod N) :=
  uniformOn Set.univ

private instance cyclicProbability (N : ℕ) [NeZero N] :
    IsProbabilityMeasure (cyclicMeasure N) := by
  unfold cyclicMeasure
  infer_instance

private lemma cyclic_singleton {N : ℕ} [NeZero N] (x : ZMod N) :
    (cyclicMeasure N).real {x} = 1 / (N : ℝ) := by
  rw [measureReal_def, cyclicMeasure, uniformOn_univ, Measure.count_singleton]
  simp [ENNReal.toReal_div, ZMod.card]

private lemma char_integral {N : ℕ} [NeZero N] (a : ZMod N) (ha : a ≠ 0) :
    ∫ x, (ZMod.stdAddChar (a * x)).re ∂cyclicMeasure N = 0 := by
  rw [integral_fintype Integrable.of_finite]
  simp_rw [cyclic_singleton, smul_eq_mul]
  rw [← mul_sum, ← Complex.re_sum, char_sum, if_neg ha]
  simp

private def sampleMeasure (N q : ℕ) [NeZero N] : Measure (Fin q → ZMod N) :=
  Measure.pi (fun _ => cyclicMeasure N)

private instance sampleProbability (N q : ℕ) [NeZero N] :
    IsProbabilityMeasure (sampleMeasure N q) := by
  unfold sampleMeasure
  infer_instance

private lemma sample_independent {N q : ℕ} [NeZero N] :
    iIndepFun (fun i : Fin q => fun X : Fin q → ZMod N => X i) (sampleMeasure N q) := by
  exact iIndepFun_pi (fun _ => (measurable_of_finite id).aemeasurable)

private lemma sample_tail {N q : ℕ} [NeZero N] (hq : q ≠ 0)
    (a : ZMod N) (ha : a ≠ 0) :
    (sampleMeasure N q).real {X | (q : ℝ) / 2 ≤
      ∑ j : Fin q, (ZMod.stdAddChar (a * X j)).re} ≤ Real.exp (-(q : ℝ) / 8) := by
  let Y : Fin q → (Fin q → ZMod N) → ℝ :=
    fun j X => (ZMod.stdAddChar (a * X j)).re
  have hi : iIndepFun Y (sampleMeasure N q) :=
    iIndepFun_pi (μ := fun _ : Fin q => cyclicMeasure N)
      (fun _ : Fin q => (measurable_of_finite
        (fun x : ZMod N => (ZMod.stdAddChar (a * x)).re)).aemeasurable)
  have hg (j : Fin q) : HasSubgaussianMGF (Y j) 1 (sampleMeasure N q) := by
    have hm : AEMeasurable (Y j) (sampleMeasure N q) :=
      (measurable_of_finite _).aemeasurable
    have hb : ∀ᵐ X ∂sampleMeasure N q, Y j X ∈ Set.Icc (-1 : ℝ) 1 := by
      apply ae_of_all
      intro X
      have hnorm : ‖ZMod.stdAddChar (a * X j)‖ = 1 :=
        (ZMod.stdAddChar (N := N)).norm_apply _
      have habs := Complex.abs_re_le_norm (ZMod.stdAddChar (a * X j))
      rw [hnorm] at habs
      exact abs_le.mp habs
    have hm0 : ∫ X, Y j X ∂sampleMeasure N q = 0 := by
      change ∫ X, (ZMod.stdAddChar (a * X j)).re
        ∂Measure.pi (fun _ : Fin q => cyclicMeasure N) = 0
      rw [integral_comp_eval (μ := fun _ : Fin q => cyclicMeasure N) (i := j)
        (f := fun x : ZMod N => (ZMod.stdAddChar (a * x)).re)
        (measurable_of_finite _).aestronglyMeasurable]
      exact char_integral a ha
    convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hm0 using 1 <;>
      norm_num
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi
    (s := univ) (c := fun _ => 1) (fun j _ => hg j)
    (show 0 ≤ (q : ℝ) / 2 by positivity)
  have he : -((q : ℝ) / 2) ^ 2 / (2 * (q : ℝ)) = -(q : ℝ) / 8 := by
    field_simp
    ring
  simpa [Y, he] using h

private lemma torsion_two_values {N : ℕ} [NeZero N] (x : ZMod N)
    (hx : 2 * x = 0) : x.val = 0 ∨ x.val = N / 2 := by
  have hv : (x + x).val = 0 := by rw [← two_mul, hx, ZMod.val_zero]
  by_cases hlt : x.val + x.val < N
  · rw [ZMod.val_add_of_lt hlt] at hv
    exact Or.inl (by omega)
  · have hge : N ≤ x.val + x.val := by omega
    rw [ZMod.val_add_of_le hge] at hv
    have hxx : x.val < N := x.val_lt
    exact Or.inr (by omega)

private lemma torsion_two_card {N : ℕ} [NeZero N] :
    ((univ : Finset (ZMod N)).filter (fun x => 2 * x = 0)).card ≤ 2 := by
  classical
  let T := (univ : Finset (ZMod N)).filter (fun x => 2 * x = 0)
  have himg : T.image ZMod.val ⊆ {0, N / 2} := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
    have ht := torsion_two_values x (mem_filter.mp hx).2
    simpa using ht
  calc
    T.card = (T.image ZMod.val).card :=
      (card_image_of_injective _ (ZMod.val_injective N)).symm
    _ ≤ ({0, N / 2} : Finset ℕ).card := card_le_card himg
    _ ≤ 2 := card_le_two

private lemma sample_eval {N q : ℕ} [NeZero N] (j : Fin q) (s : Set (ZMod N)) :
    sampleMeasure N q ((fun X => X j) ⁻¹' s) = cyclicMeasure N s := by
  exact (measurePreserving_eval (fun _ : Fin q => cyclicMeasure N) j).measure_preimage
    (Set.toFinite s).measurableSet.nullMeasurableSet

private lemma sample_eval_real {N q : ℕ} [NeZero N] (j : Fin q) (x : ZMod N) :
    (sampleMeasure N q).real {X | X j = x} = 1 / (N : ℝ) := by
  change (sampleMeasure N q ((fun X => X j) ⁻¹' {x})).toReal = _
  rw [sample_eval]
  exact cyclic_singleton x

private lemma sample_pair_real {N q : ℕ} [NeZero N] (i j : Fin q) (hij : i ≠ j)
    (x y : ZMod N) :
    (sampleMeasure N q).real {X | X i = x ∧ X j = y} = (1 / (N : ℝ)) ^ 2 := by
  have h := (sample_independent (N := N) (q := q)).indepFun hij
  have he := h.measure_inter_preimage_eq_mul {x} {y}
    (measurableSet_singleton _) (measurableSet_singleton _)
  change (sampleMeasure N q (((fun X => X i) ⁻¹' {x}) ∩
    ((fun X => X j) ⁻¹' {y}))).toReal = _
  rw [he, ENNReal.toReal_mul]
  change (sampleMeasure N q).real {X | X i = x} *
    (sampleMeasure N q).real {X | X j = y} = _
  rw [sample_eval_real, sample_eval_real, pow_two]

private lemma sample_collision {N q : ℕ} [NeZero N] (i j : Fin q) (hij : i ≠ j)
    (f : ZMod N → ZMod N) :
    (sampleMeasure N q).real {X | X j = f (X i)} ≤ 1 / (N : ℝ) := by
  have he : {X : Fin q → ZMod N | X j = f (X i)} =
      ⋃ x : ZMod N, {X | X i = x ∧ X j = f x} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun h => ⟨X i, rfl, h⟩, by rintro ⟨x, hx, hy⟩; simpa [hx] using hy⟩
  rw [he]
  calc
    _ ≤ ∑ x : ZMod N, (sampleMeasure N q).real {X | X i = x ∧ X j = f x} :=
      measureReal_iUnion_fintype_le _
    _ = (N : ℝ) * (1 / (N : ℝ)) ^ 2 := by simp [sample_pair_real i j hij, ZMod.card]
    _ = 1 / (N : ℝ) := by field_simp [NeZero.ne N]

private lemma sample_torsion {N q : ℕ} [NeZero N] (j : Fin q) :
    (sampleMeasure N q).real {X | 2 * X j = 0} ≤ 2 / (N : ℝ) := by
  let T := (univ : Finset (ZMod N)).filter (fun x => 2 * x = 0)
  have he : {X : Fin q → ZMod N | 2 * X j = 0} =
      ⋃ x ∈ T, {X | X j = x} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, T, mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨X j, h, rfl⟩, by rintro ⟨x, hx, he⟩; simpa [he] using hx⟩
  rw [he]
  calc
    _ ≤ ∑ x ∈ T, (sampleMeasure N q).real {X | X j = x} :=
      measureReal_biUnion_finset_le T _
    _ = (T.card : ℝ) / N := by simp [sample_eval_real, div_eq_mul_inv]
    _ ≤ 2 / (N : ℝ) := by
      gcongr
      exact_mod_cast torsion_two_card (N := N)

private lemma sampling_failure_lt_one {N : ℕ} (hN : familyDomain N) :
    (N : ℝ) * Real.exp (-(sampleSize N : ℝ) / 8) +
      (sampleSize N : ℝ) * ((sampleSize N : ℝ) + 1) / N < 1 := by
  have hL := large_log hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast large_order_pos hN
  have hNL : Real.exp (logOrder N) = N := Real.exp_log hn
  have hq := parameters_bounds hN
  have ht : (N : ℝ) * Real.exp (-(sampleSize N : ℝ) / 8) ≤ 1 / N := by
    calc
      _ ≤ (N : ℝ) * Real.exp (-2 * logOrder N) := by
        gcongr
        linarith [hq.1]
      _ = 1 / N := by
        rw [show -2 * logOrder N = -(logOrder N + logOrder N) by ring,
          Real.exp_neg, Real.exp_add, hNL]
        field_simp
  have hquad : (sampleSize N : ℝ) * ((sampleSize N : ℝ) + 1) ≤
      289 * logOrder N ^ 2 := by
    have hq0 : (0 : ℝ) ≤ sampleSize N := by positivity
    nlinarith [hq.2.1, sq_nonneg ((sampleSize N : ℝ) - 17 * logOrder N)]
  have hp := Real.pow_div_factorial_le_exp (logOrder N)
    (show 0 ≤ logOrder N by linarith) 4
  norm_num [Nat.factorial] at hp
  have hs : 16384 ≤ logOrder N ^ 2 := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (logOrder N))
  have hpoly : 1 + 289 * logOrder N ^ 2 < (N : ℝ) := by
    rw [← hNL]
    nlinarith
  calc
    _ ≤ 1 / (N : ℝ) + (289 * logOrder N ^ 2) / N :=
      add_le_add ht (div_le_div_of_nonneg_right hquad hn.le)
    _ < 1 := by rw [← add_div]; exact (div_lt_one hn).2 hpoly

private lemma favorable_sample {N : ℕ} [NeZero N] (hN : familyDomain N) :
    ∃ X : Fin (sampleSize N) → ZMod N,
      (∀ a : ZMod N, a ≠ 0 →
        ∑ j : Fin (sampleSize N), (ZMod.stdAddChar (a * X j)).re <
          (sampleSize N : ℝ) / 2) ∧
      (∀ j, 2 * X j ≠ 0) ∧
      (∀ i j, i ≠ j → X i ≠ X j ∧ X i ≠ -X j) := by
  classical
  let q := sampleSize N
  let μ := sampleMeasure N q
  let A : Set (Fin q → ZMod N) := ⋃ a ∈ (univ : Finset (ZMod N)).erase 0,
    {X | (q : ℝ) / 2 ≤ ∑ j : Fin q, (ZMod.stdAddChar (a * X j)).re}
  let T : Set (Fin q → ZMod N) := ⋃ j : Fin q, {X | 2 * X j = 0}
  let P : Set (Fin q → ZMod N) := ⋃ i : Fin q, ⋃ j ∈ Iio i,
    {X | X i = X j ∨ X i = -X j}
  have hq0 : q ≠ 0 := by
    have hq := (parameters_bounds hN).1
    have hL := large_log hN
    change sampleSize N ≠ 0
    intro he
    rw [he] at hq
    norm_num at hq
    linarith
  have hA : μ.real A ≤ (N : ℝ) * Real.exp (-(q : ℝ) / 8) := by
    calc
      _ ≤ ∑ a ∈ (univ : Finset (ZMod N)).erase 0,
          μ.real {X | (q : ℝ) / 2 ≤ ∑ j : Fin q, (ZMod.stdAddChar (a * X j)).re} :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _a ∈ (univ : Finset (ZMod N)).erase 0, Real.exp (-(q : ℝ) / 8) :=
        sum_le_sum (fun a ha => sample_tail hq0 a (mem_erase.mp ha).1)
      _ ≤ (N : ℝ) * Real.exp (-(q : ℝ) / 8) := by
        simp only [sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast ((card_erase_le (s := (univ : Finset (ZMod N))) (a := 0)).trans_eq
          (by simp [ZMod.card]))
  have hT : μ.real T ≤ 2 * q / (N : ℝ) := by
    calc
      _ ≤ ∑ j : Fin q, μ.real {X | 2 * X j = 0} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin q, 2 / (N : ℝ) := sum_le_sum (fun j _ => sample_torsion j)
      _ = _ := by simp; ring
  have hP : μ.real P ≤ (q : ℝ) * ((q : ℝ) - 1) / N := by
    have hpair (i j : Fin q) (hj : j ∈ Iio i) :
        μ.real {X | X i = X j ∨ X i = -X j} ≤ 2 / (N : ℝ) := by
      have hji : j ≠ i := ne_of_lt (mem_Iio.mp hj)
      calc
        _ ≤ μ.real {X | X i = X j} + μ.real {X | X i = -X j} :=
          measureReal_union_le _ _
        _ ≤ 1 / N + 1 / N := add_le_add
          (sample_collision j i hji id) (sample_collision j i hji (fun x => -x))
        _ = _ := by ring
    calc
      _ ≤ ∑ i : Fin q, μ.real (⋃ j ∈ Iio i, {X | X i = X j ∨ X i = -X j}) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ i : Fin q, ∑ _j ∈ Iio i, 2 / (N : ℝ) := by
        apply sum_le_sum
        intro i _
        exact (measureReal_biUnion_finset_le _ _).trans (sum_le_sum (hpair i))
      _ = (∑ i : Fin q, (i.val : ℝ)) * 2 / N := by simp [Fin.card_Iio, ← sum_mul, ← sum_div]; ring
      _ = _ := by
        have he := sum_range_id_mul_two q
        have he' : (∑ i ∈ range q, (i : ℝ)) * 2 = (q : ℝ) * ((q : ℝ) - 1) := by
          have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
          have heR := congrArg (fun n : ℕ => (n : ℝ)) he
          push_cast at heR
          simpa [Nat.cast_sub hq1] using heR
        rw [Fin.sum_univ_eq_sum_range, he']
  have hbad : μ.real (A ∪ T ∪ P) < 1 := by
    calc
      _ ≤ (N : ℝ) * Real.exp (-(q : ℝ) / 8) + 2 * q / N +
          (q : ℝ) * ((q : ℝ) - 1) / N :=
        (measureReal_union_le _ _).trans
          (add_le_add ((measureReal_union_le _ _).trans (add_le_add hA hT)) hP)
      _ = (N : ℝ) * Real.exp (-(sampleSize N : ℝ) / 8) +
          (sampleSize N : ℝ) * ((sampleSize N : ℝ) + 1) / N := by dsimp [q]; ring
      _ < 1 := sampling_failure_lt_one hN
  have hex : ∃ X, X ∉ A ∪ T ∪ P := by
    by_contra hn
    have he : A ∪ T ∪ P = Set.univ := by
      ext X
      simp only [Set.mem_univ, iff_true]
      by_contra hx
      exact hn ⟨X, hx⟩
    rw [he, probReal_univ] at hbad
    exact (lt_irrefl 1) hbad
  obtain ⟨X, hX⟩ := hex
  have hXA : X ∉ A := fun hx => hX (Or.inl (Or.inl hx))
  have hXT : X ∉ T := fun hx => hX (Or.inl (Or.inr hx))
  have hXP : X ∉ P := fun hx => hX (Or.inr hx)
  refine ⟨X, ?_, ?_, ?_⟩
  · intro a ha
    apply lt_of_not_ge
    intro hh
    exact hXA (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨by simp [ha], hh⟩⟩)
  · intro j hj
    exact hXT (Set.mem_iUnion.mpr ⟨j, hj⟩)
  · intro i j hij
    have hneq (i j : Fin q) (hji : j < i) : X i ≠ X j ∧ X i ≠ -X j := by
      refine ⟨?_, ?_⟩ <;> intro he <;> apply hXP <;>
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j,
          Set.mem_iUnion.mpr ⟨mem_Iio.mpr hji, by simp [he]⟩⟩⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h := hneq j i hlt
      exact ⟨Ne.symm h.1, fun he => h.2 (by rw [he, neg_neg])⟩
    · exact hneq i j hgt

private def signedSet {N q : ℕ} [NeZero N] (X : Fin q → ZMod N) : Finset (ZMod N) :=
  univ.image X ∪ univ.image (fun j => -X j)

private lemma signedSet_spec {N q : ℕ} [NeZero N] (X : Fin q → ZMod N)
    (ht : ∀ j, 2 * X j ≠ 0)
    (hc : ∀ i j, i ≠ j → X i ≠ X j ∧ X i ≠ -X j) :
    0 ∉ signedSet X ∧ (∀ s, s ∈ signedSet X ↔ -s ∈ signedSet X) ∧
      (signedSet X).card = 2 * q ∧
      ∀ a : ZMod N, ∑ s ∈ signedSet X, ‖ZMod.stdAddChar (a * s) - 1‖ ^ 2 =
        4 * (q : ℝ) - 4 * ∑ j : Fin q, (ZMod.stdAddChar (a * X j)).re := by
  classical
  have hX0 (j : Fin q) : X j ≠ 0 := fun he => ht j (by simp [he])
  have hinj : Function.Injective X := by
    intro i j he
    by_contra hn
    exact (hc i j hn).1 he
  have hminus (i j : Fin q) : X i ≠ -X j := by
    by_cases he : i = j
    · subst j
      intro h
      apply ht i
      linear_combination h
    · exact (hc i j he).2
  have hinjneg : Function.Injective (fun j => -X j) := neg_injective.comp hinj
  have hd : Disjoint (univ.image X) (univ.image (fun j => -X j)) := by
    rw [disjoint_left]
    intro s hs hs'
    obtain ⟨i, _, hi⟩ := mem_image.mp hs
    obtain ⟨j, _, hj⟩ := mem_image.mp hs'
    exact hminus i j (hi.trans hj.symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [signedSet, mem_union, mem_image, mem_univ, true_and, not_or,
      not_exists]
    exact ⟨fun j => hX0 j, fun j he => hX0 j (neg_eq_zero.mp he)⟩
  · intro s
    simp only [signedSet, mem_union, mem_image, mem_univ, true_and]
    constructor <;> rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact Or.inr ⟨j, congrArg Neg.neg hj⟩
    · exact Or.inl ⟨j, by rw [← hj, neg_neg]⟩
    · exact Or.inr ⟨j, by rw [hj, neg_neg]⟩
    · exact Or.inl ⟨j, by simpa using congrArg Neg.neg hj⟩
  · rw [signedSet, card_union_of_disjoint hd, card_image_of_injective _ hinj,
      card_image_of_injective _ hinjneg]
    simp
    omega
  · intro a
    rw [signedSet, sum_union hd, sum_image (fun i _ j _ he => hinj he),
      sum_image (fun i _ j _ he => hinjneg he)]
    have hchord (z : ℂ) (hz : ‖z‖ = 1) : ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
        Complex.normSq_eq_norm_sq, hz]
      norm_num
    have hsame (j : Fin q) : (ZMod.stdAddChar (a * -X j)).re =
        (ZMod.stdAddChar (a * X j)).re := by
      rw [mul_neg, AddChar.map_neg_eq_conj, Complex.conj_re]
    simp_rw [hchord _ ((ZMod.stdAddChar (N := N)).norm_apply _), hsame,
      sum_sub_distrib, ← mul_sum]
    simp
    ring

private lemma goodSet_exists {N : ℕ} [NeZero N] (hN : familyDomain N) :
    ∃ S : Finset (ZMod N), goodSet N S := by
  obtain ⟨X, hX, ht, hc⟩ := favorable_sample hN
  obtain ⟨h0, hsym, hcard, hsum⟩ := signedSet_spec X ht hc
  refine ⟨signedSet X, h0, hsym, hcard, ?_⟩
  have hqpos : 0 < (sampleSize N : ℝ) := by
    have h := (parameters_bounds hN).1
    have hL := large_log hN
    linarith
  have hn1 : 1 < N := by
    have hL := large_log hN
    have hn := large_order_pos hN
    by_contra h
    have he : N = 1 := by omega
    simp [he, logOrder] at hL
    norm_num at hL
  haveI : Fact (1 < N) := ⟨hn1⟩
  have hf : ((univ : Finset (ZMod N)).erase 0).Nonempty :=
    ⟨1, by simp⟩
  rw [ordinaryGap, dif_pos hf, le_inf'_iff]
  intro a ha
  have hxa := hX a (mem_erase.mp ha).1
  unfold chordAverage
  rw [hsum a, hcard]
  push_cast
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) * sampleSize N)).2
  linarith

lemma familySet_good {N : ℕ} [NeZero N] (hN : familyDomain N) :
    goodSet N (familySet N) := by
  unfold familySet
  rw [dif_pos (goodSet_exists hN)]
  exact Classical.choose_spec (goodSet_exists hN)

private lemma ordinaryGap_le {N : ℕ} [NeZero N] (S : Finset (ZMod N))
    (a : ZMod N) (ha : a ≠ 0) : ordinaryGap S ≤ chordAverage S a := by
  classical
  have hm : a ∈ (univ : Finset (ZMod N)).erase 0 := by simp [ha]
  rw [ordinaryGap, dif_pos ⟨a, hm⟩]
  exact inf'_le _ hm

lemma gap_generating {N : ℕ} [NeZero N] (S : Finset (ZMod N))
    (hgap : 0 < ordinaryGap S) : generating S := by
  classical
  let H := AddSubgroup.closure (S : Set (ZMod N))
  let A := FinitePoisson.annihilator H
  have hzero (a : A) : (a : ZMod N) = 0 := by
    by_contra ha
    have hc (s : ZMod N) (hs : s ∈ S) : ZMod.stdAddChar ((a : ZMod N) * s) = 1 :=
      a.2 s (AddSubgroup.subset_closure hs)
    have he : chordAverage S (a : ZMod N) = 0 := by
      unfold chordAverage
      have hz : ∑ s ∈ S, ‖ZMod.stdAddChar ((a : ZMod N) * s) - 1‖ ^ 2 = 0 := by
        apply sum_eq_zero
        intro s hs
        rw [hc s hs]
        norm_num
      rw [hz, zero_div]
    have hh := ordinaryGap_le S (a : ZMod N) ha
    rw [he] at hh
    exact (not_le_of_gt hgap) hh
  haveI : Unique A := ⟨⟨0⟩, fun a => Subtype.ext (hzero a)⟩
  have hh := FinitePoisson.card_mul_card_annihilator H
  have hhNat : Nat.card H * Nat.card A = N := by
    simpa only [Fintype.card_eq_nat_card] using hh
  rw [Nat.card_unique (α := A), mul_one] at hhNat
  exact H.eq_top_of_card_eq (by simpa [Nat.card_eq_fintype_card, ZMod.card] using hhNat)

end
end D5.S3.Fourier.SparseGeneratorGapObstruction
