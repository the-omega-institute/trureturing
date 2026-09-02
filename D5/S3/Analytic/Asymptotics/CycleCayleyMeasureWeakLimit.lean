/- GID: D5/S3/Analytic/Asymptotics/CycleCayleyMeasureWeakLimit
   generality: I
   mirror-B: D5/B/S3/Analytic/Asymptotics/CycleCayleyMeasureWeakLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite cyclic Cayley measures converge weakly to the standard Cauchy law. -/

/- Library-search audit trail (2026-09-02):
* Searches of `D5/**/*.lean` found no empirical measure formed by mapping the nontrivial uniform
  cyclic phases through negative cotangent, and no weak-limit theorem for that sequence.
* Body-shape searches found no existing D5 owner for the standard Cauchy CDF calculation, the
  negative-cotangent order bridge, the finite grid count, or the resulting interval masses.
* Pinned Mathlib supplies `PMF.uniformOfFintype`, `PMF.map`, the Cauchy probability measure,
  `integral_Iic_inv_one_add_sq`, `Fin.card_filter_val_lt`,
  `tendsto_nat_floor_mul_div_atTop`, and the probability-measure pi-system convergence theorem.
  These primitives are applied directly below.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology Real

namespace D5.S3.Analytic.Asymptotics.CycleCayleyMeasureWeakLimit

noncomputable section

/-- The uniform empirical measure on the nontrivial cyclic Cayley phases for cycle size `n + 2`.
The index shift makes every source size at least two occur exactly once. -/
def cycleCayleyEmpiricalMeasure (n : ℕ) : ProbabilityMeasure ℝ :=
  let phases : PMF (Fin (n + 1)) := PMF.uniformOfFintype (Fin (n + 1))
  let cayleyPhases := phases.map (fun j =>
    -Real.cot (Real.pi * (j.val + 1) / (n + 2)))
  ⟨cayleyPhases.toMeasure, inferInstance⟩

private theorem standard_cauchy_cdf (x : ℝ) :
    ProbabilityTheory.cdf (ProbabilityTheory.cauchyMeasure 0 1) x =
      (Real.arctan x + Real.pi / 2) / Real.pi := by
  rw [ProbabilityTheory.cdf_eq_real,
    ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 one_ne_zero,
    measureReal_def, withDensity_apply _ measurableSet_Iic]
  change (∫⁻ y in Iic x,
    ENNReal.ofReal (ProbabilityTheory.cauchyPDFReal 0 1 y)).toReal = _
  rw [← integral_eq_lintegral_of_nonneg_ae]
  · simp only [ProbabilityTheory.cauchyPDFReal_def, NNReal.coe_one, sub_zero, one_pow,
      mul_one]
    rw [integral_const_mul,
      show (fun a : ℝ => (a ^ 2 + 1)⁻¹) = (fun a : ℝ => (1 + a ^ 2)⁻¹) by
        funext a
        rw [add_comm],
      integral_Iic_inv_one_add_sq]
    field_simp
  · exact ae_of_all _ fun y => (ProbabilityTheory.cauchyPDF_pos 0 one_ne_zero y).le
  · exact (ProbabilityTheory.stronglyMeasurable_cauchyPDFReal 0 1).aestronglyMeasurable

private theorem neg_cot_eq_shifted_tan (theta : ℝ) :
    -Real.cot theta = Real.tan (theta - Real.pi / 2) := by
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos,
    Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]
  ring

private theorem cayley_le_iff {u x : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    -Real.cot (Real.pi * u) ≤ x ↔
      u ≤ (Real.arctan x + Real.pi / 2) / Real.pi := by
  rw [neg_cot_eq_shifted_tan]
  have hlow : -(Real.pi / 2) < Real.pi * u - Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hhigh : Real.pi * u - Real.pi / 2 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  rw [← Real.arctan_le_arctan_iff, Real.arctan_tan hlow hhigh]
  rw [le_div_iff₀ Real.pi_pos]
  constructor <;> intro h <;> nlinarith

private theorem card_grid_le (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (Finset.univ.filter (fun j : Fin (n + 1) =>
      ((j.val + 1 : ℕ) : ℝ) / (n + 2) ≤ q)).card =
      Nat.floor (q * (n + 2)) := by
  have hden : (0 : ℝ) < n + 2 := by positivity
  have hmul0 : 0 ≤ q * (n + 2 : ℝ) := mul_nonneg hq0 hden.le
  have hpred (j : Fin (n + 1)) :
      ((j.val + 1 : ℕ) : ℝ) / (n + 2) ≤ q ↔
        j.val < Nat.floor (q * (n + 2)) := by
    rw [div_le_iff₀ hden]
    rw [← Nat.le_floor_iff hmul0]
    omega
  rw [show Finset.univ.filter (fun j : Fin (n + 1) =>
      ((j.val + 1 : ℕ) : ℝ) / (n + 2) ≤ q) =
      Finset.univ.filter (fun j : Fin (n + 1) =>
        j.val < Nat.floor (q * (n + 2))) by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpred]]
  rw [Fin.card_filter_val_lt, min_eq_right]
  have hmul : q * (n + 2 : ℝ) < n + 2 :=
    mul_lt_of_lt_one_left hden hq1
  have hfloor : Nat.floor (q * (n + 2 : ℝ)) < n + 2 :=
    (Nat.floor_lt hmul0).2 (by simpa using hmul)
  omega

private theorem cauchy_quantile_mem_Ioo (x : ℝ) :
    (Real.arctan x + Real.pi / 2) / Real.pi ∈ Ioo (0 : ℝ) 1 := by
  rcases Real.arctan_mem_Ioo x with ⟨hlow, hhigh⟩
  constructor
  · exact div_pos (by linarith) Real.pi_pos
  · rw [div_lt_one Real.pi_pos]
    linarith

private theorem empirical_Iic (n : ℕ) (x : ℝ) :
    (cycleCayleyEmpiricalMeasure n : Measure ℝ) (Iic x) =
      (Nat.floor (((Real.arctan x + Real.pi / 2) / Real.pi) * (n + 2)) : ℝ≥0∞) /
        (n + 1 : ℝ≥0∞) := by
  rw [show (cycleCayleyEmpiricalMeasure n : Measure ℝ) =
      (PMF.uniformOfFintype (Fin (n + 1))).toMeasure.map
        (fun j => -Real.cot (Real.pi * (j.val + 1) / (n + 2))) by
    exact (PMF.toMeasure_map (f := fun j : Fin (n + 1) =>
      -Real.cot (Real.pi * (j.val + 1) / (n + 2))) _ Measurable.of_discrete).symm]
  rw [Measure.map_apply Measurable.of_discrete measurableSet_Iic,
    PMF.toMeasure_apply_fintype]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_Iic,
    PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hpoint (j : Fin (n + 1)) :
      -Real.cot (Real.pi * (j.val + 1) / (n + 2)) ≤ x ↔
        ((j.val + 1 : ℕ) : ℝ) / (n + 2) ≤
          (Real.arctan x + Real.pi / 2) / Real.pi := by
    have hden : (0 : ℝ) < n + 2 := by positivity
    have hu0 : (0 : ℝ) < ((j.val + 1 : ℕ) : ℝ) / (n + 2) :=
      div_pos (by positivity) hden
    have hu1 : ((j.val + 1 : ℕ) : ℝ) / (n + 2) < 1 := by
      rw [div_lt_one hden]
      norm_cast
      omega
    rw [show Real.pi * ((j.val : ℝ) + 1) / (n + 2) =
      Real.pi * (((j.val + 1 : ℕ) : ℝ) / (n + 2)) by
        norm_num
        ring]
    exact cayley_le_iff hu0 hu1
  rw [show Finset.univ.filter (fun j : Fin (n + 1) =>
      -Real.cot (Real.pi * (j.val + 1) / (n + 2)) ≤ x) =
      Finset.univ.filter (fun j : Fin (n + 1) =>
        ((j.val + 1 : ℕ) : ℝ) / (n + 2) ≤
          (Real.arctan x + Real.pi / 2) / Real.pi) by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpoint]]
  rw [card_grid_le (n := n) (cauchy_quantile_mem_Ioo x).1.le
    (cauchy_quantile_mem_Ioo x).2]
  rw [ENNReal.div_eq_inv_mul, mul_comm]
  simp only [Nat.cast_add, Nat.cast_one]

private theorem tendsto_floor_grid (q : ℝ) (hq0 : 0 ≤ q) :
    Tendsto (fun n : ℕ =>
      (Nat.floor (q * (n + 2)) : ℝ) / (n + 1)) atTop (𝓝 q) := by
  have hn2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hfloor : Tendsto (fun n : ℕ =>
      (Nat.floor (q * ((n : ℝ) + 2)) : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 q) :=
    (tendsto_nat_floor_mul_div_atTop hq0).comp hn2
  have hn1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn1
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1))
      atTop (𝓝 1) := by
    convert hone.add hinv using 1
    · funext n
      field_simp
      ring
    · ring_nf
  convert hfloor.mul hratio using 1
  · funext n
    field_simp
  · simp

private theorem tendsto_empirical_Iic (x : ℝ) :
    Tendsto (fun n => (cycleCayleyEmpiricalMeasure n : Measure ℝ) (Iic x)) atTop
      (𝓝 (ProbabilityTheory.cauchyMeasure 0 1 (Iic x))) := by
  let q := (Real.arctan x + Real.pi / 2) / Real.pi
  have hq : q ∈ Ioo (0 : ℝ) 1 := cauchy_quantile_mem_Ioo x
  have hreal : Tendsto (fun n : ℕ =>
      (Nat.floor (q * (n + 2)) : ℝ) / (n + 1)) atTop (𝓝 q) :=
    tendsto_floor_grid q hq.1.le
  have henn : Tendsto (fun n : ℕ => ENNReal.ofReal
      ((Nat.floor (q * (n + 2)) : ℝ) / (n + 1))) atTop (𝓝 (ENNReal.ofReal q)) :=
    ENNReal.tendsto_ofReal hreal
  have hsource :
      (fun n : ℕ => (cycleCayleyEmpiricalMeasure n : Measure ℝ) (Iic x)) =
        fun n : ℕ => ENNReal.ofReal
          ((Nat.floor (q * (n + 2)) : ℝ) / (n + 1)) := by
    funext n
    rw [empirical_Iic]
    change (Nat.floor (q * (n + 2)) : ℝ≥0∞) / (n + 1 : ℝ≥0∞) = _
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < n + 1),
      ENNReal.ofReal_natCast]
    rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one,
      ENNReal.ofReal_natCast]
    norm_num
  have htarget :
      ProbabilityTheory.cauchyMeasure 0 1 (Iic x) = ENNReal.ofReal q := by
    have htoReal :
        (ProbabilityTheory.cauchyMeasure 0 1 (Iic x)).toReal = q := by
      rw [← measureReal_def, ← ProbabilityTheory.cdf_eq_real]
      exact standard_cauchy_cdf x
    calc
      ProbabilityTheory.cauchyMeasure 0 1 (Iic x) =
          ENNReal.ofReal (ProbabilityTheory.cauchyMeasure 0 1 (Iic x)).toReal := by
            rw [ENNReal.ofReal_toReal]
            finiteness
      _ = ENNReal.ofReal q := congrArg ENNReal.ofReal htoReal
  rw [hsource, htarget]
  exact henn

/-- The empirical spectral measures of all nontrivial cyclic Cayley phases converge weakly to the
standard Cauchy probability measure. -/
theorem cycle_cayley_measure_weak_limit :
    Tendsto cycleCayleyEmpiricalMeasure atTop
      (𝓝 (⟨ProbabilityTheory.cauchyMeasure 0 1, inferInstance⟩ :
        ProbabilityMeasure ℝ)) := by
  let cauchy : ProbabilityMeasure ℝ :=
    ⟨ProbabilityTheory.cauchyMeasure 0 1, inferInstance⟩
  change Tendsto cycleCayleyEmpiricalMeasure atTop (𝓝 cauchy)
  refine (isPiSystem_Ioc (id : ℝ → ℝ) id).tendsto_probabilityMeasure_of_tendsto_of_mem
    ?_ ?_ ?_
  · rintro s ⟨a, b, hab, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    rcases mem_nhds_iff_exists_Ioo_subset.1 (hu.mem_nhds hx) with
      ⟨a, b, ⟨hax, hxb⟩, hab⟩
    let c := (x + b) / 2
    have hxc : x < c := by dsimp [c]; linarith
    have hcb : c < b := by dsimp [c]; linarith
    refine ⟨Ioc a c, ?_, Ioc_mem_nhds hax hxc, ?_⟩
    · exact ⟨a, c, hax.trans hxc, rfl⟩
    · exact (Ioc_subset_Ioo_right hcb).trans hab
  · rintro s ⟨a, b, hab, rfl⟩
    simp only [id_eq] at hab ⊢
    have ha := tendsto_empirical_Iic a
    have hb := tendsto_empirical_Iic b
    have hbtop : ProbabilityTheory.cauchyMeasure 0 1 (Iic b) ≠ ∞ := by
      finiteness
    have hsub := ENNReal.Tendsto.sub hb ha (Or.inl hbtop)
    have hsubNN :=
      (ENNReal.tendsto_toNNReal
        (by finiteness :
          ProbabilityTheory.cauchyMeasure 0 1 (Iic b) -
            ProbabilityTheory.cauchyMeasure 0 1 (Iic a) ≠ ∞)).comp hsub
    have hsourceIoc :
        (fun n => cycleCayleyEmpiricalMeasure n (Ioc a b)) =
          fun n => ((cycleCayleyEmpiricalMeasure n : Measure ℝ) (Iic b) -
            (cycleCayleyEmpiricalMeasure n : Measure ℝ) (Iic a)).toNNReal := by
      funext n
      change ((cycleCayleyEmpiricalMeasure n : Measure ℝ) (Ioc a b)).toNNReal = _
      rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.2 hab.le)
        nullMeasurableSet_Iic]
      finiteness
    have htargetIoc : cauchy (Ioc a b) =
        (ProbabilityTheory.cauchyMeasure 0 1 (Iic b) -
          ProbabilityTheory.cauchyMeasure 0 1 (Iic a)).toNNReal := by
      change (ProbabilityTheory.cauchyMeasure 0 1 (Ioc a b)).toNNReal = _
      rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.2 hab.le)
        nullMeasurableSet_Iic]
      finiteness
    rw [hsourceIoc, htargetIoc]
    convert hsubNN using 1
    all_goals rfl

end

end D5.S3.Analytic.Asymptotics.CycleCayleyMeasureWeakLimit
