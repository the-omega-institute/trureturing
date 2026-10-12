/- GID: D5/S3/Geometry/CentredGaussianDilationRefutation
   generality: I
   mirror-B: D5/B/S3/Geometry/CentredGaussianDilationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/CentredGaussianDilationRefutation.claim; result=D5/S3/Geometry/CentredGaussianDilationRefutation.result; claim=D5/S3/Geometry/CentredGaussianDilationRefutation.claim
   digest: A centred 16-dimensional pyramid has non-log-concave Gaussian dilations. -/

/- Source: Faifman–Polterovich, arXiv:2607.21539v2, §5.2, p. 38, Question 5.3.
   admission_basis: open-problem-resolution (#15936; Refuted)
   escape_witness: the centred 16-dimensional pyramid with
     γ(K/2)² < γ(K/4)γ(K).
   Direct frozen dependencies: none (pinned Mathlib only).
   Per-declaration proof_shape and live consumers:
     gaussianMeasure: definition; consumers=claim, gaussian_probability, box_measure, half_upper, box_mass_le, dilation_bounds, result
     IsConvexBody: definition; consumers=claim, pyramid_body
     BarycenterZero: definition; consumers=claim, result
     claim: definition; consumers=result
     gaussian_probability: bind-only; consumers=box_mass_le, result
     pyramid: definition; consumers=pyramid_closed, pyramid_convex, pyramid_compact, pyramid_body, scaled_mem, split_mem, barycenter, result
     pyramid_closed: bind-only; consumers=pyramid_compact
     pyramid_convex: bind-only; consumers=pyramid_body
     pyramid_compact: bind-only; consumers=pyramid_body, result
     pyramid_body: bind-only; consumers=result
     scaled_mem: bind-only; consumers=box_subset, half_upper, quarter_subset_half
     box: definition; consumers=box_subset, box_measure
     box_subset: bind-only; consumers=box_mass_le
     box_measure: bind-only; consumers=box_mass_le
     half_upper: bind-only; consumers=dilation_bounds
     quarter_subset_half: bind-only; consumers=result
     slice_box: definition; consumers=slice_box_iff, slice_box_measurable, slice_box_volume, slice_box_integral_coord, split_mem, barycenter
     slice_box_iff: bind-only; consumers=slice_box_integral_coord, split_mem
     slice_box_measurable: bind-only; consumers=slice_box_integral_coord, barycenter
     slice_box_volume: bind-only; consumers=barycenter
     slice_box_integral_coord: bind-only; consumers=barycenter
     split_mem: bind-only; consumers=barycenter
     polynomial_integral: bind-only; consumers=barycenter
     barycenter: bind-only; consumers=result
     μ: definition; consumers=real_apply, tail, normal_symm, half, upper_halfline, normal_box, gaussian_box_products
     c: definition; consumers=c_bounds, pdf, lower_integral, gaussian_box_bounds
     c_bounds: bind-only; consumers=gaussian_box_bounds
     pdf: bind-only; consumers=lower_integral, gaussian_box_bounds
     real_apply: bind-only; consumers=upper_halfline
     tail: bind-only; consumers=tail_bounds
     tail_bounds: bind-only; consumers=tails_strict
     gaussian_no_atoms: bind-only; consumers=half, upper_halfline
     normal_symm: bind-only; consumers=half, upper_halfline, gaussian_box_bounds
     half: bind-only; consumers=upper_halfline
     upper_halfline: bind-only; consumers=gaussian_box_bounds
     poly: definition; consumers=exp_lower, lower_integral
     exp_lower: bind-only; consumers=lower_integral
     lower_integral: bind-only; consumers=gaussian_box_bounds
     normal_box: bind-only; consumers=gaussian_box_bounds
     tails_strict: bind-only; consumers=gaussian_box_bounds
     gaussian_box_bounds: bind-only; consumers=gaussian_box_products
     gaussian_box_products: bind-only; consumers=dilation_bounds
     box_mass_le: bind-only; consumers=dilation_bounds
     dilation_bounds: bind-only; consumers=result
     result: bind-only; consumers=designated refutation conclusion
   The supporting proofs apply pinned Mathlib identities and inequalities,
   construct the explicit geometric data, and normalize exact arithmetic.
   Admission uses the external open-problem resolution. -/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

noncomputable section
open MeasureTheory ProbabilityTheory
open Set
open scoped Pointwise
namespace D5.S3.Geometry.CentredGaussianDilationRefutation
/-- The standard Gaussian measure `γ_n` on `ℝ^n`. -/
noncomputable def gaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)
/-- A convex body: a compact convex set with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty
/-- The Lebesgue barycenter of `K` is the origin. -/
def BarycenterZero {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  ∀ i : Fin n, ∫ z in K, z i = 0
/-- Question 5.3, first clause: for every convex body with Lebesgue barycenter at the origin,
`t ↦ γ_n(e^t K)` is log-concave. -/
def claim : Prop :=
  ∀ (n : ℕ) (K : Set (Fin n → ℝ)), IsConvexBody K → BarycenterZero K →
    ConcaveOn ℝ Set.univ (fun t : ℝ => Real.log ((gaussianMeasure n) (Real.exp t • K)).toReal)
private instance gaussian_probability (n : ℕ) : IsProbabilityMeasure (gaussianMeasure n) := by
  unfold gaussianMeasure
  infer_instance

private def pyramid : Set (Fin 16 → ℝ) :=
  {z | -1 ≤ z 0 ∧ z 0 ≤ 16 ∧ ∀ i : Fin 16, i ≠ 0 → |z i| ≤ 10 * (16 - z 0)}
private lemma pyramid_closed : IsClosed pyramid := by
  unfold pyramid
  apply IsClosed.inter (isClosed_le continuous_const (continuous_apply 0))
  apply IsClosed.inter (isClosed_le (continuous_apply 0) continuous_const)
  have hset : (fun z : Fin 16 → ℝ => ∀ i : Fin 16, i ≠ 0 → |z i| ≤ 10*(16-z 0)) =
      ⋂ i : Fin 16, ⋂ (_ : i ≠ 0), {z : Fin 16 → ℝ | |z i| ≤ 10*(16-z 0)} := by
    funext z
    apply propext
    change _ ↔ z ∈ ⋂ i : Fin 16, ⋂ (_ : i ≠ 0), {z : Fin 16 → ℝ | |z i| ≤ 10*(16-z 0)}
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply i).abs (by fun_prop)
private lemma pyramid_convex : Convex ℝ pyramid := by
  intro x hx y hy a b ha hb hab
  change -1 ≤ a*x 0+b*y 0 ∧ a*x 0+b*y 0 ≤ 16 ∧ _
  refine ⟨by nlinarith [mul_nonneg ha (show 0 ≤ x 0+1 by linarith [hx.1]),
    mul_nonneg hb (show 0 ≤ y 0+1 by linarith [hy.1])],
    by nlinarith [mul_nonneg ha (show 0 ≤ 16-x 0 by linarith [hx.2.1]),
    mul_nonneg hb (show 0 ≤ 16-y 0 by linarith [hy.2.1])], ?_⟩
  intro i hi
  change |a*x i+b*y i| ≤ 10*(16-(a*x 0+b*y 0))
  calc
    _ ≤ |a*x i|+|b*y i| := abs_add_le _ _
    _ = a*|x i|+b*|y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a*(10*(16-x 0))+b*(10*(16-y 0)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 i hi) ha)
        (mul_le_mul_of_nonneg_left (hy.2.2 i hi) hb)
    _ = _ := by nlinarith
private lemma pyramid_compact : IsCompact pyramid := by
  apply Metric.isCompact_of_isClosed_isBounded pyramid_closed
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin 16 => (-170:ℝ)) (fun _ => 170))).isBounded.subset
  intro z hz
  constructor <;> intro i
  all_goals by_cases hi : i = 0
  · subst i; linarith [hz.1]
  · have h := (abs_le.mp (hz.2.2 i hi)).1; linarith [hz.1]
  · subst i; linarith [hz.2.1]
  · have h := (abs_le.mp (hz.2.2 i hi)).2; linarith [hz.1]
private lemma pyramid_body : IsConvexBody pyramid := by
  refine ⟨pyramid_convex, pyramid_compact, ?_⟩
  let U : Set (Fin 16 → ℝ) := {z | -1 < z 0 ∧ z 0 < 16 ∧
    ∀ i : Fin 16, i ≠ 0 → |z i| < 10*(16-z 0)}
  have hU : IsOpen U := by
    apply IsOpen.inter (isOpen_lt continuous_const (continuous_apply 0))
    apply IsOpen.inter (isOpen_lt (continuous_apply 0) continuous_const)
    have hset : (fun z : Fin 16 → ℝ => ∀ i : Fin 16, i ≠ 0 → |z i| < 10*(16-z 0)) =
        ⋂ i : Fin 16, ⋂ (_ : i ≠ 0), {z : Fin 16 → ℝ | |z i| < 10*(16-z 0)} := by
      funext z
      apply propext
      change _ ↔ z ∈ ⋂ i : Fin 16, ⋂ (_ : i ≠ 0), {z : Fin 16 → ℝ | |z i| < 10*(16-z 0)}
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [hset]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun _ =>
      isOpen_lt (continuous_apply i).abs (by fun_prop)
  refine ⟨0, (hU.subset_interior_iff.mpr ?_) ?_⟩
  · intro z hz; exact ⟨hz.1.le, hz.2.1.le, fun i hi => (hz.2.2 i hi).le⟩
  · simp [U]


private lemma scaled_mem {c : ℝ} (hc : 0 < c) (z : Fin 16 → ℝ) :
    z ∈ c • pyramid ↔ -c ≤ z 0 ∧ z 0 ≤ 16*c ∧
      ∀ i : Fin 16, i ≠ 0 → |z i| ≤ 10*(16*c-z 0) := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne' pyramid z]
  simp only [pyramid, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul,
    ← div_eq_inv_mul, abs_div, abs_of_pos hc]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, (div_le_iff₀ hc).mp h1, ?_⟩
    · have := (le_div_iff₀ hc).mp h0; linarith
    · intro i hi
      have := (div_le_iff₀ hc).mp (h2 i hi)
      field_simp at this
      nlinarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨(le_div_iff₀ hc).mpr (by linarith), (div_le_iff₀ hc).mpr h1, ?_⟩
    intro i hi
    apply (div_le_iff₀ hc).mpr
    have := h2 i hi
    field_simp
    nlinarith
private def box (a b : ℝ) : Set (Fin 16 → ℝ) :=
  Set.pi Set.univ (fun i => if i = 0 then Set.Icc a b else Set.Icc (-5) 5)
private lemma box_subset {c a b : ℝ} (hc : 0 < c) (ha : -c ≤ a)
    (hb : b ≤ 16*c-1/2) : box a b ⊆ c • pyramid := by
  intro z hz
  have h0 : a ≤ z 0 ∧ z 0 ≤ b := by simpa [box] using hz 0 (Set.mem_univ 0)
  rw [scaled_mem hc]
  refine ⟨ha.trans h0.1, by linarith [h0.2], ?_⟩
  intro i hi
  have hi' : -5 ≤ z i ∧ z i ≤ 5 := by simpa [box, hi] using hz i (Set.mem_univ i)
  exact (abs_le.mpr hi').trans (by linarith [h0.2])
private lemma box_measure (a b : ℝ) :
    (gaussianMeasure 16) (box a b) =
      gaussianReal 0 1 (Set.Icc a b) * (gaussianReal 0 1 (Set.Icc (-5) 5))^15 := by
  rw [gaussianMeasure, box, Measure.pi_pi, Fin.prod_univ_succ]
  simp
private lemma half_upper :
    ((gaussianMeasure 16) ((1/2:ℝ) • pyramid)).toReal ≤
      (gaussianReal 0 1 (Set.Ici (-1/2))).toReal := by
  have hsub : (1/2:ℝ) • pyramid ⊆ (fun z : Fin 16 → ℝ => z 0) ⁻¹' Set.Ici (-1/2) := by
    intro z hz
    change -1/2 ≤ z 0
    have h0 := ((scaled_mem (by norm_num) z).mp hz).1
    norm_num at h0 ⊢
    exact h0
  have h := measure_mono (μ := gaussianMeasure 16) hsub
  have he := (measurePreserving_eval (fun _ : Fin 16 => gaussianReal 0 1) 0).measure_preimage (s := Set.Ici (-1/2))
    measurableSet_Ici.nullMeasurableSet
  change (gaussianMeasure 16) ((fun z : Fin 16 → ℝ => z 0) ⁻¹' Set.Ici (-1/2)) = _ at he
  rw [he] at h
  exact ENNReal.toReal_mono (measure_ne_top _ _) h


private lemma quarter_subset_half : (1/4:ℝ) • pyramid ⊆ (1/2:ℝ) • pyramid := by
  intro z hz
  rcases (scaled_mem (by norm_num) z).mp hz with ⟨h0,h1,h2⟩
  apply (scaled_mem (by norm_num) z).mpr
  refine ⟨by linarith, by linarith, fun i hi => ?_⟩
  have := h2 i hi
  linarith
private def slice_box (r : ℝ) : Set (Fin 15 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-r) r)
private lemma slice_box_iff (r : ℝ) (y : Fin 15 → ℝ) : y ∈ slice_box r ↔ ∀ j, |y j| ≤ r := by
  simp only [slice_box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
private lemma slice_box_measurable (r : ℝ) : MeasurableSet (slice_box r) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
private lemma slice_box_volume (r : ℝ) (hr : 0 ≤ r) : (volume (slice_box r)).toReal = (2*r)^15 := by
  rw [slice_box, volume_pi_pi]
  simp [Real.volume_Icc, sub_neg_eq_add, ENNReal.toReal_ofReal, hr]
  ring
private lemma slice_box_integral_coord (r : ℝ) (j : Fin 15) : ∫ y in slice_box r, y j = 0 := by
  let f : (Fin 15 → ℝ) → ℝ := (slice_box r).indicator (fun y => y j)
  have hf : ∀ y, f (-y) = - f y := by
    intro y
    have hm : -y ∈ slice_box r ↔ y ∈ slice_box r := by simp [slice_box_iff]
    by_cases h : y ∈ slice_box r <;> simp [f, hm, h, Set.indicator_of_mem, Set.indicator_of_notMem]
  have h := integral_neg_eq_self f volume
  simp_rw [hf, integral_neg] at h
  rw [← integral_indicator (slice_box_measurable r)]
  change ∫ y, f y = 0
  linarith
private lemma split_mem (x : ℝ) (y : Fin 15 → ℝ) :
    Fin.cons x y ∈ pyramid ↔ x ∈ Set.Icc (-1) 16 ∧ y ∈ slice_box (10 * (16-x)) := by
  simp only [pyramid, Set.mem_ofPred_eq, Fin.cons_zero, Set.mem_Icc, slice_box_iff]
  constructor
  · rintro ⟨ha, hb, hy⟩
    refine ⟨⟨ha,hb⟩, fun j => ?_⟩
    simpa using hy j.succ (Fin.succ_ne_zero j)
  · rintro ⟨⟨ha,hb⟩,hy⟩
    refine ⟨ha,hb,?_⟩
    intro j hj
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hj
    simpa using hy j
private lemma polynomial_integral : ∫ x in (-1:ℝ)..16, x * (20*(16-x))^15 = 0 := by
  let F : ℝ → ℝ := fun x => 20^15 * (-(16-x)^16 + (16-x)^17/17)
  have hd : ∀ x, HasDerivAt F (x * (20*(16-x))^15) x := by
    intro x
    have h := (hasDerivAt_const x 16).sub (hasDerivAt_id x)
    have hh := ((h.pow 16).neg.add ((h.pow 17).div_const 17)).const_mul (20^15)
    simp only [Pi.sub_apply, Function.id_def] at hh
    convert hh using 1 <;> try rfl
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ => x*(20*(16-x))^15)).intervalIntegrable _ _)]
  norm_num [F]
private lemma barycenter (hc : IsCompact pyramid) : ∀ i : Fin 16, ∫ z in pyramid, z i = 0 := by
  classical
  intro i
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 16 => ℝ) 0).symm
  have hp : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 16 => ℝ) 0).symm
  let f : (Fin 16 → ℝ) → ℝ := pyramid.indicator (fun z => z i)
  have hi : Integrable f volume :=
    ((continuous_apply i).continuousOn.integrableOn_compact hc).integrable_indicator hc.measurableSet
  have ht : Integrable (fun p : ℝ × (Fin 15 → ℝ) => f (e p)) volume :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr hi
  have hsplit : ∫ z in pyramid, z i = ∫ x : ℝ, ∫ y : Fin 15 → ℝ, f (Fin.cons x y) := by
    rw [← integral_indicator hc.measurableSet]
    change ∫ z, f z = _
    rw [← hp.integral_comp' f]
    simpa [Measure.volume_eq_prod, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero]
      using integral_prod _ ht
  have hin (x : ℝ) : (∫ y : Fin 15 → ℝ, f (Fin.cons x y)) =
      if x ∈ Set.Icc (-1) 16 then ∫ y in slice_box (10*(16-x)), (Fin.cons x y : Fin 16 → ℝ) i else 0 := by
    by_cases hx : x ∈ Set.Icc (-1) 16
    · simp only [if_pos hx]
      rw [← integral_indicator (slice_box_measurable _)]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [f, Set.indicator_apply, split_mem, hx, true_and]
    · simp only [if_neg hx]
      have hh : (fun y : Fin 15 → ℝ => f (Fin.cons x y)) = 0 := by
        funext y
        simp [f, split_mem, hx]
      simp [hh]
  rw [hsplit]
  simp_rw [hin]
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · simp only [Fin.cons_zero]
    have hv (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 16) :
        (∫ y in slice_box (10*(16-x)), x) = x*(20*(16-x))^15 := by
      rw [integral_const, Measure.real, Measure.restrict_apply_univ,
        slice_box_volume _ (by linarith [hx.2]), smul_eq_mul]
      ring
    calc
      _ = ∫ x in Set.Icc (-1:ℝ) 16, x*(20*(16-x))^15 := by
        rw [← integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Set.Icc (-1:ℝ) 16 <;>
          simp [hx, hv]
      _ = ∫ x in (-1:ℝ)..16, x*(20*(16-x))^15 := by
        rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
      _ = 0 := polynomial_integral
  · simp only [Fin.cons_succ, slice_box_integral_coord, ite_self, integral_zero]

private abbrev μ := gaussianReal 0 1
private def c : ℝ := 1 / Real.sqrt (2 * Real.pi)
private lemma c_bounds : 997 / 2500 < c ∧ c < 2 / 5 := by
  have hp := Real.pi_lt_d4
  have hl := Real.pi_gt_d2
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hn := Real.sqrt_nonneg (2 * Real.pi)
  dsimp [c]
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < Real.sqrt (2 * Real.pi))).2
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0 < Real.sqrt (2 * Real.pi))).2
    nlinarith
private lemma pdf (x : ℝ) : gaussianPDFReal 0 1 x = c * Real.exp (-(x ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [neg_div]
  simp [c, one_div]
private lemma real_apply (s : Set ℝ) : μ.real s = ∫ x in s, gaussianPDFReal 0 1 x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _)
private lemma tail (a : ℝ) (ha : 0 ≤ a) : μ.real (Ici a) ≤ Real.exp (-(a ^ 2 / 2)) := by
  have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun x : ℝ => x) a ha
    (integrable_exp_mul_gaussianReal a)
  rw [mgf_fun_id_gaussianReal] at h
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add] at h
  change μ.real (Ici a) ≤ _ at h
  rw [← Real.exp_add] at h
  convert h using 1
  congr 1
  ring
private lemma tail_bounds : μ.real (Ici (7/2)) < 1/350 ∧ μ.real (Ici 5) < 1/16000 := by
  have h₁ := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 49/8 by norm_num) 9
  have h₂ := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 25/2 by norm_num) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h₁ h₂
  constructor
  · have h := tail (7/2) (by norm_num)
    have hh : Real.exp (-( (7/2:ℝ)^2 / 2)) < 1/350 := by
      rw [Real.exp_neg]
      rw [inv_eq_one_div]
      apply (one_div_lt (Real.exp_pos _) (by norm_num)).2
      norm_num at *
      linarith
    exact h.trans_lt hh
  · have h := tail 5 (by norm_num)
    have hh : Real.exp (-((5:ℝ)^2 / 2)) < 1/16000 := by
      rw [Real.exp_neg]
      rw [inv_eq_one_div]
      apply (one_div_lt (Real.exp_pos _) (by norm_num)).2
      norm_num at *
      linarith
    exact h.trans_lt hh
private instance gaussian_no_atoms : NullSingletonClass μ := nullSingletonClass_gaussianReal (by norm_num)
private lemma normal_symm (s : Set ℝ) (hs : MeasurableSet s) : μ.real ((fun x : ℝ => -x) ⁻¹' s) = μ.real s := by
  have h := congrArg (fun m : Measure ℝ => m s) (gaussianReal_map_neg (μ := 0) (v := 1))
  rw [Measure.map_apply (by fun_prop) hs] at h
  simpa [measureReal_def] using congrArg ENNReal.toReal h
private lemma half : μ.real (Ioi 0) = 1/2 := by
  have h := normal_symm (Ioi 0) measurableSet_Ioi
  have he : ((fun x : ℝ => -x) ⁻¹' Ioi 0) = Iio 0 := by ext x; simp
  rw [he] at h
  have hc := measureReal_add_measureReal_compl (μ := μ) (s := Ioi 0) measurableSet_Ioi
  simp only [compl_Ioi, measureReal_def, measure_univ, ENNReal.toReal_one] at hc
  have hi : μ.real (Iic 0) = μ.real (Iio 0) := by
    rw [measureReal_def, measureReal_def]
    congr 1
    exact measure_congr (Iio_ae_eq_Iic (μ := μ)).symm
  change μ.real (Ioi 0) + μ.real (Iic 0) = 1 at hc
  rw [hi, h] at hc
  linarith
private lemma upper_halfline (a : ℝ) (ha : 0 ≤ a) :
    μ.real (Ici (-a)) = 1/2 + ∫ x in 0..a, gaussianPDFReal 0 1 x := by
  have h := normal_symm (Ici (-a)) measurableSet_Ici
  have he : ((fun x : ℝ => -x) ⁻¹' Ici (-a)) = Iic a := by ext x; simp
  rw [he] at h
  rw [← h, ← Iio_union_Icc_eq_Iic ha]
  rw [measureReal_union (by exact disjoint_left.mpr (fun x hx hy => not_lt_of_ge hy.1 hx)) measurableSet_Icc]
  have hh := normal_symm (Ioi 0) measurableSet_Ioi
  have heh : ((fun x : ℝ => -x) ⁻¹' Ioi 0) = Iio 0 := by ext x; simp
  rw [heh, half] at hh
  rw [hh, real_apply, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
private abbrev poly (x : ℝ) := 1 - x^2/2 + x^4/8 - x^6/48 - 5*x^8/1536
private lemma exp_lower (x : ℝ) (hx : x ∈ Icc 0 1) : poly x ≤ Real.exp (-(x^2/2)) := by
  rcases hx with ⟨hx0, hx1⟩
  have hsq : x^2 ≤ 1 := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have h := Real.exp_bound (x := -(x^2/2)) (n := 4) (by rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith) (by norm_num)
  rw [abs_neg, abs_of_nonneg (show 0 ≤ x^2/2 by positivity)] at h
  have hh := (abs_le.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  dsimp [poly]
  nlinarith
private lemma lower_integral (a : ℝ) (ha : a ∈ Icc 0 1) :
    c * (a - a^3/6 + a^5/40 - a^7/336 - 5*a^9/13824) ≤
      ∫ x in 0..a, gaussianPDFReal 0 1 x := by
  have h := intervalIntegral.integral_mono_on ha.1
    (f := fun x => c * poly x) (g := gaussianPDFReal 0 1)
    (by apply Continuous.intervalIntegrable; fun_prop)
    ((integrable_gaussianPDFReal 0 1).intervalIntegrable)
    (fun x hx => by rw [pdf]; exact mul_le_mul_of_nonneg_left (exp_lower x ⟨hx.1, hx.2.trans ha.2⟩) (by dsimp [c]; positivity))
  have hp : ∫ x in 0..a, c * poly x = c * (a-a^3/6+a^5/40-a^7/336-5*a^9/13824) := by
    simp only [poly, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [intervalIntegral.integral_const, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_pow, sub_zero,
      Nat.cast_ofNat, smul_eq_mul]
    ring
  rw [hp] at h
  exact h
private lemma normal_box (a b : ℝ) (hab : -a ≤ b) :
    μ.real (Icc (-a) b) = μ.real (Ici (-a)) - μ.real (Ioi b) := by
  have hs : Ici (-a) \ Ioi b = Icc (-a) b := by ext x; simp
  rw [← hs, measureReal_sdiff (show Ioi b ⊆ Ici (-a) from fun x hx => hab.trans hx.le) measurableSet_Ioi]
private lemma tails_strict : μ.real (Ioi (7/2)) < 1/350 ∧ μ.real (Ioi 5) < 1/16000 := by
  exact ⟨(measureReal_mono Ioi_subset_Ici_self).trans_lt tail_bounds.1,
    (measureReal_mono Ioi_subset_Ici_self).trans_lt tail_bounds.2⟩
private lemma gaussian_box_bounds :
    1191/2000 < μ.real (Icc (-1/4) (7/2)) ∧
    419/500 < μ.real (Icc (-1) (7/2)) ∧
    7999/8000 < μ.real (Icc (-5) 5) ∧ μ.real (Ici (-1/2)) < 7/10 := by
  have hc := c_bounds
  have hq := lower_integral (1/4) (by constructor <;> norm_num)
  have ho := lower_integral 1 (by constructor <;> norm_num)
  norm_num at hq ho
  have hqf := upper_halfline (1/4) (by norm_num)
  have hof := upper_halfline 1 (by norm_num)
  have hqbox := normal_box (1/4) (7/2) (by norm_num)
  have hob := normal_box 1 (7/2) (by norm_num)
  have htb := tails_strict
  have hb5 := normal_box 5 5 (by norm_num)
  have hs5 := normal_symm (Ici (-5)) measurableSet_Ici
  have he5 : (fun x : ℝ => -x) ⁻¹' Ici (-5) = Iic 5 := by ext x; simp
  rw [he5] at hs5
  have hh5 := measureReal_add_measureReal_compl (μ := μ) (s := Iic 5) measurableSet_Iic
  simp only [compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one] at hh5
  change μ.real (Iic 5) + μ.real (Ioi 5) = 1 at hh5
  have hh := upper_halfline (1/2) (by norm_num)
  have hu := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 1/2 by norm_num)
    ((integrable_gaussianPDFReal 0 1).intervalIntegrable)
    (f := gaussianPDFReal 0 1) (g := fun _ => c)
    (intervalIntegrable_const)
    (fun x _ => by rw [pdf]; exact mul_le_of_le_one_right (by dsimp [c]; positivity) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hu
  norm_num at hqbox hqf hh
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
private lemma gaussian_box_products :
    594/1000 < μ.real (Icc (-1/4) (7/2)) * (μ.real (Icc (-5) 5))^15 ∧
    836/1000 < μ.real (Icc (-1) (7/2)) * (μ.real (Icc (-5) 5))^15 ∧
    μ.real (Ici (-1/2)) < 7/10 := by
  rcases gaussian_box_bounds with ⟨hq, ho, hg, hh⟩
  have hpow : 7985/8000 < (μ.real (Icc (-5) 5))^15 := by
    have hp := pow_le_pow_left₀ (show (0:ℝ) ≤ 7999/8000 by norm_num) hg.le 15
    norm_num at hp
    linarith
  refine ⟨?_, ?_, hh⟩
  · nlinarith
  · nlinarith


private lemma box_mass_le {c a : ℝ} (hc : 0 < c) (ha : -c ≤ a)
    (hb : (7/2:ℝ) ≤ 16*c-1/2) :
    (gaussianReal 0 1).real (Set.Icc a (7/2)) *
        ((gaussianReal 0 1).real (Set.Icc (-5) 5))^15 ≤
      ((gaussianMeasure 16) (c • pyramid)).toReal := by
  have h := ENNReal.toReal_mono (measure_ne_top (gaussianMeasure 16) (c • pyramid))
    (measure_mono (μ := gaussianMeasure 16) (box_subset hc ha hb))
  rw [box_measure, ENNReal.toReal_mul, ENNReal.toReal_pow] at h
  exact h
private lemma dilation_bounds :
    594/1000 < ((gaussianMeasure 16) ((1/4:ℝ) • pyramid)).toReal ∧
    836/1000 < ((gaussianMeasure 16) pyramid).toReal ∧
    ((gaussianMeasure 16) ((1/2:ℝ) • pyramid)).toReal < 7/10 := by
  rcases gaussian_box_products with ⟨hq,hk,hh⟩
  refine ⟨hq.trans_le (box_mass_le (by norm_num) (by norm_num) (by norm_num)), ?_,
    half_upper.trans_lt hh⟩
  simpa only [one_smul] using hk.trans_le
    (box_mass_le (c := 1) (by norm_num) (by norm_num) (by norm_num))

/-- The centred pyramid contradicts scalar Gaussian log-concavity. -/
theorem result : ¬ claim := by
  have hbar : BarycenterZero pyramid := barycenter pyramid_compact
  rcases dilation_bounds with ⟨hq,hk,hh⟩
  intro hclaim
  have hc := hclaim 16 pyramid pyramid_body hbar
  have hmid := hc.2 (Set.mem_univ (-Real.log 4)) (Set.mem_univ (0:ℝ))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have ht : (1/2:ℝ) • (-Real.log 4) + (1/2:ℝ) • (0:ℝ) = -Real.log 2 := by
    have hl : Real.log (4:ℝ) = 2*Real.log 2 := by
      convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
    simp only [smul_eq_mul]; rw [hl]; ring
  have h4 : Real.exp (-Real.log (4:ℝ)) = (1/4:ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h2 : Real.exp (-Real.log (2:ℝ)) = (1/2:ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  rw [ht] at hmid
  simp only [h4, h2, Real.exp_zero, one_smul, smul_eq_mul] at hmid
  let A := ((gaussianMeasure 16) ((1/4:ℝ) • pyramid)).toReal
  let B := ((gaussianMeasure 16) ((1/2:ℝ) • pyramid)).toReal
  let C := ((gaussianMeasure 16) pyramid).toReal
  have hAB : A ≤ B := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono quarter_subset_half)
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := hA.trans_le hAB
  have hC : 0 < C := by dsimp [C]; linarith
  have hl : Real.log (A*C) ≤ Real.log (B^2) := by
    rw [Real.log_mul hA.ne' hC.ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    change (1/2)*Real.log A + (1/2)*Real.log C ≤ Real.log B at hmid
    linarith
  have hp := (Real.log_le_log_iff (mul_pos hA hC) (pow_pos hB 2)).mp hl
  change 594/1000 < A at hq
  change 836/1000 < C at hk
  change B < 7/10 at hh
  nlinarith
end D5.S3.Geometry.CentredGaussianDilationRefutation
