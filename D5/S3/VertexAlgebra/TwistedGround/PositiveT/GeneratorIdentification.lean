/- GID: D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original positive Gaussian T generator and its rational analytic candidate. -/

import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFinitePositiveGerm
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.Prod

/-! Absolute convergence and summation of the original finite positive T modes. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology

namespace D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification

open FiniteMode.OriginalGaussianFiniteCandidateModes OriginalGaussianExternalGenerators
open OriginalGaussianExternalAnalyticCandidate (E)

/-- The actual positive T modes equal the fixed finite candidate on the complex unit disk. -/
private theorem externalT_positive_finite_eq (p q : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    OriginalGaussianExternalResolvent.externalT true p true q z = candidateT p q z := by
  have hd : DifferentiableOn ℂ (OriginalGaussianExternalResolvent.externalT true p true q)
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    exact (OriginalGaussianExternalRadialSums.literal_differentiable
      true true p q (by simpa using hw)).differentiableWithinAt
  exact (hd.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (candidateT_analyticOnNhd p q) Metric.isPreconnected_ball
    (show (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 by simp)
    (externalT_positive_finite_germ p q) (by simpa using hz)

private def weighted (F : ℕ → ℕ → ℂ → ℂ) (u v r : ℂ) (pq : ℕ × ℕ) : ℂ :=
  F pq.1 pq.2 r * u ^ pq.1 * v ^ pq.2

/- Finite binomial bounds: the only new convergence estimate. -/
private lemma diagonal_bound (p q : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∑ j ∈ Finset.range (min p q + 1),
      (p.choose j : ℝ) * (q.choose j : ℝ) * r ^ j) ≤
      (1 + Real.sqrt r) ^ (p + q) := by
  let s := Real.sqrt r
  let C : ℕ → ℕ → ℝ := fun n j => (n.choose j : ℝ) * s ^ j
  have hs : 0 ≤ s := Real.sqrt_nonneg r
  have hC (n j : ℕ) : 0 ≤ C n j := by dsimp [C]; positivity
  have hbin (n : ℕ) : (∑ j ∈ Finset.range (n + 1), C n j) = (1 + s) ^ n := by
    simpa [C, mul_comm, add_comm] using (add_pow s (1 : ℝ) n).symm
  have hsq : s * s = r := by simpa [s, ← sq] using Real.sq_sqrt hr
  calc
    _ = ∑ j ∈ Finset.range (min p q + 1), C p j * C q j := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [C]
      rw [show r ^ j = s ^ j * s ^ j by rw [← mul_pow, hsq]]
      ring
    _ ≤ ∑ j ∈ Finset.range (min p q + 1),
        C p j * (∑ k ∈ Finset.range (q + 1), C q k) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (hC p j)
      exact Finset.single_le_sum (fun k _ => hC q k)
        (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))
    _ ≤ ∑ j ∈ Finset.range (p + 1),
        C p j * (∑ k ∈ Finset.range (q + 1), C q k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro j hj hj'
      exact mul_nonneg (hC p j) (Finset.sum_nonneg (fun k _ => hC q k))
    _ = _ := by rw [← Finset.sum_mul, hbin, hbin, pow_add]

private lemma h_norm_bound (p q : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ‖h p q (r : ℂ)‖ ≤ (1 + Real.sqrt r) ^ (p + q) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (min p q + 1),
        ‖(p.choose j : ℂ) * (q.choose j : ℂ) * (r : ℂ) ^ j‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (min p q + 1),
        (p.choose j : ℝ) * (q.choose j : ℝ) * r ^ j := by
      simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr]
    _ ≤ _ := diagonal_bound p q hr

private lemma h2_coefficient_bound (p q j : ℕ) :
    (j + 1 : ℝ) * ((p + 1).choose (j + 1) : ℝ) *
        ((q + 1).choose (j + 1) : ℝ) ≤
      (p + 1 : ℝ) * (q + 1 : ℝ) * (p.choose j : ℝ) * (q.choose j : ℝ) := by
  have hp : (p + 1 : ℝ) * (p.choose j : ℝ) =
      ((p + 1).choose (j + 1) : ℝ) * (j + 1 : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq p j
  have hq : (q + 1 : ℝ) * (q.choose j : ℝ) =
      ((q + 1).choose (j + 1) : ℝ) * (j + 1 : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq q j
  calc
    _ ≤ (j + 1 : ℝ) * ((j + 1 : ℝ) *
        ((p + 1).choose (j + 1) : ℝ) * ((q + 1).choose (j + 1) : ℝ)) :=
      le_mul_of_one_le_left (by positivity)
        (by have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith)
    _ = (((p + 1).choose (j + 1) : ℝ) * (j + 1 : ℝ)) *
        (((q + 1).choose (j + 1) : ℝ) * (j + 1 : ℝ)) := by ring
    _ = _ := by rw [← hp, ← hq]; ring

private lemma h2_norm_bound (p q : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ‖h2 p q (r : ℂ)‖ ≤
      (p + 1 : ℝ) * (q + 1 : ℝ) * (1 + Real.sqrt r) ^ (p + q) := by
  have hn (j : ℕ) : ‖(j + 1 : ℂ)‖ = (j + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (j + 1)
  calc
    _ ≤ ∑ j ∈ Finset.range (min p q + 1),
        ‖(j + 1 : ℂ) * ((p + 1).choose (j + 1) : ℂ) *
          ((q + 1).choose (j + 1) : ℂ) * (r : ℂ) ^ j‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (min p q + 1),
        (j + 1 : ℝ) * ((p + 1).choose (j + 1) : ℝ) *
          ((q + 1).choose (j + 1) : ℝ) * r ^ j := by
      simp only [norm_mul, norm_pow, hn, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr]
    _ ≤ ∑ j ∈ Finset.range (min p q + 1),
        ((p + 1 : ℝ) * (q + 1 : ℝ)) *
          ((p.choose j : ℝ) * (q.choose j : ℝ) * r ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      convert mul_le_mul_of_nonneg_right (h2_coefficient_bound p q j)
        (pow_nonneg hr j) using 1
      ring
    _ = ((p + 1 : ℝ) * (q + 1 : ℝ)) *
        (∑ j ∈ Finset.range (min p q + 1),
          (p.choose j : ℝ) * (q.choose j : ℝ) * r ^ j) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (diagonal_bound p q hr) (by positivity)

private lemma polynomial_geometric_summable {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable (fun n : ℕ => (n + 1 : ℝ) * x ^ n) := by
  have hnorm : ‖x‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx
  simpa [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    summable_choose_mul_geometric_of_norm_lt_one 1 hnorm

private lemma weighted_summable_of_bound (F : ℕ → ℕ → ℂ → ℂ)
    {r : ℝ} {u v : ℂ} (_hr : 0 ≤ r)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1)
    (hF : ∀ p q, ‖F p q r‖ ≤
      (p + 1 : ℝ) * (q + 1 : ℝ) * (1 + Real.sqrt r) ^ (p + q)) :
    Summable (fun pq => ‖weighted F u v r pq‖) := by
  let s := Real.sqrt r
  let x := ‖u‖ * (1 + s)
  let y := ‖v‖ * (1 + s)
  have hs : 0 ≤ s := Real.sqrt_nonneg r
  have hx0 : 0 ≤ x := mul_nonneg (norm_nonneg u) (by linarith)
  have hy0 : 0 ≤ y := mul_nonneg (norm_nonneg v) (by linarith)
  have hx : x < 1 := by
    have hm := mul_pos (show 0 < 1 + s by linarith)
      (show 0 < 1 - s - ‖u‖ by dsimp [s]; linarith)
    dsimp [x]
    nlinarith [sq_nonneg s]
  have hy : y < 1 := by
    have hm := mul_pos (show 0 < 1 + s by linarith)
      (show 0 < 1 - s - ‖v‖ by dsimp [s]; linarith)
    dsimp [y]
    nlinarith [sq_nonneg s]
  have hb := (polynomial_geometric_summable hx0 hx).mul_of_nonneg
    (polynomial_geometric_summable hy0 hy) (fun n => by positivity)
      (fun n => by positivity)
  apply Summable.of_nonneg_of_le (fun pq => norm_nonneg _) (fun pq => ?_) hb
  calc
    ‖weighted F u v r pq‖ = ‖F pq.1 pq.2 r‖ * ‖u‖ ^ pq.1 * ‖v‖ ^ pq.2 := by
      simp only [weighted, norm_mul, norm_pow]
    _ ≤ ((pq.1 + 1 : ℝ) * (pq.2 + 1 : ℝ) * (1 + s) ^ (pq.1 + pq.2)) *
        ‖u‖ ^ pq.1 * ‖v‖ ^ pq.2 := by
      gcongr
      exact hF pq.1 pq.2
    _ = ((pq.1 + 1 : ℝ) * x ^ pq.1) * ((pq.2 + 1 : ℝ) * y ^ pq.2) := by
      dsimp [x, y]
      rw [pow_add, mul_pow, mul_pow]
      ring

private lemma denominator_summable {r : ℝ} {u v : ℂ} (hr : 0 ≤ r)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    Summable (fun pq => ‖weighted h u v r pq‖) ∧
      Summable (fun pq => ‖weighted h2 u v r pq‖) := by
  constructor
  · apply weighted_summable_of_bound h hr hu hv
    intro p q
    apply (h_norm_bound p q hr).trans
    have hs : 0 ≤ (1 + Real.sqrt r) ^ (p + q) := by positivity
    have hpq : (1 : ℝ) ≤ (p + 1 : ℝ) * (q + 1 : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p,
        show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q]
    simpa using mul_le_mul_of_nonneg_right hpq hs
  · exact weighted_summable_of_bound h2 hr hu hv (fun p q => h2_norm_bound p q hr)

/- Guarded shifts are reindexings with zero outside the injection's range. -/
private lemma hasSum_shiftX {F : ℕ → ℕ → ℂ → ℂ} {u v r s : ℂ}
    (hf : HasSum (weighted F u v r) s) :
    HasSum (weighted (shiftX F) u v r) (u * s) := by
  let e : ℕ × ℕ → ℕ × ℕ := fun pq => (pq.1 + 1, pq.2)
  have hi : Function.Injective e := by
    rintro ⟨p,q⟩ ⟨i,j⟩ hij
    dsimp [e] at hij
    have hh := Prod.mk.inj hij
    apply Prod.ext <;> omega
  have hz : ∀ pq, pq ∉ Set.range e → weighted (shiftX F) u v r pq = 0 := by
    rintro ⟨p,q⟩ hpq
    have hp : p = 0 := by
      by_contra hp
      apply hpq
      refine ⟨(p - 1,q), ?_⟩
      dsimp [e]
      apply Prod.ext <;> omega
    simp [weighted, shiftX, hp]
  apply (hi.hasSum_iff hz).mp
  convert hf.mul_left u using 1
  funext pq
  simp only [Function.comp_def, weighted, e, shiftX, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, pow_succ]
  ring

private lemma hasSum_shiftY {F : ℕ → ℕ → ℂ → ℂ} {u v r s : ℂ}
    (hf : HasSum (weighted F u v r) s) :
    HasSum (weighted (shiftY F) u v r) (v * s) := by
  let e : ℕ × ℕ → ℕ × ℕ := fun pq => (pq.1, pq.2 + 1)
  have hi : Function.Injective e := by
    rintro ⟨p,q⟩ ⟨i,j⟩ hij
    dsimp [e] at hij
    have hh := Prod.mk.inj hij
    apply Prod.ext <;> omega
  have hz : ∀ pq, pq ∉ Set.range e → weighted (shiftY F) u v r pq = 0 := by
    rintro ⟨p,q⟩ hpq
    have hq : q = 0 := by
      by_contra hq
      apply hpq
      refine ⟨(p,q - 1), ?_⟩
      dsimp [e]
      apply Prod.ext <;> omega
    simp [weighted, shiftY, hq]
  apply (hi.hasSum_iff hz).mp
  convert hf.mul_left v using 1
  funext pq
  simp only [Function.comp_def, weighted, e, shiftY, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, pow_succ]
  ring

private lemma hasSum_shift11 {F : ℕ → ℕ → ℂ → ℂ} {u v r s : ℂ}
    (hf : HasSum (weighted F u v r) s) :
    HasSum (weighted (shift11 F) u v r) (u * v * s) := by
  have heq : shiftX (shiftY F) = shift11 F := by
    funext p q r
    cases p <;> cases q <;> simp [shiftX, shiftY, shift11]
  simpa only [heq, mul_assoc] using hasSum_shiftX (hasSum_shiftY hf)

private lemma hasSum_stencil {F : ℕ → ℕ → ℂ → ℂ} {u v r s : ℂ}
    (hf : HasSum (weighted F u v r) s) :
    HasSum (weighted (denominatorStencil F) u v r) (E u v r * s) := by
  convert ((hf.sub (hasSum_shiftX hf)).sub (hasSum_shiftY hf)).add
    ((hasSum_shift11 hf).mul_left (1 - r)) using 1
  · funext pq
    dsimp [weighted, denominatorStencil]
    ring
  · dsimp [E]
    ring

private lemma denominator_hasSums {r : ℝ} {u v : ℂ} (hr : 0 ≤ r)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    E u v r ≠ 0 ∧ HasSum (weighted h u v r) (1 / E u v r) ∧
      HasSum (weighted h2 u v r) (1 / E u v r ^ 2) := by
  have hn := denominator_summable hr hu hv
  have hh := hn.1.of_norm.hasSum
  have hh2 := hn.2.of_norm.hasSum
  have hd : HasSum (weighted (denominatorStencil h) u v r) (1 : ℂ) := by
    convert hasSum_ite_eq ((0,0) : ℕ × ℕ) (1 : ℂ) using 1
    funext pq
    rcases pq with ⟨p,q⟩
    by_cases hp : p = 0 <;> by_cases hq : q = 0 <;>
      simp [weighted, h_inverse_stencil, hp, hq]
  have heq := (hasSum_stencil hh).unique hd
  have hne : E u v r ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at heq
    exact zero_ne_one heq
  have hval : (∑' pq, weighted h u v r pq) = 1 / E u v r := by
    apply (eq_div_iff hne).mpr
    simpa only [mul_comm] using heq
  rw [hval] at hh
  have heq2 : E u v r * (∑' pq, weighted h2 u v r pq) = 1 / E u v r := by
    have hs := hasSum_stencil hh2
    have hfun : weighted (denominatorStencil h2) u v r = weighted h u v r := by
      funext pq
      simp only [weighted, h2_inverse_stencil]
    rw [hfun] at hs
    exact hs.unique hh
  have hval2 : (∑' pq, weighted h2 u v r pq) = 1 / E u v r ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hne)).mpr
    calc
      _ = (E u v r * (∑' pq, weighted h2 u v r pq)) * E u v r := by ring
      _ = 1 := by rw [heq2]; field_simp [hne]
  rw [hval2] at hh2
  exact ⟨hne, hh, hh2⟩

/- One domain-specific rectangular Cauchy product; A is literally ℕ×ℕ. -/
private lemma hasSum_rectangle {f g : ℕ × ℕ → ℂ} {s t : ℂ}
    (hf : HasSum f s) (hg : HasSum g t) :
    HasSum (fun pq : ℕ × ℕ =>
      ∑ i ∈ Finset.range (pq.1 + 1), ∑ j ∈ Finset.range (pq.2 + 1),
        f (i,j) * g (pq.1 - i,pq.2 - j)) (s * t) := by
  have hfg := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  have hc := summable_sum_mul_antidiagonal_of_summable_mul hfg
  have hv := hf.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg.summable hfg
  rw [hf.tsum_eq, hg.tsum_eq] at hv
  have hh : HasSum (fun n : ℕ × ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      f kl.1 * g kl.2) (s * t) := by
    rw [hv]
    exact hc.hasSum
  convert hh using 1
  funext pq
  have had : Finset.HasAntidiagonal.antidiagonal pq =
      (Finset.HasAntidiagonal.antidiagonal pq.1 ×ˢ Finset.HasAntidiagonal.antidiagonal pq.2).map
        (Equiv.prodProdProdComm ℕ ℕ ℕ ℕ).toEmbedding := rfl
  rw [had, Finset.sum_map, Finset.sum_product]
  simp only [Equiv.toEmbedding_apply, Equiv.prodProdProdComm_apply]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private lemma hasSum_a {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    HasSum (fun p : ℕ => a p r * u ^ p) (sourceMode true u r) := by
  simpa only [sourceMode, sourceAmplitude_true_finite] using
    (sourceAmplitude_generators hu).1.summable.hasSum

private lemma hasSum_source_pair {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    HasSum (weighted (fun p q r => a p r * a q r) u v r)
      (sourceMode true u r * sourceMode true v r) := by
  have hL : HasSum (fun p : ℕ => a p r * u ^ p) (sourceMode true u r) := hasSum_a hu
  have hR : HasSum (fun q : ℕ => a q r * v ^ q) (sourceMode true v r) := hasSum_a hv
  have hnL : Summable (fun p : ℕ => ‖a p r * u ^ p‖) := hL.summable.norm
  have hnR : Summable (fun q : ℕ => ‖a q r * v ^ q‖) := hR.summable.norm
  have hprod : Summable (fun pq : ℕ × ℕ =>
      (a pq.1 r * u ^ pq.1) * (a pq.2 r * v ^ pq.2)) :=
    summable_mul_of_summable_norm
      (f := fun p : ℕ => a p r * u ^ p) (g := fun q : ℕ => a q r * v ^ q) hnL hnR
  have hp : HasSum (fun pq : ℕ × ℕ =>
      (a pq.1 r * u ^ pq.1) * (a pq.2 r * v ^ pq.2))
      (sourceMode true u r * sourceMode true v r) :=
    HasSum.mul (f := fun p : ℕ => a p r * u ^ p)
      (g := fun q : ℕ => a q r * v ^ q) hL hR hprod
  have heq : weighted (fun p q r => a p r * a q r) u v r =
      (fun pq : ℕ × ℕ => (a pq.1 r * u ^ pq.1) * (a pq.2 r * v ^ pq.2)) := by
    funext pq
    dsimp only [weighted]
    ring
  exact heq.symm ▸ hp

private lemma hasSum_L {H : ℕ → ℕ → ℂ → ℂ} {u v r s : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hH : HasSum (weighted H u v r) s) :
    HasSum (weighted (L H) u v r)
      ((sourceMode true u r * sourceMode true v r) * s) := by
  have hc := hasSum_rectangle (hasSum_source_pair hu hv) hH
  convert hc using 1
  funext pq
  dsimp [weighted, L]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hip : i + (pq.1 - i) = pq.1 := by have := Finset.mem_range.mp hi; omega
  have hjq : j + (pq.2 - j) = pq.2 := by have := Finset.mem_range.mp hj; omega
  rw [show u ^ pq.1 = u ^ i * u ^ (pq.1 - i) by rw [← pow_add, hip],
    show v ^ pq.2 = v ^ j * v ^ (pq.2 - j) by rw [← pow_add, hjq]]
  ring

/- This is the actual unconditional generator target. No germ or mode-equality
hypothesis occurs here. All summability is obtained before evaluating sums. -/
theorem positiveT_hasSum {r : ℝ} {u v : ℂ} (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    HasSum (fun pq : ℕ × ℕ =>
      FiniteMode.OriginalGaussianFiniteCandidateModes.t pq.1 pq.2 (r : ℂ) *
        u ^ pq.1 * v ^ pq.2)
      (OriginalGaussianExternalAnalyticCandidate.candidateT u v (r : ℂ)) := by
  have hs0 := Real.sqrt_nonneg r
  have hsq := Real.sq_sqrt hr.le
  have hs1 : Real.sqrt r < 1 := by nlinarith
  have hrs : r ≤ Real.sqrt r := by
    nlinarith [mul_nonneg hs0 (show 0 ≤ 1 - Real.sqrt r by linarith)]
  have hnr : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hur : ‖u‖ + ‖(r : ℂ)‖ < 1 := by rw [hnr]; linarith
  have hvr : ‖v‖ + ‖(r : ℂ)‖ < 1 := by rw [hnr]; linarith
  obtain ⟨hne, hh, hh2⟩ := denominator_hasSums hr.le hu hv
  have hL := hasSum_L hur hvr hh
  have hL2 := hasSum_L hur hvr hh2
  change HasSum (weighted L_h u v r) _ at hL
  change HasSum (weighted L_h2 u v r) _ at hL2
  have hP := (hL.add ((hasSum_shift11 hL).mul_left (1 - (r : ℂ)))).mul_left
    ((r : ℂ) / 2)
  have hPfull := hP.add ((hasSum_shift11 hL2).mul_left ((r : ℂ) ^ 2))
  have hcor := (hasSum_source_pair hur hvr).mul_left (k (r : ℂ))
  convert hPfull.sub hcor using 1
  · funext pq
    dsimp [weighted, t, P]
    ring
  · have hk : OriginalGaussianExternalAnalyticCandidate.correction (r : ℂ) =
        k (r : ℂ) := rfl
    dsimp only [OriginalGaussianExternalAnalyticCandidate.candidateT,
      OriginalGaussianExternalAnalyticCandidate.rationalT]
    rw [hk]
    field_simp [hne]

/-- The actual positive original square-resolvent generator on its real radial bidisk. -/
theorem positiveT_eq_candidateT {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    OriginalGaussianExternalGeneratedSource.kernelMode true true true u v (Real.sqrt r : ℂ) =
      OriginalGaussianExternalAnalyticCandidate.candidateT u v (r : ℂ) := by
  have hz : ‖(Real.sqrt r : ℂ)‖ < 1 :=
    OriginalGaussianResolvent.radial_norm_lt_one hr1
  have hsq : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  rw [OriginalGaussianExternalGeneratedSource.kernelMode]
  calc
    _ = ∑' pq : ℕ × ℕ, t pq.1 pq.2 (r : ℂ) * u ^ pq.1 * v ^ pq.2 := by
      apply tsum_congr
      intro pq
      simp only [ite_true, externalT_positive_finite_eq pq.1 pq.2 hz,
        FiniteMode.OriginalGaussianFiniteCandidateModes.candidateT, hsq]
    _ = _ := (positiveT_hasSum hr hr1 hu hv).tsum_eq

end D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification
