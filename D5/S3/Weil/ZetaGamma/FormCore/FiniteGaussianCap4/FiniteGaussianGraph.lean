/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianGraph
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual finite Gaussian graph convergence and normalized Jacobi transport. -/
/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED source, 2026-10-26. No kernel or acceptance claim.

Finite real linear combinations of the supplied ACTUAL atom approximants.
The squared-error theorem consumes the supplied weighted atom convergence;
the energy theorem uses its supplied exponential bounds and ordinary DCT.
All imported attribution and license notices remain applicable.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianCentralMass
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfGaussianWeightedConvergence
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfJacobi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace FiniteGaussianCap4
open LaguerreSevenHalf

def finiteGaussianPartialSum {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ i, c i * gaussianPartialSum (site i) N x

theorem finiteGaussianPartialSum_eq_modes {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (N : ℕ) (x : ℝ) :
    finiteGaussianPartialSum c site N x =
      ∑ n ∈ Finset.range N, finiteGaussianCoefficient c site n * phi x n := by
  classical
  simp only [finiteGaussianPartialSum, gaussianPartialSum, finiteGaussianCoefficient,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteGaussianPartialSum_tendsto {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (x : ℝ) :
    Tendsto (fun N => finiteGaussianPartialSum c site N x) atTop
      (𝓝 (gaussianFeature c site x)) := by
  simpa only [finiteGaussianPartialSum_eq_modes] using
    (finite_gaussian_hasSum c site x).tendsto_sum_nat

theorem gaussianFeature_eq_sum_actual_atoms {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (x : ℝ) :
    gaussianFeature c site x = ∑ i, c i * LaguerreSevenHalf.gaussianAtom (site i) x := by
  classical
  apply tendsto_nhds_unique (finiteGaussianPartialSum_tendsto c site x)
  exact tendsto_finsetSum _ (fun i _ =>
    tendsto_const_nhds.mul (gaussianPartialSum_tendsto (site i) x))

theorem continuous_finiteGaussianPartialSum {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (N : ℕ) : Continuous (finiteGaussianPartialSum c site N) := by
  classical
  exact continuous_finsetSum _ (fun i _ =>
    continuous_const.mul (continuous_gaussianPartialSum (site i) N))

theorem continuous_gaussianFeature_actual {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) : Continuous (gaussianFeature c site) := by
  classical
  have hf : gaussianFeature c site =
      fun x => ∑ i, c i * LaguerreSevenHalf.gaussianAtom (site i) x := by
    funext x
    exact gaussianFeature_eq_sum_actual_atoms c site x
  rw [hf]
  exact continuous_finsetSum _ (fun i _ =>
    continuous_const.mul (continuous_gaussianAtom (site i)))

private theorem weighted_continuous_measurable (s : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) : AEStronglyMeasurable (fun x => x ^ s * f x)
      (volume.restrict (Ioi 0)) := by
  have hw : ContinuousOn (fun x : ℝ => x ^ s) (Ioi 0) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  exact (hw.aestronglyMeasurable measurableSet_Ioi).mul
    (hf.continuousOn.aestronglyMeasurable measurableSet_Ioi)

theorem finite_real_square_bound {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (∑ i, v i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, v i ^ 2 := by
  classical
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ)) v

/-- Actual finite-source weighted graph errors, with no convergence premise. -/
theorem finiteGaussian_weighted_square_error_convergence {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (s : ℝ) (hs : -1 < s) :
    (∀ N, IntegrableOn (fun x => x ^ s *
      |finiteGaussianPartialSum c site N x - gaussianFeature c site x| ^ 2) (Ioi 0)) ∧
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ), x ^ s *
      |finiteGaussianPartialSum c site N x - gaussianFeature c site x| ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let B (N : ℕ) (x : ℝ) : ℝ := (Fintype.card ι : ℝ) * ∑ i,
    c i ^ 2 * (x ^ s * |gaussianPartialSum (site i) N x -
      LaguerreSevenHalf.gaussianAtom (site i) x| ^ 2)
  have hBi (N : ℕ) : IntegrableOn (B N) (Ioi 0) := by
    exact (integrable_finsetSum _ (fun i _ =>
      ((gaussian_weighted_square_error_convergence (site i) s hs).1 N).const_mul
        (c i ^ 2))).const_mul _
  have hdom (N : ℕ) (x : ℝ) (hx : 0 < x) :
      x ^ s * |finiteGaussianPartialSum c site N x - gaussianFeature c site x| ^ 2 ≤ B N x := by
    have he : finiteGaussianPartialSum c site N x - gaussianFeature c site x =
        ∑ i, c i * (gaussianPartialSum (site i) N x -
          LaguerreSevenHalf.gaussianAtom (site i) x) := by
      rw [gaussianFeature_eq_sum_actual_atoms]
      simp only [finiteGaussianPartialSum, mul_sub, Finset.sum_sub_distrib]
    rw [he, sq_abs]
    have h := mul_le_mul_of_nonneg_left
      (finite_real_square_bound (fun i => c i * (gaussianPartialSum (site i) N x -
        LaguerreSevenHalf.gaussianAtom (site i) x))) (Real.rpow_nonneg hx.le s)
    convert h using 1
    simp only [B, mul_pow, sq_abs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hI (N : ℕ) : IntegrableOn (fun x => x ^ s *
      |finiteGaussianPartialSum c site N x - gaussianFeature c site x| ^ 2) (Ioi 0) := by
    apply (hBi N).mono' (weighted_continuous_measurable s
      (((continuous_finiteGaussianPartialSum c site N).sub
        (continuous_gaussianFeature_actual c site)).abs.pow 2))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change ‖x ^ s * |finiteGaussianPartialSum c site N x - gaussianFeature c site x| ^ 2‖ ≤ B N x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg hx.le s) (sq_nonneg _))]
    exact hdom N x hx
  have hBint (N : ℕ) : (∫ x in Ioi (0 : ℝ), B N x) =
      (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 *
        (∫ x in Ioi (0 : ℝ), x ^ s * |gaussianPartialSum (site i) N x -
          LaguerreSevenHalf.gaussianAtom (site i) x| ^ 2) := by
    dsimp only [B]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
      ((gaussian_weighted_square_error_convergence (site i) s hs).1 N).const_mul _)]
    simp only [integral_const_mul]
  have hBlim : Tendsto (fun N => ∫ x in Ioi (0 : ℝ), B N x) atTop (𝓝 (0 : ℝ)) := by
    simp_rw [hBint]
    simpa using tendsto_const_nhds.mul (tendsto_finsetSum _ (fun i _ =>
      tendsto_const_nhds.mul (gaussian_weighted_square_error_convergence (site i) s hs).2))
  refine ⟨hI, squeeze_zero (fun N => integral_nonneg_of_ae ?_) (fun N => ?_) hBlim⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le s) (sq_nonneg _)
  · exact integral_mono_ae (hI N) (hBi N)
      ((ae_restrict_mem measurableSet_Ioi).mono (fun x hx => hdom N x hx))


/-- Squared energy for the difference of actual prefixes and a fixed actual
prefix. Its limit supplies the exact head/tail norm transport. -/
theorem finiteGaussian_weighted_centered_energy_convergence {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (L : ℕ) (s : ℝ) (hs : -1 < s) :
    (∀ N, IntegrableOn (fun x => x ^ s *
      (finiteGaussianPartialSum c site N x - finiteGaussianPartialSum c site L x) ^ 2) (Ioi 0)) ∧
    IntegrableOn (fun x => x ^ s *
      (gaussianFeature c site x - finiteGaussianPartialSum c site L x) ^ 2) (Ioi 0) ∧
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ), x ^ s *
      (finiteGaussianPartialSum c site N x - finiteGaussianPartialSum c site L x) ^ 2)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), x ^ s *
        (gaussianFeature c site x - finiteGaussianPartialSum c site L x) ^ 2)) := by
  classical
  choose K rate hK hr hP hF hE using fun i : ι => gaussian_dominated_bounds (site i)
  let B (x : ℝ) : ℝ := (Fintype.card ι : ℝ) * ∑ i,
    (2 * c i * K i) ^ 2 * (x ^ s * Real.exp (-(2 * rate i) * x))
  have hBi : IntegrableOn B (Ioi 0) := by
    exact (integrable_finsetSum _ (fun i _ =>
      (integrable_decay_weight s (2 * rate i) hs (mul_pos (by norm_num) (hr i))).const_mul
        ((2 * c i * K i) ^ 2))).const_mul _
  have hdiff (N : ℕ) (x : ℝ) :
      finiteGaussianPartialSum c site N x - finiteGaussianPartialSum c site L x =
        ∑ i, c i * (gaussianPartialSum (site i) N x - gaussianPartialSum (site i) L x) := by
    simp only [finiteGaussianPartialSum, mul_sub, Finset.sum_sub_distrib]
  have hdom (N : ℕ) : ∀ᵐ x ∂volume.restrict (Ioi 0),
      ‖x ^ s * (finiteGaussianPartialSum c site N x -
        finiteGaussianPartialSum c site L x) ^ 2‖ ≤ B x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hx.le s) (sq_nonneg _)), hdiff]
    have hsq (i : ι) :
        (c i * (gaussianPartialSum (site i) N x - gaussianPartialSum (site i) L x)) ^ 2 ≤
          (2 * c i * K i) ^ 2 * Real.exp (-(2 * rate i) * x) := by
      have hab : |gaussianPartialSum (site i) N x - gaussianPartialSum (site i) L x| ≤
          (2 * K i) * Real.exp (-rate i * x) := by
        calc
          _ ≤ |gaussianPartialSum (site i) N x| + |gaussianPartialSum (site i) L x| :=
            abs_sub _ _
          _ ≤ K i * Real.exp (-rate i * x) + K i * Real.exp (-rate i * x) :=
            add_le_add (hP i N x hx) (hP i L x hx)
          _ = _ := by ring
      have hp := pow_le_pow_left₀ (abs_nonneg _) hab 2
      have he : Real.exp (-rate i * x) ^ 2 = Real.exp (-(2 * rate i) * x) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [sq_abs, mul_pow, he] at hp
      convert mul_le_mul_of_nonneg_left hp (sq_nonneg (c i)) using 1 <;> ring
    calc
      _ ≤ x ^ s * ((Fintype.card ι : ℝ) * ∑ i,
          (c i * (gaussianPartialSum (site i) N x - gaussianPartialSum (site i) L x)) ^ 2) :=
        mul_le_mul_of_nonneg_left (finite_real_square_bound _) (Real.rpow_nonneg hx.le s)
      _ ≤ x ^ s * ((Fintype.card ι : ℝ) * ∑ i,
          (2 * c i * K i) ^ 2 * Real.exp (-(2 * rate i) * x)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le s)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))
        exact Finset.sum_le_sum (fun i _ => hsq i)
      _ = B x := by
        simp only [B, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
  have hm (N : ℕ) := weighted_continuous_measurable s
    (((continuous_finiteGaussianPartialSum c site N).sub
      (continuous_finiteGaussianPartialSum c site L)).pow 2)
  have hlim : ∀ᵐ x ∂volume.restrict (Ioi 0),
      Tendsto (fun N => x ^ s * (finiteGaussianPartialSum c site N x -
        finiteGaussianPartialSum c site L x) ^ 2) atTop
        (𝓝 (x ^ s * (gaussianFeature c site x - finiteGaussianPartialSum c site L x) ^ 2)) :=
    Filter.Eventually.of_forall (fun x => tendsto_const_nhds.mul
      (((finiteGaussianPartialSum_tendsto c site x).sub tendsto_const_nhds).pow 2))
  have hfm := weighted_continuous_measurable s
    (((continuous_gaussianFeature_actual c site).sub
      (continuous_finiteGaussianPartialSum c site L)).pow 2)
  have hdomf : ∀ᵐ x ∂volume.restrict (Ioi 0),
      ‖x ^ s * (gaussianFeature c site x - finiteGaussianPartialSum c site L x) ^ 2‖ ≤ B x := by
    filter_upwards [ae_all_iff.2 hdom, hlim] with x hx hxl
    exact le_of_tendsto' hxl.norm hx
  exact ⟨fun N => hBi.mono' (hm N) (hdom N), hBi.mono' hfm hdomf,
    tendsto_integral_of_dominated_convergence B hm hBi hdom hlim⟩

/-- Actual finite-source energy convergence, including its integrability. -/
theorem finiteGaussian_weighted_energy_convergence {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (s : ℝ) (hs : -1 < s) :
    (∀ N, IntegrableOn (fun x => x ^ s * finiteGaussianPartialSum c site N x ^ 2) (Ioi 0)) ∧
    IntegrableOn (fun x => x ^ s * gaussianFeature c site x ^ 2) (Ioi 0) ∧
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ), x ^ s * finiteGaussianPartialSum c site N x ^ 2)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), x ^ s * gaussianFeature c site x ^ 2)) := by
  have hzero : finiteGaussianPartialSum c site 0 = fun _ => 0 := by
    funext x
    simp [finiteGaussianPartialSum, gaussianPartialSum]
  simpa only [hzero, sub_zero] using
    finiteGaussian_weighted_centered_energy_convergence c site 0 s hs

private theorem graph_sum_range_two_blocks (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), f n) =
      ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

private theorem graph_even_prefix_realization {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) (N : ℕ) (x : ℝ) :
    physicalPolynomial (∑ k ∈ Finset.range N,
      Polynomial.C (finiteGaussianNormalizedCoefficient c site (2 * k)) *
        psiPolynomial (2 * k)) x = finiteGaussianPartialSum c site (2 * N) x := by
  rw [finiteGaussianPartialSum_eq_modes, graph_sum_range_two_blocks]
  simp only [physicalPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [finite_gaussian_odd_coefficient_zero c site reflection hc hs (2 * k + 1)
    (by exact ⟨k, by omega⟩), zero_mul, add_zero]
  simp only [psiPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    finiteGaussianNormalizedCoefficient, phi]
  field_simp [(centralNormalization_pos (2 * k)).ne']
  <;> ring

private theorem graph_even_prefix_pair (d : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M) :
    polynomialPair
      (∑ k ∈ Finset.range N, Polynomial.C (d k) * psiPolynomial (2 * k))
      (∑ k ∈ Finset.range M, Polynomial.C (d k) * psiPolynomial (2 * k)) =
        ∑ k ∈ Finset.range N, d k ^ 2 := by
  classical
  have hinner (k : ℕ) (hk : k < M) :
      polynomialPair (psiPolynomial (2 * k))
        (∑ j ∈ Finset.range M, Polynomial.C (d j) * psiPolynomial (2 * j)) = d k := by
    rw [polynomialPair_comm, polynomialPair_sum_left]
    simp only [polynomialPair_C_left, polynomialPair_psi]
    have hindex (j : ℕ) : (2 * j = 2 * k) ↔ j = k := by omega
    simp_rw [hindex]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr hk)]
  rw [polynomialPair_sum_left]
  apply Finset.sum_congr rfl
  intro k hk
  rw [polynomialPair_C_left, hinner k (lt_of_lt_of_le (Finset.mem_range.mp hk) hNM)]
  ring

/-- The exact physical norm of a block of actual even prefixes. -/
theorem finiteGaussian_even_prefix_difference_norm {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) (N M : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
      (finiteGaussianPartialSum c site (2 * (N + M)) x -
        finiteGaussianPartialSum c site (2 * N) x) ^ 2) =
      ∑ i ∈ Finset.range M, finiteGaussianNormalizedCoefficient c site (2 * (N + i)) ^ 2 := by
  classical
  let d : ℕ → ℝ := fun k => finiteGaussianNormalizedCoefficient c site (2 * k)
  let P (L : ℕ) : Polynomial ℝ :=
    ∑ k ∈ Finset.range L, Polynomial.C (d k) * psiPolynomial (2 * k)
  have hpair (K L : ℕ) (hKL : K ≤ L) :
      polynomialPair (P K) (P L) = ∑ k ∈ Finset.range K, d k ^ 2 :=
    graph_even_prefix_pair d K L hKL
  have hreal (L : ℕ) (x : ℝ) :
      physicalPolynomial (P L) x = finiteGaussianPartialSum c site (2 * L) x :=
    graph_even_prefix_realization c site reflection hc hs L x
  calc
    _ = ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        physicalPolynomial (P (N + M) - P N) x *
          physicalPolynomial (P (N + M) - P N) x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [physicalPolynomial_sub, hreal]
      ring
    _ = polynomialPair (P (N + M) - P N) (P (N + M) - P N) :=
      integral_physical_product _ _
    _ = (∑ k ∈ Finset.range (N + M), d k ^ 2) -
        ∑ k ∈ Finset.range N, d k ^ 2 := by
      simp only [polynomialPair_sub_left, polynomialPair_sub_right]
      rw [hpair (N + M) (N + M) le_rfl, hpair N N le_rfl,
        hpair N (N + M) (by omega),
        polynomialPair_comm (P (N + M)) (P N), hpair N (N + M) (by omega)]
      ring
    _ = _ := by
      rw [Finset.sum_range_add]
      ring

/-- Actual H Parseval and every fixed-prefix remainder norm, without a basis
completeness assumption. At N=0 this is the complete H-energy HasSum. -/
theorem finiteGaussian_actual_remainder_norm {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) (N : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) *
      (gaussianFeature c site x - finiteGaussianPartialSum c site (2 * N) x) ^ 2) (Ioi 0) ∧
    HasSum (fun i : ℕ => finiteGaussianNormalizedCoefficient c site (2 * (N + i)) ^ 2)
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        (gaussianFeature c site x - finiteGaussianPartialSum c site (2 * N) x) ^ 2) := by
  have h := finiteGaussian_weighted_centered_energy_convergence c site (2 * N) (7 / 2)
    (by norm_num)
  refine ⟨h.2.1, ?_⟩
  have hindex : Tendsto (fun M : ℕ => 2 * (N + M)) atTop atTop :=
    tendsto_atTop_mono (fun M => by change M ≤ 2 * (N + M); omega) tendsto_id
  have hl : Tendsto (fun M : ℕ => ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
      (finiteGaussianPartialSum c site (2 * (N + M)) x -
        finiteGaussianPartialSum c site (2 * N) x) ^ 2) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        (gaussianFeature c site x - finiteGaussianPartialSum c site (2 * N) x) ^ 2)) :=
    h.2.2.comp hindex
  simp_rw [finiteGaussian_even_prefix_difference_norm c site reflection hc hs N] at hl
  exact (hasSum_iff_tendsto_nat_of_nonneg (fun i => sq_nonneg _) _).2 hl

end FiniteGaussianCap4
