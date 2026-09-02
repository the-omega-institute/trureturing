/- GID: D5/S3/Analytic/Isolation/PositiveDeterminantCoefficientCompactness
   generality: G
   mirror-B: D5/B/S3/Analytic/Isolation/PositiveDeterminantCoefficientCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coefficient limits of positive matrix determinants converge locally uniformly. -/

import D5.S3.Analytic.Isolation.PositiveFredholmLimitZeros
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

open Filter Set
open scoped BigOperators ComplexOrder Polynomial Topology

namespace D5.S3.Analytic.Isolation.PositiveDeterminantCoefficientCompactness

private theorem iteratedDeriv_polynomial_eval_zero (p : ℂ[X]) (m : ℕ) :
    iteratedDeriv m (fun w => p.eval w) 0 = (m.factorial : ℂ) * p.coeff m := by
  rw [iteratedDeriv_eq_iterate]
  have hiterate :
      deriv^[m] (fun w => p.eval w) =
        fun w => (Polynomial.derivative^[m] p).eval w := by
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        rw [ih]
        funext w
        simpa only [Function.iterate_succ_apply'] using
          ((Polynomial.derivative^[m] p).hasDerivAt w).deriv
  rw [hiterate]
  change (Polynomial.derivative^[m] p).eval 0 = _
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

private theorem positive_determinant_norm_le_exp
    {rank : ℕ} (A : Matrix (Fin rank) (Fin rank) ℂ)
    (hA : A.PosSemidef) (w : ℂ) :
    ‖Matrix.det (1 + w • A)‖ ≤ Real.exp (‖w‖ * ‖A.trace‖) := by
  let eigenvalue : Fin rank → ℝ := hA.1.eigenvalues
  have hpositive (j : Fin rank) : 0 ≤ eigenvalue j := hA.eigenvalues_nonneg j
  have hsum_nonnegative : 0 ≤ ∑ j, eigenvalue j :=
    Finset.sum_nonneg fun j _ => hpositive j
  have hsum : (∑ j, eigenvalue j) = ‖A.trace‖ := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    calc
      ∑ j, eigenvalue j = ‖((∑ j, eigenvalue j : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hsum_nonnegative]
      _ = ‖∑ j, (eigenvalue j : ℂ)‖ := by
        rw [Complex.ofReal_sum]
  rw [D5.S3.Analytic.Isolation.PositiveFredholmLimitZeros.positive_matrix_det_factorization
    A hA w, norm_prod]
  calc
    ∏ j, ‖1 + w * (eigenvalue j : ℂ)‖ ≤
        ∏ j, (1 + ‖w‖ * eigenvalue j) := by
      exact Finset.prod_le_prod
        (fun j _ => norm_nonneg _)
        (fun j _ => by
          calc
            ‖1 + w * (eigenvalue j : ℂ)‖ ≤
                ‖(1 : ℂ)‖ + ‖w * (eigenvalue j : ℂ)‖ := norm_add_le _ _
            _ = 1 + ‖w‖ * eigenvalue j := by
              rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (hpositive j)])
    _ ≤ Real.exp (∑ j, ‖w‖ * eigenvalue j) := by
      simpa using
        Real.prod_one_add_le_exp_sum Finset.univ
          (fun j => mul_nonneg (norm_nonneg w) (hpositive j))
    _ = Real.exp (‖w‖ * ‖A.trace‖) := by
      rw [← Finset.mul_sum, hsum]

private theorem polynomial_coefficient_limit_locally_uniform
    (p : ℕ → ℂ[X]) (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q)
    (hcoeff : ∀ m, Tendsto (fun N => (p N).coeff m) atTop
      (𝓝 ((m.factorial : ℂ)⁻¹ * iteratedDeriv m Q 0)))
    (hsphere : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖(p N).eval z‖ ≤ C) :
    TendstoLocallyUniformly (fun N w => (p N).eval w) Q atTop := by
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro x
  let inner : ℝ := ‖x‖ + 1
  let outer : ℝ := ‖x‖ + 2
  have hinner : 0 < inner := by dsimp [inner]; positivity
  have houter : 0 < outer := by dsimp [outer]; positivity
  have hinner_outer : inner < outer := by dsimp [inner, outer]; linarith
  let K : Set ℂ := Metric.closedBall x 1
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall x 1)
  obtain ⟨C, hC, hsphere_eventually⟩ := hsphere outer houter
  let qcoeff : ℕ → ℂ := fun m =>
    (m.factorial : ℂ)⁻¹ * iteratedDeriv m Q 0
  let coordinate : C(K, ℂ) :=
    ⟨fun z => z.1, continuous_subtype_val⟩
  let term : ℕ → ℕ → C(K, ℂ) := fun N m =>
    ContinuousMap.const K ((p N).coeff m) * coordinate ^ m
  let limitTerm : ℕ → C(K, ℂ) := fun m =>
    ContinuousMap.const K (qcoeff m) * coordinate ^ m
  let bound : ℕ → ℝ := fun m => C * (inner / outer) ^ m
  have hratio_nonnegative : 0 ≤ inner / outer := div_nonneg hinner.le houter.le
  have hratio_lt_one : inner / outer < 1 :=
    (div_lt_one houter).mpr hinner_outer
  have hbound_summable : Summable bound := by
    have hnorm : ‖(inner / outer : ℝ)‖ < 1 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hratio_nonnegative] using hratio_lt_one
    exact (summable_geometric_of_norm_lt_one hnorm).mul_left C
  have hpoint_bound (z : K) : ‖(z : ℂ)‖ ≤ inner := by
    have hz : dist (z : ℂ) x ≤ 1 := z.2
    calc
      ‖(z : ℂ)‖ = dist (z : ℂ) 0 := by rw [dist_zero_right]
      _ ≤ dist (z : ℂ) x + dist x 0 := dist_triangle _ _ _
      _ ≤ inner := by
        dsimp [inner]
        rw [dist_zero_right]
        linarith
  have hcoefficient_bound : ∀ᶠ N in atTop, ∀ m,
      ‖(p N).coeff m‖ ≤ C / outer ^ m := by
    filter_upwards [hsphere_eventually] with N hN
    intro m
    have hderivative :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m houter
        (p N).differentiable.diffContOnCl hN
    rw [iteratedDeriv_polynomial_eval_zero, norm_mul,
      Complex.norm_natCast] at hderivative
    have hfac : 0 < (m.factorial : ℝ) := by positivity
    have hcancel : (m.factorial : ℝ) * ‖(p N).coeff m‖ ≤
        (m.factorial : ℝ) * (C / outer ^ m) := by
      convert hderivative using 1
      all_goals ring
    nlinarith [hcancel]
  have hterm_bound : ∀ᶠ N in atTop, ∀ m, ‖term N m‖ ≤ bound m := by
    filter_upwards [hcoefficient_bound] with N hN
    intro m
    rw [ContinuousMap.norm_le _ (mul_nonneg hC (pow_nonneg hratio_nonnegative m))]
    intro z
    simp only [term, coordinate, ContinuousMap.mul_apply, ContinuousMap.const_apply,
      ContinuousMap.pow_apply, norm_mul, norm_pow]
    calc
      ‖(p N).coeff m‖ * ‖(z : ℂ)‖ ^ m ≤
          (C / outer ^ m) * inner ^ m :=
        mul_le_mul (hN m) (pow_le_pow_left₀ (norm_nonneg _) (hpoint_bound z) m)
          (pow_nonneg (norm_nonneg _) m) (by positivity)
      _ = bound m := by
        dsimp [bound]
        rw [div_pow]
        field_simp
  have hterm_tendsto (m : ℕ) :
      Tendsto (fun N => term N m) atTop (𝓝 (limitTerm m)) := by
    have hcontinuous : Continuous (fun a : ℂ =>
        ContinuousMap.const K a * coordinate ^ m) := by fun_prop
    exact (hcontinuous.tendsto _).comp (hcoeff m)
  have htannery :
      Tendsto (fun N => ∑' m, term N m) atTop (𝓝 (∑' m, limitTerm m)) :=
    tendsto_tsum_of_dominated_convergence hbound_summable hterm_tendsto hterm_bound
  have hterm_summable : Summable limitTerm := by
    apply hbound_summable.of_norm_bounded
    intro m
    exact le_of_tendsto (tendsto_norm.comp (hterm_tendsto m))
      (hterm_bound.mono fun N hN => hN m)
  have hpolynomial_sum (N : ℕ) :
      ∑' m, term N m =
        ⟨fun z : K => (p N).eval z, (p N).continuous.comp continuous_subtype_val⟩ := by
    rw [tsum_eq_sum (s := (p N).support)]
    · ext z
      simp only [term, coordinate, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
        ContinuousMap.const_apply, ContinuousMap.pow_apply]
      exact (p N).eval_eq_sum.symm
    · intro m hm
      have hzero : (p N).coeff m = 0 := by
        simpa [Polynomial.mem_support_iff] using hm
      simp [term, hzero]
  have hlimit_sum :
      ∑' m, limitTerm m =
        ⟨fun z : K => Q z, hQ.continuous.comp continuous_subtype_val⟩ := by
    ext z
    rw [← ContinuousMap.tsum_apply hterm_summable]
    simp only [limitTerm, coordinate, ContinuousMap.mul_apply,
      ContinuousMap.const_apply, ContinuousMap.pow_apply, qcoeff]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Complex.taylorSeries_eq_of_entire' (c := 0) (z := (z : ℂ)) hQ)
  have hmap_tendsto :
      Tendsto
        (fun N =>
          (⟨fun z : K => (p N).eval z,
            (p N).continuous.comp continuous_subtype_val⟩ : C(K, ℂ)))
        atTop
        (𝓝 (⟨fun z : K => Q z,
          hQ.continuous.comp continuous_subtype_val⟩ : C(K, ℂ))) := by
    simpa only [hpolynomial_sum, hlimit_sum] using htannery
  refine ⟨K, Metric.closedBall_mem_nhds x zero_lt_one, ?_⟩
  exact (hQ.continuous.continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun N => (p N).continuous.continuousOn)).mp hmap_tendsto

/-- If every coefficient of positive finite matrix determinants converges to the
corresponding Taylor coefficient of an entire normalized function, then the determinants
converge locally uniformly to that function and all its zeros are nonpositive real numbers. -/
theorem positive_determinant_coefficient_compactness
    (rank : ℕ → ℕ)
    (A : (N : ℕ) → Matrix (Fin (rank N)) (Fin (rank N)) ℂ)
    (hA : ∀ N, (A N).PosSemidef)
    (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q) (hQ0 : Q 0 = 1)
    (hcoeff : ∀ m, Tendsto
      (fun N =>
        (Matrix.det
          (1 + (Polynomial.X : ℂ[X]) • (A N).map Polynomial.C)).coeff m)
      atTop (𝓝 ((m.factorial : ℂ)⁻¹ * iteratedDeriv m Q 0))) :
    TendstoLocallyUniformly
        (fun N w => Matrix.det (1 + w • A N)) Q atTop ∧
      ∀ w, Q w = 0 → w.im = 0 ∧ w.re ≤ 0 := by
  let p : ℕ → ℂ[X] := fun N =>
    Matrix.det (1 + (Polynomial.X : ℂ[X]) • (A N).map Polynomial.C)
  have heval (N : ℕ) (w : ℂ) :
      (p N).eval w = Matrix.det (1 + w • A N) := by
    simp [p, eval_det, ← Matrix.smul_eq_mul_diagonal]
  let qone : ℂ := (1 : ℂ)⁻¹ * iteratedDeriv 1 Q 0
  have htrace : Tendsto (fun N => (A N).trace) atTop (𝓝 qone) := by
    simpa [p, qone, Matrix.coeff_det_one_add_X_smul_one] using hcoeff 1
  let traceBound : ℝ := ‖qone‖ + 1
  have htrace_bound : ∀ᶠ N in atTop, ‖(A N).trace‖ ≤ traceBound := by
    have hclose : ∀ᶠ N in atTop, dist ((A N).trace) qone < 1 :=
      (Metric.tendsto_nhds.1 htrace) 1 zero_lt_one
    filter_upwards [hclose] with N hN
    calc
      ‖(A N).trace‖ = dist ((A N).trace) 0 := by rw [dist_zero_right]
      _ ≤ dist ((A N).trace) qone + dist qone 0 := dist_triangle _ _ _
      _ ≤ traceBound := by
        dsimp [traceBound]
        rw [dist_zero_right]
        linarith
  have hsphere : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖(p N).eval z‖ ≤ C := by
    intro R hR
    refine ⟨Real.exp (R * traceBound), Real.exp_nonneg _, ?_⟩
    filter_upwards [htrace_bound] with N hN
    intro z hz
    have hnormz : ‖z‖ = R := by
      simpa only [mem_sphere_zero_iff_norm] using hz
    rw [heval]
    calc
      ‖Matrix.det (1 + z • A N)‖ ≤
          Real.exp (‖z‖ * ‖(A N).trace‖) :=
        positive_determinant_norm_le_exp (A N) (hA N) z
      _ ≤ Real.exp (R * traceBound) := by
        apply Real.exp_le_exp.mpr
        rw [hnormz]
        exact mul_le_mul_of_nonneg_left hN hR.le
  have hlocalPolynomial :=
    polynomial_coefficient_limit_locally_uniform p Q hQ (by simpa [p] using hcoeff) hsphere
  have hlocal : TendstoLocallyUniformly
      (fun N w => Matrix.det (1 + w • A N)) Q atTop := by
    simpa only [heval] using hlocalPolynomial
  refine ⟨hlocal, ?_⟩
  exact D5.S3.Analytic.Isolation.PositiveFredholmLimitZeros.positive_fredholm_limit_zeros
    rank A hA Q hlocal hQ0

#print axioms positive_determinant_coefficient_compactness

end D5.S3.Analytic.Isolation.PositiveDeterminantCoefficientCompactness
