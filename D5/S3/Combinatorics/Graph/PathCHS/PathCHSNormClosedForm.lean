/- GID: D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Complete homogeneous symmetric path norms admit explicit formulas. -/

/-
admission_basis: open-problem-resolution (#18565; Proved)
escape_witness: continuant_change_variable
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18981.
The zero-extended binomial coefficient uses IntegerIndexBinomial.binom;
constant-weight continuants use CiglerStripProductAlgebra.cont.
The Chebyshev degree lemma supplies the degree comparison at the path spectral nodes.
Declaration proof_shape (same-delivery helpers expanded):
  pathAdjHermitian: bind-only; consumers: prod_path_eigenvalues, prod_eigenvalues_polynomial, chs, chs_formula, path_hsymm_series.
  chs: bind-only; consumers: PathCHSNormBCSRemark43ClosedRefutation.result, chs_even_coeff, result, PathCHSNormBCSRemark43.result, PathCHSNormBCSRemark43.claim, chsNorm, PathCHSNormBCSRemark43.chs_eq_node_hsymm, PathCHSNormBCSRemark43ClosedRefutation.claim, claim, chs.eq_1, PathCHSNormBCSRemark43.chs_eq_trig, chs_formula, path_hsymm_series.
  chsNorm: bind-only; consumers: result, chsNorm.eq_1, claim.
  pathFormula: bind-only; consumers: PathCHSNormBCSRemark43ClosedRefutation.result, result, PathCHSNormBCSRemark43.result, reciprocal_closed_coefficient, PathCHSNormBCSRemark43.bilateral_eq_pathFormula, pathFormula.eq_1, claim, chs_formula.
  claim: bind-only; consumers: result.
  eval_hsymm_coeff: content; escape_witness: eval_hsymm_coeff; consumers: hsymm_series_product.
  geometric_mul_linear: bind-only; consumers: PathCHSNormBCSRemark43.hsymm_partial_fractions, hsymm_series_product.
  hsymm_series_product: content; escape_witness: eval_hsymm_coeff; consumers: PathCHSNormBCSRemark43.hsymm_partial_fractions, PathCHSNormBCSRemark43.chs_eq_node_hsymm, path_hsymm_series.
  det_path_pencil: content; escape_witness: det_path_pencil; consumers: prod_path_eigenvalues.
  prod_path_eigenvalues: content; escape_witness: det_path_pencil; consumers: prod_eigenvalues_polynomial.
  continuant_map: content; escape_witness: continuant_map; consumers: prod_eigenvalues_polynomial, continuant_constantCoeff, chs_even_coeff, PathCHSNormBCSRemark43.chs_eq_node_hsymm, path_hsymm_series.
  continuant_zero: content; escape_witness: continuant_zero; consumers: continuant_constantCoeff, chs_even_coeff, PathCHSNormBCSRemark43.node_reciprocal_product.
  continuant_change_variable: content; escape_witness: continuant_change_variable; consumers: model_subst_inverse.
  prod_eigenvalues_polynomial: content; escape_witness: det_path_pencil; consumers: path_hsymm_series.
  model: bind-only; consumers: model_subst_inverse, model.eq_1, reciprocal_coefficient_model.
  continuant_constantCoeff: content; escape_witness: continuant_map; consumers: model_subst_inverse.
  model_subst_inverse: content; escape_witness: continuant_change_variable; consumers: reciprocal_coefficient_model.
  reciprocal_coefficient_model: content; escape_witness: continuant_change_variable; consumers: reciprocal_closed_coefficient.
  coeff_inverse_one_sub_X_pow: bind-only; consumers: coeff_mul_inverse_one_sub_X_pow.
  coeff_mul_inverse_one_sub_X_pow: bind-only; consumers: reciprocal_closed_coefficient.
  second_difference: bind-only; consumers: reciprocal_closed_coefficient.
  path_hsymm_series: content; escape_witness: eval_hsymm_coeff; consumers: chs_even_coeff, PathCHSNormBCSRemark43.chs_eq_node_hsymm.
  chs_even_coeff: content; escape_witness: eval_hsymm_coeff; consumers: chs_formula.
  reciprocal_closed_coefficient: content; escape_witness: continuant_change_variable; consumers: chs_formula.
  chs_formula: content; escape_witness: continuant_change_variable; consumers: PathCHSNormBCSRemark43ClosedRefutation.result, result, PathCHSNormBCSRemark43.result.
  result: content; escape_witness: continuant_change_variable; consumers: settling result.
  chebS_degree: bind-only; consumers: PathCHSNormBCSRemark43.nodal_eq_S, AndersonDefectFamily.discriminant_attains, AndersonDefectFamily.rational_discriminant_degree.
-/

import D5.S0.Conventions.IntegerIndexBinomial
import D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductContinuants
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import D5.S3.Combinatorics.Nonnesting.CatalanLagrangeBridge

open D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

open Matrix

theorem pathAdjHermitian (n : ℕ) : ((Matrix.of (fun i j : Fin n => if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then (1 : ℝ) else 0))).IsHermitian := by
  classical
  simpa only [SimpleGraph.adjMatrix, SimpleGraph.pathGraph_adj] using
    (SimpleGraph.pathGraph n).isHermitian_adjMatrix ℝ

/-- `h_d(λ₁, …, λ_n)` for the eigenvalues of `A_n` (Mathlib's complete homogeneous symmetric
polynomial `hsymm`). -/
noncomputable def chs (n d : ℕ) : ℝ :=
  MvPolynomial.eval (pathAdjHermitian n).eigenvalues (MvPolynomial.hsymm (Fin n) ℝ d)

/-- Theorem 1.4: the CHS norm `‖P_n‖_d = h_d(λ₁, …, λ_n)^{1/d}` (d even). -/
noncomputable def chsNorm (n d : ℕ) : ℝ := chs n d ^ ((1 : ℝ) / d)

/-- The proposed closed form for `‖P_n‖_{2m}^{2m}`:
`∑_{k=0}^{⌊m/(n+1)⌋} [C(2m+n-1, m-k(n+1)) - 2 C(2m+n-1, m-k(n+1)-1) + C(2m+n-1, m-k(n+1)-2)]`. -/
def pathFormula (n m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m / (n + 1) + 1),
    ((D5.S0.Conventions.IntegerIndexBinomial.binom (2 * m + n - 1) ((m : ℤ) - k * (n + 1)) : ℤ) -
      2 * D5.S0.Conventions.IntegerIndexBinomial.binom (2 * m + n - 1) ((m : ℤ) - k * (n + 1) - 1) +
      D5.S0.Conventions.IntegerIndexBinomial.binom (2 * m + n - 1) ((m : ℤ) - k * (n + 1) - 2))

/-- Problem 1 (Chávez et al., arXiv:2311.04689): compute `‖P_n‖_d` for even `d ≥ 4`; answered by
`‖P_n‖_{2m} = (pathFormula n m)^{1/(2m)}` for all `n ≥ 1`, `m ≥ 2`. -/
def claim : Prop :=
  ∀ n m : ℕ, 1 ≤ n → 2 ≤ m →
    chs n (2 * m) = pathFormula n m ∧ chsNorm n (2 * m) = (pathFormula n m : ℝ) ^ ((1 : ℝ) / (2 * m : ℕ))


end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm


set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
open PowerSeries

noncomputable section

-- The weighted multiset sum is the coefficient of the product of geometric series.
private theorem eval_hsymm_coeff {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (a : ι → R) (d : ℕ) :
    MvPolynomial.eval a (MvPolynomial.hsymm ι R d) =
      coeff d (∏ i, (PowerSeries.mk fun k => a i ^ k)) := by
  classical
  simp only [MvPolynomial.hsymm, map_sum, map_multiset_prod,
    Multiset.map_map, Function.comp_def, MvPolynomial.eval_X]
  rw [coeff_prod]
  refine Finset.sum_bij (fun s _ => s.val.toFinsupp) ?_ ?_ ?_ ?_
  · intro s _
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨by simpa only [Function.id_def] using
      (Multiset.toFinsupp_sum_eq s.val).trans s.property, Finset.subset_univ _⟩
  · intro s _ t _ h
    apply Sym.ext
    exact Multiset.toFinsupp.injective h
  · intro f hf
    refine ⟨⟨f.toMultiset, ?_⟩, Finset.mem_univ _, ?_⟩
    · simpa only [Finsupp.card_toMultiset, Function.id_def] using (Finset.mem_finsuppAntidiag'.mp hf).1
    · simp
  · intro s _
    simp only [coeff_mk, Multiset.toFinsupp_apply]
    rw [Finset.prod_multiset_map_count]
    exact Finset.prod_subset (Finset.subset_univ _) (by
      intro i _ hi
      simp only [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_zero_of_notMem hi, pow_zero])

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm


set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
open PowerSeries
noncomputable section

theorem geometric_mul_linear {R : Type*} [CommRing R] (a : R) :
    (PowerSeries.mk fun k => a ^ k) * (1 - C a * X) = 1 := by
  have h := congrArg (PowerSeries.rescale a) (mk_one_mul_one_sub_eq_one R)
  simpa only [map_mul, map_sub, map_one, rescale_mk, Pi.one_apply, mul_one, rescale_X] using h

theorem hsymm_series_product {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (a : ι → R) :
    (PowerSeries.mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι R d)) *
      (∏ i, (1 - C (a i) * X)) = 1 := by
  have he : (PowerSeries.mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι R d)) =
      ∏ i, (PowerSeries.mk fun k => a i ^ k) := by
    ext d
    simpa only [coeff_mk] using eval_hsymm_coeff a d
  rw [he, ← Finset.prod_mul_distrib]
  simp only [geometric_mul_linear, Finset.prod_const_one]

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm


set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant

noncomputable section

private theorem det_path_pencil (n : ℕ) (t : ℝ) :
    (1 - t • (Matrix.of (fun i j : Fin n => if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then (1 : ℝ) else 0))).det =
      cont (fun _ => t ^ 2) 1 1 n := by
  have hp (k : ℕ) :
      1 - t • (Matrix.of (fun i j : Fin k => if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then (1 : ℝ) else 0)) =
        pathMatrix k (fun _ => -t) (fun _ => -t) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [pathMatrix, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply]
    · simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, pathMatrix, if_neg hij]
      split_ifs <;> simp_all
  rw [hp]
  induction n using Nat.twoStepInduction with
  | zero => simp [cont]
  | one => rw [Matrix.det_fin_one]; simp [pathMatrix, cont]
  | more n ih ih1 =>
    rw [path_det_recurrence, ih, ih1]
    simp only [cont]
    ring

private theorem prod_path_eigenvalues (n : ℕ) (t : ℝ) :
    ∏ i, (1 - t * (pathAdjHermitian n).eigenvalues i) = (cont (fun _ => (t ^ 2)) 1 1) n := by
  have h := det_one_add_smul_hermitian _ (pathAdjHermitian n) (-t)
  simp only [neg_smul, sub_eq_add_neg, neg_mul] at h ⊢
  rw [← h]
  simpa only [sub_eq_add_neg] using det_path_pencil n t

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm


set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
noncomputable section

theorem continuant_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) (n : ℕ) :
    f ((cont (fun _ => x) 1 1) n) = (cont (fun _ => (f x)) 1 1) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cont]
  | one => simp [cont]
  | more n ih ih1 => simp only [cont, map_sub, map_mul, ih, ih1]

theorem continuant_zero {R : Type*} [CommRing R] (n : ℕ) :
    (cont (fun _ => (0 : R)) 1 1) n = 1 := by
  induction n using Nat.twoStepInduction <;> simp_all [cont]

private theorem continuant_change_variable {R : Type*} [CommRing R]
    (x q : R) (h : x * (1 + q)^2 = q) (n : ℕ) :
    (1 + q)^n * (cont (fun _ => x) 1 1) n * (1 - q) = 1 - q^(n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cont]
  | one => simp only [cont, pow_one]; ring
  | more n ih ih1 =>
    simp only [cont]
    simp only [pow_add, pow_one, pow_succ] at ih ih1 ⊢
    linear_combination (1 + q) * ih1 - q * ih -
      ((1 + q)^n * (cont (fun _ => x) 1 1) n * (1 - q)) * h

private theorem prod_eigenvalues_polynomial (n : ℕ) :
    (∏ i, (1 - Polynomial.C ((D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.pathAdjHermitian n).eigenvalues i) *
      Polynomial.X)) = (cont (fun _ => (Polynomial.X ^ 2 : Polynomial ℝ)) 1 1) n := by
  apply Polynomial.funext
  intro t
  have h := continuant_map (Polynomial.evalRingHom t) (Polynomial.X ^ 2) n
  change Polynomial.eval t ((cont (fun _ => (Polynomial.X ^ 2 : Polynomial ℝ)) 1 1) n) =
    (cont (fun _ => (Polynomial.eval t (Polynomial.X ^ 2 : Polynomial ℝ))) 1 1) n at h
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_comm] using
    prod_path_eigenvalues n t

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm


set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
open PowerSeries P13CatalanLagrangeBridge
noncomputable section


private def model (n : ℕ) : (PowerSeries ℚ) := (1 - X) * (1 + X)^n * (1 - X^(n+1))⁻¹

private theorem continuant_constantCoeff (n : ℕ) :
    constantCoeff ((cont (fun _ => (X : (PowerSeries ℚ))) 1 1) n) = 1 := by
  rw [continuant_map]
  simp only [constantCoeff_X]
  exact continuant_zero n

private theorem model_subst_inverse (n : ℕ) :
    ((cont (fun _ => (X : (PowerSeries ℚ))) 1 1) n)⁻¹ = (model n).subst q := by
  have hs : HasSubst q := HasSubst.of_constantCoeff_zero' q_constantCoeff
  have hone : subst q (1 : (PowerSeries ℚ)) = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have hq : (X : (PowerSeries ℚ)) * (1 + q)^2 = q := q_equation.symm
  have hc := continuant_change_variable (X : (PowerSeries ℚ)) q hq n
  have hz : constantCoeff (1 - q^(n+1) : (PowerSeries ℚ)) ≠ 0 := by simp [q_constantCoeff]
  have hmodel : (model n).subst q =
      (1 - q) * (1 + q)^n * (1 - q^(n+1))⁻¹ := by
    have hinv : ((1 - X^(n+1) : (PowerSeries ℚ))⁻¹).subst q = (1 - q^(n+1))⁻¹ := by
      apply (eq_inv_iff_mul_eq_one hz).2
      have he := congrArg (substAlgHom hs)
        (PowerSeries.inv_mul_cancel (1 - X^(n+1) : (PowerSeries ℚ)) (by simp))
      have he' : subst q ((1 - X^(n+1) : (PowerSeries ℚ))⁻¹ * (1 - X^(n+1))) = subst q (1 : (PowerSeries ℚ)) := by
        simpa only [coe_substAlgHom] using he
      simpa only [subst_mul hs, subst_sub hs, subst_pow hs, subst_X hs, hone] using he'
    simp only [model, subst_mul hs, subst_sub hs, subst_add hs, subst_pow hs,
      subst_X hs, hinv, hone]
  rw [hmodel]
  apply (inv_eq_iff_mul_eq_one (by rw [continuant_constantCoeff]; norm_num)).2
  calc
    ((1 - q) * (1 + q)^n * (1 - q^(n+1))⁻¹) * (cont (fun _ => (X : (PowerSeries ℚ))) 1 1) n =
        ((1 + q)^n * (cont (fun _ => (X : (PowerSeries ℚ))) 1 1) n * (1 - q)) * (1 - q^(n+1))⁻¹ := by ring
    _ = 1 := by rw [hc, PowerSeries.mul_inv_cancel _ hz]

private theorem reciprocal_coefficient_model (n m : ℕ) (hm : 1 ≤ m) :
    coeff m (((cont (fun _ => (X : (PowerSeries ℚ))) 1 1) n)⁻¹) =
      coeff m ((1 - X)^2 * (1 + X)^(2*m+n-1) * (1 - X^(n+1))⁻¹ : (PowerSeries ℚ)) := by
  rw [model_subst_inverse]
  rw [q_subst_coefficient_transform (model n) m hm]
  congr 1
  unfold model
  have he : (2*m-1)+n = 2*m+n-1 := by omega
  rw [show ((1-X)*(1+X)^(2*m-1)*((1-X)*(1+X)^n*(1-X^(n+1))⁻¹) : (PowerSeries ℚ)) =
    (1-X)^2 * ((1+X)^(2*m-1)*(1+X)^n) * (1-X^(n+1))⁻¹ by ring]
  rw [← pow_add, he]

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm


set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
open PowerSeries
noncomputable section

private theorem coeff_inverse_one_sub_X_pow (N : ℕ) (hN : 0 < N) (d : ℕ) :
    coeff d ((1 - X^N : (PowerSeries ℚ))⁻¹) = if N ∣ d then 1 else 0 := by
  have hs : HasSubst (X^N : (PowerSeries ℚ)) := .X_pow (by omega)
  have he : ((PowerSeries.mk 1 : (PowerSeries ℚ)).subst (X^N)) = (1 - X^N : (PowerSeries ℚ))⁻¹ := by
    apply (eq_inv_iff_mul_eq_one (by simp [Nat.ne_of_gt hN])).2
    have h := congrArg (substAlgHom hs) (mk_one_mul_one_sub_eq_one ℚ)
    have hone : subst (X^N : (PowerSeries ℚ)) (1 : (PowerSeries ℚ)) = 1 := by
      rw [← coe_substAlgHom hs, map_one]
    have h' : subst (X^N : (PowerSeries ℚ)) ((PowerSeries.mk 1 : (PowerSeries ℚ)) * (1-X)) = subst (X^N : (PowerSeries ℚ)) (1 : (PowerSeries ℚ)) := by
      simpa only [coe_substAlgHom] using h
    simpa only [subst_mul hs, subst_sub hs, subst_X hs, hone] using h'
  rw [← he, coeff_subst_X_pow (by omega)]
  simp

private theorem coeff_mul_inverse_one_sub_X_pow (A : (PowerSeries ℚ)) (N : ℕ) (hN : 0 < N) (m : ℕ) :
    coeff m (A * (1-X^N)⁻¹) =
      ∑ k ∈ Finset.range (m/N+1), coeff (m-k*N) A := by
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_inverse_one_sub_X_pow N hN]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun k _ => k*N) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hN).1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))),
      dvd_mul_left N k⟩
  · intro k _ l _ h
    exact Nat.eq_of_mul_eq_mul_right hN h
  · intro i hi
    obtain ⟨hr, hd⟩ := Finset.mem_filter.mp hi
    refine ⟨i/N, Finset.mem_range.mpr ?_, Nat.div_mul_cancel hd⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)))
  · intro k _
    rfl

private theorem second_difference (L j : ℕ) :
    coeff j ((1-X)^2 * (1+X)^L : (PowerSeries ℚ)) =
      (D5.S0.Conventions.IntegerIndexBinomial.binom L (j : ℤ) : ℚ) - 2*(D5.S0.Conventions.IntegerIndexBinomial.binom L ((j : ℤ)-1) : ℚ) +
        (D5.S0.Conventions.IntegerIndexBinomial.binom L ((j : ℤ)-2) : ℚ) := by
  have he : ((1-X)^2 * (1+X)^L : (PowerSeries ℚ)) =
      (1+X)^L - 2*(X*(1+X)^L) + X*(X*(1+X)^L) := by ring
  rw [he]
  cases j with
  | zero => simp [D5.S0.Conventions.IntegerIndexBinomial.binom]
  | succ j =>
    cases j with
    | zero =>
      simp only [map_add, map_sub, coeff_ofNat_mul, coeff_succ_X_mul,
        coeff_zero_eq_constantCoeff, map_pow, map_add, constantCoeff_one,
        constantCoeff_X, add_zero, one_pow, map_mul, mul_zero, sub_zero]
      norm_num [D5.S0.Conventions.IntegerIndexBinomial.binom, P13CatalanLagrangeBridge.binomialCoefficient]
    | succ j =>
      simp only [map_add, map_sub, coeff_ofNat_mul, coeff_succ_X_mul,
        P13CatalanLagrangeBridge.binomialCoefficient]
      have h1 : (↑(j+1+1) : ℤ) - 1 = (j+1 : ℕ) := by omega
      have h2 : (↑(j+1+1) : ℤ) - 2 = (j : ℤ) := by omega
      rw [h1, h2]
      have hb (r : ℕ) : (D5.S0.Conventions.IntegerIndexBinomial.binom L (r : ℤ) : ℚ) =
          (Nat.choose L r : ℚ) := by
        simp only [D5.S0.Conventions.IntegerIndexBinomial.binom,
          if_neg (not_lt.mpr (Int.natCast_nonneg r)), Int.toNat_natCast, Int.cast_natCast]
      rw [hb, hb, hb]

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm


set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
open PowerSeries
noncomputable section

theorem path_hsymm_series (n : ℕ) :
    (PowerSeries.mk fun d => chs n d) * (cont (fun _ => (X^2 : PowerSeries ℝ)) 1 1) n = 1 := by
  have h := hsymm_series_product (pathAdjHermitian n).eigenvalues
  have hp : (∏ i, (1 - C ((pathAdjHermitian n).eigenvalues i)*X)) =
      (cont (fun _ => (X^2 : PowerSeries ℝ)) 1 1) n := by
    let f : Polynomial ℝ →+* PowerSeries ℝ := Polynomial.coeToPowerSeries.ringHom
    have h := congrArg f (prod_eigenvalues_polynomial n)
    rw [continuant_map] at h
    simpa [f] using h
  simpa only [hp, chs] using h

private theorem chs_even_coeff (n m : ℕ) :
    chs n (2*m) = ((coeff m (((cont (fun _ => (X : PowerSeries ℚ)) 1 1) n)⁻¹) : ℚ) : ℝ) := by
  let f : PowerSeries ℚ →+* PowerSeries ℝ :=
    (PowerSeries.expand 2 (by decide)).toRingHom.comp (PowerSeries.map (Rat.castHom ℝ))
  have hx : f X = (X^2 : PowerSeries ℝ) := by simp [f]
  have hz : constantCoeff ((cont (fun _ => (X : PowerSeries ℚ)) 1 1) n) ≠ 0 := by
    rw [continuant_map]
    simp only [constantCoeff_X, continuant_zero]
    norm_num
  have hi := congrArg f (PowerSeries.inv_mul_cancel ((cont (fun _ => (X : PowerSeries ℚ)) 1 1) n) hz)
  rw [map_mul, map_one, continuant_map, hx] at hi
  have he := path_hsymm_series n
  have hH : (PowerSeries.mk fun d => chs n d) = f (((cont (fun _ => (X : PowerSeries ℚ)) 1 1) n)⁻¹) := by
    calc
      (PowerSeries.mk fun d => chs n d) =
          (PowerSeries.mk fun d => chs n d) *
            (f (((cont (fun _ => (X : PowerSeries ℚ)) 1 1) n)⁻¹) * (cont (fun _ => (X^2 : PowerSeries ℝ)) 1 1) n) := by rw [hi, mul_one]
      _ = f (((cont (fun _ => (X : PowerSeries ℚ)) 1 1) n)⁻¹) *
          ((PowerSeries.mk fun d => chs n d) * (cont (fun _ => (X^2 : PowerSeries ℝ)) 1 1) n) := by ring
      _ = f (((cont (fun _ => (X : PowerSeries ℚ)) 1 1) n)⁻¹) := by rw [he, mul_one]
  have hc := congrArg (coeff (2*m)) hH
  simpa [f, PowerSeries.coeff_expand_mul, PowerSeries.coeff_map] using hc

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm


set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
open PowerSeries
noncomputable section

private theorem reciprocal_closed_coefficient (n m : ℕ) (hm : 1 ≤ m) :
    coeff m (((cont (fun _ => (X : PowerSeries ℚ)) 1 1) n)⁻¹) = (pathFormula n m : ℚ) := by
  rw [reciprocal_coefficient_model n m hm,
    coeff_mul_inverse_one_sub_X_pow _ (n+1) (by omega)]
  unfold pathFormula
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [second_difference]
  have hkm : k*(n+1) ≤ m :=
    (Nat.le_div_iff_mul_le (by omega : 0 < n+1)).1
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  simp only [Nat.cast_sub hkm, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

theorem chs_formula (n m : ℕ) : chs n (2*m) = (pathFormula n m : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simp [chs, pathFormula, D5.S0.Conventions.IntegerIndexBinomial.binom]
  · rw [chs_even_coeff, reciprocal_closed_coefficient n m (by omega)]
    norm_cast

theorem result : D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.claim := by
  intro n m hn hm
  have h := chs_formula n m
  exact ⟨h, by simpa only [chsNorm, h]⟩

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

theorem chebS_degree {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    (Polynomial.Chebyshev.S K (n : ℤ)).natDegree = n := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  rw [Polynomial.Chebyshev.S_eq_U_comp_half_mul_X, Polynomial.natDegree_comp]
  simp [Polynomial.Chebyshev.natDegree_U_natCast,
    invOf_eq_inv, show (2 : K) ≠ 0 by norm_num]

end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
