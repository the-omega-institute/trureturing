/- GID: D5/S3/Quantum/Walks/Riesz/Moments
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/Riesz/Moments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Riesz moment and CMV identities for scale-four self-similarity. -/

/- admission_basis: escape-witness
   Module witness: product_independent
   Direct frozen dependencies: none.
   product_independent: proof_shape: content; escape_witness: Riesz.Moments.coeff_stable
     Direct frozen dependencies: none; consumers: Riesz.Moments.moment_at.
   moment_at: proof_shape: content; escape_witness: Riesz.Moments.coeff_stable
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeLeadingTerms.moment_zero, CMV.Representation.CMVFromGramParameters.normalizedPhi_zero, Riesz.Moments.moment_decimation, Riesz.Moments.moment_closed_form, Riesz.Moments.RieszPositive.functional_stabilized.
   moment_neg: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeLeadingTerms.denominator_coefficient, CMV.SzegoRecurrence.GramBasis.sigma_symm, CMV.SzegoRecurrence.FormSymmetries.sigma_invert.
   moment_closed_form: proof_shape: content; escape_witness: Riesz.Moments.coeff_outside
     Direct frozen dependencies: none; consumers: CMV.SzegoRecurrence.GramBasis.chi_zero.
   Forms.momentForm_T_T: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PolynomialSeries.moment_coefficients, CMV.Representation.CMVFromGramParameters.normalizedPhi_zero, CMV.SzegoRecurrence.GramBasis.sigma_symm, CMV.SzegoRecurrence.GramBasis.chi_zero, CMV.SzegoRecurrence.FormSymmetries.sigma_shift, CMV.SzegoRecurrence.FormSymmetries.sigma_invert, Riesz.Moments.Forms.riesz_residue_orthogonality, Riesz.Moments.Forms.tau_monomial_density, Riesz.Moments.Forms.decimation_isometry, Riesz.Moments.RieszPositive.form_as_functional.
   Forms.J_T: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: Riesz.Decimation.Assembly.J_into_residue, Riesz.Decimation.Assembly.J_W_into_V, Riesz.Decimation.Assembly.large_projection, Riesz.Moments.Forms.decimation_isometry.
   Forms.riesz_residue_orthogonality: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: Riesz.Decimation.Assembly.large_projection, Riesz.Moments.Forms.riesz_parity_orthogonality.
   Forms.riesz_parity_orthogonality: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: Riesz.Decimation.Assembly.small_projection, Riesz.Decimation.Assembly.projection_scale_four.
   Forms.tau_density: proof_shape: content; escape_witness: Riesz.Moments.finite_decimation
     Direct frozen dependencies: none; consumers: Riesz.Decimation.Assembly.projection_scale_four.
   Forms.decimation_isometry: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: Riesz.Decimation.Assembly.large_projection, Riesz.Decimation.Assembly.projection_scale_four.
   RieszPositive.riesz_positive_definite: proof_shape: content; escape_witness: Riesz.Moments.coeff_stable
     Direct frozen dependencies: none; consumers: CMV.SzegoRecurrence.OPUCRecurrence.zero_of_window_orthogonal, CMV.SzegoRecurrence.OPUCNormalization.normSquare_pos, CMV.SzegoRecurrence.GramOPUC.gram_characterization, Riesz.Decimation.FiniteScaling.scaled_projections_exist, Riesz.Decimation.FiniteScaling.projection_norm_scale_four.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15854
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module

namespace D5.S3.Quantum.Walks.Riesz.Moments
open scoped BigOperators
open LaurentPolynomial
open LaurentPolynomial
noncomputable section

def rieszProduct (K : ℕ) : LaurentPolynomial ℚ :=
  ∏ k ∈ Finset.range K, (1 + (1/2 : ℚ) • T ((4 : ℤ)^(k+1)) + (1/2 : ℚ) • T (-((4 : ℤ)^(k+1))))

def coeffRec : ℕ → ℤ → ℚ
  | 0,j => if j=0 then 1 else 0
  | K+1,j => coeffRec K j + (coeffRec K (j-(4:ℤ)^(K+1)) + coeffRec K (j+(4:ℤ)^(K+1)))/2

private def radius : ℕ → ℤ
  | 0 => 0
  | K+1 => radius K + (4:ℤ)^(K+1)

private theorem product_zero : rieszProduct 0 = 1 := by simp [rieszProduct]

private theorem product_succ (K : ℕ) :
    rieszProduct (K+1) = rieszProduct K *
      (1 + (1/2 : ℚ) • T ((4 : ℤ)^(K+1)) + (1/2 : ℚ) • T (-((4 : ℤ)^(K+1)))) := by
  simp [rieszProduct, Finset.prod_range_succ]

private theorem coeff_T_mul (p : LaurentPolynomial ℚ) (e j : ℤ) :
    (p * T e).coeff j = p.coeff (j-e) := by
  change (p * AddMonoidAlgebra.single e (1:ℚ)).coeff j = p.coeff (j-e)
  rw [AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [mul_one, sub_eq_add_neg]

private theorem coeff_product (K : ℕ) (j : ℤ) :
    (rieszProduct K).coeff j = coeffRec K j := by
  induction K generalizing j with
  | zero =>
    rw [product_zero]
    change (Finsupp.single 0 (1:ℚ)) j = if j=0 then 1 else 0
    simp only [Finsupp.single_apply, eq_comm]
  | succ K ih =>
    rw [product_succ, mul_add, mul_add, mul_one]
    simp [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_smul,
      coeff_T_mul, ih, coeffRec]
    ring

private theorem radius_nonneg (K : ℕ) : 0 ≤ radius K := by
  induction K with
  | zero => simp [radius]
  | succ K ih => simp only [radius]; positivity

private theorem radius_bound (K : ℕ) : radius K < 2 * (4:ℤ)^K := by
  induction K with
  | zero => norm_num [radius]
  | succ K ih =>
    simp only [radius, pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℤ)<4) K]

private theorem coeff_outside (K : ℕ) (j : ℤ) (h : j < -radius K ∨ radius K < j) :
    coeffRec K j = 0 := by
  induction K generalizing j with
  | zero => simp only [radius] at h; simp [coeffRec, show j ≠ 0 by omega]
  | succ K ih =>
    have hp : 0 < (4:ℤ)^(K+1) := pow_pos (by norm_num) _
    have h0 : j < -radius K ∨ radius K < j := by simp only [radius] at h; omega
    have hm : j-(4:ℤ)^(K+1) < -radius K ∨ radius K < j-(4:ℤ)^(K+1) := by
      simp only [radius] at h; omega
    have hplus : j+(4:ℤ)^(K+1) < -radius K ∨ radius K < j+(4:ℤ)^(K+1) := by
      simp only [radius] at h; omega
    simp [coeffRec, ih _ h0, ih _ hm, ih _ hplus]

private theorem coeff_stable_succ (K : ℕ) (j : ℤ) (hlo : -(4:ℤ)^K < j) (hhi : j < (4:ℤ)^K) :
    coeffRec (K+1) j = coeffRec K j := by
  have hb := radius_bound K
  have hm : j-(4:ℤ)^(K+1) < -radius K := by rw [pow_succ]; omega
  have hp : radius K < j+(4:ℤ)^(K+1) := by rw [pow_succ]; omega
  simp [coeffRec, coeff_outside K _ (Or.inl hm), coeff_outside K _ (Or.inr hp)]

private theorem coeff_stable (K L : ℕ) (j : ℤ) (hKL : K ≤ L)
    (hlo : -(4:ℤ)^K < j) (hhi : j < (4:ℤ)^K) : coeffRec L j = coeffRec K j := by
  induction L, hKL using Nat.le_induction with
  | base => rfl
  | succ L hKL ih =>
    rw [coeff_stable_succ, ih]
    · have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤4) hKL
      omega
    · exact hhi.trans_le (pow_le_pow_right₀ (by norm_num : (1:ℤ)≤4) hKL)

def rieszMoment (j : ℤ) : ℚ := (rieszProduct (Nat.log 4 j.natAbs+1)).coeff j


private theorem abs_bounds (j : ℤ) (K : ℕ) (h : j.natAbs < 4^K) :
    -(4:ℤ)^K < j ∧ j < (4:ℤ)^K := by
  have hi : (j.natAbs : ℤ) < (4:ℤ)^K := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hi
  exact abs_lt.mp hi

theorem product_independent (j : ℤ) (K L : ℕ)
    (hK : j.natAbs < 4^K) (hL : j.natAbs < 4^L) :
    (rieszProduct K).coeff j = (rieszProduct L).coeff j := by
  rw [coeff_product, coeff_product]
  rcases le_total K L with hKL | hLK
  · exact (coeff_stable K L j hKL (abs_bounds j K hK).1 (abs_bounds j K hK).2).symm
  · exact coeff_stable L K j hLK (abs_bounds j L hL).1 (abs_bounds j L hL).2

theorem moment_at (j : ℤ) (K : ℕ) (h : j.natAbs < 4^K) :
    rieszMoment j = coeffRec K j := by
  rw [rieszMoment, product_independent j (Nat.log 4 j.natAbs + 1) K
    (Nat.lt_pow_succ_log_self (by decide) _) h, coeff_product]

private theorem coeff_mod4_zero (K : ℕ) (j : ℤ) (hj : j % 4 ≠ 0) : coeffRec K j = 0 := by
  induction K generalizing j with
  | zero => simp [coeffRec, show j ≠ 0 by omega]
  | succ K ih =>
    have hp : (4:ℤ)^(K+1) % 4 = 0 := by simp [pow_succ]
    have hm : (j-(4:ℤ)^(K+1)) % 4 ≠ 0 := by omega
    have hplus : (j+(4:ℤ)^(K+1)) % 4 ≠ 0 := by omega
    simp [coeffRec, ih j hj, ih _ hm, ih _ hplus]

private theorem moment_mod4_zero (j : ℤ) (hj : j % 4 ≠ 0) : rieszMoment j = 0 := by
  rw [rieszMoment, coeff_product]
  exact coeff_mod4_zero _ _ hj

private theorem coeff_neg (K : ℕ) (j : ℤ) : coeffRec K (-j) = coeffRec K j := by
  induction K generalizing j with
  | zero => simp [coeffRec]
  | succ K ih =>
    have hm : -j-(4:ℤ)^(K+1) = -(j+(4:ℤ)^(K+1)) := by ring
    have hp : -j+(4:ℤ)^(K+1) = -(j-(4:ℤ)^(K+1)) := by ring
    simp only [coeffRec, hm, hp, ih]
    ring

theorem moment_neg (j : ℤ) : rieszMoment (-j) = rieszMoment j := by
  simp only [rieszMoment, Int.natAbs_neg, coeff_product, coeff_neg]

private theorem finite_decimation (K : ℕ) (j : ℤ) :
    coeffRec (K+1) (4*j) = coeffRec K j + (coeffRec K (j-1)+coeffRec K (j+1))/2 := by
  induction K generalizing j with
  | zero =>
    simp only [coeffRec]
    norm_num only [Nat.zero_add, pow_one]
    have h0 : (4*j=0) ↔ j=0 := by omega
    have hm : (4*j-4=0) ↔ j-1=0 := by omega
    have hp : (4*j+4=0) ↔ j+1=0 := by omega
    simp only [h0, hm, hp]
  | succ K ih =>
    have hm : 4*j-(4:ℤ)^(K+1+1) = 4*(j-(4:ℤ)^(K+1)) := by rw [pow_succ]; ring
    have hp : 4*j+(4:ℤ)^(K+1+1) = 4*(j+(4:ℤ)^(K+1)) := by rw [pow_succ]; ring
    rw [coeffRec, hm, hp, ih, ih, ih]
    simp only [coeffRec]
    have h1 : j-(4:ℤ)^(K+1)-1 = j-1-(4:ℤ)^(K+1) := by ring
    have h2 : j+(4:ℤ)^(K+1)-1 = j-1+(4:ℤ)^(K+1) := by ring
    have h3 : j-(4:ℤ)^(K+1)+1 = j+1-(4:ℤ)^(K+1) := by ring
    have h4 : j+(4:ℤ)^(K+1)+1 = j+1+(4:ℤ)^(K+1) := by ring
    rw [h1, h2, h3, h4]
    ring


private theorem moment_decimation (j : ℤ) :
    rieszMoment (4*j) = rieszMoment j + (rieszMoment (j-1)+rieszMoment (j+1))/2 := by
  let K := max (max (4*j).natAbs j.natAbs) (max (j-1).natAbs (j+1).natAbs) + 1
  have h0 : (4*j).natAbs < K := by dsimp [K]; omega
  have h1 : j.natAbs < K := by dsimp [K]; omega
  have h2 : (j-1).natAbs < K := by dsimp [K]; omega
  have h3 : (j+1).natAbs < K := by dsimp [K]; omega
  have hexp : K < 4^K := Nat.lt_pow_self (by decide : 1 < 4)
  have hexp' : K < 4^(K+1) := hexp.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ K))
  rw [moment_at (4*j) (K+1) (h0.trans hexp'), moment_at j K (h1.trans hexp),
    moment_at (j-1) K (h2.trans hexp), moment_at (j+1) K (h3.trans hexp)]
  exact finite_decimation K j


/-- Signed sums of distinct (fun n : ℕ => (T (n:ℤ) : LaurentPolynomial ℝ)) 4^k, with k >= 1. The final index counts
how many signs are nonzero. -/
inductive SignedRep : ℕ → ℤ → ℕ → Prop
  | base : SignedRep 0 0 0
  | skip {K j p} : SignedRep K j p → SignedRep (K+1) j p
  | plus {K j p} : SignedRep K j p → SignedRep (K+1) (j+(4:ℤ)^(K+1)) (p+1)
  | minus {K j p} : SignedRep K j p → SignedRep (K+1) (j-(4:ℤ)^(K+1)) (p+1)

private theorem signed_bound {K : ℕ} {j : ℤ} {p : ℕ} (h : SignedRep K j p) :
    -radius K ≤ j ∧ j ≤ radius K := by
  induction h with
  | base => simp [radius]
  | @skip K j p h ih =>
    have hp : 0 < (4:ℤ)^(K+1) := pow_pos (by norm_num) _
    simp only [radius]; omega
  | @plus K j p h ih =>
    have hp : 0 < (4:ℤ)^(K+1) := pow_pos (by norm_num) _
    simp only [radius]; omega
  | @minus K j p h ih =>
    have hp : 0 < (4:ℤ)^(K+1) := pow_pos (by norm_num) _
    simp only [radius]; omega

private theorem twice_radius_lt (K : ℕ) : 2*radius K < (4:ℤ)^(K+1) := by
  have hb := radius_bound K
  rw [pow_succ]
  omega

private theorem signed_coeff {K : ℕ} {j : ℤ} {p : ℕ} (h : SignedRep K j p) :
    coeffRec K j = (1/2 : ℚ)^p := by
  induction h with
  | base => norm_num [coeffRec]
  | @skip K j p h ih =>
    have hb := signed_bound h
    have hr := twice_radius_lt K
    have hm : j-(4:ℤ)^(K+1) < -radius K := by omega
    have hp : radius K < j+(4:ℤ)^(K+1) := by omega
    simp [coeffRec, ih, coeff_outside K _ (Or.inl hm), coeff_outside K _ (Or.inr hp)]
  | @plus K j p h ih =>
    have hb := signed_bound h
    have hr := twice_radius_lt K
    have h0 : radius K < j+(4:ℤ)^(K+1) := by omega
    have hp : radius K < j+(4:ℤ)^(K+1)+(4:ℤ)^(K+1) := by
      have hnon := radius_nonneg K; omega
    simp only [coeffRec, add_sub_cancel_right]
    rw [coeff_outside K _ (Or.inr h0), ih, coeff_outside K _ (Or.inr hp)]
    rw [pow_succ]; ring
  | @minus K j p h ih =>
    have hb := signed_bound h
    have hr := twice_radius_lt K
    have h0 : j-(4:ℤ)^(K+1) < -radius K := by omega
    have hm : j-(4:ℤ)^(K+1)-(4:ℤ)^(K+1) < -radius K := by
      have hnon := radius_nonneg K; omega
    simp only [coeffRec, sub_add_cancel]
    rw [coeff_outside K _ (Or.inl h0), coeff_outside K _ (Or.inl hm), ih]
    rw [pow_succ]; ring

theorem moment_closed_form {K : ℕ} {j : ℤ} {p : ℕ} (h : SignedRep K j p) :
    rieszMoment j = (1/2 : ℚ)^p := by
  have hb := signed_bound h
  have hr := twice_radius_lt K
  have hnon := radius_nonneg K
  have habs : j.natAbs < 4^(K+1) := by
    have hz : |j| < (4:ℤ)^(K+1) := abs_lt.mpr (by omega)
    rw [← Int.natCast_natAbs] at hz
    exact_mod_cast hz
  rw [moment_at j (K+1) habs]
  have hm : j-(4:ℤ)^(K+1) < -radius K := by omega
  have hp : radius K < j+(4:ℤ)^(K+1) := by omega
  simp [coeffRec, coeff_outside K _ (Or.inl hm), coeff_outside K _ (Or.inr hp), signed_coeff h]

end
end D5.S3.Quantum.Walks.Riesz.Moments

noncomputable section
namespace D5.S3.Quantum.Walks.Riesz.Moments.Forms
open D5.S3.Quantum.Walks.Riesz.Moments
open LaurentPolynomial

/-- The Toeplitz moment form, expressed by two finite coefficient sums. -/
def momentForm (m : ℤ → ℝ) : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ) :=
  (Finsupp.linearCombination ℝ (fun i : ℤ =>
    (Finsupp.linearCombination ℝ (fun j : ℤ => m (j-i))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap)).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem momentForm_T_T (m : ℤ → ℝ) (i j : ℤ) :
    momentForm m (T i) (T j) = m (j-i) := by
  simp [momentForm, T, Finsupp.linearCombination_apply, -LaurentPolynomial.single_eq_C_mul_T]

def sigma : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ) := momentForm (fun j => (D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment j : ℝ))
def tau : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ) := momentForm (fun j => (D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment (4*j) : ℝ))

def J : (LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) := AddMonoidAlgebra.mapDomainLinearMap ℝ ℝ (fun e => 4*e)

@[simp] theorem J_T (i : ℤ) : J (T i) = T (4*i) := by
  simp [J, T, -LaurentPolynomial.single_eq_C_mul_T]

/-- Sigma is invariant under the fourth roots of unity at the moment level. -/
theorem riesz_residue_orthogonality (i j : ℤ) (h : i % 4 ≠ j % 4) :
    sigma (T i) (T j) = 0 := by
  simp only [sigma, momentForm_T_T]
  rw [D5.S3.Quantum.Walks.Riesz.Moments.moment_mod4_zero (j-i) (by omega)]
  norm_num

/-- In particular, the odd and even Laurent subspaces are orthogonal. -/
theorem riesz_parity_orthogonality (i j : ℤ) (h : i % 2 ≠ j % 2) :
    sigma (T i) (T j) = 0 := by
  apply riesz_residue_orthogonality
  omega

/-- The weighted functional identity on every monomial pair. -/
private theorem tau_monomial_density (i j : ℤ) :
    tau (T i) (T j) = sigma (T i) (T j) +
      (sigma (T (i-1)) (T j) + sigma (T (i+1)) (T j))/2 := by
  simp only [sigma, tau, momentForm_T_T]
  rw [D5.S3.Quantum.Walks.Riesz.Moments.moment_decimation]
  push_cast
  have h1 : j-(i-1) = (j-i)+1 := by ring
  have h2 : j-(i+1) = (j-i)-1 := by ring
  rw [h1, h2]
  ring

/-- The exact density identity needed by the parity projection lemma. -/
theorem tau_density (i : ℤ) (q : (LaurentPolynomial ℝ)) :
    tau (T i) q = sigma (T i) q +
      (sigma (T (i-1)) q + sigma (T (i+1)) q)/2 := by
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | C_mul_T j a =>
    rw [← LaurentPolynomial.smul_eq_C_mul]
    simp only [map_smul, smul_eq_mul, tau_monomial_density]
    ring

/-- Pullback by z^4 is an isometry of the two moment forms. -/
theorem decimation_isometry (p q : (LaurentPolynomial ℝ)) : sigma (J p) (J q) = tau p q := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => simp only [map_add, LinearMap.add_apply, hp, hp']
  | C_mul_T i a =>
    rw [← LaurentPolynomial.smul_eq_C_mul]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    induction q using LaurentPolynomial.induction_on' with
    | add q q' hq hq' => simp only [map_add, hq, hq']
    | C_mul_T j b =>
      rw [← LaurentPolynomial.smul_eq_C_mul]
      simp only [map_smul, smul_eq_mul]
      congr 1
      simp only [J_T, sigma, tau, momentForm_T_T]
      congr 2
      ring

end D5.S3.Quantum.Walks.Riesz.Moments.Forms
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.Riesz.Moments.Positivity
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms
open LaurentPolynomial

/-- The normalized finite Riesz density. -/
private def density (K : ℕ) : (LaurentPolynomial ℝ) :=
  AddMonoidAlgebra.mapRingHom ℤ (Rat.castHom ℝ) (rieszProduct K)

/-- The analytic polynomial whose squared modulus is the finite density. -/
private def analyticFactor (K : ℕ) : (LaurentPolynomial ℝ) :=
  ∏ k ∈ Finset.range K, (1 + T ((4:ℤ)^(k+1)))

private theorem single_density (p : ℤ) :
    (1 + (1/2:ℝ) • T p + (1/2:ℝ) • T (-p) : (LaurentPolynomial ℝ)) =
    (1/2:ℝ) • (invert (1+T p) * (1+T p)) := by
  rw [map_add,map_one,invert_T]
  have ht : (T (-p) : (LaurentPolynomial ℝ)) * T p = 1 := by rw [← T_add,neg_add_cancel,T_zero]
  simp only [mul_add,add_mul,one_mul,mul_one,ht,smul_add]
  module

private theorem density_factorization (K : ℕ) :
    density K = (1/2 : ℝ)^K • (invert (analyticFactor K) * analyticFactor K) := by
  induction K with
  | zero => simp [density,rieszProduct,analyticFactor]
  | succ K ih =>
    have hd : density (K+1) = density K *
        (1 + (1/2:ℝ) • T ((4:ℤ)^(K+1)) + (1/2:ℝ) • T (-((4:ℤ)^(K+1)))) := by
      have hc (a : ℚ) : AddMonoidAlgebra.mapRingHom ℤ (Rat.castHom ℝ) (C a) = C (a : ℝ) := by
        change AddMonoidAlgebra.mapRingHom ℤ (Rat.castHom ℝ) (AddMonoidAlgebra.single 0 a) = _
        rw [AddMonoidAlgebra.mapRingHom_single]
        rfl
      have ht (e : ℤ) : AddMonoidAlgebra.mapRingHom ℤ (Rat.castHom ℝ) (T e) = T e := by
        change AddMonoidAlgebra.mapRingHom ℤ (Rat.castHom ℝ) (AddMonoidAlgebra.single e 1) = _
        rw [AddMonoidAlgebra.mapRingHom_single,map_one]
        rfl
      simp only [density,rieszProduct,Finset.prod_range_succ,map_mul,map_add,map_one,
        smul_eq_C_mul,hc,ht]
      norm_num
    rw [hd]
    rw [single_density,ih]
    have ha : analyticFactor (K+1) = analyticFactor K * (1+T ((4:ℤ)^(K+1))) := by
      simp [analyticFactor,Finset.prod_range_succ]
    rw [ha,map_mul,pow_succ (1/2:ℝ)]
    simp only [smul_eq_C_mul]
    rw [map_mul]
    ring

/-- Parseval for finite Laurent polynomials, requiring no analysis. -/
private theorem constant_square (q : (LaurentPolynomial ℝ)) :
    (invert q * q).coeff 0 = ∑ e ∈ q.coeff.support, (q.coeff e)^2 := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  change (∑ i ∈ (invert q).coeff.support, ∑ j ∈ q.coeff.support,
    if i+j=0 then (invert q).coeff i*q.coeff j else 0) = _
  have hinv : (invert q).coeff.support = q.coeff.support.image (fun e => -e) := by
    ext e
    simp only [Finsupp.mem_support_iff, invert_apply, Finset.mem_image]
    constructor
    · intro h; exact ⟨-e,h,by simp⟩
    · rintro ⟨j,hj,rfl⟩; simpa using hj
  rw [hinv,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp [invert_apply,pow_two]
    · intro j hj hji
      have hne : -i+j ≠ 0 := by omega
      simp [hne]
    · exact fun hnot => (hnot hi).elim
  · intro i hi j hj hij
    exact neg_injective hij

private theorem constant_square_pos (q : (LaurentPolynomial ℝ)) (hq : q ≠ 0) : 0 < (invert q*q).coeff 0 := by
  classical
  rw [constant_square]
  have hsupport : q.coeff.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro hz; apply hq; exact AddMonoidAlgebra.coeff_injective hz
  obtain ⟨e,he⟩ := hsupport
  apply Finset.sum_pos' (fun i hi => sq_nonneg _) ⟨e,he,?_⟩
  exact sq_pos_of_ne_zero (Finsupp.mem_support_iff.mp he)

/-- Every finite Riesz density gives a strictly positive Laurent Gram form. -/
private theorem finite_riesz_pos (K : ℕ) (q : (LaurentPolynomial ℝ)) (hq : q ≠ 0) :
    0 < (invert q*q*density K).coeff 0 := by
  have hanalytic : analyticFactor K ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hpow : (4:ℤ)^(k+1) ≠ 0 := ne_of_gt (pow_pos (by norm_num) _)
    intro hz
    have hc := congrArg (fun p : (LaurentPolynomial ℝ) => p.coeff 0) hz
    simp [T,-single_eq_C_mul_T,hpow] at hc
  have hnq : q * analyticFactor K ≠ 0 := mul_ne_zero hq hanalytic
  have heq : invert q*q*density K =
      (1/2:ℝ)^K • (invert (q*analyticFactor K)*(q*analyticFactor K)) := by
    rw [density_factorization,map_mul]
    simp only [smul_eq_C_mul]
    ring
  rw [heq,AddMonoidAlgebra.coeff_smul]
  change 0 < (1/2:ℝ)^K * (invert (q*analyticFactor K)*(q*analyticFactor K)).coeff 0
  exact mul_pos (by positivity) (constant_square_pos _ hnq)

end D5.S3.Quantum.Walks.Riesz.Moments.Positivity
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity
open LaurentPolynomial D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity

/-- A moment functional on finitely supported Laurent coefficients. -/
private def functional (m : ℤ → ℝ) : (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ m).comp (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] private theorem functional_T (m : ℤ → ℝ) (i : ℤ) : functional m (T i) = m i := by
  simp [functional,T,-single_eq_C_mul_T]

private theorem form_as_functional (m : ℤ → ℝ) (p q : (LaurentPolynomial ℝ)) :
    momentForm m p q = functional m (invert p*q) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => simp only [map_add,LinearMap.add_apply,add_mul,hp,hp']
  | C_mul_T i a =>
    rw [← smul_eq_C_mul]
    simp only [map_smul,LinearMap.smul_apply,smul_mul_assoc,smul_eq_mul]
    congr 1
    induction q using LaurentPolynomial.induction_on' with
    | add q q' hq hq' => simp only [map_add,mul_add,hq,hq']
    | C_mul_T j b =>
      rw [← smul_eq_C_mul]
      simp only [map_smul,mul_smul_comm,smul_eq_mul]
      congr 1
      rw [invert_T,←T_add]
      simp only [momentForm_T_T,functional_T]
      congr 1
      omega

private theorem density_coeff (K : ℕ) (j : ℤ) :
    (density K).coeff j = (D5.S3.Quantum.Walks.Riesz.Moments.coeffRec K j : ℝ) := by
  rw [density,AddMonoidAlgebra.coeff_mapRingHom,coeff_product]
  rfl


private theorem functional_stabilized (q : (LaurentPolynomial ℝ)) :
    ∃ K : ℕ, functional (fun j => (D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment j : ℝ)) q = (q*density K).coeff 0 := by
  classical
  let K := q.coeff.support.sup Int.natAbs + 1
  have hK (j : ℤ) (hj : j ∈ q.coeff.support) : j.natAbs < 4^K := by
    have hjbound : j.natAbs ≤ q.coeff.support.sup Int.natAbs := Finset.le_sup hj
    have hpow : K < 4^K := Nat.lt_pow_self (by decide : 1 < 4)
    exact (by dsimp [K]; omega : j.natAbs < K).trans hpow
  refine ⟨K,?_⟩
  change q.coeff.sum (fun j a => a • (D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment j : ℝ)) = _
  rw [AddMonoidAlgebra.coeff_mul]
  change (∑ j ∈ q.coeff.support, q.coeff j*(D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment j : ℝ)) =
    ∑ j ∈ q.coeff.support, ∑ i ∈ (density K).coeff.support,
      if j+i=0 then q.coeff j*(density K).coeff i else 0
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (-j)]
  · simp only [add_neg_cancel,ite_true,density_coeff]
    rw [D5.S3.Quantum.Walks.Riesz.Moments.coeff_neg,←D5.S3.Quantum.Walks.Riesz.Moments.moment_at j K (hK j hj)]
  · intro i hi hij
    have hne : j+i ≠ 0 := by omega
    simp [hne]
  · intro hnot
    have hz : (density K).coeff (-j) = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hz]

/-- The infinite Riesz moment form is strictly positive, using only stabilized
finite products and finite coefficient Parseval. -/
theorem riesz_positive_definite (q : (LaurentPolynomial ℝ)) (hq : q ≠ 0) : 0 < sigma q q := by
  rw [sigma,form_as_functional]
  obtain ⟨K,hK⟩ := functional_stabilized (invert q*q)
  rw [hK]
  exact finite_riesz_pos K q hq

end D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive
end
