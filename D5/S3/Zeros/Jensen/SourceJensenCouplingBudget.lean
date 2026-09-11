/- GID: D5/S3/Zeros/Jensen/SourceJensenCouplingBudget
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/SourceJensenCouplingBudget
   mirror-E: none(waiver:universal-coupling-identity)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: The exact source coupling sum is the fourth cumulant budget. -/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.SourceJensenCouplingBudget
open Polynomial NormalizedJensenDegreeLowering
open SourceJensenIntegralExtension SourceJensenPositiveExtension

private theorem nodal_derivative (n : ℕ) (q : ℝ[X]) (t : Fin (n+1) → ℝ)
    (ht : Function.Injective t) (hq : q.natDegree ≤ n+2) (hmonic : q.coeff (n+2) = 1)
    (hcrit : ∀ i, q.derivative.eval (t i) = 0) :
    q.derivative = C ((n+2 : ℕ) : ℝ) * Lagrange.nodal Finset.univ t := by
  have hdeg : q.natDegree = n+2 :=
    natDegree_eq_of_le_of_coeff_ne_zero hq (by rw [hmonic]; exact one_ne_zero)
  have hqmonic : q.Monic := by simpa only [Monic, leadingCoeff, hdeg] using hmonic
  have hd : ((n+2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
  have hder : q.derivative.degree = (n+1 : ℕ) := by
    rw [degree_eq_natDegree (derivative_ne_zero.mpr (by omega)), natDegree_derivative, hdeg]
    simp
  apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ ht.injOn
  · simpa using hder.le
  · rw [hder, degree_C_mul hd, Lagrange.degree_nodal]
    simp
  · rw [leadingCoeff_derivative, hqmonic, hdeg,
      Lagrange.nodal_monic.leadingCoeff_C_mul]
    simp
  · intro i _
    simp [hcrit, Lagrange.eval_nodal_at_node (Finset.mem_univ i)]

private theorem residue_sum (n : ℕ) (q : ℝ[X]) (t : Fin (n+1) → ℝ) (a₁ a₂ : ℝ)
    (ht : Function.Injective t) (hq : q.natDegree ≤ n+2)
    (h₀ : q.coeff (n+2) = 1) (h₁ : q.coeff (n+1) = -a₁)
    (h₂ : q.coeff n = ((n+1 : ℕ) : ℝ) / ((n+2 : ℕ) : ℝ) * a₂)
    (hcrit : ∀ i, q.derivative.eval (t i) = 0) :
    (∑ i, -((n+2 : ℕ) : ℝ) * q.eval (t i) / q.derivative.derivative.eval (t i)) =
      ((n+1 : ℕ) : ℝ) / ((n+2 : ℕ) : ℝ)^2 * (a₁^2 - 2*a₂) := by
  let d : ℝ := ((n+2 : ℕ) : ℝ)
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (show n+2 ≠ 0 by omega)
  have hdc : (n : ℝ) + 2 ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
  let R := q - C d⁻¹ * X * q.derivative + C (a₁ / d^2) * q.derivative
  have hc (k : ℕ) : R.coeff k = q.coeff k - d⁻¹ * (q.coeff k * (k : ℝ)) +
      (a₁/d^2) * (q.coeff (k+1) * ((k+1 : ℕ) : ℝ)) := by
    have hh : (X*q.derivative).coeff k = q.coeff k * (k : ℝ) := by
      cases k <;> simp [coeff_X_mul, coeff_derivative]
    simp only [R, coeff_add, coeff_sub, mul_assoc, coeff_C_mul, hh, coeff_derivative]
    push_cast
    rfl
  have hRdeg : R.degree < (n+1 : ℕ) := by
    apply (degree_lt_iff_coeff_zero R (n+1)).mpr
    intro k hk
    rw [hc]
    by_cases hk₁ : k = n+1
    · subst k
      rw [h₁, h₀]
      dsimp [d]
      push_cast
      field_simp [hdc]
      ring
    · by_cases hk₂ : k = n+2
      · subst k
        rw [h₀, coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n+2+1)]
        dsimp [d]
        push_cast
        field_simp [hdc]
        ring
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k),
          coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k+1)]
        ring
  have hRc : R.coeff n = -(((n+1 : ℕ) : ℝ)/d^2 * (a₁^2-2*a₂)) := by
    rw [hc, h₂, h₁]
    dsimp [d]
    push_cast
    field_simp
    ring
  have hRe (i : Fin (n+1)) : R.eval (t i) = q.eval (t i) := by
    simp [R, hcrit]
  have hnodal := nodal_derivative n q t ht hq h₀ hcrit
  have hdd (i : Fin (n+1)) : q.derivative.derivative.eval (t i) =
      d * ∏ j ∈ Finset.univ.erase i, (t i-t j) := by
    rw [hnodal, derivative_C_mul, eval_mul, eval_C,
      Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]
  have hLag := Lagrange.coeff_eq_sum (s := Finset.univ) ht.injOn (P := R) (by simpa using hRdeg)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, hRe] at hLag
  calc
    _ = -(∑ i, q.eval (t i) / ∏ j ∈ Finset.univ.erase i, (t i-t j)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hdd]
      change -d * _ / (d * _) = _
      rw [neg_mul, neg_div, mul_div_mul_left _ _ hd]
    _ = -(R.coeff n) := by rw [hLag]
    _ = _ := by rw [hRc]; ring

private theorem q_degree (d : ℕ) : (sourceQ d).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (((sourceP d).comp (C (-1)*X)).reflect d).coeff k = 0
  simp only [coeff_reflect, revAt_eq_self_of_lt hk, comp_C_mul_X_coeff]
  have hc : (sourceP d).coeff k = 0 := by
    simp only [sourceP, finsetSum_coeff, coeff_C_mul_X_pow]
    simp [Finset.mem_range, show ¬ k < d+1 by omega]
  rw [hc, zero_mul]

private theorem q_coeff (d k : ℕ) (hk : k ≤ d) :
    (sourceQ d).coeff k = (sourceP d).coeff (d-k)*(-1)^(d-k) := by
  change (((sourceP d).comp (C (-1)*X)).reflect d).coeff k = _
  simp only [coeff_reflect, revAt_le hk, comp_C_mul_X_coeff]

private theorem source_top_three (n : ℕ) (h0 : sourceThetaCoefficient 0 = 1) :
    (sourceQ (n+2)).coeff (n+2) = 1 ∧
    (sourceQ (n+2)).coeff (n+1) = -sourceThetaCoefficient 1 ∧
    (sourceQ (n+2)).coeff n =
      ((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)*sourceThetaCoefficient 2 := by
  have hc (k : ℕ) (hk : k ≤ n+2) : (sourceP (n+2)).coeff k =
      ((n+2).descFactorial k : ℝ)/((n+2 : ℕ) : ℝ)^k*sourceThetaCoefficient k := by
    simp only [sourceP, finsetSum_coeff, coeff_C_mul_X_pow]
    simp [Finset.mem_range, show k < n+2+1 by omega]
  have hd : (n : ℝ)+2 ≠ 0 := by positivity
  constructor
  · rw [q_coeff _ _ le_rfl, Nat.sub_self, hc 0 (by omega)]
    simp [h0]
  constructor
  · rw [q_coeff _ _ (by omega), show n+2-(n+1)=1 by omega, hc 1 (by omega)]
    simp [Nat.descFactorial, hd]
  · rw [q_coeff _ _ (by omega), show n+2-n=2 by omega, hc 2 (by omega)]
    simp [Nat.descFactorial]
    field_simp [hd]
    ring_nf
    simp

private theorem source_cumulant (n : ℕ) :
    ((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)^2 *
        (sourceThetaCoefficient 1 ^ 2 - 2*sourceThetaCoefficient 2) =
    -((n+1 : ℕ) : ℝ)/(12*((n+2 : ℕ) : ℝ)^2) *
        (sourceThetaMoment 2 - 3*sourceThetaMoment 1 ^ 2) := by
  have h₁ : sourceThetaCoefficient 1 = sourceThetaMoment 1 / 2 := by
    norm_num [sourceThetaCoefficient]
  have h₂ : sourceThetaCoefficient 2 = sourceThetaMoment 2 / 24 := by
    norm_num [sourceThetaCoefficient]
  rw [h₁, h₂]
  have hd : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hd]
  ring

/-- The same source couplings as the positive-extension criterion have the exact
coefficient and fourth-cumulant sums. Nonnegativity of the couplings is not required. -/
theorem source_jensen_coupling_budget (n : ℕ) (h0 : sourceThetaCoefficient 0 = 1)
    (lam : Fin (n+1) → ℝ) (hlam : Function.Injective lam)
    (hlampos : ∀ i, 0 < lam i) (hroot : ∀ i, (sourceQ (n+1)).eval (lam i) = 0) :
    let t := fun i => scale (n+2) * lam i
    (∀ i, (sourceQ (n+2)).derivative.derivative.eval (t i) ≠ 0) ∧
    (∑ i, sourceCoupling (n+2) (t i)) =
      ((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)^2 *
        (sourceThetaCoefficient 1 ^ 2 - 2*sourceThetaCoefficient 2) ∧
    (∑ i, sourceCoupling (n+2) (t i)) =
      -((n+1 : ℕ) : ℝ)/(12*((n+2 : ℕ) : ℝ)^2) *
        (sourceThetaMoment 2 - 3*sourceThetaMoment 1 ^ 2) := by
  let t := fun i => scale (n+2) * lam i
  have hs : 0 < scale (n+2) := by
    dsimp [scale]
    exact div_pos (by exact_mod_cast (show 0 < n+2-1 by omega)) (by positivity)
  have ht : Function.Injective t := by
    intro i j hij
    exact hlam (mul_left_cancel₀ hs.ne' hij)
  have hcrit (i : Fin (n+1)) : (sourceQ (n+2)).derivative.eval (t i) = 0 := by
    rw [(source_jensen_integral_extension (n+2) (by omega)).2.1]
    simp only [eval_mul, eval_C, eval_comp, eval_X]
    have hx : (scale (n+2))⁻¹ * t i = lam i := by
      dsimp [t]
      rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    rw [hx, show n+2-1=n+1 by omega, hroot i, mul_zero]
  obtain ⟨h₀, h₁, h₂⟩ := source_top_three n h0
  have hsum := residue_sum n (sourceQ (n+2)) t _ _ ht (q_degree _) h₀ h₁ h₂ hcrit
  exact ⟨(source_jensen_positive_extension n h0 lam hlam hlampos hroot).2.1,
    hsum, hsum.trans (source_cumulant n)⟩

#print axioms source_jensen_coupling_budget
end D5.S3.Zeros.Jensen.SourceJensenCouplingBudget
