/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: ExtendedAvoidanceClosedForm for extendably 312-avoiding rectangles. -/


/-
admission_basis: open-problem-resolution (#14736; Proved)
Root.u_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_subst_u, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.main_binomial_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.Q_subst, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.main_diagonal
Root.u_first: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_subst_u, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.main_binomial_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_equation
Root.u_second: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.main_binomial_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_equation
Root.u_equation: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_jacobian, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_lagrange
Root.Q_subst: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.main_binomial_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.main_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_lagrange
Root.u_lagrange: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.main_diagonal
Root.u_jacobian: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.main_diagonal
Root.main_diagonal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.main_binomial_diagonal
Formula.coeff_B: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.coeff_B_neg_one, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.correction_coeff, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_coeff, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.last_coeff, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.rescaled_B, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.shift_coeff
Formula.B_add: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_and_last, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_subst_u, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_subst_v, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.first_defect, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_identity, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.rest_defect, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.third_coeff, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_diagonal
Formula.B_nat: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_one, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_subst_u, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_subst_v, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.first_defect, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.rescale_B_nat, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.rest_defect, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.third_coeff
Formula.B_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_and_last, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_diagonal
Formula.B_one: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_and_last, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_identity, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_diagonal
Formula.shift_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.correction_coeff, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.third_coeff
Formula.rescaled_B: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.first_coeff
Formula.correction_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.first_coeff
Formula.sum_remove_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.first_coeff, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.last_coeff
Formula.first_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_coeff
Formula.neg_subst: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.evenPart_subst_identity
Formula.evenPart_identity: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.evenPart_subst_identity
Formula.evenPart_subst_identity: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.evenPart_schroder
Formula.evenPart_schroder: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_diagonal
Formula.B_subst_u: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.main_binomial_diagonal
Formula.main_binomial_diagonal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_defect_series
Formula.rescale_B_nat: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.first_defect
Formula.first_defect: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_defect_series
Formula.coeff_B_neg_one: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.last_coeff
Formula.last_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_coeff
Formula.B_and_last: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_coeff
Formula.y_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.third_coeff
Formula.even_mul_subst: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.third_coeff
Formula.third_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_coeff
Formula.formula_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_defect_series
Formula.v_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_subst_v, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_equation, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.y_subst_v
Formula.v_first: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.B_subst_v, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_derivative, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_equation, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.y_subst_v
Formula.v_equation: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_diagonal
Formula.v_derivative: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_diagonal
Formula.v_diagonal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_diagonal
Formula.B_subst_v: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_diagonal
Formula.y_subst_v: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_diagonal
Formula.rest_defect: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_defect_series
Formula.residual_identity: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_diagonal
Formula.residual_diagonal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_defect_series
Formula.formula_defect_series: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_defect_coeff
Formula.formula_defect_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.algebraic_result
algebraic_result: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational.rational_recurrence_unique
result_of_recurrences: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational.rational_recurrence_unique
literal_recurrenceSpec: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
result: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
Frozen declaration identities at baseline fa35d5b92f08d07c133bfdb44ecc1966ee2247a3:
D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.D; statement_id: sha256:9dee6618039736037570533c60b5ac8bb383c2e3bbcbf9bebff0af5196139bc6
D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.R; statement_id: sha256:9a18180ee4a05a407235a19ea47c640767832d29d620f04cff7dff718f1c33b8
D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.R_eq; statement_id: sha256:b813d05982d3e9b32410090139dafc3b3059f47125d12aaf84c5d5945ef4acbd
D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.R_zero; statement_id: sha256:e4d45700c59f9233b4e30735d0d696af1f9741f04a0e4ba46eae2a14ee85d22c
D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.derivative_primitive; statement_id: sha256:84cb0cf03eda76f6600f94e0fc0f9dba81ba88868975faa6d6ed4e9f68fbdb6d
D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.primitive; statement_id: sha256:5307ee56aed2781f6e0c200229b08566948885d20d4d3271f41c37b99e30b59b
D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.quadratic_unique; statement_id: sha256:f5bfb837aa3d574e79bb11a67865a67b67dedd2e0d25579209dd6b153401648b
D5/S1/Recurrence/Invariants/TripleIterateProductModFour.pow_low; statement_id: sha256:ced2e0cfecd9487b28481d56c57b1d0eeae47ca858c9708d54d603ba8055ce2f
D5/S1/Recurrence/Invariants/TripleIterateProductModFour.subst_coeff; statement_id: sha256:5f70c320808ed9ef8922be3ab49f186152edfb70c497d139f633464affec91f7
D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.rescale_outer; statement_id: sha256:ce7f3c30536cd35b86778a86c8c4a95b6a71d2906517f8266a8ff727a06b7f12
D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.den; statement_id: sha256:66f795105f92dfbfefe4819196ce833ca700aa3e088193fd24f1d0d3aedd76c7
D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient; statement_id: sha256:81f9e16808d9c491ff86a34e6bc2734ff65bb35128a1cae2aac5acffd2329b46
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
import D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
import D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence

open D5.S1.Recurrence.Algebraic.SchroderIntegralEGF (R)

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
private noncomputable def binom (m j : ℤ) : ℤ := if j < 0 then 0 else Ring.choose m j.toNat

noncomputable def F (r k d : ℕ) : ℤ :=
  (∑ i ∈ Icc 1 d, (2 : ℤ) ^ (i - 1) * Ring.choose (k : ℤ) i *
    (binom ((r : ℤ) - 2) ((d : ℤ) - i) -
      2 * binom ((r : ℤ) - 2) ((d : ℤ) - i - 2))) +
  Ring.choose (r : ℤ) d +
  (∑ i ∈ range (d + 1), (catalan (2 * i) : ℤ) *
    binom ((r : ℤ) - 1 + 2 * i) ((d : ℤ) - 1 - 2 * i)) +
  2 * ∑ i ∈ Icc 1 d, (-1 : ℤ) ^ i * Ring.choose (r : ℤ) (d - i)

def claim : Prop := ∀ r k d : ℕ, d ≤ r → d ≤ k → (S r k d : ℤ) = F r k d

end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries
noncomputable section

private def u : (PowerSeries ℚ) := q * U

private def Q : (PowerSeries ℚ) := (1 + X) * (1 + 2 * X)

private lemma u_constant : constantCoeff u = 0 := by simp [u, q_constant]

private lemma u_first : 1 + u = U := by
  dsimp [u]
  linear_combination -U_left

private lemma u_second : 1 + 2 * u = R := by
  rw [R_as_q]
  dsimp [u]
  linear_combination -U_left

private lemma u_equation : u = X * ((1 + u) * (1 + 2 * u)) := by
  rw [u_first, u_second]
  dsimp [u, q]
  ring

private lemma Q_subst : Q.subst u = (1 + u) * (1 + 2 * u) := by
  have hs : HasSubst u := HasSubst.of_constantCoeff_zero' u_constant
  simp only [Q, subst_mul hs, subst_add hs, subst_X hs]
  have ho : subst u (1 : (PowerSeries ℚ)) = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have ht : subst u (2 : (PowerSeries ℚ)) = 2 := by
    rw [← coe_substAlgHom hs]
    exact map_ofNat _ 2
  rw [ho, ht]

private lemma u_lagrange : u = X * Q.subst u := by rw [Q_subst]; exact u_equation

private lemma u_jacobian : (1 - 2 * u ^ 2) * derivative ℚ u =
    ((1 + u) * (1 + 2 * u)) ^ 2 := by
  have hd := congrArg (derivative ℚ) u_equation
  have dconst : derivative ℚ (2 : (PowerSeries ℚ)) = 0 := by
    have ht : (2 : (PowerSeries ℚ)) = 1 + 1 := by ring
    rw [ht, map_add, derivative_one, add_zero]
  simp only [Derivation.leibniz, map_add, derivative_X, derivative_one,
    dconst, smul_eq_mul, zero_add, zero_mul, add_zero, one_mul] at hd
  linear_combination ((1 + u) * (1 + 2 * u)) * hd -
    ((derivative ℚ u) * ((1 + 2 * u) + (1 + u) * 2)) * u_equation

private lemma main_diagonal (H : (PowerSeries ℚ)) :
    D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform ((1 - 2 * X ^ 2) * H) Q =
      H.subst u * Q.subst u := by
  have hQ : constantCoeff Q ≠ 0 := by
    simp [Q, constantCoeff_X, show (2 : (PowerSeries ℚ)) = 1 + 1 by ring]
  have hs : HasSubst u := HasSubst.of_constantCoeff_zero' u_constant
  rw [D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform_eq _ Q Q⁻¹ u u_constant u_lagrange
    (PowerSeries.inv_mul_cancel Q hQ)]
  rw [subst_mul hs, subst_mul hs, subst_sub hs, subst_mul hs, subst_pow hs,
    subst_X hs]
  have ho : subst u (1 : (PowerSeries ℚ)) = 1 := by rw [← coe_substAlgHom hs, map_one]
  have ht : subst u (2 : (PowerSeries ℚ)) = 2 := by
    rw [← coe_substAlgHom hs]
    exact map_ofNat _ 2
  rw [ho, ht]
  have hinv : (Q⁻¹).subst u * Q.subst u = 1 := by
    have h := congrArg (substAlgHom hs) (PowerSeries.inv_mul_cancel Q hQ)
    simpa only [map_mul, map_one, coe_substAlgHom] using h
  rw [Q_subst] at hinv ⊢
  calc
    (1 - 2 * u ^ 2) * H.subst u * (Q⁻¹).subst u * derivative ℚ u =
      H.subst u * (Q⁻¹).subst u * ((1 - 2 * u ^ 2) * derivative ℚ u) := by ring
    _ = H.subst u * (Q⁻¹).subst u * ((1 + u) * (1 + 2 * u)) ^ 2 := by rw [u_jacobian]
    _ = H.subst u * ((Q⁻¹).subst u * ((1 + u) * (1 + 2 * u))) *
      ((1 + u) * (1 + 2 * u)) := by ring
    _ = H.subst u * ((1 + u) * (1 + 2 * u)) := by rw [hinv, mul_one]

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries Finset
noncomputable section

private lemma coeff_B (e : ℤ) (n : ℕ) : coeff n ((binomialSeries (R := ℤ) ℚ) e) = ((Ring.choose e n : ℤ) : ℚ) := by
  simp only [binomialSeries_coeff, zsmul_eq_mul, mul_one]

private lemma B_add (e f : ℤ) : (binomialSeries (R := ℤ) ℚ) (e + f) = (binomialSeries (R := ℤ) ℚ) e * (binomialSeries (R := ℤ) ℚ) f := binomialSeries_add e f

private lemma B_nat (n : ℕ) : (binomialSeries (R := ℤ) ℚ) (n : ℤ) = (1 + X) ^ n := binomialSeries_nat n

private lemma B_zero : (binomialSeries (R := ℤ) ℚ) 0 = 1 := binomialSeries_zero

private lemma B_one : (binomialSeries (R := ℤ) ℚ) 1 = 1 + X := by simpa using B_nat 1

private lemma shift_coeff (m n : ℕ) (e : ℤ) :
    coeff n (X ^ m * (binomialSeries (R := ℤ) ℚ) e) = (binom e ((n : ℤ) - m) : ℚ) := by
  rw [coeff_X_pow_mul']
  by_cases h : m ≤ n
  · rw [if_pos h, coeff_B]
    have hz : ¬ ((n : ℤ) - m < 0) := by omega
    have hn : ((n : ℤ) - m).toNat = n - m := by omega
    simp only [binom, if_neg hz, hn]
  · rw [if_neg h]
    have hz : (n : ℤ) - m < 0 := by omega
    simp [binom, hz]

private def first (r k : ℕ) : (PowerSeries ℚ) :=
  C (1 / 2 : ℚ) * (rescale 2 ((binomialSeries (R := ℤ) ℚ) (k : ℤ)) - 1) *
    ((binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 2) - C 2 * X ^ 2 * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 2))

private lemma rescaled_B (k n : ℕ) :
    coeff n (rescale 2 ((binomialSeries (R := ℤ) ℚ) (k : ℤ)) - 1) =
      if n = 0 then 0 else (2 : ℚ) ^ n * ((Ring.choose (k : ℤ) n : ℤ) : ℚ) := by
  rw [map_sub, coeff_rescale, coeff_B, coeff_one]
  by_cases h : n = 0
  · subst n
    simp
  · simp [h]

private lemma correction_coeff (r n : ℕ) :
    coeff n ((binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 2) - C 2 * X ^ 2 * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 2)) =
      (binom ((r : ℤ) - 2) n : ℚ) - 2 *
        (binom ((r : ℤ) - 2) ((n : ℤ) - 2) : ℚ) := by
  rw [map_sub]
  have h : C (2 : ℚ) * X ^ 2 * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 2) =
      C 2 * (X ^ 2 * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 2)) := by ring
  rw [h, coeff_C_mul, shift_coeff, coeff_B]
  simp only [binom, if_neg (show ¬ ((n : ℤ) < 0) by omega), Int.toNat_natCast, Nat.cast_ofNat]

private lemma sum_remove_zero (n : ℕ) (h : ℕ → ℚ) :
    (∑ i ∈ range (n + 1), h i) = h 0 + ∑ i ∈ Icc 1 n, h i := by
  have hs : Ico 1 (n + 1) = Icc 1 n := by
    ext i
    simp only [mem_Ico, mem_Icc]
    omega
  rw [sum_range_eq_add_Ico _ (show 1 ≤ n + 1 by omega), hs]

private lemma first_coeff (r k d : ℕ) : coeff d (first r k) =
    ((∑ i ∈ Icc 1 d, (2 : ℤ) ^ (i - 1) * Ring.choose (k : ℤ) i *
      (binom ((r : ℤ) - 2) ((d : ℤ) - i) -
        2 * binom ((r : ℤ) - 2) ((d : ℤ) - i - 2))) : ℚ) := by
  rw [first, mul_assoc, coeff_C_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_remove_zero]
  simp only [rescaled_B, correction_coeff, ↓reduceIte, zero_mul, zero_add]
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hb := mem_Icc.mp hi
  rw [if_neg (by omega : i ≠ 0)]
  have hs : (d - i : ℕ) = (d : ℤ) - i := by omega
  have hpow : (2 : ℚ) ^ i = 2 * 2 ^ (i - 1) := by
    calc
      (2 : ℚ) ^ i = 2 ^ (i - 1 + 1) := congrArg (fun n : ℕ => (2 : ℚ) ^ n) (by omega)
      _ = 2 * 2 ^ (i - 1) := by rw [pow_succ]; ring
  rw [hs, hpow]
  ring

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries
noncomputable section

private lemma neg_subst (B u : (PowerSeries ℚ)) (hu : constantCoeff u = 0) :
    (rescale (-1 : ℚ) B).subst u = B.subst (-u) := by
  simpa using D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.rescale_outer
    (-1 : ℚ) B u hu


private def evenPart : (PowerSeries ℚ) := mk fun n => if Even n then (catalan n : ℚ) else 0

private lemma evenPart_identity : P13CatalanLagrangeBridge.catalanUnit + rescale (-1 : ℚ) P13CatalanLagrangeBridge.catalanUnit = C 2 * evenPart := by
  ext n
  simp only [P13CatalanLagrangeBridge.catalanUnit, map_add, coeff_map, catalanSeries_coeff, coeff_rescale,
    coeff_C_mul, evenPart, coeff_mk, Nat.coe_castRingHom]
  rcases Nat.even_or_odd n with hn | hn
  · rw [if_pos hn, hn.neg_one_pow]
    ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn), hn.neg_one_pow]
    ring


private lemma evenPart_subst_identity (u : (PowerSeries ℚ)) (hu : constantCoeff u = 0) :
    P13CatalanLagrangeBridge.catalanUnit.subst u + P13CatalanLagrangeBridge.catalanUnit.subst (-u) = C 2 * evenPart.subst u := by
  have hs : HasSubst u := HasSubst.of_constantCoeff_zero' hu
  have h := congrArg (substAlgHom hs) evenPart_identity
  simp only [map_add, map_mul, coe_substAlgHom] at h
  rw [neg_subst P13CatalanLagrangeBridge.catalanUnit u hu] at h
  have hc : (C (2 : ℚ)).subst u = C 2 := by exact subst_C _
  rw [hc] at h
  exact h

private lemma evenPart_schroder : 1 + C 2 * z * evenPart.subst z = A * V := by
  calc
    1 + C 2 * z * evenPart.subst z = 1 + z * (C 2 * evenPart.subst z) := by ring
    _ = A * V := by rw [← evenPart_subst_identity z z_constant]; exact even_Catalan_identity

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries
noncomputable section

private lemma B_subst_u (a : ℕ) : ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2)).subst u * U ^ 2 = U ^ a := by
  have hs : HasSubst u := HasSubst.of_constantCoeff_zero' u_constant
  have hb : (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (binomialSeries (R := ℤ) ℚ) 2 = (binomialSeries (R := ℤ) ℚ) (a : ℤ) := by
    rw [← B_add]
    congr 1
    ring
  have h := congrArg (substAlgHom hs) hb
  simp only [map_mul, coe_substAlgHom] at h
  rw [show (2 : ℤ) = (2 : ℕ) by rfl, B_nat 2, B_nat a,
    subst_pow hs, subst_pow hs, subst_add hs, subst_X hs] at h
  have ho : subst u (1 : (PowerSeries ℚ)) = 1 := by rw [← coe_substAlgHom hs, map_one]
  rw [ho, u_first] at h
  exact h

private lemma main_binomial_diagonal (a b : ℕ) :
    D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform ((1 - 2 * X ^ 2) *
      ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (1 + 2 * X) ^ b)) Q = A * R ^ b * U ^ a := by
  rw [main_diagonal]
  have hs : HasSubst u := HasSubst.of_constantCoeff_zero' u_constant
  rw [subst_mul hs, subst_pow hs, subst_add hs, subst_mul hs, subst_X hs]
  have ho : subst u (1 : (PowerSeries ℚ)) = 1 := by rw [← coe_substAlgHom hs, map_one]
  have ht : subst u (2 : (PowerSeries ℚ)) = 2 := by rw [← coe_substAlgHom hs]; exact map_ofNat _ 2
  rw [ho, ht, u_second, Q_subst, u_first, u_second]
  have hu := B_subst_u a
  have hr := R_as_q
  change R = A * U at hr
  calc
    ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2)).subst u * R ^ b * (U * R) =
      A * R ^ b * (((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2)).subst u * U ^ 2) := by
        rw [hr]
        ring
    _ = A * R ^ b * U ^ a := by rw [hu]

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries
noncomputable section

private def Q₁ : (PowerSeries ℚ) := 1 + X

private def H (a b : ℕ) : (PowerSeries ℚ) := (1 - 2 * X ^ 2) * (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (1 + 2 * X) ^ b

private lemma rescale_B_nat (k : ℕ) : rescale (2 : ℚ) ((binomialSeries (R := ℤ) ℚ) (k : ℤ)) = (1 + 2 * X) ^ k := by
  rw [B_nat]
  simp only [map_pow, map_add, map_one, rescale_X]
  have ht : C (2 : ℚ) = (2 : (PowerSeries ℚ)) := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
    ring
  rw [ht]

private lemma first_defect (a b d : ℕ) :
    coeff d (first (d + a) (d + b)) =
      (1 / 2 : ℚ) * (coeff d (H a b * Q ^ d) - coeff d (H a 0 * Q₁ ^ d)) := by
  rw [first, rescale_B_nat]
  have hB : (binomialSeries (R := ℤ) ℚ) ((d + a : ℕ) - 2 : ℤ) = (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (1 + X) ^ d := by
    rw [← B_nat, ← B_add]
    congr 1
    push_cast
    ring
  rw [hB]
  rw [show d + b = b + d by omega, pow_add]
  have he : C (1 / 2 : ℚ) * ((1 + 2 * X) ^ b * (1 + 2 * X) ^ d - 1) *
      ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (1 + X) ^ d -
        C 2 * X ^ 2 * ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (1 + X) ^ d)) =
      C (1 / 2 : ℚ) * (H a b * Q ^ d - H a 0 * Q₁ ^ d) := by
    dsimp [H, Q, Q₁]
    rw [mul_pow]
    have ht : C (2 : ℚ) = (2 : (PowerSeries ℚ)) := by
      rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
      ring
    rw [ht]
    ring
  rw [he, coeff_C_mul, map_sub]

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries Finset
noncomputable section

private def y : (PowerSeries ℚ) := X * (1 + X)

private def third (r : ℕ) : (PowerSeries ℚ) := X * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 1) * evenPart.subst y

private def last (r : ℕ) : (PowerSeries ℚ) := C 2 * ((binomialSeries (R := ℤ) ℚ) (-1) - 1) * (binomialSeries (R := ℤ) ℚ) (r : ℤ)

private def rest (r : ℕ) : (PowerSeries ℚ) := (1 - X) * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 1) + third r

private lemma coeff_B_neg_one (n : ℕ) : coeff n ((binomialSeries (R := ℤ) ℚ) (-1)) = (-1 : ℚ) ^ n := by
  rw [coeff_B]
  have h : Ring.choose (-1 : ℤ) n = (-1 : ℤ) ^ n := by
    rw [Ring.choose_neg, show (1 : ℤ) + n - 1 = n by ring, Ring.choose_natCast]
    simp [Units.smul_def, Int.coe_negOnePow_natCast]
  rw [h]
  norm_cast

private lemma last_coeff (r d : ℕ) : coeff d (last r) =
    ((2 * ∑ i ∈ Icc 1 d, (-1 : ℤ) ^ i * Ring.choose (r : ℤ) (d - i) : ℤ) : ℚ) := by
  rw [last, mul_assoc, coeff_C_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_remove_zero]
  simp only [map_sub, coeff_one]
  simp only [coeff_B_neg_one]
  simp only [coeff_B]
  simp only [pow_zero, ↓reduceIte, sub_self, zero_mul, zero_add]
  push_cast
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [if_neg (by have hb := mem_Icc.mp hi; omega : i ≠ 0)]
  simp

private lemma B_and_last (r : ℕ) : (binomialSeries (R := ℤ) ℚ) (r : ℤ) + last r = (1 - X) * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 1) := by
  have hB : (binomialSeries (R := ℤ) ℚ) (r : ℤ) = (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 1) * (1 + X) := by
    rw [← B_one, ← B_add]
    congr 1
    ring
  have hm : (binomialSeries (R := ℤ) ℚ) (-1) * (1 + X) = 1 := by
    rw [← B_one, ← B_add, show (-1 : ℤ) + 1 = 0 by ring, B_zero]
  have ht : C (2 : ℚ) = (2 : (PowerSeries ℚ)) := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
    ring
  rw [last, ht, hB]
  linear_combination 2 * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 1) * hm

private lemma y_constant : constantCoeff y = 0 := by simp [y]

private lemma even_mul_subst (A u : (PowerSeries ℚ)) (hu : constantCoeff u = 0) (n : ℕ) :
    coeff n (A * evenPart.subst u) =
      ∑ i ∈ range (n + 1), (catalan (2 * i) : ℚ) * coeff n (A * u ^ (2 * i)) := by
  rw [D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.finite_mul_subst A evenPart u hu]
  simp only [evenPart, coeff_mk, ite_mul, zero_mul]
  rw [D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.even_sum_reindex]
  apply sum_congr rfl
  intro i hi
  by_cases h : 2 * i ≤ n
  · rw [if_pos h]
  · rw [if_neg h, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.mul_pow_vanish A u hu n (2 * i) (by omega), mul_zero]

private lemma third_coeff (r d : ℕ) : coeff d (third r) =
    ((∑ i ∈ range (d + 1), (catalan (2 * i) : ℤ) *
      binom ((r : ℤ) - 1 + 2 * i) ((d : ℤ) - 1 - 2 * i) : ℤ) : ℚ) := by
  rw [third, even_mul_subst _ y y_constant]
  push_cast
  apply sum_congr rfl
  intro i hi
  have he : X * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 1) * y ^ (2 * i) =
      X ^ (2 * i + 1) * (binomialSeries (R := ℤ) ℚ) ((r : ℤ) - 1 + 2 * i) := by
    rw [y, mul_pow, ← B_nat (2 * i), Nat.cast_mul, Nat.cast_ofNat, B_add]
    rw [pow_succ]
    ring
  rw [he, shift_coeff]
  congr 2
  push_cast
  ring

private lemma formula_coeff (r k d : ℕ) : (F r k d : ℚ) = coeff d (first r k + rest r) := by
  rw [rest, ← B_and_last, map_add, map_add, first_coeff, third_coeff]
  rw [map_add, coeff_B, last_coeff]
  simp only [F]
  push_cast
  ring

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries
noncomputable section

private def v : (PowerSeries ℚ) := X * V

private lemma v_constant : constantCoeff v = 0 := by simp [v]

private lemma v_first : 1 + v = V := by
  dsimp [v]
  linear_combination -V_left

private lemma v_equation : v = X * Q₁.subst v := by
  have hs : HasSubst v := HasSubst.of_constantCoeff_zero' v_constant
  rw [Q₁, subst_add hs, subst_X hs]
  have ho : subst v (1 : (PowerSeries ℚ)) = 1 := by rw [← coe_substAlgHom hs, map_one]
  rw [ho, v_first]
  rfl

private lemma v_derivative : derivative ℚ v = V ^ 2 := by
  have he : v = X * (1 + v) := by rw [v_first]; rfl
  have hd := congrArg (derivative ℚ) he
  simp only [Derivation.leibniz, map_add, derivative_X, derivative_one,
    smul_eq_mul, zero_add, one_mul] at hd
  rw [v_first] at hd
  linear_combination V * hd - derivative ℚ v * V_left

private lemma v_diagonal (K : (PowerSeries ℚ)) : D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform K Q₁ = K.subst v * V := by
  have hs : HasSubst v := HasSubst.of_constantCoeff_zero' v_constant
  have hinv : (binomialSeries (R := ℤ) ℚ) (-1) * Q₁ = 1 := by
    rw [Q₁, ← B_one, ← B_add, show (-1 : ℤ) + 1 = 0 by ring, B_zero]
  rw [D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform_eq K Q₁ ((binomialSeries (R := ℤ) ℚ) (-1)) v v_constant v_equation hinv]
  rw [subst_mul hs, v_derivative]
  have hi := congrArg (substAlgHom hs) hinv
  simp only [map_mul, map_one, coe_substAlgHom] at hi
  have hQ : Q₁.subst v = V := by
    rw [Q₁, subst_add hs, subst_X hs]
    have ho : subst v (1 : (PowerSeries ℚ)) = 1 := by rw [← coe_substAlgHom hs, map_one]
    rw [ho, v_first]
  rw [hQ] at hi
  calc
    K.subst v * ((binomialSeries (R := ℤ) ℚ) (-1)).subst v * V ^ 2 = K.subst v * (((binomialSeries (R := ℤ) ℚ) (-1)).subst v * V) * V := by ring
    _ = K.subst v * V := by rw [hi, mul_one]

private lemma B_subst_v (a : ℕ) : ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2)).subst v * V ^ 2 = V ^ a := by
  have hs : HasSubst v := HasSubst.of_constantCoeff_zero' v_constant
  have hb : (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (binomialSeries (R := ℤ) ℚ) 2 = (binomialSeries (R := ℤ) ℚ) (a : ℤ) := by
    rw [← B_add]; congr 1; ring
  have h := congrArg (substAlgHom hs) hb
  simp only [map_mul, coe_substAlgHom] at h
  rw [show (2 : ℤ) = (2 : ℕ) by rfl, B_nat 2, B_nat a,
    subst_pow hs, subst_pow hs, subst_add hs, subst_X hs] at h
  have ho : subst v (1 : (PowerSeries ℚ)) = 1 := by rw [← coe_substAlgHom hs, map_one]
  rw [ho, v_first] at h
  exact h

private lemma y_subst_v : y.subst v = z := by
  have hs : HasSubst v := HasSubst.of_constantCoeff_zero' v_constant
  rw [y, subst_mul hs, subst_add hs, subst_X hs]
  have ho : subst v (1 : (PowerSeries ℚ)) = 1 := by rw [← coe_substAlgHom hs, map_one]
  rw [ho, v_first]
  dsimp [v, z]
  ring

private lemma rest_defect (a d : ℕ) :
    rest (d + a) = ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 1) * ((1 - X) + X * evenPart.subst y)) * Q₁ ^ d := by
  have hb : (binomialSeries (R := ℤ) ℚ) ((d + a : ℕ) - 1 : ℤ) = (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 1) * Q₁ ^ d := by
    rw [Q₁, ← B_nat, ← B_add]; congr 1; push_cast; ring
  rw [rest, third, hb]
  ring

private lemma residual_identity (a : ℕ) :
    (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 1) * ((1 - X) + X * evenPart.subst y) - C (1 / 2 : ℚ) * H a 0 =
      C (1 / 2 : ℚ) * (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (1 + C 2 * y * evenPart.subst y) := by
  have hb : (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 1) = (binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (1 + X) := by
    rw [← B_one, ← B_add]; congr 1; ring
  rw [hb, H, pow_zero, mul_one, y]
  have ht : C (2 : ℚ) = (2 : (PowerSeries ℚ)) := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]; ring
  rw [ht]
  linear_combination -((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2) * (1 - X ^ 2 + X * (1 + X) * evenPart.subst (X * (1 + X)))) * half_cancel

private lemma residual_diagonal (a : ℕ) :
    D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform
      ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 1) * ((1 - X) + X * evenPart.subst y) - C (1 / 2 : ℚ) * H a 0) Q₁ =
    C (1 / 2 : ℚ) * A * V ^ a := by
  rw [residual_identity, v_diagonal]
  have hs : HasSubst v := HasSubst.of_constantCoeff_zero' v_constant
  rw [subst_mul hs, subst_mul hs, subst_add hs, subst_mul hs, subst_mul hs,
    subst_C, subst_C]
  have ho : subst v (1 : (PowerSeries ℚ)) = 1 := by rw [← coe_substAlgHom hs, map_one]
  rw [ho, subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' y_constant) hs, y_subst_v]
  change C (1 / 2 : ℚ) * ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2)).subst v *
    (1 + C 2 * z * evenPart.subst z) * V = C (1 / 2 : ℚ) * A * V ^ a
  have he : 1 + C 2 * z * evenPart.subst z = A * V := evenPart_schroder
  rw [he]
  calc
    C (1 / 2 : ℚ) * ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2)).subst v * (A * V) * V =
      C (1 / 2 : ℚ) * A * (((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 2)).subst v * V ^ 2) := by ring
    _ = C (1 / 2 : ℚ) * A * V ^ a := by rw [B_subst_v]

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries
noncomputable section

private theorem formula_defect_series (a b : ℕ) :
    mk (fun d => (F (d + a) (d + b) d : ℚ)) = G a b := by
  have hmain : D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform (H a b) Q = A * R ^ b * U ^ a := by
    rw [H]
    simpa only [mul_assoc] using main_binomial_diagonal a b
  have hres := residual_diagonal a
  ext d
  have hm := congrArg (coeff d) hmain
  have hr := congrArg (coeff d) hres
  simp only [D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform, coeff_mk, map_sub, coeff_C_mul] at hm hr
  rw [coeff_mk, formula_coeff, map_add, first_defect, rest_defect]
  have hrest : coeff d (((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 1) * ((1 - X) + X * evenPart.subst y)) * Q₁ ^ d) -
      (1 / 2 : ℚ) * coeff d (H a 0 * Q₁ ^ d) =
      (1 / 2 : ℚ) * coeff d (A * V ^ a) := by
    have he : ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 1) * ((1 - X) + X * evenPart.subst y) - C (1 / 2 : ℚ) * H a 0) * Q₁ ^ d =
      ((binomialSeries (R := ℤ) ℚ) ((a : ℤ) - 1) * ((1 - X) + X * evenPart.subst y)) * Q₁ ^ d -
      C (1 / 2 : ℚ) * (H a 0 * Q₁ ^ d) := by ring
    rw [he, map_sub, coeff_C_mul] at hr
    simpa only [mul_assoc, coeff_C_mul] using hr
  have hG : G a b = C (1 / 2 : ℚ) * (A * R ^ b * U ^ a + A * V ^ a) := by
    dsimp [G]; ring
  rw [hG, coeff_C_mul, map_add]
  linear_combination (1 / 2 : ℚ) * hm + hrest

private lemma formula_defect_coeff (a b d : ℕ) :
    (F (d + a) (d + b) d : ℚ) = coeff d (G a b) := by
  have h := congrArg (coeff d) (formula_defect_series a b)
  simpa only [coeff_mk] using h

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open PowerSeries
noncomputable section

private theorem algebraic_result : ∀ r k d : ℕ, d ≤ r → d ≤ k → T r k d = F r k d := by
  intro r k d hr hk
  have hT := D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.series_eq_T r k d
  rw [D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_admissible r k d hr hk] at hT
  have hF := D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.formula_defect_coeff (r - d) (k - d) d
  rw [Nat.add_sub_of_le hr, Nat.add_sub_of_le hk] at hF
  exact_mod_cast hT.symm.trans hF.symm

private theorem result_of_recurrences (hS : D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.RecurrenceSpec (fun r k d => (S r k d : ℤ))) : claim := by
  intro r k d hr hk
  exact (D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.recurrence_unique _ hS r k d).trans (algebraic_result r k d hr hk)

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm

namespace D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
noncomputable section

private theorem literal_recurrenceSpec : D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.RecurrenceSpec (fun r k d => (S r k d : ℤ)) where
  outside := S_outside
  zero := by intro r k; rw [S_zero]; rfl
  diagonal := S_diagonal
  row := S_row
  col := S_col
  interior := S_interior

theorem result : claim :=
  D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.result_of_recurrences
    literal_recurrenceSpec

example : ∃ r k d : ℕ, d ≤ r ∧ d ≤ k := by
  exact ⟨0, 0, 0, le_rfl, le_rfl⟩

example : ∃ R : Matrix (Fin 1) (Fin 1) SignType, IsASR R := by
  exact ⟨!![1], by
    constructor
    · intro i
      fin_cases i
      simp [IsASR, Alternates, StartsOne, EndsOne]
    · intro j
      fin_cases j
      simp [Alternates, StartsOne]⟩

end
end D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm
