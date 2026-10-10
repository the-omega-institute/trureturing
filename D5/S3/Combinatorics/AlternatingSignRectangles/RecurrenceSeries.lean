/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: RecurrenceSeries for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
T_outside: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.T_cast_spec
T_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.T_cast_spec
T_diagonal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.T_cast_spec
T_row: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.T_cast_spec
T_col: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.T_cast_spec
T_interior: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.T_cast_spec
Rational.rational_recurrence_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational.rational_recurrence_unique
Series.q_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_constant, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_col_transform, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_constant, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.U_right, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.V_subst_q
Series.U_right: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.R_as_q, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.U_left, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.V_subst_q
Series.U_left: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_first, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_second
Series.V_right: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.V_left, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.V_power_coeff
Series.V_left: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_derivative, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_first, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.V_subst_q, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.even_Catalan_identity, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.z_w
Series.R_unit: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.R_as_q
Series.R_as_q: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.main_binomial_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.u_second
Series.A_R_minus: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_horizontal
Series.half_cancel: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.residual_identity, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_horizontal, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_zero
Series.G_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_diagonal
Series.G_horizontal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_source_horizontal
Diagonal.lagrange_source: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.transform_eq
Diagonal.transform_eq: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.v_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Root.main_diagonal
Series.Cat_equation: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cat_subst_equation
Series.z_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.evenPart_schroder, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cat_neg_z, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cat_z
Series.z_w: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cat_neg_z, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cat_z
Series.Cat_subst_equation: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cat_neg_z, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cat_z
Series.Cat_z: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.even_Catalan_identity
Series.Cat_neg_z: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.even_Catalan_identity
Series.even_Catalan_identity: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.evenPart_schroder
Series.R_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_horizontal_coeff_succ
Series.U_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_constant
Series.V_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_constant, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.V_power_constant
Series.G_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_zero, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_horizontal_coeff_succ
Series.G_diagonal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_diagonal
Series.V_power_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_interior, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_col_coeff
Series.G_source_horizontal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_horizontal_coeff_succ
Diagonal.finite_subst_large: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.finite_mul_subst
Diagonal.finite_mul_subst: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.even_mul_subst, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_col_transform
Diagonal.mul_pow_vanish: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.even_mul_subst
Diagonal.even_sum_reindex: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.Formula.even_mul_subst
Series.V_power_constant: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_horizontal_coeff_succ
Series.G_horizontal_coeff_succ: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_horizontal_coeff
Series.range_to_Icc: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_horizontal_coeff
Series.G_horizontal_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_interior, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_row
Series.V_subst_q: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_col_transform
Series.G_col_transform: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.G_col_coeff
Series.G_col_coeff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_col
Series.Cnt_admissible: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.algebraic_result, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_col, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_diagonal, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_interior, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_left, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_pred, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_row, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_shift, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_zero
Series.Cnt_outside: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_spec
Series.Cnt_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_spec
Series.Cnt_diagonal: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_spec
Series.Cnt_left: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_interior, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_row
Series.Cnt_pred: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_interior, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_row
Series.Cnt_shift: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_interior, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_row
Series.Cnt_row: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_spec
Series.Cnt_col: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_spec
Series.Cnt_interior: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.Cnt_spec
Series.Cnt_spec: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.series_eq_T
Series.T_cast_spec: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series.series_eq_T, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.recurrence_unique
Series.series_eq_T: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational.rational_recurrence_unique
recurrence_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational.rational_recurrence_unique
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
D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.den; statement_id: sha256:66f795105f92dfbfefe4819196ce833ca700aa3e088193fd24f1d0d3aedd76c7
D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient; statement_id: sha256:81f9e16808d9c491ff86a34e6bc2734ff65bb35128a1cae2aac5acffd2329b46
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S1.Recurrence.Invariants.CatalanCubicCompositionParity
import D5.S1.Recurrence.Invariants.TripleIterateProductModFour
import D5.S1.Recurrence.Residue.DiagonalPowerRatioModTwelve
import D5.S1.Recurrence.Algebraic.SchroderIntegralEGF
import D5.S3.Combinatorics.Nonnesting.CatalanLagrangeBridge
import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo

open D5.S1.Recurrence.Invariants.CatalanCubicCompositionParity (quadratic_unique)
open D5.S1.Recurrence.Algebraic.SchroderIntegralEGF (R R_eq R_zero primitive derivative_primitive)
open D5.S1.Recurrence.Invariants.TripleIterateProductModFour (subst_coeff pow_low)
open D5.S1.Recurrence.Residue.DiagonalPowerRatioModTwelve (den)

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
set_option autoImplicit false
open Finset


def T (r k d : ℕ) : ℤ :=
  if hbad : r < d ∨ k < d then 0
  else if hz : d = 0 then 1
  else if hdiag : r = d ∧ k = d then (Nat.largeSchroder (d - 1) : ℤ)
  else if hrow : d = r then
    T r (k - 1) d + T (r - 1) (k - 1) (d - 1) +
      ∑ i : ↥(Icc 2 d), (Nat.largeSchroder (i.val - 2) : ℤ) *
        T (r + 1 - i.val) (k + 1 - i.val) (d + 1 - i.val)
  else if hcol : d = k then
    ∑ j : Fin (k + 1), T j.val k j.val * (Nat.choose (r - j.val - 1) (k - j.val) : ℤ)
  else
    T r (k - 1) d + T (r - 1) (k - 1) (d - 1) +
      ∑ i : ↥(Icc 2 d), (Nat.largeSchroder (i.val - 2) : ℤ) *
        (T (r + 1 - i.val) (k + 1 - i.val) (d + 1 - i.val) -
          (Nat.choose (r - i.val) (d + 1 - i.val) : ℤ))
termination_by r + k
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have hi := Finset.mem_Icc.mp i.property
  all_goals omega

private lemma T_outside (r k d : ℕ) (h : r < d ∨ k < d) : T r k d = 0 := by
  rw [T, dif_pos h]

private lemma T_zero (r k : ℕ) : T r k 0 = 1 := by
  rw [T]
  simp

private lemma T_diagonal (d : ℕ) (hd : 0 < d) : T d d d = (Nat.largeSchroder (d - 1) : ℤ) := by
  rw [T]
  simp [Nat.ne_of_gt hd]

private lemma T_row (r k : ℕ) (hr : 0 < r) (hk : r < k) :
    T r k r = T r (k - 1) r + T (r - 1) (k - 1) (r - 1) +
      ∑ i : ↥(Icc 2 r), (Nat.largeSchroder (i.val - 2) : ℤ) *
        T (r + 1 - i.val) (k + 1 - i.val) (r + 1 - i.val) := by
  rw [T]
  simp [Nat.ne_of_gt hr, Nat.not_lt.mpr (Nat.le_of_lt hk), Nat.ne_of_gt hk]

private lemma T_col (r k : ℕ) (hk : 0 < k) (hr : k < r) :
    T r k k = ∑ j : Fin (k + 1),
      T j.val k j.val * (Nat.choose (r - j.val - 1) (k - j.val) : ℤ) := by
  rw [T]
  simp [Nat.ne_of_gt hk, Nat.not_lt.mpr (Nat.le_of_lt hr), Nat.ne_of_lt hr, Nat.ne_of_gt hr]

private lemma T_interior (r k d : ℕ) (hd : 0 < d) (hr : d < r) (hk : d < k) :
    T r k d = T r (k - 1) d + T (r - 1) (k - 1) (d - 1) +
      ∑ i : ↥(Icc 2 d), (Nat.largeSchroder (i.val - 2) : ℤ) *
        (T (r + 1 - i.val) (k + 1 - i.val) (d + 1 - i.val) -
          (Nat.choose (r - i.val) (d + 1 - i.val) : ℤ)) := by
  rw [T]
  simp [Nat.ne_of_gt hd, Nat.not_lt.mpr (Nat.le_of_lt hr), Nat.not_lt.mpr (Nat.le_of_lt hk),
    Nat.ne_of_gt hr, Nat.ne_of_gt hk, Nat.ne_of_lt hr, Nat.ne_of_lt hk]

end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
open Finset

structure RecurrenceSpec (f : ℕ → ℕ → ℕ → ℤ) : Prop where
  outside : ∀ r k d, r < d ∨ k < d → f r k d = 0
  zero : ∀ r k, f r k 0 = 1
  diagonal : ∀ d, 0 < d → f d d d = (Nat.largeSchroder (d - 1) : ℤ)
  row : ∀ r k, 0 < r → r < k →
    f r k r = f r (k - 1) r + f (r - 1) (k - 1) (r - 1) +
      ∑ i : ↥(Icc 2 r), (Nat.largeSchroder (i.val - 2) : ℤ) *
        f (r + 1 - i.val) (k + 1 - i.val) (r + 1 - i.val)
  col : ∀ r k, 0 < k → k < r →
    f r k k = ∑ j : Fin (k + 1),
      f j.val k j.val * (Nat.choose (r - j.val - 1) (k - j.val) : ℤ)
  interior : ∀ r k d, 0 < d → d < r → d < k →
    f r k d = f r (k - 1) d + f (r - 1) (k - 1) (d - 1) +
      ∑ i : ↥(Icc 2 d), (Nat.largeSchroder (i.val - 2) : ℤ) *
        (f (r + 1 - i.val) (k + 1 - i.val) (d + 1 - i.val) -
          (Nat.choose (r - i.val) (d + 1 - i.val) : ℤ))



end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
open Finset

private structure rationalRecurrenceSpec (f : ℕ → ℕ → ℕ → ℚ) : Prop where
  outside : ∀ r k d, r < d ∨ k < d → f r k d = 0
  zero : ∀ r k, f r k 0 = 1
  diagonal : ∀ d, 0 < d → f d d d = (Nat.largeSchroder (d - 1) : ℚ)
  row : ∀ r k, 0 < r → r < k →
    f r k r = f r (k - 1) r + f (r - 1) (k - 1) (r - 1) +
      ∑ i : ↥(Icc 2 r), (Nat.largeSchroder (i.val - 2) : ℚ) *
        f (r + 1 - i.val) (k + 1 - i.val) (r + 1 - i.val)
  col : ∀ r k, 0 < k → k < r →
    f r k k = ∑ j : Fin (k + 1),
      f j.val k j.val * (Nat.choose (r - j.val - 1) (k - j.val) : ℚ)
  interior : ∀ r k d, 0 < d → d < r → d < k →
    f r k d = f r (k - 1) d + f (r - 1) (k - 1) (d - 1) +
      ∑ i : ↥(Icc 2 d), (Nat.largeSchroder (i.val - 2) : ℚ) *
        (f (r + 1 - i.val) (k + 1 - i.val) (d + 1 - i.val) -
          (Nat.choose (r - i.val) (d + 1 - i.val) : ℚ))

private theorem rational_recurrence_unique (f g : ℕ → ℕ → ℕ → ℚ) (hf : rationalRecurrenceSpec f) (hg : rationalRecurrenceSpec g) :
    ∀ r k d, f r k d = g r k d := by
  have h : ∀ n r k d, r + k = n → f r k d = g r k d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r k d hn
      by_cases hout : r < d ∨ k < d
      · rw [hf.outside r k d hout, hg.outside r k d hout]
      have hr : d ≤ r := by omega
      have hk : d ≤ k := by omega
      by_cases hz : d = 0
      · subst d
        rw [hf.zero, hg.zero]
      have hd : 0 < d := by omega
      by_cases hrow : d = r
      · subst r
        by_cases hcol : d = k
        · subst k
          rw [hf.diagonal d hd, hg.diagonal d hd]
        have hdlt : d < k := by omega
        rw [hf.row d k hd hdlt, hg.row d k hd hdlt]
        congr 1
        · congr 1
          · exact ih (d + (k - 1)) (by omega) d (k - 1) d rfl
          · exact ih ((d - 1) + (k - 1)) (by omega) (d - 1) (k - 1) (d - 1) rfl
        · apply sum_congr rfl
          intro i _
          congr 1
          have hi := mem_Icc.mp i.property
          exact ih ((d + 1 - i.val) + (k + 1 - i.val)) (by omega)
            _ _ _ rfl
      by_cases hcol : d = k
      · subst k
        have hdlt : d < r := by omega
        rw [hf.col r d hd hdlt, hg.col r d hd hdlt]
        apply sum_congr rfl
        intro j _
        congr 1
        exact ih (j.val + d) (by have hj := j.isLt; omega) _ _ _ rfl
      have hdr : d < r := by omega
      have hdk : d < k := by omega
      rw [hf.interior r k d hd hdr hdk, hg.interior r k d hd hdr hdk]
      congr 1
      · congr 1
        · exact ih (r + (k - 1)) (by omega) r (k - 1) d rfl
        · exact ih ((r - 1) + (k - 1)) (by omega) (r - 1) (k - 1) (d - 1) rfl
      · apply sum_congr rfl
        intro i _
        congr 2
        have hi := mem_Icc.mp i.property
        exact ih ((r + 1 - i.val) + (k + 1 - i.val)) (by omega) _ _ _ rfl
  intro r k d
  exact h (r + k) r k d rfl

end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational
open Finset

end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational
open Finset

end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational
open PowerSeries
noncomputable section

def q : (PowerSeries ℚ) := X * R

def A : (PowerSeries ℚ) := 1 + q

def U : (PowerSeries ℚ) := D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.D⁻¹

def V : (PowerSeries ℚ) := (den : PowerSeries ℚ)⁻¹

def G (a b : ℕ) : (PowerSeries ℚ) := C (1 / 2 : ℚ) * A * (R ^ b * U ^ a + V ^ a)

lemma q_constant : constantCoeff q = 0 := by simp [q]

private lemma U_right : (1 - q) * U = 1 := by
  apply PowerSeries.mul_inv_cancel
  simp [q_constant]

lemma U_left : U * (1 - q) = 1 := by simpa [mul_comm] using U_right

private lemma V_right : (1 - (X : (PowerSeries ℚ))) * V = 1 := by
  apply PowerSeries.mul_inv_cancel
  simp

lemma V_left : V * (1 - (X : (PowerSeries ℚ))) = 1 := by simpa [mul_comm] using V_right

private lemma R_unit : R * (1 - q) = 1 + q := by
  dsimp [q]
  linear_combination R_eq

lemma R_as_q : R = (1 + q) * U := by
  calc
    R = R * ((1 - q) * U) := by rw [U_right, mul_one]
    _ = (1 + q) * U := by rw [← mul_assoc, R_unit]

private lemma A_R_minus : A * (R - 1) = 2 * X * R ^ 2 := by
  dsimp [A, q]
  linear_combination R_eq

lemma half_cancel : (2 : (PowerSeries ℚ)) * C (1 / 2 : ℚ) = 1 := by
  have ht : (2 : (PowerSeries ℚ)) = 1 + 1 := by ring
  rw [ht]
  simp only [add_mul, one_mul, ← map_add]
  norm_num

private lemma G_zero : G 0 0 = A := by
  dsimp [G]
  simp only [pow_zero, one_mul]
  linear_combination A * half_cancel

private lemma G_horizontal (a b : ℕ) : G a (b + 1) = R * G a b - X * R ^ 2 * V ^ a := by
  dsimp [G]
  rw [pow_succ]
  have h := A_R_minus
  have hh := half_cancel
  linear_combination -C (1 / 2 : ℚ) * V ^ a * h - X * R ^ 2 * V ^ a * hh

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
open PowerSeries Finset
noncomputable section

private lemma lagrange_source (B u Q : (PowerSeries ℚ)) (hu : constantCoeff u = 0)
    (heq : u = X * Q.subst u) (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) * coeff (n + 1) (B.subst u) =
      coeff n (derivative ℚ B * Q ^ (n + 1)) := by
  rw [subst_coeff B u hu, mul_sum, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hzero : coeff (n + 1) (u ^ 0) = 0 := by simp
  rw [sum_range_succ', hzero, mul_zero, mul_zero, add_zero]
  apply sum_congr rfl
  intro p hp
  rw [coeff_derivative]
  have hlag := D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient
    u Q hu heq (n + 1) (p + 1) (by omega) (by simpa using mem_range.mp hp)
  have e : n + 1 - (p + 1) = n - p := by omega
  rw [e] at hlag
  push_cast at hlag ⊢
  linear_combination coeff (p + 1) B * hlag

def transform (B Q : (PowerSeries ℚ)) : (PowerSeries ℚ) := mk fun n => coeff n (B * Q ^ n)

lemma transform_eq (B Q Qinv u : (PowerSeries ℚ)) (hu : constantCoeff u = 0)
    (heq : u = X * Q.subst u) (hinv : Qinv * Q = 1) :
    transform B Q = (B * Qinv).subst u * derivative ℚ u := by
  have hs : HasSubst u := HasSubst.of_constantCoeff_zero' hu
  rw [← derivative_primitive (B * Qinv), ← derivative_subst hs]
  ext n
  rw [transform, coeff_mk, coeff_derivative]
  have hlag := lagrange_source (primitive (B * Qinv)) u Q hu heq n
  rw [derivative_primitive] at hlag
  have he : (B * Qinv) * Q ^ (n + 1) = B * Q ^ n := by
    rw [pow_succ]
    calc
      B * Qinv * (Q ^ n * Q) = B * Q ^ n * (Qinv * Q) := by ring
      _ = B * Q ^ n := by rw [hinv, mul_one]
  rw [he] at hlag
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hlag.symm

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
open PowerSeries
noncomputable section

def z : (PowerSeries ℚ) := X * V ^ 2

private lemma Cat_equation : P13CatalanLagrangeBridge.catalanUnit = 1 + X * P13CatalanLagrangeBridge.catalanUnit ^ 2 := by
  simpa only [add_comm, mul_comm] using P13CatalanLagrangeBridge.catalanUnit_equation.symm

lemma z_constant : constantCoeff z = 0 := by simp [z]

private lemma z_w : z * den ^ 2 = X := by
  dsimp [z, den]
  calc
    X * V ^ 2 * (1 - X) ^ 2 = X * (V * (1 - X)) ^ 2 := by ring
    _ = X := by rw [V_left]; ring

private lemma Cat_subst_equation (y : (PowerSeries ℚ)) (hy : constantCoeff y = 0) :
    P13CatalanLagrangeBridge.catalanUnit.subst y = 1 + y * (P13CatalanLagrangeBridge.catalanUnit.subst y) ^ 2 := by
  have hs : HasSubst y := HasSubst.of_constantCoeff_zero' hy
  have h := congrArg (substAlgHom hs) Cat_equation
  simpa only [coe_substAlgHom, map_add, map_mul, map_one, map_pow, subst_X hs] using h

private lemma Cat_z : P13CatalanLagrangeBridge.catalanUnit.subst z = den * R := by
  have hcandidate : den * R = 1 + z * (den * R) ^ 2 := by
    have hr := R_eq
    have hz := z_w
    dsimp [den] at hr hz ⊢
    linear_combination hr - R ^ 2 * hz
  have hcat := Cat_subst_equation z z_constant
  have hz := z_constant
  exact quadratic_unique hz hcat hcandidate

private lemma Cat_neg_z : P13CatalanLagrangeBridge.catalanUnit.subst (-z) = den := by
  have hcandidate : den = 1 + (-z) * den ^ 2 := by
    have hz := z_w
    dsimp [den] at hz ⊢
    linear_combination hz
  have hz : constantCoeff (-z) = 0 := by simp [z_constant]
  have hcat := Cat_subst_equation (-z) hz
  exact quadratic_unique hz hcat hcandidate

lemma even_Catalan_identity : 1 + z * (P13CatalanLagrangeBridge.catalanUnit.subst z + P13CatalanLagrangeBridge.catalanUnit.subst (-z)) = A * V := by
  rw [Cat_z, Cat_neg_z]
  calc
    1 + z * (den * R + den) = 1 + X * (V * (1 - X)) * V * (R + 1) := by
      dsimp [z, den]
      ring
    _ = 1 + X * V * (R + 1) := by rw [V_left, mul_one]
    _ = A * V := by
      dsimp [A, q]
      linear_combination -V_left

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
open PowerSeries Finset
noncomputable section

private lemma R_coeff (n : ℕ) : coeff n R = (Nat.largeSchroder n : ℚ) := by simp [R]

private lemma U_constant : constantCoeff U = 1 := by simp [U, D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.D]

private lemma V_constant : constantCoeff V = 1 := by simp [V, den]

private lemma G_constant (a b : ℕ) : constantCoeff (G a b) = 1 := by
  simp only [G, A, map_mul, map_add, map_one, map_pow, constantCoeff_C, q_constant, R_zero, U_constant, V_constant]
  norm_num

private lemma G_diagonal (d : ℕ) (hd : 0 < d) : coeff d (G 0 0) =
    (Nat.largeSchroder (d - 1) : ℚ) := by
  rw [G_zero]
  cases d with
  | zero => omega
  | succ d => simp [A, q, R_coeff, coeff_succ_X_mul]

private lemma V_power_coeff (a n : ℕ) (ha : 0 < a) : coeff n (V ^ a) =
    (Nat.choose (a - 1 + n) n : ℚ) := by
  have he : V ^ a = (invOneSubPow ℚ a).val := by
    have hleft : (1 - (X : (PowerSeries ℚ))) ^ a * V ^ a = 1 := by
      rw [← mul_pow, V_right, one_pow]
    have hright : (invOneSubPow ℚ a).val * (1 - (X : (PowerSeries ℚ))) ^ a = 1 := by
      simpa only [invOneSubPow_inv_eq_one_sub_pow] using (invOneSubPow ℚ a).val_inv
    calc
      V ^ a = (invOneSubPow ℚ a).val * ((1 - X) ^ a * V ^ a) := by rw [← mul_assoc, hright, one_mul]
      _ = (invOneSubPow ℚ a).val := by rw [hleft, mul_one]
  rw [he, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℚ a ha, coeff_mk]
  have hs : Nat.choose (a - 1 + n) (a - 1) = Nat.choose (a - 1 + n) n :=
    Nat.choose_symm_of_eq_add rfl
  exact_mod_cast hs

private lemma G_source_horizontal (a b : ℕ) :
    G a (b + 1) = G a b + X * (1 + R) * G a (b + 1) - X * R * V ^ a := by
  have he : (1 - X - X * R) * R = 1 := by
    linear_combination R_eq
  have hh := G_horizontal a b
  linear_combination hh * (1 - X - X * R) +
    (G a b - X * R * V ^ a) * he

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
open PowerSeries Finset
noncomputable section

private lemma finite_subst_large (B u : (PowerSeries ℚ)) (hu : constantCoeff u = 0) (n m : ℕ) (hn : n ≤ m) :
    coeff n (B.subst u) = ∑ p ∈ range (m + 1), coeff p B * coeff n (u ^ p) := by
  rw [subst_coeff B u hu n]
  apply sum_subset
  · exact range_mono (by omega)
  · intro p hp hpn
    have hb : n < p := by simp only [mem_range] at hpn; omega
    simp [pow_low hu hb]

lemma finite_mul_subst (A B u : (PowerSeries ℚ)) (hu : constantCoeff u = 0) (n : ℕ) :
    coeff n (A * B.subst u) =
      ∑ p ∈ range (n + 1), coeff p B * coeff n (A * u ^ p) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hf (i : ℕ) : coeff (n - i) (B.subst u) =
      ∑ p ∈ range (n + 1), coeff p B * coeff (n - i) (u ^ p) :=
    finite_subst_large B u hu (n - i) n (by omega)
  simp_rw [hf, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

lemma mul_pow_vanish (A u : (PowerSeries ℚ)) (hu : constantCoeff u = 0) (n p : ℕ) (h : n < p) :
    coeff n (A * u ^ p) = 0 := by
  apply PowerSeries.coeff_mul_of_lt_order
  exact (show (n : ENat) < (p : ENat) by exact_mod_cast h).trans_le
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero p hu)

lemma even_sum_reindex (n : ℕ) (f : ℕ → ℚ) :
    (∑ p ∈ range (n + 1), if Even p then f p else 0) =
      ∑ i ∈ range (n + 1), if 2 * i ≤ n then f (2 * i) else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  apply sum_bij (fun p _ => p / 2)
  · intro p hp
    obtain ⟨hpn, he⟩ := mem_filter.mp hp
    obtain ⟨j, hj⟩ := he
    apply mem_filter.mpr
    constructor
    · apply mem_range.mpr
      have hp' := mem_range.mp hpn
      omega
    · have hp' := mem_range.mp hpn
      omega
  · intro p hp q hq heq
    obtain ⟨_, hp⟩ := mem_filter.mp hp
    obtain ⟨_, hq⟩ := mem_filter.mp hq
    obtain ⟨i, hi⟩ := hp
    obtain ⟨j, hj⟩ := hq
    omega
  · intro i hi
    obtain ⟨hir, hib⟩ := mem_filter.mp hi
    refine ⟨2 * i, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, ?_⟩
    · exact ⟨i, by omega⟩
    · omega
  · intro p hp
    obtain ⟨_, he⟩ := mem_filter.mp hp
    obtain ⟨i, hi⟩ := he
    congr 1
    omega

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
open PowerSeries Finset
noncomputable section

private lemma V_power_constant (a : ℕ) : constantCoeff (V ^ a) = 1 := by simp [V_constant]

private lemma G_horizontal_coeff_succ (a b n : ℕ) :
    coeff (n + 1) (G a (b + 1)) = coeff (n + 1) (G a b) + coeff n (G a (b + 1)) +
      ∑ j ∈ range n, (Nat.largeSchroder j : ℚ) *
        (coeff (n - j) (G a (b + 1)) - coeff (n - j) (V ^ a)) := by
  have hh := congrArg (coeff (n + 1)) (G_source_horizontal a b)
  simp only [map_add, map_sub] at hh
  have hfirst : X * (1 + R) * G a (b + 1) = X * (G a (b + 1) + R * G a (b + 1)) := by ring
  have hlast : X * R * V ^ a = X * (R * V ^ a) := by ring
  rw [hfirst, hlast, coeff_succ_X_mul, coeff_succ_X_mul, map_add] at hh
  rw [coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, sum_range_succ] at hh
  simp only [Nat.sub_self, coeff_zero_eq_constantCoeff_apply, G_constant,
    V_power_constant, mul_one] at hh
  simp_rw [R_coeff] at hh
  simp_rw [mul_sub]
  rw [sum_sub_distrib]
  linear_combination hh

private lemma range_to_Icc (d : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range (d - 1), f j) = ∑ i ∈ Icc 2 d, f (i - 2) := by
  apply sum_bij (fun j _ => j + 2)
  · intro j hj
    have hh := mem_range.mp hj
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj l hl he
    omega
  · intro i hi
    have hh := mem_Icc.mp hi
    exact ⟨i - 2, mem_range.mpr (by omega), by omega⟩
  · intro j hj
    congr 1

private lemma G_horizontal_coeff (a b d : ℕ) (hd : 0 < d) :
    coeff d (G a (b + 1)) = coeff d (G a b) + coeff (d - 1) (G a (b + 1)) +
      ∑ i ∈ Icc 2 d, (Nat.largeSchroder (i - 2) : ℚ) *
        (coeff (d + 1 - i) (G a (b + 1)) - coeff (d + 1 - i) (V ^ a)) := by
  have hh := G_horizontal_coeff_succ a b (d - 1)
  rw [show d - 1 + 1 = d by omega, range_to_Icc] at hh
  rw [hh]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hb := mem_Icc.mp hi
  rw [show d - 1 - (i - 2) = d + 1 - i by omega]

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
open PowerSeries Finset
noncomputable section

private lemma V_subst_q : V.subst q = U := by
  have hs : HasSubst q := HasSubst.of_constantCoeff_zero' q_constant
  have h := congrArg (substAlgHom hs) V_left
  simp only [map_mul, map_one, map_sub, coe_substAlgHom, subst_X hs] at h
  calc
    V.subst q = V.subst q * ((1 - q) * U) := by rw [U_right, mul_one]
    _ = U := by rw [← mul_assoc, h, one_mul]

private lemma G_col_transform (a d : ℕ) :
    coeff d (G a 0) = ∑ m ∈ range (d + 1),
      coeff m (V ^ a) * coeff (d - m) (G 0 m) := by
  have hs : HasSubst q := HasSubst.of_constantCoeff_zero' q_constant
  have hU : (V ^ a).subst q = U ^ a := by rw [subst_pow hs, V_subst_q]
  have he : G a 0 = C (1 / 2 : ℚ) * (A * (V ^ a).subst q + V ^ a * A) := by
    rw [hU]
    dsimp [G]
    simp only [pow_zero, one_mul]
    ring
  rw [he, coeff_C_mul, map_add, D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal.finite_mul_subst A (V ^ a) q q_constant,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hmd : m ≤ d := by have hh := mem_range.mp hm; omega
  have hp : A * q ^ m = X ^ m * (A * R ^ m) := by dsimp [q]; rw [mul_pow]; ring
  rw [hp, coeff_X_pow_mul', if_pos hmd]
  have hG : G 0 m = C (1 / 2 : ℚ) * (A * R ^ m + A) := by
    dsimp [G]; simp only [pow_zero, mul_one]; ring
  rw [hG, coeff_C_mul, map_add]
  ring

private lemma G_col_coeff (a d : ℕ) (ha : 0 < a) :
    coeff d (G a 0) = ∑ j ∈ range (d + 1),
      coeff j (G 0 (d - j)) * (Nat.choose (a + d - j - 1) (d - j) : ℚ) := by
  rw [G_col_transform]
  simp_rw [V_power_coeff a _ ha]
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hdj : j ≤ d := by have hh := mem_range.mp hj; omega
  have he : d + 1 - 1 - j = d - j := by omega
  rw [he, Nat.sub_sub_self hdj]
  have he' : a - 1 + (d - j) = a + d - j - 1 := by omega
  rw [he']
  ring

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series

namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Diagonal D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series
open PowerSeries Finset
noncomputable section

def Cnt (r k d : ℕ) : ℚ :=
  if r < d ∨ k < d then 0 else coeff d (G (r - d) (k - d))

lemma Cnt_admissible (r k d : ℕ) (hr : d ≤ r) (hk : d ≤ k) :
    Cnt r k d = coeff d (G (r - d) (k - d)) := by
  simp only [Cnt, if_neg (show ¬ (r < d ∨ k < d) by omega)]

private lemma Cnt_outside (r k d : ℕ) (h : r < d ∨ k < d) : Cnt r k d = 0 := by simp [Cnt, h]

private lemma Cnt_zero (r k : ℕ) : Cnt r k 0 = 1 := by
  rw [Cnt_admissible r k 0 (by omega) (by omega), coeff_zero_eq_constantCoeff_apply, G_constant]

private lemma Cnt_diagonal (d : ℕ) (hd : 0 < d) : Cnt d d d = (Nat.largeSchroder (d - 1) : ℚ) := by
  rw [Cnt_admissible d d d le_rfl le_rfl, Nat.sub_self, G_diagonal d hd]

private lemma Cnt_left (r k d : ℕ) (hr : d ≤ r) (hk : d < k) :
    Cnt r (k - 1) d = coeff d (G (r - d) (k - d - 1)) := by
  rw [Cnt_admissible _ _ _ hr (by omega), show k - 1 - d = k - d - 1 by omega]

private lemma Cnt_pred (r k d : ℕ) (hd : 0 < d) (hr : d ≤ r) (hk : d ≤ k) :
    Cnt (r - 1) (k - 1) (d - 1) = coeff (d - 1) (G (r - d) (k - d)) := by
  rw [Cnt_admissible _ _ _ (by omega) (by omega),
    show r - 1 - (d - 1) = r - d by omega,
    show k - 1 - (d - 1) = k - d by omega]

private lemma Cnt_shift (r k d i : ℕ) (hr : d ≤ r) (hk : d ≤ k) (hi : i ≤ d + 1) :
    Cnt (r + 1 - i) (k + 1 - i) (d + 1 - i) =
      coeff (d + 1 - i) (G (r - d) (k - d)) := by
  rw [Cnt_admissible _ _ _ (by omega) (by omega),
    show r + 1 - i - (d + 1 - i) = r - d by omega,
    show k + 1 - i - (d + 1 - i) = k - d by omega]

private lemma Cnt_row (r k : ℕ) (hr : 0 < r) (hk : r < k) :
    Cnt r k r = Cnt r (k - 1) r + Cnt (r - 1) (k - 1) (r - 1) +
      ∑ i : ↥(Icc 2 r), (Nat.largeSchroder (i.val - 2) : ℚ) *
        Cnt (r + 1 - i.val) (k + 1 - i.val) (r + 1 - i.val) := by
  rw [Cnt_admissible _ _ _ le_rfl (by omega), Cnt_left _ _ _ le_rfl hk,
    Cnt_pred _ _ _ hr le_rfl (by omega), Nat.sub_self]
  have hh := G_horizontal_coeff 0 (k - r - 1) r hr
  rw [show k - r - 1 + 1 = k - r by omega] at hh
  rw [hh]
  congr 1
  rw [← Finset.sum_subtype (Icc 2 r) (fun _ => Iff.rfl)
    (fun i : ℕ => (Nat.largeSchroder (i - 2) : ℚ) *
      Cnt (r + 1 - i) (k + 1 - i) (r + 1 - i))]
  apply sum_congr rfl
  intro i hi
  have hb := mem_Icc.mp hi
  rw [Cnt_shift _ _ _ _ le_rfl (by omega) (by omega), Nat.sub_self, pow_zero,
    coeff_one, if_neg (by omega : r + 1 - i ≠ 0), sub_zero]

private lemma Cnt_col (r k : ℕ) (hk : 0 < k) (hr : k < r) :
    Cnt r k k = ∑ j : Fin (k + 1), Cnt j.val k j.val *
      (Nat.choose (r - j.val - 1) (k - j.val) : ℚ) := by
  rw [Cnt_admissible _ _ _ (by omega) le_rfl, Nat.sub_self,
    G_col_coeff (r - k) k (by omega)]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => Cnt j k j *
    (Nat.choose (r - j - 1) (k - j) : ℚ)) (k + 1)]
  apply sum_congr rfl
  intro j hj
  have hb : j ≤ k := by have hh := mem_range.mp hj; omega
  rw [Cnt_admissible _ _ _ le_rfl hb, Nat.sub_self]
  rw [show r - k + k - j - 1 = r - j - 1 by omega]

private lemma Cnt_interior (r k d : ℕ) (hd : 0 < d) (hr : d < r) (hk : d < k) :
    Cnt r k d = Cnt r (k - 1) d + Cnt (r - 1) (k - 1) (d - 1) +
      ∑ i : ↥(Icc 2 d), (Nat.largeSchroder (i.val - 2) : ℚ) *
        (Cnt (r + 1 - i.val) (k + 1 - i.val) (d + 1 - i.val) -
          (Nat.choose (r - i.val) (d + 1 - i.val) : ℚ)) := by
  rw [Cnt_admissible _ _ _ (by omega) (by omega), Cnt_left _ _ _ (by omega) hk,
    Cnt_pred _ _ _ hd (by omega) (by omega)]
  have hh := G_horizontal_coeff (r - d) (k - d - 1) d hd
  rw [show k - d - 1 + 1 = k - d by omega] at hh
  rw [hh]
  congr 1
  rw [← Finset.sum_subtype (Icc 2 d) (fun _ => Iff.rfl)
    (fun i : ℕ => (Nat.largeSchroder (i - 2) : ℚ) *
      (Cnt (r + 1 - i) (k + 1 - i) (d + 1 - i) -
        (Nat.choose (r - i) (d + 1 - i) : ℚ)))]
  apply sum_congr rfl
  intro i hi
  have hb := mem_Icc.mp hi
  rw [Cnt_shift _ _ _ _ (by omega) (by omega) (by omega),
    V_power_coeff _ _ (by omega : 0 < r - d),
    show r - d - 1 + (d + 1 - i) = r - i by omega]

private lemma Cnt_spec : D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational.rationalRecurrenceSpec Cnt :=
  ⟨Cnt_outside, Cnt_zero, Cnt_diagonal, Cnt_row, Cnt_col, Cnt_interior⟩

private lemma T_cast_spec : D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational.rationalRecurrenceSpec (fun r k d => (T r k d : ℚ)) := by
  constructor
  · intro r k d h
    rw [T_outside _ _ _ h]
    norm_num
  · intro r k
    rw [T_zero]
    norm_num
  · intro d hd
    rw [T_diagonal _ hd]
    norm_cast
  · intro r k hr hk
    rw [T_row _ _ hr hk]
    push_cast
    rfl
  · intro r k hk hr
    rw [T_col _ _ hk hr]
    push_cast
    rfl
  · intro r k d hd hr hk
    rw [T_interior _ _ _ hd hr hk]
    push_cast
    rfl

lemma series_eq_T (r k d : ℕ) : Cnt r k d = (T r k d : ℚ) :=
  D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Rational.rational_recurrence_unique Cnt (fun r k d => (T r k d : ℚ)) Cnt_spec T_cast_spec r k d

end
end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries.Series


namespace D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
set_option autoImplicit false
open Rational Series Finset

theorem recurrence_unique (f : ℕ → ℕ → ℕ → ℤ) (hf : RecurrenceSpec f) :
    ∀ r k d, f r k d = T r k d := by
  have hc : Rational.rationalRecurrenceSpec (fun r k d => (f r k d : ℚ)) := by
    constructor
    · intro r k d h
      exact_mod_cast hf.outside r k d h
    · intro r k
      exact_mod_cast hf.zero r k
    · intro d hd
      exact_mod_cast hf.diagonal d hd
    · intro r k hr hk
      exact_mod_cast hf.row r k hr hk
    · intro r k hk hr
      exact_mod_cast hf.col r k hk hr
    · intro r k d hd hr hk
      exact_mod_cast hf.interior r k d hd hr hk
  intro r k d
  exact_mod_cast Rational.rational_recurrence_unique _ _ hc Series.T_cast_spec r k d

end D5.S3.Combinatorics.AlternatingSignRectangles.RecurrenceSeries
