/- GID: D5/S1/Recurrence/Invariants/MatharA000159Recurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/MatharA000159Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The three-hit ménage coefficients satisfy Mathar's six-step recurrence. -/

/-
proof_shape: factorialSeries: bind-only; consumers: factorial_equation, theta_one, theta_two,
  theta_three, factorialPullback, pullback_differential, weighted_euler, model_reduction.
proof_shape: factorial_equation: bind-only; consumers: theta_one, pullback_differential.
proof_shape: theta_one: bind-only; consumers: theta_two, theta_three, model_reduction.
proof_shape: theta_two: bind-only; consumers: theta_three, model_reduction.
proof_shape: theta_three: bind-only; consumers: model_reduction.
proof_shape: Z: bind-only; consumers: factorialPullback, pullback_differential, degreeThreeModel,
  model_coefficient, model_reduction.
proof_shape: factorialPullback: bind-only; consumers: pullback_differential, model_reduction,
  degree_three_diagonal, result.
proof_shape: pullback_differential: bind-only; consumers: result.
proof_shape: r: bind-only; consumers: differential_certificate, model_reduction,
  degree_three_diagonal.
proof_shape: s: bind-only; consumers: differential_certificate, model_reduction,
  degree_three_diagonal.
proof_shape: d: bind-only; consumers: differential_certificate, model_reduction,
  degree_three_diagonal.
proof_shape: q: bind-only; consumers: differential_certificate, result.
proof_shape: b: bind-only; consumers: differential_certificate, result.
proof_shape: c: bind-only; consumers: differential_certificate, result.
proof_shape: p2: bind-only; consumers: differential_certificate, coefficient_recurrence, result.
proof_shape: p1: bind-only; consumers: differential_certificate, coefficient_recurrence, result.
proof_shape: p0: bind-only; consumers: differential_certificate, coefficient_recurrence, result.
proof_shape: forcing: bind-only; consumers: differential_certificate, coefficient_recurrence,
  result.
proof_shape: differential_certificate: bind-only; consumers: result.
proof_shape: coefficient_recurrence: bind-only; consumers: result.
proof_shape: U: bind-only; consumers: a, hit_coefficient_sum, source_series_eq_model.
proof_shape: a: bind-only; consumers: claim, hit_coefficient_sum, sourceSeries,
  source_series_eq_model, result.
proof_shape: claim: bind-only; consumers: result.
proof_shape: hit_coefficient_sum: bind-only; consumers: source_series_eq_model.
proof_shape: rook_decomposition: bind-only; consumers: source_series_eq_model.
proof_shape: prefactor_subst_coeff: bind-only; consumers: model_coefficient.
proof_shape: plusSeries: bind-only; consumers: degreeThreeModel, model_coefficient,
  weighted_euler, model_reduction.
proof_shape: minusSeries: bind-only; consumers: degreeThreeModel, model_coefficient,
  weighted_euler, model_reduction.
proof_shape: binomial_weights: bind-only; consumers: weighted_euler.
proof_shape: three_hit_binomial_transfer: bind-only; consumers: source_series_eq_model.
proof_shape: sourceSeries: bind-only; consumers: source_series_eq_model, degree_three_diagonal,
  result.
proof_shape: degreeThreeModel: bind-only; consumers: model_coefficient, source_series_eq_model,
  model_reduction, degree_three_diagonal.
proof_shape: model_coefficient: bind-only; consumers: source_series_eq_model.
proof_shape: source_series_eq_model: bind-only; consumers: degree_three_diagonal.
proof_shape: weighted_euler: bind-only; consumers: model_reduction.
proof_shape: model_reduction: bind-only; consumers: degree_three_diagonal.
proof_shape: degree_three_diagonal: bind-only; consumers: result.
proof_shape: result: bind-only; consumers: external named problem settlement.
escape_witness: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24479
admission_basis: open-problem-resolution (#24301; Proved).
Direct frozen dependencies: coeff_subst_sum, in prefactor_subst_coeff and its
consumers model_coefficient, source_series_eq_model, degree_three_diagonal, result;
all other declarations: none.
Dependency GID: D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.coeff_subst_sum
Dependency statement_id: sha256:6e74241c27837447560e3a5962da1004a411b276cdd7d64f7d2be9aa6fff2657
The polynomial U and its coefficient a use the OEIS expressions. The Euler
operator is written as X * derivative directly; the reciprocal (1 + X)⁻¹
is inlined. No duplicate operator or reciprocal alias is defined.
All identities are formal power-series identities over the rationals; no
convergence or inversion of X is assumed. The recurrence is asserted for n ≥ 9.
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
import Mathlib.RingTheory.PowerSeries.Binomial

/-! The coefficient of degree three in the ménage hit polynomial satisfies
Mathar's recurrence by a formal differential equation for the factorial series. -/

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open PowerSeries
private noncomputable def factorialSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.factorial n : ℚ)

private theorem factorial_equation :
    X ^ 2 * derivative factorialSeries + (X - 1) * factorialSeries = -1 := by
  ext n
  cases n with
  | zero => simp [factorialSeries]
  | succ n =>
    cases n with
    | zero => norm_num [pow_two, mul_assoc, sub_mul, factorialSeries]
    | succ n =>
      simp only [pow_two, mul_assoc, sub_mul, map_add, map_sub,
        coeff_succ_X_mul, coeff_derivative, factorialSeries, coeff_mk,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        one_mul, map_neg, coeff_one, Nat.succ_ne_zero, ite_false, neg_zero]
      ring

private theorem theta_one :
    X * (X * derivative factorialSeries) = (1 - X) * factorialSeries - 1 := by
  linear_combination factorial_equation

private theorem theta_two :
    X ^ 2 * (X * derivative ((X * derivative factorialSeries))) =
      (X ^ 2 - 3 * X + 1) * factorialSeries + 2 * X - 1 := by
  have hd := congrArg (derivative (R := ℚ)) theta_one
  simp only [Derivation.leibniz, map_sub, derivative_X, derivative_one,
    sub_zero, zero_sub, smul_eq_mul, mul_one, one_mul] at hd ⊢
  have h1 := theta_one
  linear_combination X ^ 2 * hd + (1 - 2 * X) * h1

private theorem theta_three :
    X ^ 3 * (X * derivative ((X * derivative ((X * derivative factorialSeries))))) =
      (-X ^ 3 + 7 * X ^ 2 - 6 * X + 1) * factorialSeries - 3 * X ^ 2 + 5 * X - 1 := by
  have hc2 : derivative (2 : PowerSeries ℚ) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative (R := ℚ)).map_natCast 2
  have hc3 : derivative (3 : PowerSeries ℚ) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative (R := ℚ)).map_natCast 3
  have hd := congrArg (derivative (R := ℚ)) theta_two
  simp only [Derivation.leibniz, map_sub, map_add, derivative_X, derivative_one,
    derivative_pow, hc2, hc3, smul_eq_mul, sub_zero, zero_sub, one_mul, mul_one,
    zero_mul, add_zero, sub_self] at hd ⊢
  have h1 := theta_one
  have h2 := theta_two
  simp only [Derivation.leibniz, derivative_X, smul_eq_mul, mul_one, one_mul] at h2
  linear_combination X ^ 2 * hd - 2 * X * h2 +
    (X ^ 2 - 3 * X + 1) * h1

private noncomputable def Z : PowerSeries ℚ := X * ((1 + (X : PowerSeries ℚ))⁻¹) ^ 2
private noncomputable def factorialPullback : PowerSeries ℚ := factorialSeries.subst Z

private theorem pullback_differential :
    X ^ 2 * (1 + X) * derivative factorialPullback =
      (1 - X ^ 3) * factorialPullback + (X ^ 2 - 1) * (1 + X) := by
  let df : PowerSeries ℚ := (derivative factorialSeries).subst Z
  have hz : HasSubst Z := PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [Z])
  have hf := congrArg (substAlgHom (R := ℚ) hz) factorial_equation
  simp only [map_add, map_mul, map_pow, map_sub, map_neg, map_one,
    substAlgHom_X, coe_substAlgHom] at hf
  change Z^2 * df + (Z-1)*factorialPullback = -1 at hf
  have hu : (1 + (X : PowerSeries ℚ)) * ((1 + (X : PowerSeries ℚ))⁻¹) = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hV : derivative ((1 + (X : PowerSeries ℚ))⁻¹) = -((1 + (X : PowerSeries ℚ))⁻¹)^2 := by simp
  have hdz : (1 + X)^3 * derivative Z = 1 - (X : PowerSeries ℚ) := by
    rw [Z, Derivation.leibniz, derivative_X, derivative_pow, hV]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul]
    calc
      _ = ((1+X)*((1 + (X : PowerSeries ℚ))⁻¹))^2*(1+X) - 2*X*((1+X)*((1 + (X : PowerSeries ℚ))⁻¹))^3 := by ring
      _ = _ := by rw [hu]; ring
  have hz2 : (1 + X)^4 * Z^2 = (X : PowerSeries ℚ)^2 := by
    dsimp [Z]
    calc
      _ = X^2*((1+X)*((1 + (X : PowerSeries ℚ))⁻¹))^4 := by ring
      _ = _ := by rw [hu]; ring
  have hz1 : (1 + X)^4 * Z = (X : PowerSeries ℚ)*(1+X)^2 := by
    dsimp [Z]
    calc
      _ = X*(1+X)^2*((1+X)*((1 + (X : PowerSeries ℚ))⁻¹))^2 := by ring
      _ = _ := by rw [hu]; ring
  have hf4 : X^2*df + (X*(1+X)^2-(1+X)^4)*factorialPullback = -(1+X)^4 := by
    linear_combination (1+X)^4*hf - df*hz2 - factorialPullback*hz1
  have hd : (1+X)^3 * derivative factorialPullback = df*(1-X) := by
    unfold factorialPullback
    rw [derivative_subst hz]
    change (1+X)^3*(df * derivative Z) = df*(1-X)
    linear_combination df*hdz
  have hY : (1 + (X : PowerSeries ℚ)) ≠ 0 := by
    intro he
    have := congrArg constantCoeff he
    norm_num at this
  apply mul_left_cancel₀ (pow_ne_zero 2 hY)
  linear_combination X^2*hd + (1-X)*hf4

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence

set_option maxHeartbeats 1200000

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open PowerSeries
private noncomputable def r (x : (PowerSeries ℚ)) : (PowerSeries ℚ) := -2 * (2*x^5-3*x^4-5*x^3-4*x^2-3*x-2)
private noncomputable def s (x : (PowerSeries ℚ)) : (PowerSeries ℚ) := 2 * (2*x^5-x^4-8*x^3-7*x^2-5*x-2)
private noncomputable def d (x : (PowerSeries ℚ)) : (PowerSeries ℚ) := 3 * (1+x)^2
private noncomputable def q (x : (PowerSeries ℚ)) : (PowerSeries ℚ) := x^2*(1+x)
private noncomputable def b (x : (PowerSeries ℚ)) : (PowerSeries ℚ) := 1-x^3
private noncomputable def c (x : (PowerSeries ℚ)) : (PowerSeries ℚ) := (x^2-1)*(1+x)
private noncomputable def p2 (x : (PowerSeries ℚ)) : (PowerSeries ℚ) :=
  -375862*x^7-405481*x^6+746598*x^5+1280831*x^4+504614*x^3
private noncomputable def p1 (x : (PowerSeries ℚ)) : (PowerSeries ℚ) :=
  -375862*x^7-35945*x^6+2525682*x^5+2312643*x^4-993731*x^3-1849143*x^2-504614*x
private noncomputable def p0 (x : (PowerSeries ℚ)) : (PowerSeries ℚ) :=
  -1133912*x^6+2249705*x^5+2743028*x^4-3357337*x^3-3210883*x^2+2259779*x+2082154
private noncomputable def forcing (x : (PowerSeries ℚ)) : (PowerSeries ℚ) := 1136624*x^3-10348*x^4+1516100*x^5

private theorem differential_certificate (A B : (PowerSeries ℚ))
    (hA : d X * A = r X * B + s X)
    (hB : q X * derivative B = b X * B + c X) :
    p2 X * derivative (derivative A) + p1 X * derivative A + p0 X * A = forcing X := by
  have hc2 : derivative (2 : (PowerSeries ℚ)) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative (R := ℚ)).map_natCast 2
  have hc3 : derivative (3 : (PowerSeries ℚ)) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative (R := ℚ)).map_natCast 3
  have hc4 : derivative (4 : (PowerSeries ℚ)) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative (R := ℚ)).map_natCast 4
  have hc5 : derivative (5 : (PowerSeries ℚ)) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative (R := ℚ)).map_natCast 5
  have hc7 : derivative (7 : (PowerSeries ℚ)) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative (R := ℚ)).map_natCast 7
  have hc8 : derivative (8 : (PowerSeries ℚ)) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative (R := ℚ)).map_natCast 8
  have ha1 := congrArg (derivative (R := ℚ)) hA
  have ha2 := congrArg (derivative (R := ℚ)) ha1
  have hb1 := congrArg (derivative (R := ℚ)) hB
  dsimp [r, s, d, q, b, c] at hA hB ha1 ha2 hb1
  simp only [Derivation.leibniz, map_add, map_sub, map_neg, derivative_pow,
    derivative_X, derivative_one, Derivation.map_natCast, hc2, hc3, hc4, hc5, hc7, hc8, map_zero, neg_zero, smul_eq_mul, mul_one, one_mul,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub,
    pow_zero, pow_one, Nat.reduceSub, Nat.cast_ofNat] at ha1 ha2 hb1
  have hd : d (X : (PowerSeries ℚ)) ≠ 0 := by
    intro hz
    have hc := congrArg constantCoeff hz
    norm_num [d, map_ofNat] at hc
  apply mul_left_cancel₀ hd
  dsimp [d, p2, p1, p0, forcing]
  linear_combination
    (-X^3*(X+1)*(375862*X^3+29619*X^2-776217*X-504614)) * ha2 +
    (-X*(375862*X^6-1467503*X^5-2644158*X^4+792225*X^3+3012187*X^2+1849143*X+504614)) * ha1 +
    (-382188*X^6-685301*X^5+448956*X^4-1031249*X^3-521825*X^2+3269007*X+2082154) * hA +
    (2*X*(375862*X^3+29619*X^2-776217*X-504614)*(2*X^5-3*X^4-5*X^3-4*X^2-3*X-2)) * hb1 +
    (4*(X+1)*(1133912*X^7-1494818*X^6-1547291*X^5+3866787*X^4+3383937*X^3-200660*X^2-3553163*X-2082154)) * hB

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence
namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open PowerSeries
private theorem coefficient_recurrence (A : (PowerSeries ℚ))
    (hE : p2 X * derivative (derivative A) + p1 X * derivative A + p0 X * A = forcing X)
    (n : ℕ) (hn : 9 ≤ n) :
    2 * (-252307 * (n : ℚ) + 1041077) * coeff n A +
    (504614 * (n : ℚ) ^ 2 - 3362985 * (n : ℚ) + 5118150) * coeff (n - 1) A +
    (1280831 * (n : ℚ) ^ 2 - 7397886 * (n : ℚ) + 6461565) * coeff (n - 2) A +
    (746598 * (n : ℚ) ^ 2 - 2913543 * (n : ℚ) - 1336090) * coeff (n - 3) A +
    (-405481 * (n : ℚ) ^ 2 + 6175011 * (n : ℚ) - 15469320) * coeff (n - 4) A +
    (-375862 * (n : ℚ) ^ 2 + 4098537 * (n : ℚ) - 8846430) * coeff (n - 5) A +
    2 * (-187931 * (n : ℚ) + 560630) * coeff (n - 6) A = 0 := by
  have hx (f : (PowerSeries ℚ)) : coeff n (X*f) = coeff (n-1) f := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      (coeff_succ_X_mul (n-1) f)
  have h := congrArg (coeff n) hE
  dsimp [p2, p1, p0, forcing] at h
  simp only [add_mul, sub_mul, neg_mul, mul_assoc, map_add, map_sub, map_neg,
    coeff_ofNat_mul, coeff_intCast_mul, coeff_X_pow_mul', coeff_X_pow, hx] at h
  simp (disch := omega) only [if_pos, if_neg, ite_true, ite_false] at h
  simp only [coeff_derivative] at h
  simp only [show n - 7 + 1 = n - 6 by omega,
    show n - 6 + 1 = n - 5 by omega, show n - 5 + 1 = n - 4 by omega,
    show n - 4 + 1 = n - 3 by omega, show n - 3 + 1 = n - 2 by omega,
    show n - 2 + 1 = n - 1 by omega, show n - 1 + 1 = n by omega] at h
  simp (disch := omega) only [Nat.cast_sub] at h
  norm_num only [Nat.cast_ofNat] at h
  linear_combination h

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence

open Polynomial

/-- A058087's displayed rook sum, with the source's U_0 = 1 convention. -/
noncomputable def U (n : ℕ) : Polynomial ℚ :=
  if n = 0 then 1 else
    ∑ k ∈ Finset.range (n + 1),
      C (((2 * n : ℕ) : ℚ) / ((2 * n - k : ℕ) : ℚ) *
        (Nat.choose (2 * n - k) k : ℚ) * (Nat.factorial (n - k) : ℚ)) *
        (X - 1) ^ k

/-- Descending row order gives A058087(n,n-3) = [t^3] U_n(t) for n ≥ 3. -/
noncomputable def a (n : ℕ) : ℚ := (U n).coeff 3

/-- Mathar's first A000159 FORMULA conjecture on the sequence's full domain. -/
def claim : Prop :=
  ∀ n : ℕ, 9 ≤ n →
    2 * (-252307 * (n : ℚ) + 1041077) * a n +
    (504614 * (n : ℚ) ^ 2 - 3362985 * (n : ℚ) + 5118150) * a (n - 1) +
    (1280831 * (n : ℚ) ^ 2 - 7397886 * (n : ℚ) + 6461565) * a (n - 2) +
    (746598 * (n : ℚ) ^ 2 - 2913543 * (n : ℚ) - 1336090) * a (n - 3) +
    (-405481 * (n : ℚ) ^ 2 + 6175011 * (n : ℚ) - 15469320) * a (n - 4) +
    (-375862 * (n : ℚ) ^ 2 + 4098537 * (n : ℚ) - 8846430) * a (n - 5) +
    2 * (-187931 * (n : ℚ) + 560630) * a (n - 6) = 0

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open Polynomial
private theorem hit_coefficient_sum (n : ℕ) (hn : n ≠ 0) :
    a n = ∑ k ∈ Finset.range (n + 1),
      (((2*n : ℕ) : ℚ) / ((2*n-k : ℕ) : ℚ) *
      (Nat.choose (2*n-k) k : ℚ) * (Nat.factorial (n-k) : ℚ)) *
      ((-1 : ℚ) ^ (k-3) * (Nat.choose k 3 : ℚ)) := by
  unfold a U
  rw [if_neg hn]
  simp only [finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simpa only [sub_eq_add_neg, C_neg, C_1] using
    (coeff_X_add_C_pow (-1 : ℚ) k 3)

private theorem rook_decomposition (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    (((2*n : ℕ) : ℚ) / ((2*n-k : ℕ) : ℚ)) *
      (Nat.choose (2*n-k) k : ℚ) =
    (Nat.choose (2*n-k) k : ℚ) +
      if k = 0 then 0 else (Nat.choose (2*n-k-1) (k-1) : ℚ) := by
  cases k with
  | zero =>
    have h2 : ((2*n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2*n ≠ 0)
    simp [h2, Nat.ne_of_gt hn]
  | succ k =>
    have hN : 0 < 2*n-(k+1) := by omega
    have hchoose := Nat.add_one_mul_choose_eq (2*n-(k+1)-1) k
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2*n-(k+1))] at hchoose
    have hc : ((k+1 : ℕ) : ℚ) * (Nat.choose (2*n-(k+1)) (k+1) : ℚ) =
        ((2*n-(k+1) : ℕ) : ℚ) * (Nat.choose (2*n-(k+1)-1) k : ℚ) := by
      exact_mod_cast (by simpa only [mul_comm] using hchoose.symm)
    have he : ((2*n : ℕ) : ℚ) = ((2*n-(k+1) : ℕ) : ℚ) + ((k+1 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : 2*n = (2*n-(k+1))+(k+1))
    simp only [Nat.succ_eq_add_one, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have hz : ((2*n-(k+1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2*n-(k+1) ≠ 0)
    field_simp [hz]
    linear_combination (Nat.choose (2*n-(k+1)) (k+1) : ℚ) * he + hc

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open PowerSeries Finset
open D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators (coeff_subst_sum)

private theorem prefactor_subst_coeff {R : Type*} [CommRing R]
    (f G W : PowerSeries R) (n : ℕ) :
    coeff n (G * f.subst (X * W)) =
      ∑ k ∈ range (n+1), coeff k f * coeff n (G * (X*W)^k) := by
  have hz : constantCoeff (X*W) = 0 := by simp
  have hsub (j : ℕ) (hj : j ≤ n) :
      coeff j (f.subst (X*W)) =
        ∑ k ∈ range (n+1), coeff k f * coeff j ((X*W)^k) := by
    rw [coeff_subst_sum hz]
    apply Finset.sum_subset (Finset.range_mono (by omega : j+1 ≤ n+1))
    intro k hkn hkj
    have hkj' : ¬ k ≤ j := by
      simp only [Finset.mem_range] at hkj
      omega
    simp only [mul_pow, coeff_X_pow_mul', if_neg hkj', mul_zero]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i G * coeff j (f.subst (X*W))) n]
  simp_rw [hsub _ (Nat.sub_le _ _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i G * coeff j ((X*W)^k)) n, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open PowerSeries
private noncomputable def plusSeries : PowerSeries ℚ := mk fun k =>
  ((Nat.choose (2*k+3) 3 : ℚ) + (Nat.choose (2*k+2) 2 : ℚ)) * (k.factorial : ℚ)
private noncomputable def minusSeries : PowerSeries ℚ := mk fun k =>
  (-(Nat.choose (2*k+3) 3 : ℚ) + (Nat.choose (2*k+2) 2 : ℚ)) * (k.factorial : ℚ)

private theorem binomial_weights (k : ℕ) :
    3*((Nat.choose (2*k+3) 3 : ℚ)+(Nat.choose (2*k+2) 2 : ℚ)) =
      4*(k:ℚ)^3+18*(k:ℚ)^2+20*(k:ℚ)+6 ∧
    3*(-(Nat.choose (2*k+3) 3 : ℚ)+(Nat.choose (2*k+2) 2 : ℚ)) =
      -4*(k:ℚ)^3-6*(k:ℚ)^2-2*(k:ℚ) := by
  have h3 : ((2*k+3).descFactorial 3 : ℚ) =
      ((3 : ℕ).factorial : ℚ)*(Nat.choose (2*k+3) 3 : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (2*k+3) 3
  have h2 : ((2*k+2).descFactorial 2 : ℚ) =
      ((2 : ℕ).factorial : ℚ)*(Nat.choose (2*k+2) 2 : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (2*k+2) 2
  norm_num only [Nat.descFactorial, Nat.factorial, Nat.reduceSub,
    Nat.sub_zero, Nat.cast_mul, Nat.cast_one, Nat.mul_one] at h3 h2
  simp (disch := omega) only [Nat.cast_sub, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at h3 h2
  constructor
  · linear_combination -h3/2 - 3*h2/2
  · linear_combination h3/2 - 3*h2/2

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
private theorem three_hit_binomial_transfer (k j : ℕ) (hj : 3 ≤ j) :
    (Nat.choose (2*k+j) j + Nat.choose (2*k+j-1) (j-1)) * Nat.choose j 3 =
      Nat.choose (2*k+3) 3 * Nat.choose (2*k+j) (j-3) +
      Nat.choose (2*k+3) 3 *
        (if j = 3 then 0 else Nat.choose (2*k+j-1) (j-4)) +
      Nat.choose (2*k+2) 2 * Nat.choose (2*k+j-1) (j-3) := by
  by_cases hj4 : 4 ≤ j
  · have h1 := Nat.choose_mul (n := 2*k+j) (k := j) (s := j-3) (Nat.sub_le _ _)
    rw [Nat.choose_symm hj,
      show 2*k+j-(j-3) = 2*k+3 by omega,
      show j-(j-3) = 3 by omega] at h1
    have h2 := Nat.choose_mul (n := 2*k+j-1) (k := j-1) (s := j-3) (by omega)
    rw [show j-3 = (j-1)-2 by omega,
      Nat.choose_symm (by omega : 2 ≤ j-1),
      show 2*k+j-1-((j-1)-2) = 2*k+2 by omega,
      show j-1-((j-1)-2) = 2 by omega] at h2
    have h3 := Nat.choose_mul (n := 2*k+j-1) (k := j-1) (s := j-4) (by omega)
    rw [show j-4 = (j-1)-3 by omega,
      Nat.choose_symm (by omega : 3 ≤ j-1),
      show 2*k+j-1-((j-1)-3) = 2*k+3 by omega,
      show j-1-((j-1)-3) = 3 by omega] at h3
    have hp := Nat.choose_succ_succ' (j-1) 2
    rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hp
    simp only [show j ≠ 3 by omega, ite_false]
    calc
      _ = Nat.choose (2*k+j) j * Nat.choose j 3 +
          Nat.choose (2*k+j-1) (j-1) *
            (Nat.choose (j-1) 2 + Nat.choose (j-1) 3) := by rw [← hp]; ring
      _ = _ := by
        rw [mul_add, h1, h2, h3]
        simp only [show (j-1)-2 = j-3 by omega, show (j-1)-3 = j-4 by omega]
        ring
  · have he : j = 3 := by omega
    subst j
    rw [show 2*k+3-1 = 2*k+2 by omega]
    norm_num <;> ring

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence
namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open PowerSeries Finset
private noncomputable def sourceSeries : (PowerSeries ℚ) := mk a
private noncomputable def degreeThreeModel : (PowerSeries ℚ) :=
  X^3 * ((1 + (X : PowerSeries ℚ))⁻¹)^4 * plusSeries.subst Z + X^4 * ((1 + (X : PowerSeries ℚ))⁻¹)^4 * minusSeries.subst Z

private theorem model_coefficient (n : ℕ) :
    coeff n degreeThreeModel = ∑ k ∈ range (n+1), (k.factorial : ℚ) *
      (((Nat.choose (2*k+3) 3 : ℚ)+(Nat.choose (2*k+2) 2 : ℚ)) *
        coeff n (X^(k+3)*((1 + (X : PowerSeries ℚ))⁻¹)^(2*k+4)) +
       (-(Nat.choose (2*k+3) 3 : ℚ)+(Nat.choose (2*k+2) 2 : ℚ)) *
        coeff n (X^(k+4)*((1 + (X : PowerSeries ℚ))⁻¹)^(2*k+4))) := by
  unfold degreeThreeModel Z
  rw [map_add, prefactor_subst_coeff, prefactor_subst_coeff, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have h3 : (X^3*((1 + (X : PowerSeries ℚ))⁻¹)^4)*(X*((1 + (X : PowerSeries ℚ))⁻¹)^2)^k = (X : (PowerSeries ℚ))^(k+3)*((1 + (X : PowerSeries ℚ))⁻¹)^(2*k+4) := by
    simp only [pow_add, pow_mul, mul_pow]
    ring
  have h4 : (X^4*((1 + (X : PowerSeries ℚ))⁻¹)^4)*(X*((1 + (X : PowerSeries ℚ))⁻¹)^2)^k = (X : (PowerSeries ℚ))^(k+4)*((1 + (X : PowerSeries ℚ))⁻¹)^(2*k+4) := by
    simp only [pow_add, pow_mul, mul_pow]
    ring
  rw [h3, h4]
  simp only [plusSeries, minusSeries, coeff_mk]
  ring

private theorem source_series_eq_model : sourceSeries = degreeThreeModel := by
  have hv : ((1 + (X : PowerSeries ℚ))⁻¹) = rescale (-1 : ℚ) (mk 1) := by
    apply (inv_eq_iff_mul_eq_one (by simp)).mpr
    simpa only [rescale_mk, Pi.one_apply, mul_one] using
      (mk_neg_one_pow_mul_one_add_eq_one ℚ)
  have hinv (d i : ℕ) : coeff i (((1 + (X : PowerSeries ℚ))⁻¹)^(d+1)) =
      (-1 : ℚ)^i * (Nat.choose (d+i) d : ℚ) := by
    rw [hv, ← map_pow, mk_one_pow_eq_mk_choose_add, coeff_rescale, coeff_mk]
  ext n
  rw [sourceSeries, coeff_mk, model_coefficient]
  by_cases hn : n = 0
  · subst n
    simp [a, U, coeff_X_pow_mul', Polynomial.coeff_one]
  · rw [hit_coefficient_sum n hn]
    rw [← Finset.sum_range_reflect (fun j =>
      (((2*n : ℕ) : ℚ) / ((2*n-j : ℕ) : ℚ) *
        (Nat.choose (2*n-j) j : ℚ) * (Nat.factorial (n-j) : ℚ)) *
        ((-1 : ℚ)^(j-3)*(Nat.choose j 3 : ℚ))) (n+1)]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Finset.mem_range_succ_iff.mp hk
    rw [rook_decomposition n (n-k) (by omega) (Nat.sub_le _ _),
      Nat.sub_sub_self hkn]
    generalize hj : n-k = j
    have hnj : n = k+j := by exact (Nat.sub_eq_iff_eq_add' hkn).mp hj
    subst n
    have hN : 2*(k+j)-j = 2*k+j := by omega
    rw [hN]
    by_cases hj3 : 3 ≤ j
    · have hj0 : j ≠ 0 := by exact Nat.ne_zero_of_lt hj3
      simp only [hj0, ite_false]
      by_cases hj4 : 4 ≤ j
      · have hs3 : k+j-(k+3) = j-3 := by exact Nat.add_sub_add_left k j 3
        have hs4 : k+j-(k+4) = j-4 := by exact Nat.add_sub_add_left k j 4
        rw [coeff_X_pow_mul', if_pos (by omega), hs3,
          coeff_X_pow_mul', if_pos (by omega), hs4,
          show 2*k+4 = (2*k+3)+1 by omega,
          hinv, hinv]
        have hb3 : Nat.choose (2*k+3+(j-3)) (2*k+3) =
            Nat.choose (2*k+j) (j-3) := by
          rw [show 2*k+3+(j-3) = 2*k+j by omega]
          exact Nat.choose_symm_of_eq_add (by omega)
        have hb4 : Nat.choose (2*k+3+(j-4)) (2*k+3) =
            Nat.choose (2*k+j-1) (j-4) := by
          rw [show 2*k+3+(j-4) = 2*k+j-1 by omega]
          exact Nat.choose_symm_of_eq_add (by omega)
        rw [hb3, hb4]
        have hsign : (-1 : ℚ)^(j-4) = -(-1 : ℚ)^(j-3) := by
          rw [show j-3 = (j-4)+1 by omega, pow_succ]
          ring
        rw [hsign]
        have ht : ((Nat.choose (2*k+j) j : ℚ)+
            (Nat.choose (2*k+j-1) (j-1) : ℚ))*(Nat.choose j 3 : ℚ) =
            (Nat.choose (2*k+3) 3 : ℚ)*(Nat.choose (2*k+j) (j-3) : ℚ) +
            (Nat.choose (2*k+3) 3 : ℚ)*(Nat.choose (2*k+j-1) (j-4) : ℚ) +
            (Nat.choose (2*k+2) 2 : ℚ)*(Nat.choose (2*k+j-1) (j-3) : ℚ) := by
          have htnat := three_hit_binomial_transfer k j hj3
          simp only [show j ≠ 3 by omega, ite_false] at htnat
          exact_mod_cast htnat
        have hp := Nat.choose_succ_succ' (2*k+j-1) (j-4)
        rw [show 2*k+j-1+1 = 2*k+j by omega,
          show j-4+1 = j-3 by omega] at hp
        have hpq : (Nat.choose (2*k+j) (j-3) : ℚ) =
            (Nat.choose (2*k+j-1) (j-4) : ℚ)+
            (Nat.choose (2*k+j-1) (j-3) : ℚ) := by exact_mod_cast hp
        linear_combination (k.factorial : ℚ)*(-1 : ℚ)^(j-3)*ht -
          (k.factorial : ℚ)*(-1 : ℚ)^(j-3)*(Nat.choose (2*k+2) 2 : ℚ)*hpq
      · have hjexact : j = 3 := by omega
        subst j
        simp only [coeff_X_pow_mul', if_pos (by omega : k+3 ≤ k+3),
          if_neg (by omega : ¬ k+4 ≤ k+3), Nat.sub_self,
          show 2*k+3-1 = 2*k+2 by omega,
          Nat.reduceSub, pow_zero, Nat.choose_self, Nat.cast_one,
          mul_one, mul_zero, add_zero]
        simp [] <;> ring
    · have hzero : Nat.choose j 3 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hzero, coeff_X_pow_mul', show ¬ k+3 ≤ k+j by omega,
        show ¬ k+4 ≤ k+j by omega]

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence
open PowerSeries

private theorem weighted_euler :
    3*plusSeries = 4*(X * derivative ((X * derivative ((X * derivative factorialSeries))))) +
      18*(X * derivative ((X * derivative factorialSeries)))+20*(X * derivative factorialSeries)+6*factorialSeries ∧
    3*minusSeries = -4*(X * derivative ((X * derivative ((X * derivative factorialSeries))))) -
      6*(X * derivative ((X * derivative factorialSeries)))-2*(X * derivative factorialSeries) := by
  constructor
  · ext n
    have hw := (binomial_weights n).1
    cases n with
    | zero => norm_num [plusSeries, factorialSeries, map_ofNat]
    | succ n =>
      simp only [Nat.cast_add, Nat.cast_one] at hw
      simp only [neg_mul, map_add, map_sub, map_neg, coeff_ofNat_mul, coeff_intCast_mul,
        plusSeries, coeff_mk, coeff_succ_X_mul, coeff_derivative,
        factorialSeries]
      linear_combination ((n+1).factorial : ℚ)*hw
  · ext n
    have hw := (binomial_weights n).2
    cases n with
    | zero => norm_num [minusSeries, factorialSeries, map_ofNat]
    | succ n =>
      simp only [Nat.cast_add, Nat.cast_one] at hw
      simp only [neg_mul, map_add, map_sub, map_neg, coeff_ofNat_mul, coeff_intCast_mul,
        minusSeries, coeff_mk, coeff_succ_X_mul, coeff_derivative,
        factorialSeries]
      linear_combination ((n+1).factorial : ℚ)*hw

private theorem model_reduction :
    d X * degreeThreeModel = r X * factorialPullback + s X := by
  let g1 : (PowerSeries ℚ) := ((X * derivative factorialSeries)).subst Z
  let g2 : (PowerSeries ℚ) := ((X * derivative ((X * derivative factorialSeries)))).subst Z
  let g3 : (PowerSeries ℚ) := ((X * derivative ((X * derivative ((X * derivative factorialSeries)))))).subst Z
  have hz : HasSubst Z := PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [Z])
  have hu : (1+(X : (PowerSeries ℚ)))*((1 + (X : PowerSeries ℚ))⁻¹) = 1 := PowerSeries.mul_inv_cancel _ (by simp)
  have hw1 := congrArg (substAlgHom (R := ℚ) hz) weighted_euler.1
  have hw2 := congrArg (substAlgHom (R := ℚ) hz) weighted_euler.2
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, coe_substAlgHom] at hw1 hw2
  have hw1' : 3*plusSeries.subst Z = 4*g3+18*g2+20*g1+6*factorialPullback := by
    simpa only [g1, g2, g3, factorialPullback, subst_mul hz, subst_X hz] using hw1
  have hw2' : 3*minusSeries.subst Z = -4*g3-6*g2-2*g1 := by
    simpa only [g1, g2, g3, factorialPullback, subst_mul hz, subst_X hz] using hw2
  have hm : 3*degreeThreeModel =
      X^3*((1 + (X : PowerSeries ℚ))⁻¹)^4*(4*g3+18*g2+20*g1+6*factorialPullback) +
      X^4*((1 + (X : PowerSeries ℚ))⁻¹)^4*(-4*g3-6*g2-2*g1) := by
    dsimp [degreeThreeModel]
    linear_combination X^3*((1 + (X : PowerSeries ℚ))⁻¹)^4*hw1' + X^4*((1 + (X : PowerSeries ℚ))⁻¹)^4*hw2'
  have hm4 : (1+X)^4*(3*degreeThreeModel) =
      X^3*((4-4*X)*g3+(18-6*X)*g2+(20-2*X)*g1+6*factorialPullback) := by
    rw [hm]
    calc
      _ = ((1+X)*((1 + (X : PowerSeries ℚ))⁻¹))^4 *
        (X^3*((4-4*X)*g3+(18-6*X)*g2+(20-2*X)*g1+6*factorialPullback)) := by ring
      _ = _ := by rw [hu]; ring
  have ht1 := congrArg (substAlgHom (R := ℚ) hz) theta_one
  have ht2 := congrArg (substAlgHom (R := ℚ) hz) theta_two
  have ht3 := congrArg (substAlgHom (R := ℚ) hz) theta_three
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, map_one,
    map_ofNat, substAlgHom_X, coe_substAlgHom] at ht1 ht2 ht3
  have ht1' : Z*g1 = (1-Z)*factorialPullback-1 := by
    simpa only [g1, factorialPullback, subst_mul hz, subst_X hz] using ht1
  have ht2' : Z^2*g2 = (Z^2-3*Z+1)*factorialPullback+2*Z-1 := by
    simpa only [g2, factorialPullback, subst_mul hz, subst_X hz] using ht2
  have ht3' : Z^3*g3 =
      (-Z^3+7*Z^2-6*Z+1)*factorialPullback-3*Z^2+5*Z-1 := by
    simpa only [g3, factorialPullback, subst_mul hz, subst_X hz] using ht3
  have hz1 : (1+X)^2*Z = (X : (PowerSeries ℚ)) := by
    dsimp [Z]
    calc
      _ = X*((1+X)*((1 + (X : PowerSeries ℚ))⁻¹))^2 := by ring
      _ = _ := by rw [hu]; ring
  have hz2 : (1+X)^4*Z^2 = (X : (PowerSeries ℚ))^2 := by
    dsimp [Z]
    calc
      _ = X^2*((1+X)*((1 + (X : PowerSeries ℚ))⁻¹))^4 := by ring
      _ = _ := by rw [hu]; ring
  have hz3 : (1+X)^6*Z^3 = (X : (PowerSeries ℚ))^3 := by
    dsimp [Z]
    calc
      _ = X^3*((1+X)*((1 + (X : PowerSeries ℚ))⁻¹))^6 := by ring
      _ = _ := by rw [hu]; ring
  have h1 : X*g1 = ((1+X)^2-X)*factorialPullback-(1+X)^2 := by
    linear_combination (1+X)^2*ht1' - (g1+factorialPullback)*hz1
  have h2 : X^2*g2 =
      (X^2-3*X*(1+X)^2+(1+X)^4)*factorialPullback+2*X*(1+X)^2-(1+X)^4 := by
    linear_combination (1+X)^4*ht2' - (g2-factorialPullback)*hz2 +
      (2-3*factorialPullback)*(1+X)^2*hz1
  have h3 : X^3*g3 =
      (-X^3+7*X^2*(1+X)^2-6*X*(1+X)^4+(1+X)^6)*factorialPullback -
      3*X^2*(1+X)^2+5*X*(1+X)^4-(1+X)^6 := by
    linear_combination (1+X)^6*ht3' - (g3+factorialPullback)*hz3 +
      (7*factorialPullback-3)*(1+X)^2*hz2 +
      (5-6*factorialPullback)*(1+X)^4*hz1
  have hy : (1+(X : (PowerSeries ℚ))) ≠ 0 := by
    intro he
    have := congrArg constantCoeff he
    norm_num at this
  apply mul_left_cancel₀ (pow_ne_zero 2 hy)
  dsimp [d, r, s]
  linear_combination hm4 + (4-4*X)*h3 + X*(18-6*X)*h2 + X^2*(20-2*X)*h1

private theorem degree_three_diagonal :
    d X * sourceSeries = r X * factorialPullback + s X := by
  rw [source_series_eq_model]
  exact model_reduction

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence

namespace D5.S1.Recurrence.Invariants.MatharA000159Recurrence

theorem result : claim := by
  intro n hn
  have hE := differential_certificate sourceSeries factorialPullback
    degree_three_diagonal (by simpa only [q, b, c] using pullback_differential)
  have h := coefficient_recurrence sourceSeries hE n hn
  simpa only [sourceSeries, PowerSeries.coeff_mk] using h

end D5.S1.Recurrence.Invariants.MatharA000159Recurrence
