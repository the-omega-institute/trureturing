/- GID: D5/S3/Combinatorics/MotzkinHankel/KimStantonSimultaneousDenominator
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/KimStantonSimultaneousDenominator
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer polynomial denominators of contiguous basic hypergeometric coefficients. -/

/-
proof_shape: per-declaration classifications below.
Classification: bind-only helpers are inlined in the compiled proof-term classification;
source helpers have actual consumers on the settling proof path.
escape_witness: KimStantonDenominatorCore.inverse_floor_bound
admission_basis: open-problem-resolution (#21468; Proved)
Protected-baseline frozen dependencies: none. The Core module is a same-delivery prerequisite;
its declaration identities are supplied by the scoped Lean report.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21724
Declarations: name | proof_shape | escape_witness | consumer(s).
gamma | bind-only | none | claim
claim | bind-only | none | result
degreeStep | bind-only | none | coeff_F_degreeStep, norlund_contiguous, norlund_scalar
parameterStep | bind-only | none | coeff_F_parameterStep, norlund_contiguous, norlund_scalar
bWeight | bind-only | none | norlund_contiguous, norlund_scalar, ratio_mem, u_recurrence, weights_mem
aWeight | bind-only | none | norlund_contiguous, norlund_scalar, ratio_mem, u_recurrence, weights_mem
lWeight | bind-only | none | norlund_contiguous, norlund_scalar, ratio_mem, u_recurrence, weights_mem
norlund_scalar | bind-only | none | norlund_contiguous
coeff_F_degreeStep | bind-only | none | norlund_contiguous
coeff_F_parameterStep | bind-only | none | norlund_contiguous
norlund_contiguous | bind-only | none | u_recurrence
u_recurrence | bind-only | none | ratio_mem
weights_mem | bind-only | none | ratio_mem
ratio_mem | content | KimStantonDenominatorCore.recurrence_coefficients_mem | result
result | content | KimStantonDenominatorCore.inverse_floor_bound | settling result
-/

import D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
noncomputable section
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonSimultaneousDenominator
open D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore

/-- The coefficient of the contiguous formal quotient. -/
def gamma (n : ℕ) : FractionRing (MvPolynomial (Fin 4) ℤ) :=
  PowerSeries.coeff n (F (a * q) (b * q) (c * q) q * (F a b c q)⁻¹)

/-- Kim–Stanton Conjecture 8.3. -/
def claim : Prop :=
  ∀ n : ℕ, ∃ P : MvPolynomial (Fin 4) ℤ,
    gamma n / (1 - c) = algebraMap (MvPolynomial (Fin 4) ℤ)
      (FractionRing (MvPolynomial (Fin 4) ℤ)) P / D n


private def degreeStep (A B C Q t : (FractionRing (MvPolynomial (Fin 4) ℤ))) : (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  (1 - A * t) * (1 - B * t) / ((1 - C * t) * (1 - Q * t))

private def parameterStep (A B C t : (FractionRing (MvPolynomial (Fin 4) ℤ))) : (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  (1 - A * t) * (1 - B * t) * (1 - C) /
    ((1 - A) * (1 - B) * (1 - C * t))

private def bWeight (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) : (FractionRing (MvPolynomial (Fin 4) ℤ)) := (A + B - A * B - A * B * Q) / (1 - C)
private def aWeight (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) : (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  -(1 - A * Q) * (1 - B * Q) * C / ((1 - C) * (1 - C * Q))
private def lWeight (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) : (FractionRing (MvPolynomial (Fin 4) ℤ)) :=
  (1 - A * Q) * (1 - B * Q) * A * B * Q / ((1 - C) * (1 - C * Q))

private theorem norlund_scalar (A B C Q t : (FractionRing (MvPolynomial (Fin 4) ℤ)))
    (ha : 1 - A ≠ 0) (hb : 1 - B ≠ 0) (haq : 1 - A * Q ≠ 0) (hbq : 1 - B * Q ≠ 0)
    (hc : 1 - C ≠ 0) (hcq : 1 - C * Q ≠ 0)
    (hct : 1 - C * t ≠ 0) (hcqt : 1 - C * (t * Q) ≠ 0)
    (hcq2t : 1 - C * (t * Q ^ 2) ≠ 0)
    (hqt : 1 - Q * t ≠ 0) (hq2t : 1 - Q * (t * Q) ≠ 0) :
    degreeStep A B C Q t * degreeStep A B C Q (t * Q) =
      degreeStep A B C Q t * degreeStep A B C Q (t * Q) * parameterStep A B C (t * Q ^ 2) -
      bWeight A B C Q * degreeStep A B C Q t * parameterStep A B C (t * Q) -
      aWeight A B C Q * degreeStep A B C Q t * parameterStep A B C (t * Q) *
        parameterStep (A * Q) (B * Q) (C * Q) (t * Q) -
      lWeight A B C Q * parameterStep A B C t * parameterStep (A * Q) (B * Q) (C * Q) t := by
  have hcqt' : 1 - (C * Q) * t ≠ 0 := by simpa only [mul_assoc, mul_comm Q t] using hcqt
  have hcq2t' : 1 - (C * Q) * (t * Q) ≠ 0 := by
    convert hcq2t using 1 <;> ring
  unfold degreeStep parameterStep bWeight aWeight lWeight
  field_simp (disch := simp_all [pow_two, mul_assoc, mul_comm, mul_left_comm])
  <;> ring

end D5.S3.Combinatorics.MotzkinHankel.KimStantonSimultaneousDenominator

end



set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonSimultaneousDenominator
open D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore
open PowerSeries

private theorem coeff_F_degreeStep (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ) :
    coeff (n + 1) (F A B C Q) = coeff n (F A B C Q) * degreeStep A B C Q (Q ^ n) := by
  simpa only [degreeStep, pow_succ', mul_div_assoc] using coeff_F_succ A B C Q n

private theorem coeff_F_parameterStep (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ))) (n : ℕ)
    (ha : 1 - A ≠ 0) (hb : 1 - B ≠ 0)
    (hc : ∀ m : ℕ, 1 - C * Q ^ m ≠ 0)
    (hq : ∀ m : ℕ, 1 - Q ^ (m + 1) ≠ 0) :
    coeff n (F (A * Q) (B * Q) (C * Q) Q) =
      coeff n (F A B C Q) * parameterStep A B C (Q ^ n) := by
  simpa only [parameterStep, mul_div_assoc] using coeff_shift_abc A B C Q n ha hb hc hq

private theorem norlund_contiguous (A B C Q : (FractionRing (MvPolynomial (Fin 4) ℤ)))
    (ha : ∀ m : ℕ, 1 - A * Q ^ m ≠ 0)
    (hb : ∀ m : ℕ, 1 - B * Q ^ m ≠ 0)
    (hc : ∀ m : ℕ, 1 - C * Q ^ m ≠ 0)
    (hq : ∀ m : ℕ, 1 - Q ^ (m + 1) ≠ 0) :
    F A B C Q = (1 - PowerSeries.C (bWeight A B C Q) * X) *
        F (A * Q) (B * Q) (C * Q) Q -
      (PowerSeries.C (aWeight A B C Q) * X +
        PowerSeries.C (lWeight A B C Q) * X ^ 2) *
        F (A * Q ^ 2) (B * Q ^ 2) (C * Q ^ 2) Q := by
  have ha0 : 1 - A ≠ 0 := by simpa using ha 0
  have hb0 : 1 - B ≠ 0 := by simpa using hb 0
  have hc0 : 1 - C ≠ 0 := by simpa using hc 0
  have ha1 : 1 - A * Q ≠ 0 := by simpa using ha 1
  have hb1 : 1 - B * Q ≠ 0 := by simpa using hb 1
  have hc1 : 1 - C * Q ≠ 0 := by simpa using hc 1
  have hq0 : 1 - Q ≠ 0 := by simpa using hq 0
  have hc' : ∀ m : ℕ, 1 - (C * Q) * Q ^ m ≠ 0 := by
    intro m
    simpa only [mul_assoc, ← pow_succ'] using hc (m + 1)
  have htwo : F (A * Q ^ 2) (B * Q ^ 2) (C * Q ^ 2) Q =
      F ((A * Q) * Q) ((B * Q) * Q) ((C * Q) * Q) Q := by congr 1 <;> ring
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, F_constant]
  | succ n =>
    cases n with
    | zero =>
      simp only [sub_mul, add_mul, mul_assoc, map_sub, map_add,
        one_mul, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul']
      simp only [show ¬ 2 ≤ (0 + 1 : ℕ) by omega, ite_false,
        coeff_zero_eq_constantCoeff, F_constant, mul_zero]
      simp only [coeff_shift_abc A B C Q 1 ha0 hb0 hc hq, coeff_F_succ]
      simp only [coeff_zero_eq_constantCoeff, F_constant, pow_zero, pow_one,
        mul_one, one_mul]
      unfold bWeight aWeight
      field_simp [ha0, hb0, ha1, hb1, hc0, hc1, hq0]
      <;> ring
    | succ n =>
      simp only [sub_mul, add_mul, mul_assoc, map_sub, map_add,
        one_mul, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul']
      simp only [show 2 ≤ n + 1 + 1 by omega, ite_true,
        show n + 1 + 1 - 2 = n by omega]
      simp only [htwo]
      simp only [coeff_F_parameterStep (A * Q) (B * Q) (C * Q) Q (n + 1) ha1 hb1 hc' hq,
        coeff_F_parameterStep (A * Q) (B * Q) (C * Q) Q n ha1 hb1 hc' hq,
        coeff_F_parameterStep A B C Q (n + 1 + 1) ha0 hb0 hc hq,
        coeff_F_parameterStep A B C Q (n + 1) ha0 hb0 hc hq,
        coeff_F_parameterStep A B C Q n ha0 hb0 hc hq,
        coeff_F_degreeStep A B C Q (n + 1), coeff_F_degreeStep A B C Q n]
      have hscalar := norlund_scalar A B C Q (Q ^ n) ha0 hb0 ha1 hb1 hc0 hc1 (hc n)
        (by simpa only [← pow_succ] using hc (n + 1))
        (by simpa only [← pow_add] using hc (n + 2))
        (by simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hq n)
        (by simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hq (n + 1))
      simp only [pow_succ, pow_zero, one_mul, mul_assoc] at *
      linear_combination coeff n (F A B C Q) * hscalar

end D5.S3.Combinatorics.MotzkinHankel.KimStantonSimultaneousDenominator

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Combinatorics.MotzkinHankel.KimStantonSimultaneousDenominator
open D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore
open PowerSeries





private theorem u_recurrence (m : ℕ) :
    (fun m : ℕ => F (a * q ^ m) (b * q ^ m) (c * q ^ m) q) m = (1 - PowerSeries.C ((fun m : ℕ => bWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) m) * X) * (fun m : ℕ => F (a * q ^ m) (b * q ^ m) (c * q ^ m) q) (m + 1) -
      (PowerSeries.C ((fun m : ℕ => aWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) m) * X + PowerSeries.C ((fun m : ℕ => lWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) m) * X ^ 2) * (fun m : ℕ => F (a * q ^ m) (b * q ^ m) (c * q ^ m) q) (m + 2) := by
  have ha : ∀ j : ℕ, 1 - (a * q ^ m) * q ^ j ≠ 0 := by
    intro j
    simpa only [a, q, mul_assoc, ← pow_add] using variable_factor_ne_zero 0 3 (m + j)
  have hb : ∀ j : ℕ, 1 - (b * q ^ m) * q ^ j ≠ 0 := by
    intro j
    simpa only [b, q, mul_assoc, ← pow_add] using variable_factor_ne_zero 1 3 (m + j)
  have hc : ∀ j : ℕ, 1 - (c * q ^ m) * q ^ j ≠ 0 := by
    intro j
    simpa only [c, q, mul_assoc, ← pow_add] using variable_factor_ne_zero 2 3 (m + j)
  have hq : ∀ j : ℕ, 1 - q ^ (j + 1) ≠ 0 :=
    fun j => one_sub_q_pow_ne_zero (j + 1) (by omega)
  simpa only [pow_add, pow_one, mul_assoc] using
    norlund_contiguous (a * q ^ m) (b * q ^ m) (c * q ^ m) q ha hb hc hq

private theorem weights_mem (m : ℕ) : (fun m : ℕ => bWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) m ∈ S ∧ (fun m : ℕ => aWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) m ∈ S ∧ (fun m : ℕ => lWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) m ∈ S := by
  have ha : a * q ^ m ∈ S :=
    S.mul_mem (S.algebraMap_mem _) (S.pow_mem (S.algebraMap_mem _) m)
  have hb : b * q ^ m ∈ S :=
    S.mul_mem (S.algebraMap_mem _) (S.pow_mem (S.algebraMap_mem _) m)
  have hc : c * q ^ m ∈ S :=
    S.mul_mem (S.algebraMap_mem _) (S.pow_mem (S.algebraMap_mem _) m)
  have hq : q ∈ S := S.algebraMap_mem _
  have hA := S.sub_mem S.one_mem (S.mul_mem ha hq)
  have hB := S.sub_mem S.one_mem (S.mul_mem hb hq)
  have hC := S_inv_p m
  have hC' := S_inv_p (m + 1)
  have hshift : (c * q ^ m) * q = c * q ^ (m + 1) := by rw [pow_succ, mul_assoc]
  constructor
  · simpa only [bWeight, div_eq_mul_inv] using
      S.mul_mem (S.sub_mem (S.sub_mem (S.add_mem ha hb) (S.mul_mem ha hb))
        (S.mul_mem (S.mul_mem ha hb) hq)) hC
  · constructor
    · dsimp only
      unfold aWeight
      rw [div_eq_mul_inv, mul_inv_rev, hshift]
      exact S.mul_mem (S.mul_mem (S.mul_mem (S.neg_mem hA) hB) hc)
        (S.mul_mem hC' hC)
    · dsimp only
      unfold lWeight
      rw [div_eq_mul_inv, mul_inv_rev, hshift]
      exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem hA hB) ha) hb) hq)
        (S.mul_mem hC' hC)

private theorem ratio_mem (n : ℕ) :
    coeff n (ratio (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 0 * MvPolynomial.X 3) (MvPolynomial.X 1 * MvPolynomial.X 3)) ∈ S := by
  have h := D5.S3.Combinatorics.MotzkinHankel.KimStantonDenominatorCore.quotient_coefficients_mem S.toSubring
    (fun m : ℕ => F (a * q ^ m) (b * q ^ m) (c * q ^ m) q) (fun m : ℕ => bWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) (fun m : ℕ => aWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) (fun m : ℕ => lWeight (a * q ^ m) (b * q ^ m) (c * q ^ m) q) (fun m => F_constant _ _ _ _)
    (fun m => (weights_mem m).1) (fun m => (weights_mem m).2.1)
    (fun m => (weights_mem m).2.2) u_recurrence n 0
  simpa only [Nat.zero_add, pow_zero, mul_one, pow_one, ratio, map_mul, a, b, c, q, Subalgebra.mem_toSubring] using h

theorem result : claim := by
  simpa only [claim, gamma, ratio, map_mul, a, b, c, q] using
    denominator_from_localization (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 0 * MvPolynomial.X 3) (MvPolynomial.X 1 * MvPolynomial.X 3) ratio_mem

end D5.S3.Combinatorics.MotzkinHankel.KimStantonSimultaneousDenominator

end
