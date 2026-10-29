/- GID: D5/S3/Arith/Congruence/TebniA350759PrimeCongruences
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/TebniA350759PrimeCongruences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both prime congruences in Tebni's OEIS A350759 COMMENTS. -/
/-
admission_basis: open-problem-resolution (#22481; Proved).
escape_witness: none for every declaration.
Direct frozen dependencies (declaration GIDs):
F1: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_add
F2: D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.egf
F3: D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.derivative_egfSeries
F4: D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfMul
F5: D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries
F6: D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries_mul
Declaration statement_id readings are pending the Stage B scoped report;
the existing report predates the merged base and does not contain the Dold owner.
The generated egf.eq_1 equation is accounted for under its egf owner F2.
Each row gives its proof shape, direct frozen owners and actual consumers.
Expansion.G: proof_shape: bind-only; frozen: none;
  consumers: Expansion.G_zero, Expansion.H, Expansion.H_ode, Expansion.H_zero, Expansion.diagonal_G, Expansion.diagonal_H.
Expansion.G_zero: proof_shape: bind-only; frozen: none;
  consumers: Expansion.H_ode, Expansion.H_zero, Expansion.diagonal_H.
Expansion.H: proof_shape: bind-only; frozen: none;
  consumers: Expansion.H_coeff, Expansion.H_ode, Expansion.H_recurrence, Expansion.H_zero, Expansion.diagonal_H, Expansion.diagonal_H_coeff, Expansion.diagonal_H_sum, Expansion.scaled_residue, source_residue, source_split.
Expansion.H_coeff: proof_shape: content; frozen: none;
  consumers: Expansion.diagonal_H_sum.
Expansion.H_ode: proof_shape: bind-only; frozen: none;
  consumers: Expansion.H_recurrence.
Expansion.H_recurrence: proof_shape: bind-only; frozen: none;
  consumers: Expansion.H_coeff.
Expansion.H_zero: proof_shape: bind-only; frozen: none;
  consumers: Expansion.H_coeff.
Expansion.P: proof_shape: bind-only; frozen: none;
  consumers: Expansion.P_constant, Expansion.P_zero, Expansion.diagonal_H_coeff, Expansion.diagonal_H_sum, Expansion.phi_asc, Expansion.scaled_residue, Expansion.scaled_term_multiple.
Expansion.P_constant: proof_shape: bind-only; frozen: none;
  consumers: Expansion.scaled_term_multiple.
Expansion.P_zero: proof_shape: bind-only; frozen: none;
  consumers: Expansion.scaled_residue.
Expansion.diagonal: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_C, Expansion.diagonal_G, Expansion.diagonal_H, Expansion.diagonal_H_coeff, Expansion.diagonal_H_sum, Expansion.diagonal_X, Expansion.diagonal_apply, Expansion.diagonal_continuous, Expansion.diagonal_lift, Expansion.diagonal_subst, Expansion.scaled_residue, source_residue, source_split.
Expansion.diagonal_C: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_G.
Expansion.diagonal_G: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_H.
Expansion.diagonal_H: proof_shape: bind-only; frozen: none;
  consumers: source_split.
Expansion.diagonal_H_coeff: proof_shape: content; frozen: none;
  consumers: Expansion.scaled_residue.
Expansion.diagonal_H_sum: proof_shape: content; frozen: none;
  consumers: Expansion.diagonal_H_coeff.
Expansion.diagonal_X: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_lift.
Expansion.diagonal_apply: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_C, Expansion.diagonal_H_sum, Expansion.diagonal_X, Expansion.diagonal_continuous.
Expansion.diagonal_continuous: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_subst.
Expansion.diagonal_lift: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_G.
Expansion.diagonal_subst: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_H, Expansion.diagonal_lift.
Expansion.factorial_ratio: proof_shape: bind-only; frozen: none;
  consumers: Expansion.scaled_term_multiple.
Expansion.phi_asc: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal_H_sum.
Expansion.polynomialUniformSpace: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal, Expansion.diagonal_C, Expansion.diagonal_H_sum, Expansion.diagonal_X, Expansion.diagonal_apply, Expansion.diagonal_continuous, Expansion.diagonal_subst.
Expansion.rationalUniformSpace: proof_shape: bind-only; frozen: none;
  consumers: Expansion.diagonal, Expansion.diagonal_C, Expansion.diagonal_H_coeff, Expansion.diagonal_H_sum, Expansion.diagonal_X, Expansion.diagonal_apply, Expansion.diagonal_continuous, Expansion.diagonal_subst.
Expansion.scaled_residue: proof_shape: content; frozen: none;
  consumers: source_residue.
Expansion.scaled_term_multiple: proof_shape: bind-only; frozen: none;
  consumers: Expansion.scaled_residue.
IsSourceSequence: proof_shape: bind-only; frozen: F2;
  consumers: claim, prime_successor, result, source_exists, source_initial, source_recurrence, source_uniform.
claim: proof_shape: bind-only; frozen: F2;
  consumers: result.
logSeq: proof_shape: bind-only; frozen: none;
  consumers: log_egf, prime_successor, source_recurrence.
log_egf: proof_shape: bind-only; frozen: F5;
  consumers: source_recurrence.
prime_successor: proof_shape: bind-only; frozen: F2,F3,F4,F5,F6;
  consumers: result.
result: proof_shape: content; frozen: F1,F2,F3,F4,F5,F6;
  consumers: settling conclusion.
sourceSeries: proof_shape: bind-only; frozen: none;
  consumers: IsSourceSequence, source_derivative, source_exists, source_initial, source_recurrence, source_residue, source_split, source_uniform, source_zero.
source_derivative: proof_shape: bind-only; frozen: none;
  consumers: source_recurrence.
source_exists: proof_shape: content; frozen: F1,F2;
  consumers: result.
source_exponent_zero: proof_shape: bind-only; frozen: none;
  consumers: source_derivative, source_zero.
source_initial: proof_shape: bind-only; frozen: F2,F5;
  consumers: prime_successor.
source_recurrence: proof_shape: bind-only; frozen: F2,F3,F4,F5,F6;
  consumers: prime_successor.
source_residue: proof_shape: content; frozen: F1;
  consumers: source_exists, source_uniform.
source_split: proof_shape: bind-only; frozen: F1;
  consumers: source_residue.
source_uniform: proof_shape: content; frozen: F1,F2;
  consumers: result.
source_zero: proof_shape: bind-only; frozen: none;
  consumers: source_initial.
H_coeff carries a coefficient-invariant induction. The other content rows retain
that induction after inlining the helpers of this module; normalization and
owner applications are labelled bind-only. The admission basis is the external
settlement, not an escape-witness claim.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22632.
The source EGF is kept in its published expression. The proof uses the original
EGF convolution and derivative owners and the exponential addition owner.
The polynomial-coefficient expansion is a formal derivation of Hanna's
rising-factorial expansion in OEIS A176118; the all-index divisibility supplies
the second modulus in both prime congruences.
-/

import Mathlib.Algebra.Algebra.Hom.Rat
import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
import D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Choose.Dvd

namespace D5.S3.Arith.Congruence.TebniA350759PrimeCongruences

open PowerSeries
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (egf)

/-- The published EGF exp(-1 + (1 + x)*(1 - log(1 + x))).
Mathlib's `log ℚ` is log(1 + X), and `subst inner outer` substitutes inner into outer. -/
noncomputable def sourceSeries : PowerSeries ℚ :=
  PowerSeries.subst
    (-1 + (1 + X) * (1 - PowerSeries.log ℚ))
    (PowerSeries.exp ℚ)

/-- The source sequence has integer terms and precisely the published EGF. -/
def IsSourceSequence (a : ℕ → ℤ) : Prop :=
  egf (fun n => (a n : ℚ)) = sourceSeries

/-- Both consecutive COMMENTS conjectures, including existence of the source sequence. -/
def claim : Prop :=
  (∃ a : ℕ → ℤ, IsSourceSequence a) ∧
    ∀ a : ℕ → ℤ, IsSourceSequence a →
      ∀ p : ℕ, Nat.Prime p →
        Int.ModEq (p : ℤ) (a p + a (p + 1) - 2) 0 ∧
        Int.ModEq (((p + 1) * p : ℕ) : ℤ) (a (p + 1)) 1

end D5.S3.Arith.Congruence.TebniA350759PrimeCongruences

open PowerSeries Finset
open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality (expSeries_add)
open scoped PowerSeries.WithPiTopology

namespace D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.Expansion

private local instance rationalUniformSpace : UniformSpace ℚ := ⊥
private local instance polynomialUniformSpace : UniformSpace (Polynomial ℚ) := ⊥

private noncomputable def G : PowerSeries (Polynomial ℚ) :=
  -(C Polynomial.X) * log (Polynomial ℚ)
private noncomputable def H : PowerSeries (Polynomial ℚ) :=
  subst G (exp ℚ)

private theorem G_zero : constantCoeff G = 0 := by
  simp [G]

private theorem H_zero : constantCoeff H = 1 := by
    have h := constantCoeff_subst_of_constantCoeff_zero G_zero (exp ℚ)
    change constantCoeff (subst G (exp ℚ)) = _ at h
    simpa [H] using h

private theorem H_ode : derivative H * (1 + X) = -(C Polynomial.X) * H := by
    have hrepr : H = subst G (exp (Polynomial ℚ)) := by
      rw [← PowerSeries.map_exp (algebraMap ℚ (Polynomial ℚ)),
        PowerSeries.map_algebraMap_eq_subst_X,
        PowerSeries.subst_comp_subst_apply HasSubst.X' (.of_constantCoeff_zero G_zero),
        PowerSeries.subst_X (.of_constantCoeff_zero G_zero)]
      rfl
    simp only [hrepr]
    rw [derivative_subst (.of_constantCoeff_zero G_zero), derivative_exp]
    simp only [G, Derivation.leibniz, map_neg, derivative_C, neg_zero,
      zero_mul, zero_add, smul_eq_mul]
    calc
      _ = -(C Polynomial.X) * subst G (exp (Polynomial ℚ)) *
          (derivative (log (Polynomial ℚ)) * (1 + X)) := by simp only [G, neg_mul]; ring
      _ = _ := by rw [derivative_log_mul_one_add_X]; simp only [G, neg_mul]; ring

private theorem H_recurrence (k : ℕ) :
    (k + 1 : Polynomial ℚ) * coeff (k + 1) H =
      -(Polynomial.X + (k : Polynomial ℚ)) * coeff k H := by
    have h := congrArg (coeff k) H_ode
    simp only [mul_add, mul_one, map_add, neg_mul, map_neg, coeff_C_mul] at h
    cases k with
    | zero => simpa [coeff_derivative] using h
    | succ k =>
      rw [coeff_succ_mul_X] at h
      simp only [coeff_derivative, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_succ] at h
      simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one]
      linear_combination h

private theorem H_coeff (k : ℕ) :
    coeff k H = Polynomial.C ((-1 : ℚ)^k / (k.factorial : ℚ)) *
      ascPochhammer ℚ k := by
    induction k with
    | zero => simpa [coeff_zero_eq_constantCoeff] using H_zero
    | succ k ih =>
      have hr := H_recurrence k
      rw [ih] at hr
      apply_fun (fun z : Polynomial ℚ => Polynomial.C (1 / (k+1 : ℚ)) * z) at hr
      have hk : (k+1 : ℚ) ≠ 0 := by exact Nat.cast_add_one_ne_zero k
      have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      have ha : Polynomial.C (1 / (k+1 : ℚ)) * (k+1 : Polynomial ℚ) = 1 := by
        rw [show (k+1 : Polynomial ℚ) = Polynomial.C (k+1 : ℚ) by simp, ← map_mul]
        simp [hk]
      rw [← mul_assoc, ha, one_mul] at hr
      rw [hr, ascPochhammer_succ_right]
      have hs : Polynomial.C (1 / (k+1 : ℚ)) *
          (-Polynomial.C ((-1 : ℚ)^k / (k.factorial : ℚ))) =
          Polynomial.C ((-1 : ℚ)^(k+1) / ((k+1).factorial : ℚ)) := by
        rw [← map_neg, ← map_mul]
        congr 1
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp
      linear_combination (ascPochhammer ℚ k) *
        (Polynomial.X + (k : Polynomial ℚ)) * hs



private noncomputable def diagonal : PowerSeries (Polynomial ℚ) →ₐ[ℚ] PowerSeries ℚ :=
  (PowerSeries.eval₂Hom
    (φ := Polynomial.eval₂RingHom (PowerSeries.C : ℚ →+* PowerSeries ℚ) (1 + X))
    continuous_of_discreteTopology (PowerSeries.HasEval.X (R := ℚ))).toRatAlgHom

private theorem diagonal_apply (f : PowerSeries (Polynomial ℚ)) :
    diagonal f = PowerSeries.eval₂ (Polynomial.eval₂RingHom PowerSeries.C (1 + X)) X f := by
  rw [diagonal, RingHom.toRatAlgHom_apply, PowerSeries.coe_eval₂Hom]

private theorem diagonal_continuous : Continuous diagonal := by
  change Continuous (fun f => diagonal f)
  simp_rw [diagonal_apply]
  exact PowerSeries.continuous_eval₂
    (φ := Polynomial.eval₂RingHom (PowerSeries.C : ℚ →+* PowerSeries ℚ) (1 + X))
    continuous_of_discreteTopology (PowerSeries.HasEval.X (R := ℚ))

private theorem diagonal_C (p : Polynomial ℚ) : diagonal (C p) = (Polynomial.eval₂RingHom PowerSeries.C (1 + X)) p := by
  rw [diagonal_apply, PowerSeries.eval₂_C]

private theorem diagonal_X : diagonal X = X := by
  rw [diagonal_apply, PowerSeries.eval₂_X]

private theorem diagonal_subst (f : PowerSeries ℚ) (b : PowerSeries (Polynomial ℚ))
    (hb : constantCoeff b = 0) (hdb : constantCoeff (diagonal b) = 0) :
    diagonal (subst b f) = subst (diagonal b) f := by
    have h := MvPowerSeries.comp_subst_apply
      (R := ℚ) (S := Polynomial ℚ) (ε := diagonal)
      (PowerSeries.HasSubst.of_constantCoeff_zero hb).const diagonal_continuous f
    have hd : HasSubst (diagonal b) := .of_constantCoeff_zero hdb
    change diagonal (subst b f) = PowerSeries.aeval hd.hasEval f at h
    rw [← PowerSeries.substAlgHom_eq_aeval hd] at h
    simpa only [PowerSeries.coe_substAlgHom] using h

private theorem diagonal_lift (f : PowerSeries ℚ) :
    diagonal (f.map (algebraMap ℚ (Polynomial ℚ))) = f := by
    rw [PowerSeries.map_algebraMap_eq_subst_X,
      diagonal_subst f X (by simp) (by rw [diagonal_X]; simp), diagonal_X, PowerSeries.X_subst]

private theorem diagonal_G : diagonal G = -(1 + X) * log ℚ := by
    rw [G, map_mul, map_neg, diagonal_C]
    have hlog := diagonal_lift (log ℚ)
    rw [map_log] at hlog
    rw [hlog]
    simp

private theorem diagonal_H : diagonal H = subst (-(1 + X) * log ℚ) (exp ℚ) := by
    rw [H, diagonal_subst _ G G_zero (by rw [diagonal_G]; simp), diagonal_G]

private noncomputable def P (k : ℕ) : PowerSeries ℤ :=
  (ascPochhammer ℤ k).eval₂ PowerSeries.C (1 + X)

private theorem P_zero : P 0 = 1 := by
  simp [P]

private theorem P_constant (k : ℕ) : constantCoeff (P k) = (k.factorial : ℤ) := by
    rw [P, Polynomial.hom_eval₂]
    have hc : (constantCoeff : PowerSeries ℤ →+* ℤ).comp PowerSeries.C = RingHom.id ℤ := by
      exact constantCoeff_comp_C
    simp [hc, Polynomial.eval₂_at_apply]

private theorem phi_asc (k : ℕ) :
    (Polynomial.eval₂RingHom PowerSeries.C (1 + X)) (ascPochhammer ℚ k) = (P k).map (Int.castRingHom ℚ) := by
  change (ascPochhammer ℚ k).eval₂ C (1 + X) =
    PowerSeries.map (Int.castRingHom ℚ) ((ascPochhammer ℤ k).eval₂ C (1 + X))
  rw [Polynomial.hom_eval₂, ← ascPochhammer_eval₂, ← ascPochhammer_eval₂]
  simp

private theorem diagonal_H_sum :
    HasSum (fun k : ℕ => C ((-1 : ℚ)^k / (k.factorial : ℚ)) *
        (P k).map (Int.castRingHom ℚ) * X^k) (diagonal H) := by
    have h := PowerSeries.hasSum_eval₂ (φ := (Polynomial.eval₂RingHom PowerSeries.C (1 + X)))
      continuous_of_discreteTopology (PowerSeries.HasEval.X) H
    rw [← diagonal_apply H] at h
    simp only [H_coeff, map_mul, phi_asc] at h
    simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using h

private theorem diagonal_H_coeff (n : ℕ) :
    coeff n ((exp ℚ) * diagonal H) =
      ∑ k ∈ range (n+1), ((-1 : ℚ)^k / (k.factorial : ℚ)) *
        coeff (n-k) ((exp ℚ) * (P k).map (Int.castRingHom ℚ)) := by
    have h : HasSum (fun k : ℕ => coeff n ((exp ℚ) *
        (C ((-1 : ℚ)^k / (k.factorial : ℚ)) *
          (P k).map (Int.castRingHom ℚ) * X^k)))
        (coeff n ((exp ℚ) * diagonal H)) :=
      (diagonal_H_sum.mul_left (exp ℚ)).map
        (coeff n) (PowerSeries.WithPiTopology.continuous_coeff ℚ n)
    have hterm (k : ℕ) :
        coeff n ((exp ℚ) * (C ((-1 : ℚ)^k / (k.factorial : ℚ)) *
          (P k).map (Int.castRingHom ℚ) * X^k)) =
        if k ≤ n then ((-1 : ℚ)^k / (k.factorial : ℚ)) *
          coeff (n-k) ((exp ℚ) * (P k).map (Int.castRingHom ℚ)) else 0 := by
      rw [show (exp ℚ) * (C ((-1 : ℚ)^k / (k.factorial : ℚ)) *
          (P k).map (Int.castRingHom ℚ) * X^k) =
          (C ((-1 : ℚ)^k / (k.factorial : ℚ)) *
          ((exp ℚ) * (P k).map (Int.castRingHom ℚ))) * X^k by ring]
      rw [coeff_mul_X_pow']
      split_ifs <;> simp [coeff_C_mul]
    simp_rw [hterm] at h
    rw [← h.tsum_eq, tsum_eq_sum (s := range (n+1))]
    · apply sum_congr rfl
      intro k hk
      rw [if_pos (by have := mem_range.mp hk; omega)]
    · intro k hk
      exact if_neg (by have := hk; simp only [mem_range, not_lt] at this; omega)

private theorem factorial_ratio (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ n-k) :
    (((n+1).factorial : ℕ) : ℚ) / ((k.factorial : ℚ) * (j.factorial : ℚ)) =
      (n+1 : ℚ) * ((n-k-j).factorial : ℚ) * (n.choose k : ℚ) *
        ((n-k).choose j : ℚ) := by
    have hf1 : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n-k).factorial : ℚ) =
        (n.factorial : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    have hf2 : ((n-k).choose j : ℚ) * (j.factorial : ℚ) * ((n-k-j).factorial : ℚ) =
        ((n-k).factorial : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
    apply (div_eq_iff (mul_ne_zero (by exact_mod_cast k.factorial_ne_zero)
      (by exact_mod_cast j.factorial_ne_zero))).mpr
    calc
      ((n+1).factorial : ℚ) = (n+1 : ℚ) * (n.factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      _ = (n+1 : ℚ) * ((n.choose k : ℚ) * (k.factorial : ℚ) *
          (((n-k).choose j : ℚ) * (j.factorial : ℚ) * ((n-k-j).factorial : ℚ))) := by
        rw [hf2, hf1]
      _ = _ := by ring

private theorem scaled_term_multiple (n k : ℕ) (hk : k ≤ n+1) (hk0 : 0 < k) :
    (((n+1).factorial : ℚ) * ((-1 : ℚ)^k / (k.factorial : ℚ)) *
      coeff (n+1-k) ((exp ℚ) * (P k).map (Int.castRingHom ℚ))) ∈
        AddSubgroup.zmultiples (n+1 : ℚ) := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
    apply AddSubgroup.sum_mem
    intro j hj
    have hj' : j ≤ n+1-k := by exact mem_range_succ_iff.mp hj
    simp only [coeff_exp, Algebra.algebraMap_self_apply, coeff_map, Int.coe_castRingHom]
    by_cases he : n+1-k-j = 0
    · rw [he, coeff_zero_eq_constantCoeff, P_constant]
      have hjn : j ≤ n := by omega
      have hfac := factorial_ratio n 0 j (by omega) (by simpa using hjn)
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.sub_zero,
        Nat.choose_zero_right, mul_one] at hfac
      refine AddSubgroup.mem_zmultiples_iff.mpr
        ⟨(-1 : ℤ)^k * (n.choose j : ℤ) * ((n-j).factorial : ℤ), ?_⟩
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one, Int.cast_natCast]
      have hkf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      calc
        _ = ((-1 : ℚ)^k) * (((n+1).factorial : ℚ) / (j.factorial : ℚ)) := by
          rw [hfac]; ring
        _ = _ := by field_simp
    · have hkn : k ≤ n := by omega
      have hjn : j ≤ n-k := by omega
      have hfac := factorial_ratio n k j hkn hjn
      refine AddSubgroup.mem_zmultiples_iff.mpr
        ⟨(-1 : ℤ)^k * ((n-k-j).factorial : ℤ) * (n.choose k : ℤ) *
          ((n-k).choose j : ℤ) * coeff (n+1-k-j) (P k), ?_⟩
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one, Int.cast_natCast]
      calc
        _ = ((-1 : ℚ)^k) * (((n+1).factorial : ℚ) /
              ((k.factorial : ℚ) * (j.factorial : ℚ))) *
              ((coeff (n+1-k-j) (P k) : ℤ) : ℚ) := by rw [hfac]; ring
        _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

private theorem scaled_residue (n : ℕ) : ∃ z : ℤ,
    (n.factorial : ℚ) * coeff n ((exp ℚ) * diagonal H) = 1 + (n : ℚ) * (z : ℚ) := by
    cases n with
    | zero =>
      refine ⟨0, ?_⟩
      rw [diagonal_H_coeff]
      simp [P_zero]
    | succ n =>
      let term := fun k : ℕ => ((n+1).factorial : ℚ) *
        ((-1 : ℚ)^k / (k.factorial : ℚ)) *
        coeff (n+1-k) ((exp ℚ) * (P k).map (Int.castRingHom ℚ))
      have ht0 : term 0 = 1 := by
        simp [term, P_zero, Nat.factorial_ne_zero]
      have he : ((n+1).factorial : ℚ) * coeff (n+1) ((exp ℚ) * diagonal H) - 1 =
          ∑ k ∈ (range (n+2)).erase 0, term k := by
        rw [diagonal_H_coeff, mul_sum]
        simp only [← mul_assoc]
        have hsum := Finset.sum_erase_add (range (n+2)) term
          (mem_range.mpr (by omega : 0 < n+2))
        rw [ht0] at hsum
        change (∑ k ∈ range (n+2), term k) - 1 = _
        linear_combination -hsum
      have hm : ((n+1).factorial : ℚ) * coeff (n+1) ((exp ℚ) * diagonal H) - 1 ∈
          AddSubgroup.zmultiples (n+1 : ℚ) := by
        rw [he]
        apply AddSubgroup.sum_mem
        intro k hk
        have hks := mem_erase.mp hk
        exact scaled_term_multiple n k (by have := mem_range.mp hks.2; omega)
          (Nat.pos_of_ne_zero hks.1)
      obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
      refine ⟨z, ?_⟩
      simp only [zsmul_eq_mul] at hz
      push_cast
      linear_combination -hz

end D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.Expansion



namespace D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
open PowerSeries Finset
open D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree (egfSeries egfMul)
open D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree (egfSeries_mul derivative_egfSeries)
open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality (expSeries_add)

private theorem source_exponent_zero :
    constantCoeff (-1 + (1 + X) * (1 - log ℚ) : PowerSeries ℚ) = 0 := by
  simp

private theorem source_zero : constantCoeff sourceSeries = 1 := by
    have h := constantCoeff_subst_of_constantCoeff_zero source_exponent_zero (exp ℚ)
    change constantCoeff (subst _ (exp ℚ)) = _ at h
    simpa [sourceSeries] using h

private theorem source_derivative : derivative sourceSeries = -(log ℚ) * sourceSeries := by
    rw [sourceSeries, derivative_subst (.of_constantCoeff_zero source_exponent_zero), derivative_exp]
    have he : derivative (-1 + (1 + X) * (1 - log ℚ) : PowerSeries ℚ) = -(log ℚ) := by
      simp only [map_add, map_sub, map_neg, derivative_one, neg_zero,
        Derivation.leibniz, derivative_X, zero_add, one_mul, zero_sub, smul_eq_mul]
      have hl := derivative_log_mul_one_add_X (A := ℚ)
      linear_combination -hl
    rw [he]
    ring

private theorem source_initial (a : ℕ → ℤ) (ha : IsSourceSequence a) : a 0 = 1 := by
    have h := congrArg constantCoeff ha
    change constantCoeff (egfSeries (fun n => (a n : ℚ))) = constantCoeff sourceSeries at h
    rw [source_zero] at h
    simp only [egfSeries, ← coeff_zero_eq_constantCoeff, coeff_mk,
      Nat.factorial_zero, Nat.cast_one, div_one] at h
    exact_mod_cast h

private def logSeq (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1)^ (n+1) * ((n-1).factorial : ℤ)

private theorem log_egf : egfSeries (fun n => (logSeq n : ℚ)) = log ℚ := by
    ext n
    cases n with
    | zero => simp [egfSeries, logSeq]
    | succ n =>
      simp only [egfSeries, coeff_mk, logSeq, Nat.succ_ne_zero, if_false,
        Nat.succ_eq_add_one, Nat.add_sub_cancel, Int.cast_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one, Int.cast_natCast, coeff_log, Algebra.algebraMap_self_apply]
      rw [Nat.factorial_succ]
      push_cast
      field_simp

private theorem source_recurrence (a : ℕ → ℤ) (ha : IsSourceSequence a) (n : ℕ) :
    a (n+1) = - ∑ r ∈ range (n+1),
      (n.choose r : ℤ) * logSeq r * a (n-r) := by
    have hf : egfSeries (fun n => (a n : ℚ)) = sourceSeries := ha
    have hd := source_derivative
    simp only [← hf] at hd
    rw [derivative_egfSeries, ← log_egf] at hd
    have hm := egfSeries_mul (fun n => (logSeq n : ℚ)) (fun n => (a n : ℚ))
    rw [neg_mul, ← hm] at hd
    have hc := congrArg (coeff n) hd
    simp only [egfSeries, coeff_mk, map_neg] at hc
    have hq : (a (n+1) : ℚ) = - egfMul (fun n => (logSeq n : ℚ))
        (fun n => (a n : ℚ)) n := by
      have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      apply (div_left_inj' hn).mp
      simpa only [neg_div] using hc
    simp only [egfMul] at hq
    exact_mod_cast hq

private theorem prime_successor (a : ℕ → ℤ) (ha : IsSourceSequence a)
    (p : ℕ) (hp : Nat.Prime p) : Int.ModEq (p : ℤ) (a (p+1)) 1 := by
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    rw [← ZMod.intCast_eq_intCast_iff]
    have hr := source_recurrence a ha p
    have h0 := source_initial a ha
    have hz : (a (p+1) : ZMod p) = - (logSeq p : ZMod p) := by
      rw [hr, Int.cast_neg, Int.cast_sum]
      congr 1
      rw [Finset.sum_eq_single p]
      · simp [h0]
      · intro r hmem hrp
        by_cases hr0 : r = 0
        · subst r; simp [logSeq]
        · have hrd : p ∣ p.choose r := hp.dvd_choose_self hr0 (by
            have := mem_range.mp hmem; omega)
          have hcast : (p.choose r : ZMod p) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).mpr hrd
          simp [Int.cast_mul, Int.cast_natCast, hcast]
      · intro hnot; exact False.elim (hnot (mem_range.mpr (by omega)))
    rw [hz]
    by_cases hp2 : p = 2
    · subst p
      norm_num [logSeq]
    · have hpodd := hp.odd_of_ne_two hp2
      have hsign : (-1 : ZMod p)^(p+1) = 1 := (hpodd.add_odd odd_one).neg_one_pow
      simp only [logSeq, if_neg hp.ne_zero, Int.cast_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one, Int.cast_natCast]
      rw [hsign, one_mul, ZMod.wilsons_lemma]
      simp

private theorem source_split : sourceSeries = (exp ℚ) * D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.Expansion.diagonal D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.Expansion.H := by
    rw [D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.Expansion.diagonal_H]
    change subst (-1 + (1 + X) * (1 - log ℚ)) (exp ℚ) = _
    rw [show (-1 + (1 + X) * (1 - log ℚ) : PowerSeries ℚ) =
        X + (-(1 + X) * log ℚ) by ring,
      expSeries_add (by simp) (by simp), PowerSeries.X_subst]

private theorem source_residue (n : ℕ) : ∃ z : ℤ,
    (n.factorial : ℚ) * coeff n sourceSeries = 1 + (n : ℚ) * (z : ℚ) := by
    rw [source_split]
    exact D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.Expansion.scaled_residue n

private theorem source_exists : ∃ a : ℕ → ℤ, IsSourceSequence a := by
    classical
    let z := fun n => Classical.choose (source_residue n)
    refine ⟨fun n => 1 + (n : ℤ) * z n, ?_⟩
    ext n
    have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h := Classical.choose_spec (source_residue n)
    rw [D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.egf, coeff_mk]
    change ((1 + (n : ℤ) * z n : ℤ) : ℚ) / (n.factorial : ℚ) = _
    apply (div_eq_iff hn).mpr
    push_cast
    dsimp [z]
    linear_combination -h

private theorem source_uniform (a : ℕ → ℤ) (ha : IsSourceSequence a) (n : ℕ) :
    Int.ModEq (n : ℤ) (a n) 1 := by
    obtain ⟨z, hz⟩ := source_residue n
    rw [← ha] at hz
    simp only [D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.egf,
      coeff_mk] at hz
    have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hq : (a n : ℚ) = (1 + (n : ℤ) * z : ℤ) := by
      push_cast
      field_simp at hz
      linear_combination hz
    have hi : a n = 1 + (n : ℤ) * z := by exact Rat.intCast_inj.mp hq
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-z, ?_⟩
    rw [hi]
    ring

theorem result : claim := by
    refine ⟨source_exists, ?_⟩
    intro a ha p hp
    have hu := source_uniform a ha p
    have hs := prime_successor a ha p hp
    have hv := source_uniform a ha (p+1)
    constructor
    · convert (hu.add hs).sub (Int.ModEq.refl (n := (p : ℤ)) 2) using 1 <;> ring
    · have hcop : (p : ℤ).natAbs.Coprime ((p+1 : ℕ) : ℤ).natAbs := by
        simp only [Int.natAbs_natCast]
        rw [Nat.coprime_self_add_right]
        exact Nat.coprime_one_right p
      have hm := (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hs, hv⟩
      simpa [Nat.cast_mul, mul_comm] using hm


end D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
