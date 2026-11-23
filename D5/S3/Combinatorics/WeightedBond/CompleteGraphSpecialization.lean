/- GID: D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization
   generality: I
   mirror-B: D5/B/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization
   mirror-E: none(waiver:kernel-checked-source-model)
   anchors: []
   utility: none
   digest: The complete-graph weighted bond evaluations in both coefficient conventions. -/

import D5.S3.Combinatorics.WeightedBond.CountableColors
import D5.S3.Combinatorics.WeightedBond.ExponentialSeries
import D5.S3.Combinatorics.WeightedBond.LagrangeBurmann
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! The complete-graph weighted bond evaluations in both coefficient conventions. -/

set_option autoImplicit false
open Finset PowerSeries

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

abbrev Mark := Polynomial ℚ

private def unmarked (r : ℕ) : PowerSeries Mark :=
  (oneBlockEGF r).map (algebraMap ℚ Mark)

private def kernel (q : ℕ) : PowerSeries Mark :=
  (inverseEGF (q+2)).map (algebraMap ℚ Mark)

private theorem kernel_subst (q : ℕ) : (kernel q).subst (unmarked (q+2)) = X := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ Mark))
    (inverseEGF_subst_oneBlockEGF (q+2) (by omega))
  change (MvPowerSeries.map (algebraMap ℚ Mark))
    ((inverseEGF (q+2)).subst (oneBlockEGF (q+2))) =
    (PowerSeries.map (algebraMap ℚ Mark)) X at h
  rw [PowerSeries.map_subst (.of_constantCoeff_zero
    (show constantCoeff (oneBlockEGF (q+2)) = 0 from blockSeries_zero _)), map_X] at h
  exact h

private theorem kernel_factor (q : ℕ) :
    kernel q = X * (inverseFactor q * PowerSeries.exp Mark) := by
  have hp : (inverseFactor q : PowerSeries ℚ).map (algebraMap ℚ Mark) = inverseFactor q := by
    ext j
    simp [coeff_map, inverseFactor]
  unfold kernel
  rw [inverseEGF_factor, _root_.map_mul, _root_.map_mul, map_X, hp, map_exp]

private theorem unmarked_eq (r : ℕ) :
    unmarked r = blockSeries (fun n => Polynomial.C (muComplete r n : ℚ)) := by
  ext n
  rw [unmarked, coeff_map]
  simp only [oneBlockEGF, blockSeries, coeff_mk]
  split_ifs <;> simp

private theorem marked_mul (r : ℕ) :
    C (Polynomial.X : Mark) * markedBlockEGF r =
      rescale Polynomial.X (unmarked r) := by
  ext n
  rw [coeff_C_mul, coeff_rescale, unmarked_eq]
  simp only [markedBlockEGF, blockSeries, coeff_mk]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [pow_succ]
    ring

private theorem subst_comp_mark (a b f : PowerSeries Mark) (ha : HasSubst a) (hb : HasSubst b) :
    PowerSeries.subst b (PowerSeries.subst a f) =
      PowerSeries.subst (PowerSeries.subst b a) f :=
  subst_comp_subst_apply (R := Mark) ha hb f

private theorem rescale_subst_mark (t : Mark) (f : PowerSeries Mark) :
    rescale t f = f.subst (C t * X) := by
  rw [rescale_eq_subst, PowerSeries.smul_eq_C_mul]

private theorem scaled_kernel_subst (q : ℕ) :
    PowerSeries.subst (markedBlockEGF (q+2))
      (X * rescale Polynomial.X (inverseFactor q * PowerSeries.exp Mark)) = X := by
  let t : Mark := Polynomial.X
  let A : PowerSeries Mark := markedBlockEGF (q+2)
  let B : PowerSeries Mark := unmarked (q+2)
  let U : PowerSeries Mark := inverseFactor q * PowerSeries.exp Mark
  let v : PowerSeries Mark := C t * X
  have hA : HasSubst A := .of_constantCoeff_zero (blockSeries_zero _)
  have hv : HasSubst v := .of_constantCoeff_zero
    (show constantCoeff (C t * (X : PowerSeries Mark)) = 0 by simp)
  have hB : HasSubst B := .of_constantCoeff_zero
    (show constantCoeff (unmarked (q+2)) = 0 by rw [unmarked_eq, blockSeries_zero])
  have hmark : PowerSeries.subst A v = rescale t B := by
    change PowerSeries.subst A (C t * X) = _
    rw [subst_mul hA, subst_C, subst_X hA]
    exact marked_mul (q+2)
  have hsub : PowerSeries.subst A (rescale t (kernel q)) = C t * X := by
    have h₁ : rescale t (kernel q) = PowerSeries.subst v (kernel q) :=
      rescale_subst_mark t (kernel q)
    have h₂ : PowerSeries.subst A v = PowerSeries.subst v B :=
      hmark.trans (rescale_subst_mark t B)
    calc
      _ = PowerSeries.subst A (PowerSeries.subst v (kernel q)) :=
        congrArg (PowerSeries.subst A) h₁
      _ = PowerSeries.subst (PowerSeries.subst A v) (kernel q) :=
        subst_comp_mark v A (kernel q) hv hA
      _ = PowerSeries.subst (PowerSeries.subst v B) (kernel q) :=
        congrArg (fun H : PowerSeries Mark => PowerSeries.subst H (kernel q)) h₂
      _ = PowerSeries.subst v (PowerSeries.subst B (kernel q)) :=
        (subst_comp_mark B v (kernel q) hB hv).symm
      _ = rescale t (PowerSeries.subst B (kernel q)) :=
        (rescale_subst_mark t (PowerSeries.subst B (kernel q))).symm
      _ = C t * X := by rw [kernel_subst, rescale_X]
  have hr : rescale t (kernel q) = C t * (X * rescale t U) := by
    rw [kernel_factor]
    change rescale t (X * U) = _
    rw [_root_.map_mul, rescale_X, mul_assoc]
  have hscaled : PowerSeries.subst A (C t * (X * rescale t U)) = C t * X := by
    exact (congrArg (PowerSeries.subst A) hr.symm).trans hsub
  rw [subst_mul hA, subst_C] at hscaled
  have hnonzero : C t ≠ 0 := fun hz => Polynomial.X_ne_zero (C_injective (hz.trans (map_zero C).symm))
  exact mul_left_cancel₀ hnonzero hscaled

@[simp] private theorem constant_inverseFactor (q : ℕ) :
    constantCoeff (inverseFactor q : PowerSeries Mark) = 1 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [inverseFactor]

private theorem constant_rescale (a : Mark) (P : PowerSeries Mark) :
    constantCoeff (rescale a P) = constantCoeff P := by
  simp [← coeff_zero_eq_constantCoeff, coeff_rescale]

/-- The inverse of the nonexponential factor has constant term one. -/
def reciprocalFactor (q : ℕ) (t : Mark) : PowerSeries Mark :=
  invOfUnit (rescale t (inverseFactor q)) 1

private theorem inverse_unit (q : ℕ) (t : Mark) :
    (rescale t (inverseFactor q) * rescale t (PowerSeries.exp Mark)) *
      (rescale (-t) (PowerSeries.exp Mark) * reciprocalFactor q t) = 1 := by
  have he := exp_mul_exp_eq_exp_add t (-t)
  rw [add_neg_cancel, rescale_zero_apply, constantCoeff_exp, map_one] at he
  have hp := mul_invOfUnit (rescale t (inverseFactor q)) 1
    (by rw [constant_rescale, constant_inverseFactor]; rfl)
  calc
    _ = (rescale t (inverseFactor q) * reciprocalFactor q t) *
        (rescale t (PowerSeries.exp Mark) * rescale (-t) (PowerSeries.exp Mark)) := by ac_rfl
    _ = 1 := by rw [he, mul_one]; exact hp

private theorem inverse_root (A U F : PowerSeries Mark) (hA : HasSubst A)
    (he : (X * U).subst A = X) (hU : U * F = 1) :
    A = X * F.subst A := by
  rw [subst_mul hA, subst_X hA] at he
  have hp := congrArg (substAlgHom hA) hU
  simp only [_root_.map_mul, _root_.map_one, coe_substAlgHom] at hp
  calc
    A = A * (U.subst A * F.subst A) := by rw [hp, mul_one]
    _ = X * F.subst A := by rw [← mul_assoc, he]

private theorem factor_power (n q : ℕ) (s t : Mark) :
    rescale s (PowerSeries.exp Mark) *
        (rescale (-t) (PowerSeries.exp Mark) * reciprocalFactor q t)^n =
      rescale (s-(n : Mark)*t) (PowerSeries.exp Mark) * (reciprocalFactor q t)^n := by
  rw [mul_pow, ← _root_.map_pow, exp_pow_eq_rescale_exp, rescale_rescale, ← mul_assoc,
    exp_mul_exp_eq_exp_add]
  congr 3
  ring

/-- The coefficient of the rank polynomial, with t the polynomial indeterminate. -/
theorem psiComplete_closed (n q : ℕ) :
    psiComplete (n+1) (q+2) =
      (n.factorial : Mark) * coeff n
        (rescale (1-(n+1 : Mark)*Polynomial.X) (PowerSeries.exp Mark) *
          (reciprocalFactor q Polynomial.X)^(n+1)) := by
  let t : Mark := Polynomial.X
  let A := markedBlockEGF (q+2)
  let F := rescale (-t) (PowerSeries.exp Mark) * reciprocalFactor q t
  have h0 : constantCoeff A = 0 := blockSeries_zero _
  have hA := inverse_root A (rescale t (inverseFactor q * PowerSeries.exp Mark)) F
    (.of_constantCoeff_zero h0) (scaled_kernel_subst q)
    (by rw [_root_.map_mul]; exact inverse_unit q t)
  have h := lagrange_burmann A (PowerSeries.exp Mark) F h0 hA n
  rw [derivative_exp] at h
  have he := factor_power (n+1) q (1 : Mark) t
  simp only [rescale_one, RingHom.id_apply, Nat.cast_succ] at he
  rw [he] at h
  rw [psiComplete_exponential, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  change _ * coeff (n+1) ((PowerSeries.exp Mark).subst A) = _
  linear_combination (n.factorial : Mark) * h

private theorem derivative_rescale_exp (s : Mark) :
    derivative (R := Mark) (rescale s (PowerSeries.exp Mark)) =
      C s * rescale s (PowerSeries.exp Mark) := by
  ext1 n
  rw [coeff_derivative, coeff_C_mul, coeff_rescale, coeff_rescale, coeff_exp, coeff_exp,
    pow_succ]
  have h : (algebraMap ℚ Mark) (1 / ((n+1).factorial : ℚ)) * (n+1 : Mark) =
      (algebraMap ℚ Mark) (1 / (n.factorial : ℚ)) := by
    have hq : 1 / ((n+1).factorial : ℚ) * (n+1 : ℚ) = 1 / (n.factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    simpa only [_root_.map_mul, _root_.map_add, _root_.map_one, map_natCast] using
      congrArg (algebraMap ℚ Mark) hq
  calc
    _ = s^(n+1) * ((algebraMap ℚ Mark) (1 / ((n+1).factorial : ℚ)) * (n+1 : Mark)) := by ring
    _ = _ := by rw [h, pow_succ]; ring

private theorem reverse_exponential (n r : ℕ) :
    Polynomial.X * reversePsi (n+1) r =
      ((n+1).factorial : Mark) * coeff (n+1)
        ((rescale Polynomial.X (PowerSeries.exp Mark)).subst (unmarked r)) := by
  open IncidenceAlgebra in
  have hh := sum_mu_grouped (V := Fin (n+1)) r (R := Mark)
    (fun p => Polynomial.X ^ (p.parts.card-1))
  have h := labeled_subst (R := Mark) (univ : Finset (Fin (n+1)))
    (fun k => Polynomial.X ^ k) (fun j => Polynomial.C (muComplete r j : ℚ))
  have hE : assemblyKernel (fun k => (Polynomial.X : Mark) ^ k) =
      rescale Polynomial.X (PowerSeries.exp Mark) := by
    ext k
    rw [assemblyKernel, coeff_mk, coeff_rescale, coeff_exp]
    ac_rfl
  simp only [card_univ, Fintype.card_fin, hE] at h
  rw [unmarked_eq, ← h]
  unfold reversePsi
  have hcast (z : ℤ) : Polynomial.C (z : ℚ) = (z : Mark) :=
    _root_.map_intCast (Polynomial.C (R := ℚ)) z
  simp only [hcast]
  rw [hh, mul_sum]
  apply sum_congr rfl
  intro p _
  have hp : 0 < p.parts.card := by
    by_contra! hn
    have hs := p.sum_card_parts
    simp [card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)] at hs
  rw [← hcast, partitionProduct, Int.cast_prod, map_prod,
    mul_left_comm, ← pow_succ', Nat.sub_add_cancel hp]
  ac_rfl

/-- The rank-reversed polynomial, including the constant coefficient at s = 0. -/
theorem reversePsi_closed (n q : ℕ) :
    reversePsi (n+1) (q+2) =
      (n.factorial : Mark) * coeff n
        (rescale (Polynomial.X-(n+1 : Mark)) (PowerSeries.exp Mark) *
          (reciprocalFactor q 1)^(n+1)) := by
  let s : Mark := Polynomial.X
  let A := unmarked (q+2)
  let F := rescale (-(1 : Mark)) (PowerSeries.exp Mark) * reciprocalFactor q 1
  have h0 : constantCoeff A = 0 := by
    change constantCoeff (unmarked (q+2)) = 0
    rw [unmarked_eq, blockSeries_zero]
  have hK := kernel_subst q
  rw [kernel_factor] at hK
  have hA := inverse_root A (inverseFactor q * PowerSeries.exp Mark) F
    (.of_constantCoeff_zero h0) hK (by
      have h := inverse_unit q 1
      simpa only [rescale_one, RingHom.id_apply] using h)
  have h := lagrange_burmann A (rescale s (PowerSeries.exp Mark)) F h0 hA n
  rw [derivative_rescale_exp, mul_assoc, coeff_C_mul] at h
  have he := factor_power (n+1) q s 1
  simp only [mul_one, Nat.cast_succ] at he
  rw [he] at h
  apply mul_left_cancel₀ (show s ≠ 0 from Polynomial.X_ne_zero)
  rw [reverse_exponential, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  change _ * coeff (n+1) ((rescale s (PowerSeries.exp Mark)).subst A) = _
  linear_combination (n.factorial : Mark) * h

theorem reversePsi_at_zero (n r : ℕ) :
    (reversePsi (n+1) r).eval 0 = (psiComplete (n+1) r).coeff n := by
  rw [reversePsi_eq_reflect (Nat.succ_pos _), ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
    Polynomial.revAt_zero, Nat.succ_sub_one]

end
end D5.S3.Combinatorics.WeightedBond

namespace D5.S3.Combinatorics.WeightedBond

open PowerSeries

/-- Question 7.1 with its source convention, and the printed rank reversal. -/
theorem result (n q : ℕ) :
    sourceSpecialization (n + 1) (q + 2) =
      (n.factorial : Mark) * coeff n
        (rescale (1 - (n + 1 : Mark) * Polynomial.X) (PowerSeries.exp Mark) *
          reciprocalFactor q Polynomial.X ^ (n + 1)) ∧
    reversePsi (n + 1) (q + 2) =
      (n.factorial : Mark) * coeff n
        (rescale (Polynomial.X - (n + 1 : Mark)) (PowerSeries.exp Mark) *
          reciprocalFactor q 1 ^ (n + 1)) ∧
    reversePsi (n + 1) (q + 2) = (sourceSpecialization (n + 1) (q + 2)).reflect n ∧
    (reversePsi (n + 1) (q + 2)).eval 0 =
      (sourceSpecialization (n + 1) (q + 2)).coeff n := by
  rw [sourceSpecialization_eq]
  exact ⟨psiComplete_closed n q, reversePsi_closed n q,
    by simpa using reversePsi_eq_reflect (Nat.succ_pos n) (q + 2),
    reversePsi_at_zero n (q + 2)⟩

end D5.S3.Combinatorics.WeightedBond
