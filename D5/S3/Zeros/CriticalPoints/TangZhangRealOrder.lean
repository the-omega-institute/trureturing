/- GID: D5/S3/Zeros/CriticalPoints/TangZhangRealOrder
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/TangZhangRealOrder
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Hadamard]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.conjecture; result=D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.counterexample; claim=D5/S3/Zeros/CriticalPoints/TangZhangRealOrder.conjecture
   digest: The real-order reciprocal critical-point conjecture and its equality boundary. -/

import D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
import Mathlib.Tactic.FinCases

/-! The real-order reciprocal critical-point inequality and its equality boundary. -/

set_option autoImplicit false
noncomputable section

open Set Complex Matrix
open scoped BigOperators ComplexConjugate
namespace D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots

open Polynomial
open TangZhangOrderMinusTwo (P)

private theorem derivative_constant (m : ℕ) (a : ℂ) :
    derivative (P (fun _ : Fin (m + 1) => a)) =
      C ((m : ℂ) + 2) * ((X - C a) ^ m * (X - C (a / ((m : ℂ) + 2)))) := by
  have hn : (m : ℂ) + 2 ≠ 0 := by
    have hr : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    exact_mod_cast ne_of_gt hr
  have hd : (C ((m : ℂ) + 2) : ℂ[X]) * C (a / ((m : ℂ) + 2)) = C a := by
    rw [← map_mul, mul_div_cancel₀ _ hn]
  calc
    derivative (P (fun _ : Fin (m + 1) => a)) =
        (X - C a) ^ m * (C ((m : ℂ) + 2) * X - C a) := by
      have hP : P (fun _ : Fin (m + 1) => a) = X * (X - C a) ^ (m + 1) := by
        simp only [P, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hP, derivative_mul, derivative_X, one_mul, derivative_X_sub_C_pow,
        Nat.add_sub_cancel, pow_succ]
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_ofNat, map_one]
      ring
    _ = C ((m : ℂ) + 2) * ((X - C a) ^ m * (X - C (a / ((m : ℂ) + 2)))) := by
      linear_combination (X - C a) ^ m * hd

private theorem roots_constant (m : ℕ) (a : ℂ) :
    (derivative (P (fun _ : Fin (m + 1) => a))).roots =
      m • ({a} : Multiset ℂ) + {a / ((m : ℂ) + 2)} := by
  have hn : (m : ℂ) + 2 ≠ 0 := by
    have hr : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    exact_mod_cast ne_of_gt hr
  rw [derivative_constant, roots_C_mul _ hn,
    roots_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
    roots_pow, roots_X_sub_C, roots_X_sub_C]

/-- Coincident nonzero roots attain the asserted coefficient at every real order. -/
private theorem constant_roots_moment (n : ℕ) (hn : 1 ≤ n) (a : ℂ) (ha : a ≠ 0) (p : ℝ) :
    ((derivative (P (fun _ : Fin n => a))).roots.map (fun w => ‖w‖ ^ (-p))).sum =
      ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ _ : Fin n, ‖a‖ ^ (-p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hnorm : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 := by
    convert Complex.norm_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) + 2 by positivity) using 1 <;>
      push_cast <;> rfl
  have hmoment : ‖a / ((m : ℂ) + 2)‖ ^ (-p) = ((m : ℝ) + 2) ^ p * ‖a‖ ^ (-p) := by
    rw [norm_div, hnorm, Real.div_rpow (norm_nonneg _) (by positivity),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 2)]
    simp only [div_inv_eq_mul, mul_comm]
  rw [roots_constant]
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.nsmul_singleton,
    Multiset.map_replicate, Multiset.map_singleton, Multiset.sum_replicate,
    Multiset.sum_singleton, nsmul_eq_mul, hmoment, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hn' : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
  field_simp [hn']
  ring

end D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots

namespace D5.S3.Zeros.CriticalPoints.TangZhangRealOrder

open TangZhangOrderMinusTwo (P)

def c (n : ℕ) (p : ℝ) : ℝ := (((n : ℝ) + 1) ^ p + n - 1) / n

/-- Conjecture 1.13, including its proposed equality criterion at every real order. -/
def conjecture : Prop :=
    ∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) → ∀ p : ℝ, 1 ≤ p →
      (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum ≤
        c n p * ∑ j, ‖z j‖ ^ (-p)) ∧
      ((((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum =
        c n p * ∑ j, ‖z j‖ ^ (-p)) ↔ ∀ i j, z i = z j)

end D5.S3.Zeros.CriticalPoints.TangZhangRealOrder

namespace D5.S3.Zeros.CriticalPoints.TangZhangRealOrder

open Polynomial
open TangZhangOrderMinusTwo (P)

private theorem explicit_roots :
    (derivative (P ![(1 : ℂ), 2])).roots =
      {((1 - Real.sqrt 3 / 3 : ℝ) : ℂ), ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ)} := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsc : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by exact_mod_cast hs
  have hf : derivative (P ![(1 : ℂ), 2]) =
      C (3 : ℂ) * ((X - C ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ)) *
        (X - C ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ))) := by
    simp only [P, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      derivative_mul, derivative_X_sub_C, derivative_X]
    have hab : ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ) +
        ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ) = 2 := by push_cast; ring
    have hprod : (3 : ℂ) * ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ) *
        ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ) = 2 := by
      push_cast
      linear_combination -(1 / 3 : ℂ) * hsc
    have habC : (C ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ) +
        C ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ) : ℂ[X]) = 2 := by
      simpa only [map_add, map_ofNat] using congrArg (C : ℂ →+* ℂ[X]) hab
    have hprodC : (3 : ℂ[X]) * C ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ) *
        C ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ) = 2 := by
      simpa only [map_mul, map_ofNat] using congrArg (C : ℂ →+* ℂ[X]) hprod
    norm_num only [map_one, map_ofNat]
    linear_combination (3 * X) * habC - hprodC
  rw [hf, roots_C_mul _ (by norm_num), roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

private theorem explicit_sum :
    ((derivative (P ![(1 : ℂ), 2])).roots.map (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum = 3 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsl : Real.sqrt 3 < 3 := by nlinarith
  have ha : 0 < 1 - Real.sqrt 3 / 3 := by linarith
  have hb : 0 < 1 + Real.sqrt 3 / 3 := by linarith
  rw [explicit_roots]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, Real.rpow_neg_one, Complex.norm_real,
    Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
  field_simp
  nlinarith

/-- The proposed equality characterization at real order one fails. -/
theorem counterexample : ¬ conjecture := by
  intro h
  have hz : ∀ j : Fin 2, ![(1 : ℂ), 2] j ≠ 0 := by
    intro j
    fin_cases j <;> norm_num
  have he : ((derivative (P ![(1 : ℂ), 2])).roots.map
      (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum =
      ((((2 : ℝ) + 1) ^ (1 : ℝ) + 2 - 1) / 2) *
        ∑ j : Fin 2, ‖![(1 : ℂ), 2] j‖ ^ (-(1 : ℝ)) := by
    rw [explicit_sum]
    norm_num [Fin.sum_univ_two, Real.rpow_neg_one]
  have hc := (h 2 (by omega) ![(1 : ℂ), 2] hz 1 le_rfl).2.mp
    (show _ from he) (0 : Fin 2) (1 : Fin 2)
  norm_num at hc

end D5.S3.Zeros.CriticalPoints.TangZhangRealOrder

namespace D5.S3.Zeros.CriticalPoints.TangZhangRealOrder

open TangZhangOrderMinusTwo (P)

def claim : Prop :=
    (∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) → ∀ p : ℝ, 1 ≤ p →
       ((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum ≤
         c n p * ∑ j, ‖z j‖ ^ (-p)) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) → ∀ p : ℝ, 1 < p →
       (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum =
         c n p * ∑ j, ‖z j‖ ^ (-p) ↔ ∀ i j, z i = z j)) ∧
    ¬ conjecture

/-- The real-order inequality, its strict-order equality criterion, and the endpoint refutation. -/
theorem result : claim := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn z hz p hp
    have h := SchurMomentInequality.spectral_bound_and_rigidity (by omega : 0 < n)
      (fun j => (z j)⁻¹) (fun j => inv_ne_zero (hz j)) p hp
    rw [← SchurMomentNormalization.reciprocal_moment z hz p] at h
    simpa only [c, norm_inv, ← Real.rpow_neg_eq_inv_rpow] using h.1
  · intro n hn z hz p hp
    constructor
    · intro heq
      have h := SchurMomentInequality.spectral_bound_and_rigidity (by omega : 0 < n)
        (fun j => (z j)⁻¹) (fun j => inv_ne_zero (hz j)) p hp.le
      rw [← SchurMomentNormalization.reciprocal_moment z hz p] at h
      have he : ((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum =
          ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, ‖(z j)⁻¹‖ ^ p := by
        simpa only [c, norm_inv, ← Real.rpow_neg_eq_inv_rpow] using heq
      intro i j
      exact inv_injective (h.2 hp he i j)
    · intro heq
      let i₀ : Fin n := ⟨0, by omega⟩
      have hzconst : z = fun _ : Fin n => z i₀ := funext fun j => heq j i₀
      rw [hzconst]
      exact TangZhangConstantRoots.constant_roots_moment n hn (z i₀) (hz i₀) p
  · exact counterexample

end D5.S3.Zeros.CriticalPoints.TangZhangRealOrder
