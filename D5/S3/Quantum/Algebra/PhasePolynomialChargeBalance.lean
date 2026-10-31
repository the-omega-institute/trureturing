/- GID: D5/S3/Quantum/Algebra/PhasePolynomialChargeBalance
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PhasePolynomialChargeBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pinned diagonal charge balance used by complex phase polynomial invariants. -/

/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/physlib-phase-polynomial-LICENSE.txt.
Authors: Joseph Tooby-Smith

Source: leanprover-community/physlib, a8823c76303bab825824ddecb7bd540880c4ae62,
PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM/ChargeBalance.lean
and Invariants.lean (exists_infiniteOrder_unitary only).
Retirement: when this repository's pinned Mathlib supplies equivalent declarations,
remove the corresponding transplants and replace consumers with direct Mathlib imports.
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Tactic

namespace MvPolynomial

/-!

## A. Rescaling the variables

-/

open scoped Classical in
/-- Rescaling each variable `Xᵢ` by a constant `d i` multiplies the coefficient of the monomial `m`
  by `∏ᵢ (d i) ^ (m i)`. -/
lemma coeff_aeval_diag {σ R : Type*} [CommRing R] (d : σ → R) (f : MvPolynomial σ R)
    (m : σ →₀ ℕ) :
    (aeval (fun i => C (d i) * X i) f).coeff m = (m.prod fun i k => d i ^ k) * f.coeff m := by
  induction f using MvPolynomial.induction_on generalizing m with
  | C a =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, coeff_C]
    by_cases hm : (0 : σ →₀ ℕ) = m
    · subst hm; simp
    · rw [ite_eq_right hm, mul_zero]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp m, hq m, mul_add]
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    have hrw : (aeval (fun i => C (d i) * X i) p) * (C (d i) * X i)
        = C (d i) * ((aeval (fun i => C (d i) * X i) p) * X i) := by
      rw [mul_left_comm]
    rw [hrw, coeff_C_mul, coeff_mul_X', coeff_mul_X']
    by_cases hi : i ∈ m.support
    · rw [ite_eq_left hi, ite_eq_left hi, hp (m - Finsupp.single i 1)]
      have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.mpr hmi
      have hsplit : m = (m - Finsupp.single i 1) + Finsupp.single i 1 :=
        (tsub_add_cancel_of_le hle).symm
      have hprod : (m.prod fun i k => d i ^ k)
          = ((m - Finsupp.single i 1).prod fun i k => d i ^ k) * d i := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.prod_add_index' (by intro a; simp) (by intro a b c; rw [pow_add]),
          Finsupp.prod_single_index (by simp)]
        simp
      rw [hprod]
      ring
    · rw [ite_eq_right hi, ite_eq_right hi, mul_zero, mul_zero]

/-!

## B. Charge balancing

-/

/-- **Charge balancing.** If each variable `Xᵢ` carries an integer charge `w i`, `c` is a phase of
  infinite order, and the polynomial `f` is invariant under the charge rotation
  `Xᵢ ↦ c^{wᵢ} Xᵢ`, then every monomial with nonzero net charge has vanishing coefficient. -/
lemma coeff_eq_zero_of_charge_ne_zero {σ K : Type*} [Field K] (w : σ → ℤ) (c : K) (hc : c ≠ 0)
    (hroot : ∀ n : ℤ, c ^ n = 1 → n = 0) {f : MvPolynomial σ K}
    (hf : aeval (fun i => C (c ^ (w i)) * X i) f = f) {m : σ →₀ ℕ}
    (hm : ∑ i ∈ m.support, (m i : ℤ) * w i ≠ 0) :
    f.coeff m = 0 := by
  classical
  have key := coeff_aeval_diag (fun i => c ^ (w i)) f m
  rw [hf] at key
  have hgen : ∀ s : Finset σ, ∏ i ∈ s, (c ^ (w i)) ^ (m i)
      = c ^ (∑ i ∈ s, (m i : ℤ) * w i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert x t hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ hc]
      congr 1
      rw [← zpow_natCast (c ^ w x) (m x), ← zpow_mul, mul_comm]
  rw [Finsupp.prod, hgen] at key
  have hne : c ^ (∑ i ∈ m.support, (m i : ℤ) * w i) ≠ 1 := fun h => hm (hroot _ h)
  have h2 : (1 - c ^ (∑ i ∈ m.support, (m i : ℤ) * w i)) * f.coeff m = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · exact h

end MvPolynomial

namespace TwoHiggsDoublet.EffectivePotential
/-- There is a gauge phase of infinite order (`exp i`), needed to run charge balancing. -/
lemma exists_infiniteOrder_unitary :
    ∃ ω : unitary ℂ, ∀ n : ℤ, (ω : ℂ) ^ n = 1 → n = 0 := by
  have key : star (Complex.exp Complex.I) * Complex.exp Complex.I = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, Complex.conj_I, ← Complex.exp_add]; simp
  have key2 : Complex.exp Complex.I * star (Complex.exp Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, Complex.conj_I, ← Complex.exp_add]; simp
  refine ⟨⟨Complex.exp Complex.I, key, key2⟩, fun n hn => ?_⟩
  simp only at hn
  rw [← Complex.exp_int_mul, Complex.exp_eq_one_iff] at hn
  obtain ⟨k, hk⟩ := hn
  have hc : (n : ℂ) = (k : ℂ) * (2 * Real.pi) := by
    have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
    apply mul_right_cancel₀ hI
    rw [hk]; ring
  have hr : (n : ℝ) = (k : ℝ) * (2 * Real.pi) := by exact_mod_cast hc
  rcases eq_or_ne k 0 with hk0 | hk0
  · simp [hk0] at hr; exact_mod_cast hr
  · exfalso
    have h2k : (2 * (k : ℝ)) ≠ 0 := by
      simp only [mul_ne_zero_iff]; exact ⟨two_ne_zero, by exact_mod_cast hk0⟩
    have hpi : Real.pi = (n : ℝ) / (2 * (k : ℝ)) := by rw [eq_div_iff h2k, hr]; ring
    exact irrational_pi.ne_rat ((n : ℚ) / (2 * (k : ℚ))) (by rw [hpi]; push_cast; ring)


end TwoHiggsDoublet.EffectivePotential
