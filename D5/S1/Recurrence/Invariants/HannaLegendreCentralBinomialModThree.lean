/- GID: D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's central-binomial power-series residue conjecture holds at every index. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19311
admission_basis: open-problem-resolution (#18887; Proved)
escape_witness: none
Direct frozen dependencies: D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.map_inverse.
This is a declaration address; no module pin is used as a declaration identity.
The rational summands and coefficient claims use the source expressions unchanged.
Declaration assessment (definitions have no proof_shape):
  term: definition; consumers: A, series3_eq.
  A: definition; consumers: claim, series3_eq, integral3, result.
  claim: definition; consumers: result.
  series3_eq: bind-only; consumers: integral3.
  integral3: bind-only; consumers: result.
  signed_central_mod_three: content; consumers: R_mod_three.
  R_mod_three: content; consumers: result.
  mod_three_series: bind-only; consumers: result.
  result: content; consumers: settling conclusion.
-/

import D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform
import Mathlib.Data.Nat.Choose.Lucas

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialModThree
open PowerSeries Finset D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform
attribute [local instance] Classical.propDecidable

/-- The summand `x^n / (1-2*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] * [Sum_{k=0..n} C(n,k)^2 * 3^k * x^k]`
of OEIS A246056. -/
noncomputable def term (n : ℕ) : PowerSeries ℚ :=
  X ^ n * ((1 - 2 * X : PowerSeries ℚ) ^ (2 * n + 1))⁻¹ *
    (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) ^ 2 * 2 ^ k) * X ^ k) *
    (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) ^ 2 * 3 ^ k) * X ^ k)

/-- OEIS A246056: "G.f.: Sum_{n>=0} x^n / (1-2*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] *
[Sum_{k=0..n} C(n,k)^2 * 3^k * x^k]", coefficientwise: the summand `n` has order `n`, so only `n ≤ m` contribute
to `x^m`. -/
noncomputable def A : PowerSeries ℚ := mk fun m => coeff m (∑ n ∈ Finset.range (m + 1), term n)

/-- OEIS A246056 (P. D. Hanna), conjecture: "a(n) == 1 (mod 3) when n = 2*A005836(k) for k >= 0, and
a(n) == 0 (mod 3) otherwise, where A005836 gives numbers whose base-3 representation contains no 2".
The terms are integers. -/
def claim : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, coeff n A = z ∧
    ((∃ m : ℕ, n = 2 * m ∧ 2 ∉ Nat.digits 3 m) → z ≡ 1 [ZMOD 3]) ∧
    ((¬ ∃ m : ℕ, n = 2 * m ∧ 2 ∉ Nat.digits 3 m) → z ≡ 0 [ZMOD 3])

private theorem series3_eq : weighted (Function.const ℕ 1) (2:ℚ) 2 3 = A := by
  ext m
  simp only [weighted, A, coeff_mk, Function.const_apply, map_one, one_mul]
  apply congrArg (coeff m)
  apply Finset.sum_congr rfl
  intro n hn
  unfold summand
  rw [rational_den]
  simp only [Q, term, map_ofNat]

private theorem integral3 (m : ℕ) : coeff m A =
    ((coeff m (weighted (Function.const ℕ 1) (2:ℤ) 2 3) : ℤ) : ℚ) := by
  have h := congrArg (coeff m) (map_series (Int.castRingHom ℚ) (2:ℤ) 2 3)
  rw [coeff_map] at h
  change ((coeff m (weighted (Function.const ℕ 1) (2:ℤ) 2 3) : ℤ) : ℚ) =
    coeff m (weighted (Function.const ℕ 1) (2:ℚ) 2 3) at h
  rw [series3_eq] at h
  exact h.symm

private theorem signed_central_mod_three (m : ℕ) :
    ((-1 : ZMod 3)^m * ((2*m).choose m : ZMod 3)) =
      if 2 ∉ Nat.digits 3 m then 1 else 0 := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · subst m
      norm_num [Nat.digits_zero]
    have hdiv : m / 3 < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by decide)
    have hsmall := ih (m / 3) hdiv
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div (p := 3) (n := 2*m) (k := m)
    have hl' : ((2*m).choose m : ZMod 3) =
        ((2*m % 3).choose (m % 3) : ZMod 3) *
        (((2*m) / 3).choose (m / 3) : ZMod 3) := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).mpr hl
    rw [Nat.digits_eq_cons_digits_div (by decide) hm]
    have hreconstruct : m = 3 * (m / 3) + m % 3 := by exact (Nat.div_add_mod m 3).symm
    have hsign : (-1 : ZMod 3)^m = (-1 : ZMod 3)^(m / 3) * (-1)^(m % 3) := by
      nth_rw 1 [hreconstruct]
      rw [pow_add, pow_mul]
      norm_num
    have hmod : m % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hd : m % 3 <;>
      simp only [List.mem_cons, not_or, hd, OfNat.one_ne_ofNat, OfNat.ofNat_ne_zero,
        false_or, not_false_eq_true, true_and, not_true_eq_false, false_and, ite_false] <;>
      rw [hl', hsign] <;>
      simp only [hd] at *
    · have ht : 2*m % 3 = 0 := by omega
      have hq : (2*m) / 3 = 2*(m / 3) := by omega
      simpa [ht, hq] using hsmall
    · have ht : 2*m % 3 = 2 := by omega
      have hq : (2*m) / 3 = 2*(m / 3) := by omega
      simpa [ht, hq, Nat.choose, mul_assoc, show (2 : ZMod 3) = -1 by decide] using hsmall
    · have ht : 2*m % 3 = 1 := by omega
      simp [ht, Nat.choose]


private theorem R_mod_three (N : ℕ) :
    ((coeff N (weighted (Function.const ℕ 1) (-1) (-1) 0) : ℤ) : ZMod 3) = if ∃ m : ℕ, N = 2*m ∧ 2 ∉ Nat.digits 3 m then 1 else 0 := by
  by_cases hd : 2 ∣ N
  · obtain ⟨m,rfl⟩ := hd
    have hp : (∃ r : ℕ, 2*m = 2*r ∧ 2 ∉ Nat.digits 3 r) ↔ 2 ∉ Nat.digits 3 m := by
      constructor
      · rintro ⟨r,hr,hgood⟩
        have : r = m := by omega
        simpa [this] using hgood
      · intro hgood
        exact ⟨m,rfl,hgood⟩
    rw [R_coeff]
    simp only [dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ (by decide : 0 < 2), hp,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    exact signed_central_mod_three m
  · have hp : ¬ ∃ m : ℕ, N = 2*m ∧ 2 ∉ Nat.digits 3 m := by
      rintro ⟨m,hm,_⟩
      exact hd ⟨m,hm⟩
    rw [R_coeff]
    simp [hd, hp]

private theorem mod_three_series :
    (weighted (Function.const ℕ 1) (2:ℤ) 2 3).map (Int.castRingHom (ZMod 3)) =
      (weighted (Function.const ℕ 1) (-1) (-1) 0).map (Int.castRingHom (ZMod 3)) := by
  rw [map_series, map_series]
  congr 1 <;> decide



theorem result : claim := by
  intro N
  let z : ℤ := coeff N (weighted (Function.const ℕ 1) (2:ℤ) 2 3)
  refine ⟨z, ?_, ?_, ?_⟩
  · exact integral3 N
  · intro hp
    have h := congrArg (coeff N) mod_three_series
    simp only [coeff_map] at h
    have hr := R_mod_three N
    rw [if_pos hp] at hr
    apply (ZMod.intCast_eq_intCast_iff z 1 3).mp
    simpa only [z, Int.coe_castRingHom, Int.cast_one] using h.trans hr
  · intro hp
    have h := congrArg (coeff N) mod_three_series
    simp only [coeff_map] at h
    have hr := R_mod_three N
    rw [if_neg hp] at hr
    apply (ZMod.intCast_eq_intCast_iff z 0 3).mp
    simpa only [z, Int.coe_castRingHom, Int.cast_zero] using h.trans hr

end D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialModThree
