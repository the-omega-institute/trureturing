/- GID: D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's central-binomial power-series residue conjecture holds at every index. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19311
admission_basis: open-problem-resolution (#18888; Proved)
escape_witness: none
Direct frozen dependencies: D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.map_inverse.
This is a declaration address; no module pin is used as a declaration identity.
The rational summands and coefficient claims use the source expressions unchanged.
Declaration assessment (definitions have no proof_shape):
  term: definition; consumers: A, series4_eq, result.
  A: definition; consumers: claim, series4_eq, integral4, result.
  claim: definition; consumers: result.
  series4_eq: bind-only; consumers: integral4.
  integral4: bind-only; consumers: result.
  half_central_mod_two: content; consumers: central_mod_four.
  central_mod_four: content; consumers: R_mod_four.
  Q_two: bind-only; consumers: term_reduction_four.
  term_reduction_four: bind-only; consumers: coefficient_reduction_four.
  coefficient_reduction_four: bind-only; consumers: integer_coefficient_reduction_four.
  map_source_four: bind-only; consumers: integer_coefficient_reduction_four.
  map_R_four: bind-only; consumers: integer_coefficient_reduction_four.
  map_T2_four: bind-only; consumers: integer_coefficient_reduction_four.
  integer_coefficient_reduction_four: bind-only; consumers: source_residue_four.
  square_moment_mod_two: bind-only; consumers: twice_T2_four.
  sign_two: bind-only; consumers: R_mod_four.
  twice_T2_four: content; consumers: source_residue_four.
  R_mod_four: content; consumers: source_residue_four.
  source_residue_four: content; consumers: result.
  result: content; consumers: settling conclusion.
-/

import D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform
import Mathlib.Data.Nat.Choose.Lucas

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialModFour
open PowerSeries Finset D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform
attribute [local instance] Classical.propDecidable

/-- The summand `x^n / (1-3*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] * [Sum_{k=0..n} C(n,k)^2 * 3^k * x^k]`
of OEIS A246423. -/
noncomputable def term (n : ℕ) : PowerSeries ℚ :=
  X ^ n * ((1 - 3 * X : PowerSeries ℚ) ^ (2 * n + 1))⁻¹ *
    (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) ^ 2 * 2 ^ k) * X ^ k) *
    (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) ^ 2 * 3 ^ k) * X ^ k)

/-- OEIS A246423: "G.f.: Sum_{n>=0} x^n / (1-3*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] *
[Sum_{k=0..n} C(n,k)^2 * 3^k * x^k]", coefficientwise: the summand `n` has order `n`, so only `n ≤ m` contribute
to `x^m`. -/
noncomputable def A : PowerSeries ℚ := mk fun m => coeff m (∑ n ∈ Finset.range (m + 1), term n)

/-- OEIS A246423 (P. D. Hanna), conjecture: "a(n) == 2 (mod 4) iff n = 2^k for k>=2, and a(n) == 0 (mod 4)
elsewhere except at a(0)=1". The terms are integers. -/
def claim : Prop :=
  coeff 0 A = 1 ∧ ∀ n : ℕ, 0 < n → ∃ z : ℤ, coeff n A = z ∧
    (z ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k) ∧ ((¬ ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k) → z ≡ 0 [ZMOD 4])

private theorem series4_eq : weighted (Function.const ℕ 1) (3:ℚ) 2 3 = A := by
  ext m
  simp only [weighted, A, coeff_mk, Function.const_apply, map_one, one_mul]
  apply congrArg (coeff m)
  apply Finset.sum_congr rfl
  intro n hn
  unfold summand
  rw [rational_den]
  simp only [Q, term, map_ofNat]

private theorem integral4 (m : ℕ) : coeff m A =
    ((coeff m (weighted (Function.const ℕ 1) (3:ℤ) 2 3) : ℤ) : ℚ) := by
  have h := congrArg (coeff m) (map_series (Int.castRingHom ℚ) (3:ℤ) 2 3)
  rw [coeff_map] at h
  change ((coeff m (weighted (Function.const ℕ 1) (3:ℤ) 2 3) : ℤ) : ℚ) =
    coeff m (weighted (Function.const ℕ 1) (3:ℚ) 2 3) at h
  rw [series4_eq] at h
  exact h.symm

private theorem half_central_mod_two (m : ℕ) (hm : 0 < m) :
    ((2*m-1).choose (m-1) : ZMod 2) = if ∃ k : ℕ, m = 2^k then 1 else 0 := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h1 : m = 1
    · subst m
      norm_num
      exact ⟨0, rfl⟩
    have hq : 0 < m / 2 := by omega
    have hlt : m / 2 < m := Nat.div_lt_self hm (by decide)
    have hr := ih (m/2) hlt hq
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div (p := 2) (n := 2*m-1) (k := m-1)
    have hl' : ((2*m-1).choose (m-1) : ZMod 2) =
        (((2*m-1)%2).choose ((m-1)%2) : ZMod 2) *
        (((2*m-1)/2).choose ((m-1)/2) : ZMod 2) := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).mpr hl
    have hd : m % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases he : m % 2
    · have htop : (2*m-1)%2 = 1 := by omega
      have hbot : (m-1)%2 = 1 := by omega
      have htd : (2*m-1)/2 = 2*(m/2)-1 := by omega
      have hbd : (m-1)/2 = m/2-1 := by omega
      have hp : (∃ k : ℕ, m = 2^k) ↔ ∃ k : ℕ, m/2 = 2^k := by
        constructor
        · rintro ⟨k,hk⟩
          cases k with
          | zero => simp at hk; omega
          | succ k =>
            refine ⟨k, ?_⟩
            rw [hk, pow_succ]
            exact Nat.mul_div_cancel _ (by decide)
        · rintro ⟨k,hk⟩
          refine ⟨k+1, ?_⟩
          rw [pow_succ, ← hk]
          omega
      simpa [hl', htop, hbot, htd, hbd, hp] using hr
    · have htop : (2*m-1)%2 = 1 := by omega
      have hbot : (m-1)%2 = 0 := by exact Nat.sub_mod_eq_zero_of_mod_eq he
      have htd : (2*m-1)/2 = 2*(m/2) := by omega
      have hbd : (m-1)/2 = m/2 := by omega
      have hz : ((2*(m/2)).choose (m/2) : ZMod 2) = 0 := by
        apply (ZMod.natCast_eq_zero_iff _ _).mpr
        exact Nat.two_dvd_centralBinom_of_one_le hq
      have hp : ¬ ∃ k : ℕ, m = 2^k := by
        rintro ⟨k,hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k => rw [pow_succ] at hk; omega
      simp [hl', htop, hbot, htd, hbd, hz, hp]


private theorem central_mod_four (m : ℕ) (hm : 0 < m) :
    ((2*m).choose m : ℤ) ≡ (if ∃ k : ℕ, m = 2^k then 2 else 0) [ZMOD 4] := by
  have hc : (2*m).choose m = 2 * (2*m-1).choose (m-1) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    have h := Nat.choose_succ_succ (2*j+1) j
    have hs : (2*j+1).choose j = (2*j+1).choose (j+1) :=
      Nat.choose_symm_of_eq_add (by omega)
    have ht : 2*j.succ = (2*j+1).succ := by exact (Nat.add_zero (2*j+2)).symm
    rw [ht]
    simpa only [Nat.succ_sub_one] using (show (2*j+1).succ.choose j.succ =
      2 * (2*j+1).choose j from by rw [h, ← hs]; omega)
  have hh := half_central_mod_two m hm
  have hmod : ((2*m-1).choose (m-1) : ℤ) ≡
      (if ∃ k : ℕ, m = 2^k then 1 else 0) [ZMOD 2] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    simpa only [Int.cast_natCast, Int.cast_ite, Int.cast_one, Int.cast_zero] using hh
  have hmul := hmod.mul_left' (c := 2)
  rw [hc, Nat.cast_mul, Nat.cast_ofNat]
  simpa only [mul_ite, mul_one, mul_zero, Int.reduceMul] using hmul

private theorem Q_two (n : ℕ) :
    Q (2:ZMod 4) n = 1 + C (2*(n:ZMod 4)^2) * X := by
  ext k
  simp only [Q_coeff, map_add, coeff_C_mul]
  rcases k with _ | _ | k
  · simp [Q_coeff]
  · simp [Q_coeff, Nat.choose_one_right] <;> ring
  · have hp : (2:ZMod 4)^(k+1+1) = 0 := by
      rw [show k+1+1 = k+2 by omega, pow_add]
      rw [show (2:ZMod 4)^2 = 0 by decide, mul_zero]
    simp [Q_coeff, hp, coeff_X, show k+1+1 ≠ 0 by omega, show k+1+1 ≠ 1 by omega]

private theorem term_reduction_four (n : ℕ) :
    summand (-1:ZMod 4) 2 (-1) n = summand (-1) (-1) 0 n +
      C (2*(n:ZMod 4)^2) * X * summand (-1) (-1) 0 n := by
  simp only [summand, Q_zero, Q_two, mul_one]
  ring


private theorem coefficient_reduction_four (N : ℕ) :
    coeff (N+1) (weighted (Function.const ℕ 1) (-1:ZMod 4) 2 (-1)) =
      coeff (N+1) (weighted (Function.const ℕ 1) (-1:ZMod 4) (-1) 0) +
      2 * coeff N (weighted (fun n => (n:ZMod 4)^2) (-1) (-1) 0) := by
  simp only [weighted, coeff_mk, map_sum, Function.const_apply, map_one, one_mul]
  have hw : (∑ n ∈ range (N+1+1),
      coeff N (C ((n:ZMod 4)^2) * summand (-1) (-1) 0 n)) =
      ∑ n ∈ range (N+1), coeff N (C ((n:ZMod 4)^2) * summand (-1) (-1) 0 n) := by
    rw [sum_range_succ]
    simp only [coeff_C_mul, term_low (-1:ZMod 4) (-1) 0 (N+1) N (by omega), mul_zero,
      add_zero]
  rw [← hw, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  rw [term_reduction_four, map_add]
  rw [mul_assoc (C (2*(n:ZMod 4)^2)) X (summand (-1) (-1) 0 n),
    coeff_C_mul, coeff_succ_X_mul, coeff_C_mul]
  ring

private theorem map_source_four :
    (weighted (Function.const ℕ 1) (3:ℤ) 2 3).map (Int.castRingHom (ZMod 4)) = weighted (Function.const ℕ 1) (-1:ZMod 4) 2 (-1) := by
  rw [map_series]
  congr 1 <;> decide

private theorem map_R_four :
    (weighted (Function.const ℕ 1) (-1) (-1) 0).map (Int.castRingHom (ZMod 4)) = weighted (Function.const ℕ 1) (-1:ZMod 4) (-1) 0 := by
  rw [map_series]
  rfl

private theorem map_T2_four :
    (weighted (fun n => (n:ℤ)^2) (-1) (-1) 0).map (Int.castRingHom (ZMod 4)) = weighted (fun n => (n:ZMod 4)^2) (-1) (-1) 0 := by
  rw [map_weighted]
  congr 1
  funext n
  simp

private theorem integer_coefficient_reduction_four (N : ℕ) :
    ((coeff (N+1) (weighted (Function.const ℕ 1) (3:ℤ) 2 3) : ℤ) : ZMod 4) =
      ((coeff (N+1) (weighted (Function.const ℕ 1) (-1) (-1) 0) : ℤ) : ZMod 4) + 2*((coeff N (weighted (fun n => (n:ℤ)^2) (-1) (-1) 0) : ℤ) : ZMod 4) := by
  have h := coefficient_reduction_four N
  rw [← map_source_four, ← map_R_four, ← map_T2_four] at h
  simpa only [coeff_map, Int.coe_castRingHom] using h

private theorem square_moment_mod_two :
    (weighted (fun n => (n:ℤ)^2) (-1) (-1) 0).map (Int.castRingHom (ZMod 2)) = (weighted (fun n => (n:ℤ)) (-1) (-1) 0).map (Int.castRingHom (ZMod 2)) := by
  rw [map_weighted, map_weighted]
  congr 1
  funext n
  simp only [Int.coe_castRingHom, Int.cast_pow, Int.cast_natCast, ZMod.pow_card]


private theorem sign_two (m : ℕ) : (-1:ZMod 4)^m * 2 = 2 := by
  rcases neg_one_pow_eq_or (ZMod 4) m with h | h <;> rw [h] <;> decide

private theorem twice_T2_four (N : ℕ) :
    (2:ZMod 4) * ((coeff N (weighted (fun n => (n:ℤ)^2) (-1) (-1) 0) : ℤ) : ZMod 4) = if N = 1 then 2 else 0 := by
  have h := congrArg (coeff N) (square_moment_mod_two.trans T_mod_two)
  simp only [coeff_map, Int.coe_castRingHom, coeff_X] at h
  have hm : coeff N (weighted (fun n => (n:ℤ)^2) (-1) (-1) 0) ≡ (if N = 1 then 1 else 0) [ZMOD 2] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    simpa using h
  have hmul := hm.mul_left' (c := 2)
  have he := (ZMod.intCast_eq_intCast_iff _ _ 4).mpr hmul
  simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_ite, mul_one, mul_zero] using he

private theorem R_mod_four (N : ℕ) (hN : 0 < N) :
    ((coeff N (weighted (Function.const ℕ 1) (-1) (-1) 0) : ℤ) : ZMod 4) = if ∃ k : ℕ, 1 ≤ k ∧ N = 2^k then 2 else 0 := by
  by_cases hd : 2 ∣ N
  · obtain ⟨m,rfl⟩ := hd
    have hm : 0 < m := by exact Nat.pos_of_mul_pos_left hN
    have hp : (∃ k : ℕ, 1 ≤ k ∧ 2*m = 2^k) ↔ ∃ k : ℕ, m = 2^k := by
      constructor
      · rintro ⟨k,hk,he⟩
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        refine ⟨j, ?_⟩
        rw [pow_succ] at he
        omega
      · rintro ⟨k,rfl⟩
        exact ⟨k+1, by omega, by rw [pow_succ]; omega⟩
    have hc := (ZMod.intCast_eq_intCast_iff _ _ 4).mpr
      (central_mod_four m hm)
    simp only [Int.cast_natCast, Int.cast_ite, Int.cast_ofNat, Int.cast_zero] at hc
    rw [R_coeff]
    simp only [dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, hc, hp]
    split <;> simp [sign_two]
  · have hp : ¬ ∃ k : ℕ, 1 ≤ k ∧ N = 2^k := by
      rintro ⟨k,hk,rfl⟩
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      apply hd
      exact ⟨2^j, by rw [pow_succ]; omega⟩
    rw [R_coeff]
    simp [hd, hp]

private theorem source_residue_four (N : ℕ) (hN : 0 < N) :
    ((coeff N (weighted (Function.const ℕ 1) (3:ℤ) 2 3) : ℤ) : ZMod 4) =
      if ∃ k : ℕ, 2 ≤ k ∧ N = 2^k then 2 else 0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have h := integer_coefficient_reduction_four j
  rw [R_mod_four _ (by omega), twice_T2_four] at h
  have hp : (∃ k : ℕ, 1 ≤ k ∧ j+1 = 2^k) ↔
      j = 1 ∨ ∃ k : ℕ, 2 ≤ k ∧ j+1 = 2^k := by
    constructor
    · rintro ⟨k,hk,he⟩
      by_cases hk1 : k = 1
      · left; subst k; norm_num at he; omega
      · right; exact ⟨k, by omega, he⟩
    · rintro (hj | ⟨k,hk,he⟩)
      · exact ⟨1, by omega, by simpa [hj]⟩
      · exact ⟨k, by omega, he⟩
  rw [hp] at h
  by_cases hj : j = 1
  · have hn : ¬ ∃ k : ℕ, 2 ≤ k ∧ j+1 = 2^k := by
      rintro ⟨k,hk,he⟩
      have hle := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
      norm_num [hj] at he
      norm_num at hle
      omega
    rw [if_neg hn]
    simpa [hj, show (2:ZMod 4)+2 = 0 by decide] using h
  · simpa [hj] using h



theorem result : claim := by
  constructor
  · simp [A, term, coeff_mul, Finset.Nat.antidiagonal_zero]
  · intro N hN
    let z : ℤ := coeff N (weighted (Function.const ℕ 1) (3:ℤ) 2 3)
    have hz := source_residue_four N hN
    refine ⟨z, ?_, ?_, ?_⟩
    · exact integral4 N
    · constructor
      · intro he
        by_contra hp
        rw [if_neg hp] at hz
        have he' := (ZMod.intCast_eq_intCast_iff z 2 4).mpr he
        have : (0:ZMod 4) = 2 := by simpa only [z, hz, Int.cast_ofNat] using he'
        exact (by decide : (0:ZMod 4) ≠ 2) this
      · intro hp
        rw [if_pos hp] at hz
        apply (ZMod.intCast_eq_intCast_iff z 2 4).mp
        simpa [z] using hz
    · intro hp
      rw [if_neg hp] at hz
      apply (ZMod.intCast_eq_intCast_iff z 0 4).mp
      simpa [z] using hz

end D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialModFour
