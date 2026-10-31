/- GID: D5/S1/Recurrence/Invariants/LuschnyA323206Parity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/LuschnyA323206Parity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Ballot coefficients and Catalan parity prove Luschny's A323206 conjecture. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#22903; Proved).
Direct frozen dependencies (declaration statement_id):
D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.binary_catalan
  sha256:22e9a38eaef0b535a11f074b5cb2bbf9af2f900fa6a30c3aafefb6160b7ff175;
D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalanSeries
  sha256:18682fb8cb0da671f4d582ed20b987849bfe41eba3bfcb33e1279f655fae00a0.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23031.
All private theorems are consumed bind-only steps. Their consumers are:
ratio_pochhammer, neg_pochhammer_ne, pos_pochhammer -> coeff_eq;
first_sum, second_sum -> row_sum_q; row_sum_q -> row_sum_catalan_q;
coeff_eq -> z_cast_eq_A; row_sum_catalan_q -> sum_b_mod_two;
sum_b_mod_two -> sum_eval_odd; z_mod_two, catalan_mod_two_iff,
sum_eval_even, sum_eval_odd -> odd_z_iff; z_cast_eq_A, odd_z_iff -> result.
The literal terminating sum in A and the proposition in claim use the
preregistered expressions. Proofs reuse ordinaryHypergeometricCoefficient and
binary_catalan. The ballot coefficient is inlined: its private owner ballotE
in ShankarQStieltjesRefutation has generality I and cannot be imported here.
-/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

open scoped BigOperators
open PowerSeries
namespace D5.S1.Recurrence.Invariants.LuschnyA323206Parity

noncomputable def A (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1),
    ordinaryHypergeometricCoefficient (-(k : ℚ)) ((k : ℚ) + 1)
      (-(k : ℚ) - 1) j * (n : ℚ) ^ j


private theorem ratio_pochhammer (k j : ℕ) (hjk : j ≤ k) :
    (k + 1 : ℚ) * (ascPochhammer ℚ j).eval (-(k : ℚ)) =
      (k + 1 - j : ℕ) * (ascPochhammer ℚ j).eval (-(k : ℚ) - 1) := by
  have h : (ascPochhammer ℚ (j + 1)).eval (-(k : ℚ) - 1) =
      (-(k : ℚ) - 1) * (ascPochhammer ℚ j).eval (-(k : ℚ)) := by
    rw [ascPochhammer_succ_left]
    simp
  rw [ascPochhammer_succ_eval] at h
  rw [Nat.cast_sub (by omega : j ≤ k + 1)]
  push_cast
  linear_combination h


private theorem neg_pochhammer_ne (k j : ℕ) (hjk : j ≤ k) :
    (ascPochhammer ℚ j).eval (-(k : ℚ) - 1) ≠ 0 := by
  intro hz
  rw [ascPochhammer_eval_eq_zero_iff] at hz
  obtain ⟨r, hr, heq⟩ := hz
  have heq' : r = k + 1 := by
    have : (r : ℚ) = (k + 1 : ℚ) := by
      rw [heq]
      ring
    exact_mod_cast this
  omega

private theorem pos_pochhammer (k j : ℕ) :
    (ascPochhammer ℚ j).eval ((k : ℚ) + 1) =
      (j.factorial : ℚ) * ((k+j).choose j : ℚ) := by
  have h := ascPochhammer_nat_eq_natCast_descFactorial ℚ (k + 1) j
  rw [show (k : ℚ) + 1 = ((k + 1 : ℕ) : ℚ) by norm_num, h]
  rw [show k + 1 + j - 1 = k + j by omega]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rfl


private theorem coeff_eq (k j : ℕ) (hjk : j ≤ k) :
    ordinaryHypergeometricCoefficient (-(k : ℚ)) ((k : ℚ) + 1)
      (-(k : ℚ) - 1) j = ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ℚ) := by
  by_cases hj : j = 0
  · subst j
    simp [ordinaryHypergeometricCoefficient]
  rw [ordinaryHypergeometricCoefficient]
  have hden := neg_pochhammer_ne k j hjk
  have hratio := ratio_pochhammer k j hjk
  have hpos := pos_pochhammer k j
  have hfac : (j.factorial : ℚ) ≠ 0 := by positivity
  have hk : (k + 1 : ℚ) ≠ 0 := by positivity
  simp only [hj, ite_false, Int.cast_natCast]
  rw [hpos]
  have hchoose : ((k+j).choose (j-1) : ℚ) =
      ((j : ℚ) / (k + 1 : ℚ)) * ((k+j).choose j : ℚ) := by
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    rw [Nat.cast_choose ℚ (by omega : j' ≤ k + (j' + 1))]
    rw [Nat.cast_choose ℚ (by omega : j' + 1 ≤ k + (j' + 1))]
    have hs : k + (j' + 1) - j' = k + 1 := by omega
    have ht : k + (j' + 1) - (j' + 1) = k := by omega
    rw [hs, ht]
    simp only [Nat.factorial_succ]
    field_simp
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  rw [hchoose]
  have hratio' : (ascPochhammer ℚ j).eval (-(k : ℚ)) =
      (((k + 1 - j : ℕ) : ℚ) / (k + 1 : ℚ)) *
        (ascPochhammer ℚ j).eval (-(k : ℚ) - 1) := by
    calc
      (ascPochhammer ℚ j).eval (-(k : ℚ)) =
          (((k + 1 - j : ℕ) : ℚ) *
            (ascPochhammer ℚ j).eval (-(k : ℚ) - 1)) / (k + 1 : ℚ) := by
              field_simp [hk]
              simpa [mul_comm] using hratio
      _ = (((k + 1 - j : ℕ) : ℚ) / (k + 1 : ℚ)) *
            (ascPochhammer ℚ j).eval (-(k : ℚ) - 1) := by ring
  rw [hratio']
  field_simp [hden, hfac, hk]
  rw [Nat.cast_sub (by omega : j ≤ k + 1)]
  push_cast
  ring

end D5.S1.Recurrence.Invariants.LuschnyA323206Parity

namespace D5.S1.Recurrence.Invariants.LuschnyA323206Parity

private theorem first_sum (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), ((k + j).choose j : ℚ)) =
      ((2 * k + 1).choose (k + 1) : ℚ) := by
  have h := Nat.sum_range_add_choose k k
  have hn : (∑ j ∈ Finset.range (k + 1), (k + j).choose j) =
      (2 * k + 1).choose (k + 1) := by
    calc
      _ = ∑ j ∈ Finset.range (k + 1), (k + j).choose k := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa [Nat.add_sub_cancel_left] using
          (Nat.choose_symm (n := k + j) (k := k) (by omega : k ≤ k + j))
      _ = _ := by
        have hh : 2 * k + 1 = k + k + 1 := by omega
        rw [hh]
        simpa [Nat.add_comm] using h
  exact_mod_cast hn

private theorem second_sum (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      (if j = 0 then (0 : ℚ) else ((k + j).choose (j - 1) : ℚ))) =
      ((2 * k + 1).choose (k + 2) : ℚ) := by
  cases k with
  | zero => norm_num [Nat.choose]
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, ite_false, ite_true, add_zero]
    have h := Nat.sum_range_add_choose k (k + 2)
    simp only [Nat.add_sub_cancel]
    have hn : (∑ j ∈ Finset.range (k + 1),
        ((k + 1 + (j + 1)).choose (k + 2) : ℚ)) =
        ((k + k + 3).choose (k + 3) : ℚ) := by
      have hq := congrArg (fun x : ℕ => (x : ℚ)) h
      simpa [Nat.cast_sum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hq
    calc
      (∑ x ∈ Finset.range (k + 1), ((k + 1 + (x + 1)).choose x : ℚ)) =
          (∑ x ∈ Finset.range (k + 1), ((k + 1 + (x + 1)).choose (k + 2) : ℚ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hh := Nat.choose_symm (n := k + 1 + (j + 1)) (k := k + 2)
              (by omega : k + 2 ≤ k + 1 + (j + 1))
            rw [show k + 1 + (j + 1) - (k + 2) = j by omega] at hh
            exact_mod_cast hh
      _ = ((2 * (k + 1) + 1).choose (k + 3) : ℚ) := by
        rw [show 2 * (k + 1) + 1 = k + k + 3 by omega]
        exact hn
      _ = ((2 * (k + 1) + 1).choose ((k + 1) + 2) : ℚ) := by congr 2

private theorem row_sum_q (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ℚ)) =
      ((2 * k + 1).choose (k + 1) : ℚ) - ((2 * k + 1).choose (k + 2) : ℚ) := by
  calc
    (∑ j ∈ Finset.range (k + 1), ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ℚ)) =
        ∑ j ∈ Finset.range (k + 1),
          (((k+j).choose j : ℚ) -
            (if j = 0 then (0 : ℚ) else ((k+j).choose (j-1) : ℚ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j = 0
      · simp [h]
      · simp [h]
    _ = (∑ j ∈ Finset.range (k + 1), ((k+j).choose j : ℚ)) -
        (∑ j ∈ Finset.range (k + 1),
          (if j = 0 then (0 : ℚ) else ((k+j).choose (j-1) : ℚ))) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by rw [first_sum, second_sum]


private theorem row_sum_catalan_q (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ℚ)) =
      (catalan (k + 1) : ℚ) := by
  rw [row_sum_q]
  have hpascal : (2 * k + 2).choose (k + 2) =
      (2 * k + 1).choose (k + 1) + (2 * k + 1).choose (k + 2) := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega,
      show k + 2 = (k + 1) + 1 by omega, Nat.choose_succ_succ]
  have hcentral : (2 * k + 2).choose (k + 1) =
      2 * (2 * k + 1).choose (k + 1) := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega,
      Nat.choose_succ_left _ _ (by omega : 0 < k + 1)]
    have hs0 := Nat.choose_symm (n := 2 * k + 1) (k := k + 1)
      (by omega : k + 1 ≤ 2 * k + 1)
    rw [show 2 * k + 1 - (k + 1) = k by omega] at hs0
    have hs : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) := hs0
    rw [Nat.add_one_sub_one, hs]
    ring
  have hrel : (2 * k + 2) * (2 * k + 1).choose (k + 1) =
      (2 * k + 2).choose (k + 2) * (k + 2) := by
    simpa using Nat.add_one_mul_choose_eq (2 * k + 1) (k + 1)
  have hcat := succ_mul_catalan_eq_centralBinom (k + 1)
  have hcatQ := congrArg (fun x : ℕ => (x : ℚ)) hcat
  have hpascalQ := congrArg (fun x : ℕ => (x : ℚ)) hpascal
  have hcentralQ := congrArg (fun x : ℕ => (x : ℚ)) hcentral
  have hrelQ := congrArg (fun x : ℕ => (x : ℚ)) hrel
  dsimp [Nat.centralBinom] at hcatQ
  push_cast at hcatQ hpascalQ hcentralQ hrelQ
  have hdiff : (k + 2 : ℚ) *
      (((2 * k + 1).choose (k + 1) : ℚ) - ((2 * k + 1).choose (k + 2) : ℚ)) =
      ((2 * k + 2).choose (k + 1) : ℚ) := by
    nlinarith [hrelQ, hpascalQ, hcentralQ]
  have hcatQ' : (k + 2 : ℚ) * (catalan (k + 1) : ℚ) =
      ((2 * k + 2).choose (k + 1) : ℚ) := by
    convert hcatQ using 1; ring
  apply (mul_left_cancel₀ (by positivity : (k + 2 : ℚ) ≠ 0))
  exact hdiff.trans hcatQ'.symm


private noncomputable def z (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) * (n : ℤ) ^ j

private theorem z_cast_eq_A (n k : ℕ) :
    (z n k : ℚ) = A n k := by
  rw [z, A]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
  rw [coeff_eq k j hj']
  push_cast
  rfl

private theorem z_mod_two (n k : ℕ) :
    (z n k : ZMod 2) =
      ∑ j ∈ Finset.range (k + 1), ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ZMod 2) * (n : ZMod 2) ^ j := by
  rw [z]
  push_cast
  rfl


private theorem sum_b_mod_two (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ZMod 2)) =
      (catalan (k + 1) : ZMod 2) := by
  have hi : (∑ j ∈ Finset.range (k + 1), (if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ℤ) = (catalan (k + 1) : ℤ) := by
    exact_mod_cast row_sum_catalan_q k
  calc
    (∑ j ∈ Finset.range (k + 1), ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ZMod 2)) =
        ((∑ j ∈ Finset.range (k + 1), (if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ℤ) : ZMod 2) := by
      push_cast
      rfl
    _ = (catalan (k + 1) : ZMod 2) := by rw [hi]; norm_cast

private theorem catalan_mod_two_iff (k : ℕ) :
    (catalan (k + 1) : ZMod 2) = 1 ↔ ∃ e : ℕ, 0 < e ∧ k + 2 = 2 ^ e := by
  have h := D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.binary_catalan ((k + 1) + 1)
  change coeff ((k + 1) + 1)
    ((X * PowerSeries.catalanSeries.map (Nat.castRingHom ℤ)).map
      (Int.castRingHom (ZMod 2))) = 1 ↔ _ at h
  simp only [coeff_map, coeff_succ_X_mul, PowerSeries.catalanSeries_coeff] at h
  constructor
  · intro hk
    obtain ⟨e, he⟩ := h.mp hk
    refine ⟨e, ?_, he⟩
    cases e with
    | zero => simp at he
    | succ e => exact Nat.zero_lt_succ e
  · rintro ⟨e, he, hk⟩
    exact h.mpr ⟨e, hk⟩

private theorem sum_eval_even (n k : ℕ) (hn : Even n) :
    (∑ j ∈ Finset.range (k + 1), ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ZMod 2) * (n : ZMod 2) ^ j) = 1 := by
  have hn0 : (n : ZMod 2) = 0 := Even.natCast_zmod_two hn
  rw [Finset.sum_range_succ']
  simp [hn0]

private theorem sum_eval_odd (n k : ℕ) (hn : Odd n) :
    (∑ j ∈ Finset.range (k + 1), ((if j = 0 then (1 : ℤ) else ((k+j).choose j : ℤ) - (k+j).choose (j-1)) : ZMod 2) * (n : ZMod 2) ^ j) =
      (catalan (k + 1) : ZMod 2) := by
  have hn1 : (n : ZMod 2) = 1 := Odd.natCast_zmod_two hn
  rw [Finset.sum_congr rfl (fun j hj => by rw [hn1, one_pow, mul_one])]
  exact sum_b_mod_two k

private theorem odd_z_iff (n k : ℕ) :
    Odd (z n k) ↔
      Even n ∨ (Odd n ∧ ∃ e : ℕ, 0 < e ∧ k + 2 = 2 ^ e) := by
  rw [← ZMod.intCast_eq_one_iff_odd, z_mod_two]
  rcases Nat.even_or_odd n with he | ho
  · constructor
    · intro _
      exact Or.inl he
    · intro _
      rw [sum_eval_even n k he]
  · constructor
    · intro hs
      exact Or.inr ⟨ho, by
        rw [sum_eval_odd n k ho, catalan_mod_two_iff] at hs
        exact hs⟩
    · intro hrhs
      rcases hrhs with he' | ⟨_, hpow⟩
      · rcases he' with ⟨m, rfl⟩
        rcases ho with ⟨q, hq⟩
        omega
      · rw [sum_eval_odd n k ho, catalan_mod_two_iff]
        exact hpow

/-- The COMMENTS conjecture, with integrality explicit and oddness taken in Z. -/
def claim : Prop :=
  ∀ (n : ℕ) (k : ℕ), ∃ a : ℤ,
    (a : ℚ) = A n k ∧
      (Odd a ↔ Even n ∨ (Odd n ∧ ∃ e : ℕ, 0 < e ∧ k + 2 = 2 ^ e))

theorem result : claim := by
  intro n k
  refine ⟨z n k, z_cast_eq_A n k, odd_z_iff n k⟩


end D5.S1.Recurrence.Invariants.LuschnyA323206Parity
