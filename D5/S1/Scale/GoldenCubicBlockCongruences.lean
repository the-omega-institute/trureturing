/- GID: D5/S1/Scale/GoldenCubicBlockCongruences
   generality: I
   mirror-B: D5/B/S1/Scale/GoldenCubicBlockCongruences
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Cubic golden blocks have exact Lucas and Fibonacci residues and two-adic depths. -/

import D5.S1.Scale.Lucas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace D5.S1.Scale

open D5.S0.Carrier

/-- For every actual golden block index `3^j`, the Lucas value is four modulo
seventy-two. In particular its two-adic valuation is exactly two and the
cubic radicand `L_(3^j)^2 + 3` is one modulo nine. -/
theorem golden_cubic_lucas_block (j : ℕ) (hj : 1 ≤ j) :
    ((goldenLucas (3 ^ j) : ℤ) : ZMod 72) = 4 ∧
      padicValInt 2 (goldenLucas (3 ^ j)) = 2 ∧
      (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 9)) = 1 ∧
      (((goldenLucas (3 ^ j) ^ 2 : ℤ) : ZMod 5)) = 1 ∧
      (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 80)) = 19 ∧
      goldenLucas (3 ^ (j + 1)) =
        goldenLucas (3 ^ j) * (goldenLucas (3 ^ j) ^ 2 + 3) := by
  have trace_cube (z : GoldenInt) :
      trace (z ^ 3) = trace z ^ 3 - 3 * norm z * trace z := by
    simp [pow_succ, trace, norm, a_mul, b_mul]
    ring
  have triple (n : ℕ) :
      goldenLucas (3 * n) =
        goldenLucas n ^ 3 - 3 * (-1 : ℤ) ^ n * goldenLucas n := by
    calc
      goldenLucas (3 * n) = trace ((phi ^ n) ^ 3) := by
        rw [goldenLucas, pow_mul']
      _ = trace (phi ^ n) ^ 3 - 3 * norm (phi ^ n) * trace (phi ^ n) :=
        trace_cube (phi ^ n)
      _ = goldenLucas n ^ 3 - 3 * (-1 : ℤ) ^ n * goldenLucas n := by
        rw [golden_lucas_eq_trace_phi_pow, norm_phi_pow]
  have hmod : ∀ k : ℕ, ((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 72) = 4 := by
    intro k
    induction k with
    | zero => norm_num [goldenLucas, trace, phi, pow_succ]
    | succ k ih =>
        have hodd : Odd (3 ^ (k + 1)) := (by decide : Odd (3 : ℕ)).pow
        have hn : 3 ^ (k + 2) = 3 * 3 ^ (k + 1) := by ring
        rw [hn, triple, hodd.neg_one_pow]
        push_cast
        rw [ih]
        decide
  have hfive : ∀ k : ℕ,
      (((goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 : ℤ) : ZMod 5)) = 1 := by
    intro k
    induction k with
    | zero => norm_num [goldenLucas, trace, phi, pow_succ]; decide
    | succ k ih =>
        have hodd : Odd (3 ^ (k + 1)) := (by decide : Odd (3 : ℕ)).pow
        have hn : 3 ^ (k + 2) = 3 * 3 ^ (k + 1) := by ring
        rw [hn, triple, hodd.neg_one_pow]
        push_cast
        have hsq : ((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 5) ^ 2 = 1 := by
          simpa only [Int.cast_pow] using ih
        calc
          (((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 5) ^ 3 -
              -3 * ((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 5)) ^ 2 =
            ((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 5) ^ 2 *
              (((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 5) ^ 2 + 3) ^ 2 := by
                ring
          _ = 1 := by rw [hsq]; decide
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hx72 : ((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 72) = 4 := by
    simpa [Nat.add_comm] using hmod k
  have hx8 : ((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 8) = 4 := by
    have h := congrArg (ZMod.castHom (by decide : 8 ∣ 72) (ZMod 8)) hx72
    simpa only [map_intCast, map_ofNat] using h
  have hx8mod : goldenLucas (3 ^ (k + 1) : ℕ) % 8 = 4 :=
    (ZMod.intCast_eq_intCast_iff' (goldenLucas (3 ^ (k + 1))) 4 8).mp hx8
  have hx0 : goldenLucas (3 ^ (k + 1) : ℕ) ≠ 0 := by omega
  have hd4 : (4 : ℤ) ∣ goldenLucas (3 ^ (k + 1) : ℕ) := by omega
  have hn8 : ¬(8 : ℤ) ∣ goldenLucas (3 ^ (k + 1) : ℕ) := by omega
  have hlo : 2 ≤ padicValInt 2 (goldenLucas (3 ^ (k + 1) : ℕ)) := by
    have h := (padicValInt_dvd_iff_of_ne_one (by decide : 2 ≠ 1) 2
      (goldenLucas (3 ^ (k + 1)))).mp (by simpa using hd4)
    exact h.resolve_left hx0
  have hhi : ¬3 ≤ padicValInt 2 (goldenLucas (3 ^ (k + 1) : ℕ)) := by
    intro hv
    have hd8 : (8 : ℤ) ∣ goldenLucas (3 ^ (k + 1) : ℕ) := by
      have h := (padicValInt_dvd_iff_of_ne_one (by decide : 2 ≠ 1) 3
        (goldenLucas (3 ^ (k + 1)))).mpr (Or.inr hv)
      simpa using h
    exact hn8 hd8
  have hvx : padicValInt 2 (goldenLucas (3 ^ (k + 1) : ℕ)) = 2 := by omega
  have hx9 : ((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 9) = 4 := by
    have h := congrArg (ZMod.castHom (by decide : 9 ∣ 72) (ZMod 9)) hx72
    simpa only [map_intCast, map_ofNat] using h
  have hB : (((goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 + 3 : ℤ) : ZMod 9)) = 1 := by
    push_cast
    rw [hx9]
    decide
  have hC : (((goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 : ℤ) : ZMod 5)) = 1 :=
    hfive k
  have h16 : (((goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 + 3 : ℤ) : ZMod 16)) = 3 := by
    obtain ⟨a, ha⟩ := hd4
    rw [ha]
    calc
      (((4 * a) ^ 2 + 3 : ℤ) : ZMod 16) = 16 * (a : ZMod 16) ^ 2 + 3 := by
        push_cast
        ring
      _ = 3 := by
        rw [show (16 : ZMod 16) = 0 by decide]
        ring
  have h5 : (((goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 + 3 : ℤ) : ZMod 5)) = 4 := by
    simp only [Int.cast_add, hC]
    decide
  have h80 : (((goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 + 3 : ℤ) : ZMod 80)) = 19 := by
    have hm16 : (goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 + 3) % 16 = 3 :=
      (ZMod.intCast_eq_intCast_iff' _ 3 16).mp h16
    have hm5 : (goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 + 3) % 5 = 4 :=
      (ZMod.intCast_eq_intCast_iff' _ 4 5).mp h5
    apply (ZMod.intCast_eq_intCast_iff' _ 19 80).mpr
    omega
  have hstep : goldenLucas (3 ^ ((k + 1) + 1)) =
      goldenLucas (3 ^ (k + 1)) * (goldenLucas (3 ^ (k + 1)) ^ 2 + 3) := by
    have hn : 3 ^ ((k + 1) + 1) = 3 * 3 ^ (k + 1) := by ring
    have hodd : Odd (3 ^ (k + 1)) := (by decide : Odd (3 : ℕ)).pow
    rw [hn, triple, hodd.neg_one_pow]
    ring
  simpa [Nat.add_comm] using
    (And.intro hx72
      (And.intro hvx (And.intro hB (And.intro hC (And.intro h80 hstep)))))

/-- At every positive power-of-three index the original Fibonacci value is
two modulo four, so its two-adic valuation is exactly one. -/
theorem golden_cubic_fibonacci_block (j : ℕ) (hj : 1 ≤ j) :
    ((Nat.fib (3 ^ j) : ℕ) : ZMod 4) = 2 ∧
      padicValNat 2 (Nat.fib (3 ^ j)) = 1 ∧
      (Nat.fib (3 ^ (j + 1)) : ℤ) =
        (Nat.fib (3 ^ j) : ℤ) * (goldenLucas (3 ^ j) ^ 2 + 1) := by
  have coord_cube (z : GoldenInt) :
      (z ^ 3).b = z.b * (trace z ^ 2 - norm z) := by
    simp [pow_succ, trace, norm, a_mul, b_mul]
    ring
  have triple (n : ℕ) :
      (Nat.fib (3 * n) : ℤ) =
        (Nat.fib n : ℤ) * (goldenLucas n ^ 2 - (-1 : ℤ) ^ n) := by
    calc
      (Nat.fib (3 * n) : ℤ) = (phi ^ (3 * n)).b :=
        (golden_phi_pow_b_eq_fib_index (3 * n)).symm
      _ = ((phi ^ n) ^ 3).b := by rw [pow_mul']
      _ = (phi ^ n).b * (trace (phi ^ n) ^ 2 - norm (phi ^ n)) :=
        coord_cube (phi ^ n)
      _ = (Nat.fib n : ℤ) * (goldenLucas n ^ 2 - (-1 : ℤ) ^ n) := by
        rw [golden_phi_pow_b_eq_fib_index, ← golden_lucas_eq_trace_phi_pow, norm_phi_pow]
  have hmod : ∀ k : ℕ, ((Nat.fib (3 ^ (k + 1) : ℕ) : ℕ) : ZMod 4) = 2 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        have hodd : Odd (3 ^ (k + 1)) := (by decide : Odd (3 : ℕ)).pow
        have hx72 := (golden_cubic_lucas_block (k + 1) (by omega)).1
        have hx4 : ((goldenLucas (3 ^ (k + 1) : ℕ) : ℤ) : ZMod 4) = 0 := by
          have h := congrArg (ZMod.castHom (by decide : 4 ∣ 72) (ZMod 4)) hx72
          simpa only [map_intCast, map_ofNat, show (4 : ZMod 4) = 0 by decide] using h
        have hn : 3 ^ (k + 2) = 3 * 3 ^ (k + 1) := by ring
        rw [hn, ← Int.cast_natCast, triple, hodd.neg_one_pow]
        push_cast
        rw [ih, hx4]
        decide
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hf4 : ((Nat.fib (3 ^ (k + 1) : ℕ) : ℕ) : ZMod 4) = 2 := by
    simpa [Nat.add_comm] using hmod k
  have hfmod : Nat.fib (3 ^ (k + 1) : ℕ) % 4 = 2 :=
    (ZMod.natCast_eq_natCast_iff' (Nat.fib (3 ^ (k + 1))) 2 4).mp hf4
  have hf0 : Nat.fib (3 ^ (k + 1) : ℕ) ≠ 0 := by omega
  have hd2 : 2 ∣ Nat.fib (3 ^ (k + 1) : ℕ) := by omega
  have hn4 : ¬4 ∣ Nat.fib (3 ^ (k + 1) : ℕ) := by omega
  have hlo : 1 ≤ padicValNat 2 (Nat.fib (3 ^ (k + 1) : ℕ)) := by
    have h := (padicValNat_dvd_iff_le_of_ne_one (n := 1)
      (by decide : 2 ≠ 1) hf0).mp (by simpa using hd2)
    exact h
  have hhi : ¬2 ≤ padicValNat 2 (Nat.fib (3 ^ (k + 1) : ℕ)) := by
    intro hv
    have hd4 : 4 ∣ Nat.fib (3 ^ (k + 1) : ℕ) := by
      have h := (padicValNat_dvd_iff_le_of_ne_one (n := 2)
        (by decide : 2 ≠ 1) hf0).mpr hv
      simpa using h
    exact hn4 hd4
  have hvf : padicValNat 2 (Nat.fib (3 ^ (k + 1) : ℕ)) = 1 := by omega
  have hstep : (Nat.fib (3 ^ ((k + 1) + 1) : ℕ) : ℤ) =
      (Nat.fib (3 ^ (k + 1) : ℕ) : ℤ) *
        (goldenLucas (3 ^ (k + 1) : ℕ) ^ 2 + 1) := by
    have hn : 3 ^ ((k + 1) + 1) = 3 * 3 ^ (k + 1) := by ring
    have hodd : Odd (3 ^ (k + 1)) := (by decide : Odd (3 : ℕ)).pow
    rw [hn, triple, hodd.neg_one_pow]
    ring
  simpa [Nat.add_comm] using (And.intro hf4 (And.intro hvf hstep))

/-- A cubic block at an earlier index divides every later Lucas value, so
the later block is three modulo the square of the earlier block. -/
theorem golden_cubic_block_interlevel (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (goldenLucas (3 ^ j) ^ 2 + 3) %
      ((goldenLucas (3 ^ i) ^ 2 + 3) ^ 2) = 3 := by
  let x (n : ℕ) : ℤ := goldenLucas (3 ^ n)
  have step (n : ℕ) (hn : 1 ≤ n) : x (n + 1) = x n * (x n ^ 2 + 3) := by
    exact (golden_cubic_lucas_block n hn).2.2.2.2.2
  have hdiv : ∀ t : ℕ, x i ^ 2 + 3 ∣ x (i + 1 + t) := by
    intro t
    induction t with
    | zero =>
        simp [step i hi]
    | succ t ih =>
        have hn : i + 1 + (t + 1) = (i + 1 + t) + 1 := by omega
        rw [hn, step _ (by omega)]
        exact dvd_mul_of_dvd_left ih _
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ j by omega)
  have hd : x i ^ 2 + 3 ∣ x (i + 1 + t) := hdiv t
  have hd2 : (x i ^ 2 + 3) ^ 2 ∣ x (i + 1 + t) ^ 2 := pow_dvd_pow_of_dvd hd 2
  have hm : 3 < (x i ^ 2 + 3) ^ 2 := by nlinarith [sq_nonneg (x i)]
  dsimp [x] at hd2 hm ⊢
  have hzero : goldenLucas (3 ^ (i + 1 + t)) ^ 2 %
      (goldenLucas (3 ^ i) ^ 2 + 3) ^ 2 = 0 := Int.emod_eq_zero_of_dvd hd2
  have hthree : (3 : ℤ) % (goldenLucas (3 ^ i) ^ 2 + 3) ^ 2 = 3 :=
    Int.emod_eq_of_lt (by omega) hm
  rw [Int.add_emod, hzero, hthree]
  simp [hthree]

/-- The Lucas value at each positive power-of-three index is the product of
all earlier cubic blocks, starting with the value four at the first layer. -/
theorem golden_cubic_block_product (j : ℕ) (hj : 1 ≤ j) :
    goldenLucas (3 ^ j) =
      4 * ∏ i ∈ Finset.Ico 1 j, (goldenLucas (3 ^ i) ^ 2 + 3) := by
  let x (n : ℕ) : ℤ := goldenLucas (3 ^ n)
  have step (n : ℕ) (hn : 1 ≤ n) : x (n + 1) = x n * (x n ^ 2 + 3) := by
    exact (golden_cubic_lucas_block n hn).2.2.2.2.2
  have hprod : ∀ k : ℕ,
      x (k + 1) = 4 * ∏ i ∈ Finset.Ico 1 (k + 1), (x i ^ 2 + 3) := by
    intro k
    induction k with
    | zero => norm_num [x, goldenLucas, trace, phi, pow_succ]
    | succ k ih =>
        calc
          x ((k + 1) + 1) = x (k + 1) * (x (k + 1) ^ 2 + 3) :=
            step _ (by omega)
          _ = (4 * ∏ i ∈ Finset.Ico 1 (k + 1), (x i ^ 2 + 3)) *
                (x (k + 1) ^ 2 + 3) := by rw [ih]
          _ = 4 * ∏ i ∈ Finset.Ico 1 ((k + 1) + 1), (x i ^ 2 + 3) := by
            rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1)]
            ring
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  simpa only [Nat.add_comm] using hprod k

end D5.S1.Scale
