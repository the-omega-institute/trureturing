/- GID: D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Both all-shift Gibonacci window gcds have a common period on positive odd lengths. -/

import D5.S0.Carrier.Euclidean
import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Ring.Parity

/-! Integer-seeded Fibonacci windows, their universal gcds, and joint odd-length periodicity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity

open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step)
open scoped BigOperators

/-- The integer Fibonacci step orbit with the specified two initial values. -/
def g (a b : ℤ) (n : ℕ) : ℤ := (step^[n] (a, b)).1

/-- The actual sum at shift `t`, with summation indices one through `k`. -/
def sumWindow (a b : ℤ) (t k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, g a b (t + i + 1)

/-- The actual sum of squares at the same shift and length. -/
def squareWindow (a b : ℤ) (t k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, g a b (t + i + 1) ^ 2

/-- A nonnegative finite representative of the infinite linear-window gcd. -/
def sumGcd (a b : ℤ) (k : ℕ) : ℕ :=
  Int.gcd (sumWindow a b 0 k) (sumWindow a b 1 k)

/-- A nonnegative finite representative of the infinite square-window gcd. -/
def squareGcd (a b : ℤ) (k : ℕ) : ℕ :=
  Nat.gcd (Int.gcd (squareWindow a b 0 k) (squareWindow a b 1 k))
    (squareWindow a b 2 k).natAbs

private theorem g_zero (a b : ℤ) : g a b 0 = a := rfl

private theorem g_one (a b : ℤ) : g a b 1 = b := rfl

private theorem g_rec (a b : ℤ) (n : ℕ) :
    g a b (n + 2) = g a b n + g a b (n + 1) := by
  simp only [g, Function.iterate_succ_apply', step]

private theorem g_unique (a b : ℤ) (u : ℕ → ℤ)
    (hzero : u 0 = a) (hone : u 1 = b)
    (hrec : ∀ n, u (n + 2) = u n + u (n + 1)) :
    ∀ n, u n = g a b n := by
  let E : LinearRecurrence ℤ := ⟨2, fun _ => 1⟩
  have solution (v : ℕ → ℤ) (hv : ∀ n, v (n + 2) = v n + v (n + 1)) :
      E.IsSolution v := by
    intro n
    change v (n + 2) = ∑ i : Fin 2, (1 : ℤ) * v (n + i)
    simpa [Fin.sum_univ_two] using hv n
  have same : u = g a b :=
    (E.eq_iff_eqOn_range_order u (g a b) (solution u hrec)
      (solution (g a b) (g_rec a b))).mpr (by
        intro n hn
        have hlt : n < 2 := Finset.mem_range.mp hn
        have hcases : n = 0 ∨ n = 1 := by omega
        rcases hcases with rfl | rfl
        · simpa only [g_zero] using hzero
        · simpa only [g_one] using hone)
  exact fun n => congrFun same n

private theorem sum_shift (a b : ℤ) (t k : ℕ) :
    sumWindow a b (t + 2) k = sumWindow a b t k + sumWindow a b (t + 1) k := by
  simp only [sumWindow, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    g_rec a b (t + i + 1)

private theorem square_term_rec (a b : ℤ) (n : ℕ) :
    g a b (n + 3) ^ 2 =
      2 * g a b (n + 2) ^ 2 + 2 * g a b (n + 1) ^ 2 - g a b n ^ 2 := by
  have h := g_rec a b (n + 1)
  rw [show n + 1 + 2 = n + 3 by omega] at h
  rw [h, g_rec]
  ring

private theorem square_shift (a b : ℤ) (t k : ℕ) :
    squareWindow a b (t + 3) k =
      2 * squareWindow a b (t + 2) k + 2 * squareWindow a b (t + 1) k -
        squareWindow a b t k := by
  simp only [squareWindow, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    square_term_rec a b (t + i + 1)

private theorem sum_spec (a b d : ℤ) (k : ℕ) :
    d ∣ (sumGcd a b k : ℤ) ↔ ∀ t : ℕ, d ∣ sumWindow a b t k := by
  have hfinite : d ∣ (sumGcd a b k : ℤ) ↔
      d ∣ sumWindow a b 0 k ∧ d ∣ sumWindow a b 1 k := by
    simp only [sumGcd, Int.gcd_def, Int.dvd_natCast, Nat.dvd_gcd_iff,
      Int.natAbs_dvd_natAbs]
  rw [hfinite]
  constructor
  · rintro ⟨hzero, hone⟩
    have h : ∀ t, d ∣ sumWindow a b t k ∧ d ∣ sumWindow a b (t + 1) k := by
      intro t
      induction t with
      | zero => exact ⟨hzero, hone⟩
      | succ t ih =>
        refine ⟨ih.2, ?_⟩
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, sum_shift] using
          (dvd_add ih.1 ih.2)
    exact fun t => (h t).1
  · intro h
    exact ⟨h 0, h 1⟩

private theorem square_spec (a b d : ℤ) (k : ℕ) :
    d ∣ (squareGcd a b k : ℤ) ↔ ∀ t : ℕ, d ∣ squareWindow a b t k := by
  have hfinite : d ∣ (squareGcd a b k : ℤ) ↔
      (d ∣ squareWindow a b 0 k ∧ d ∣ squareWindow a b 1 k) ∧
        d ∣ squareWindow a b 2 k := by
    simp only [squareGcd, Int.gcd_def, Int.dvd_natCast, Nat.dvd_gcd_iff,
      Int.natAbs_dvd_natAbs]
  rw [hfinite]
  constructor
  · rintro ⟨⟨hzero, hone⟩, htwo⟩
    have h : ∀ t, d ∣ squareWindow a b t k ∧
        d ∣ squareWindow a b (t + 1) k ∧ d ∣ squareWindow a b (t + 2) k := by
      intro t
      induction t with
      | zero => exact ⟨hzero, hone, htwo⟩
      | succ t ih =>
        refine ⟨ih.2.1, ih.2.2, ?_⟩
        have hd := dvd_sub (dvd_add (dvd_mul_of_dvd_right ih.2.2 2)
          (dvd_mul_of_dvd_right ih.2.1 2)) ih.1
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, square_shift] using hd
    exact fun t => (h t).1
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩

private theorem sum_telescope (a b : ℤ) (t k : ℕ) :
    sumWindow a b t k = g a b (t + k + 2) - g a b (t + 2) := by
  induction k with
  | zero => simp [sumWindow]
  | succ k ih =>
    rw [sumWindow, Finset.sum_range_succ]
    change sumWindow a b t k + g a b (t + k + 1) = _
    rw [ih]
    have h := g_rec a b (t + k + 1)
    rw [show t + k + 1 + 2 = t + (k + 1) + 2 by omega] at h
    rw [h]
    ring

private theorem square_telescope (a b : ℤ) (t k : ℕ) :
    squareWindow a b t k =
      g a b (t + k) * g a b (t + k + 1) - g a b t * g a b (t + 1) := by
  induction k with
  | zero => simp [squareWindow]
  | succ k ih =>
    rw [squareWindow, Finset.sum_range_succ]
    change squareWindow a b t k + g a b (t + k + 1) ^ 2 = _
    rw [ih]
    have h := g_rec a b (t + k)
    rw [show t + k + 2 = t + (k + 1) + 1 by omega] at h
    rw [h]
    have hi : t + (k + 1) = t + k + 1 := by omega
    rw [hi]
    ring

private theorem square_difference (a b : ℤ) (t k : ℕ) :
    squareWindow a b (t + 1) k - squareWindow a b t k =
      g a b (t + k + 1) ^ 2 - g a b (t + 1) ^ 2 := by
  rw [square_telescope, square_telescope]
  rw [show t + 1 + k = t + k + 1 by omega]
  rw [show t + k + 1 + 1 = t + k + 2 by omega, g_rec]
  rw [show t + 1 + 1 = t + 2 by omega, g_rec]
  ring

private def q (x y : ℤ) : ℤ := y ^ 2 - x * y - x ^ 2

private theorem q_orbit (a b : ℤ) (n : ℕ) :
    q (g a b n) (g a b (n + 1)) = (-1) ^ n * q a b := by
  induction n with
  | zero => simp [g_zero, g_one]
  | succ n ih =>
    calc
      q (g a b (n + 1)) (g a b (n + 1 + 1)) =
          -q (g a b n) (g a b (n + 1)) := by
        rw [show n + 1 + 1 = n + 2 by omega, g_rec]
        dsimp [q]
        ring
      _ = (-1) ^ (n + 1) * q a b := by rw [ih, pow_succ]; ring

private theorem q_difference_dvd (d x y X Y : ℤ)
    (hx : d ∣ X - x) (hy : d ∣ Y - y) : d ∣ q X Y - q x y := by
  have h : q X Y - q x y =
      (Y - y) * (Y + y - X) - (X - x) * (x + X + y) := by
    dsimp [q]
    ring
  rw [h]
  exact dvd_sub (dvd_mul_of_dvd_left hy _) (dvd_mul_of_dvd_left hx _)

private theorem sum_cap (a b : ℤ) (k : ℕ) (hk : Odd k) :
    (sumGcd a b k : ℤ) ∣ 2 * q a b := by
  have hw := (sum_spec a b (sumGcd a b k) k).mp dvd_rfl
  have hzero := hw 0
  have hone := hw 1
  rw [sum_telescope, Nat.zero_add] at hzero
  rw [sum_telescope, show 1 + k + 2 = k + 3 by omega] at hone
  have h := q_difference_dvd _ _ _ _ _ hzero hone
  have hi : q (g a b (k + 2)) (g a b (k + 3)) - q (g a b 2) (g a b 3) =
      -(2 * q a b) := by
    have hlarge := q_orbit a b (k + 2)
    have hsmall := q_orbit a b 2
    rw [pow_add, hk.neg_one_pow] at hlarge
    norm_num at hlarge hsmall
    rw [show k + 2 + 1 = k + 3 by omega] at hlarge
    rw [hlarge, hsmall]
    ring
  rw [hi] at h
  exact dvd_neg.mp h

private theorem square_cap (a b : ℤ) (k : ℕ) (hk : Odd k) :
    (squareGcd a b k : ℤ) ∣ 2 * q a b := by
  have hw := (square_spec a b (squareGcd a b k) k).mp dvd_rfl
  have hd := dvd_sub (dvd_sub (hw 2) (dvd_mul_of_dvd_right (hw 1) 3))
    (dvd_neg.mpr (hw 0))
  have hi : squareWindow a b 2 k - 3 * squareWindow a b 1 k -
      -squareWindow a b 0 k =
      q (g a b (k + 1)) (g a b (k + 2)) - q (g a b 1) (g a b 2) := by
    have hzero := square_difference a b 0 k
    have hone := square_difference a b 1 k
    have ht := square_telescope a b 1 k
    simp only [Nat.zero_add, Nat.reduceAdd] at hzero hone ht
    rw [show 1 + k + 1 = k + 2 by omega] at hone
    rw [show 1 + k = k + 1 by omega, show k + 1 + 1 = k + 2 by omega] at ht
    dsimp [q]
    linear_combination hone - hzero - ht
  rw [hi] at hd
  have hlarge := q_orbit a b (k + 1)
  have hsmall := q_orbit a b 1
  rw [pow_add, hk.neg_one_pow] at hlarge
  norm_num at hlarge hsmall
  rw [show k + 1 + 1 = k + 2 by omega] at hlarge
  rw [hlarge, hsmall] at hd
  convert hd using 1; ring

private theorem q_zero_iff (a b : ℤ) : q a b = 0 ↔ a = 0 ∧ b = 0 := by
  have hn : D5.S0.Carrier.norm (⟨a, b⟩ : D5.S0.Carrier.GoldenInt) = -q a b := by
    dsimp [D5.S0.Carrier.norm, q]
    ring
  constructor
  · intro h
    have hz := (D5.S0.Carrier.norm_eq_zero_iff
      (⟨a, b⟩ : D5.S0.Carrier.GoldenInt)).mp (by rw [hn, h]; rfl)
    exact ⟨congrArg D5.S0.Carrier.GoldenInt.a hz,
      congrArg D5.S0.Carrier.GoldenInt.b hz⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem g_scale (a b c : ℤ) (n : ℕ) :
    g (c * a) (c * b) n = c * g a b n := by
  symm
  apply g_unique (c * a) (c * b) (fun n => c * g a b n)
  · rw [g_zero]
  · rw [g_one]
  · intro j
    rw [g_rec, mul_add]

private theorem sum_scale (a b c : ℤ) (t k : ℕ) :
    sumWindow (c * a) (c * b) t k = c * sumWindow a b t k := by
  simp only [sumWindow, g_scale, Finset.mul_sum]

private theorem square_scale (a b c : ℤ) (t k : ℕ) :
    squareWindow (c * a) (c * b) t k = c ^ 2 * squareWindow a b t k := by
  simp only [squareWindow, g_scale, mul_pow, Finset.mul_sum]

private theorem gcd_scale (a b c : ℤ) (k : ℕ) :
    sumGcd (c * a) (c * b) k = c.natAbs * sumGcd a b k ∧
    squareGcd (c * a) (c * b) k = c.natAbs ^ 2 * squareGcd a b k := by
  constructor
  · simp only [sumGcd, sum_scale, Int.gcd_def, Int.natAbs_mul, Nat.gcd_mul_left]
  · simp only [squareGcd, square_scale, Int.gcd_def, Int.natAbs_mul,
      Int.natAbs_pow, Nat.gcd_mul_left]

private theorem zero_gcds (k : ℕ) : sumGcd 0 0 k = 0 ∧ squareGcd 0 0 k = 0 := by
  simpa only [zero_mul, Int.natAbs_zero, zero_pow (by decide : 2 ≠ 0)] using
    gcd_scale 0 0 0 k

private theorem cast_state (a b : ℤ) (M n : ℕ) :
    (((step^[n] (a, b)).1 : ZMod M), ((step^[n] (a, b)).2 : ZMod M)) =
      step^[n] ((a : ZMod M), (b : ZMod M)) := by
  let castPair : ℤ × ℤ → ZMod M × ZMod M := fun v => (v.1, v.2)
  have hc : Function.Semiconj castPair step step := by
    intro v
    ext <;> simp [castPair, step]
  exact hc.iterate_right n (a, b)

private theorem g_mod_return (a b : ℤ) (M R : ℕ)
    (hR : ∀ v : ZMod M × ZMod M, step^[R] v = v) (n : ℕ) :
    (g a b (n + R) : ZMod M) = (g a b n : ZMod M) := by
  have hp :
      (((step^[n + R] (a, b)).1 : ZMod M),
        ((step^[n + R] (a, b)).2 : ZMod M)) =
      (((step^[n] (a, b)).1 : ZMod M), ((step^[n] (a, b)).2 : ZMod M)) := by
    rw [cast_state, cast_state, Function.iterate_add_apply, hR]
  exact congrArg Prod.fst hp

private theorem window_congruences (a b : ℤ) (M T : ℕ)
    (hG : ∀ n, (g a b (n + T) : ZMod M) = (g a b n : ZMod M)) (t k : ℕ) :
    (M : ℤ) ∣ sumWindow a b t (k + T) - sumWindow a b t k ∧
    (M : ℤ) ∣ squareWindow a b t (k + T) - squareWindow a b t k := by
  have hs : (sumWindow a b t (k + T) : ZMod M) = (sumWindow a b t k : ZMod M) := by
    simp only [sum_telescope, Int.cast_sub]
    rw [show t + (k + T) + 2 = (t + k + 2) + T by omega, hG]
  have hq : (squareWindow a b t (k + T) : ZMod M) =
      (squareWindow a b t k : ZMod M) := by
    simp only [square_telescope, Int.cast_sub, Int.cast_mul]
    rw [show t + (k + T) = (t + k) + T by omega,
      show t + k + T + 1 = (t + k + 1) + T by omega, hG, hG]
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, hs, sub_self]
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, hq, sub_self]

private theorem gcd_eq_of_congruences (W : ℕ → ℕ → ℤ) (A : ℕ → ℕ)
    (hspec : ∀ (d : ℤ) (k : ℕ), d ∣ (A k : ℤ) ↔ ∀ t, d ∣ W t k)
    (M k l : ℕ) (hk : A k ∣ M) (hl : A l ∣ M)
    (hdiff : ∀ t, (M : ℤ) ∣ W t l - W t k) : A l = A k := by
  have forward (k l : ℕ) (hcap : A k ∣ M)
      (hd : ∀ t, (M : ℤ) ∣ W t l - W t k) : A k ∣ A l := by
    apply Int.natCast_dvd_natCast.mp
    apply (hspec (A k) l).mpr
    intro t
    have hfirst := (hspec (A k) k).mp dvd_rfl t
    have hdelta := (Int.natCast_dvd_natCast.mpr hcap).trans (hd t)
    have hsum := dvd_add hdelta hfirst
    simpa only [sub_add_cancel] using hsum
  exact Nat.dvd_antisymm (forward l k hl (fun t => by
    simpa only [neg_sub] using dvd_neg.mpr (hdiff t))) (forward k l hk hdiff)

private theorem joint_period (a b : ℤ) :
    ∃ P : ℕ, 0 < P ∧ ∀ j : ℕ,
      sumGcd a b (2 * (j + P) + 1) = sumGcd a b (2 * j + 1) ∧
      squareGcd a b (2 * (j + P) + 1) = squareGcd a b (2 * j + 1) := by
  by_cases hz : q a b = 0
  · obtain ⟨rfl, rfl⟩ := (q_zero_iff a b).mp hz
    exact ⟨1, by decide, fun j => by rw [(zero_gcds _).1, (zero_gcds _).1,
      (zero_gcds _).2, (zero_gcds _).2]; exact ⟨rfl, rfl⟩⟩
  · let M := 2 * (q a b).natAbs
    have hM : 0 < M := Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hz)
    let R := (M ^ 2).factorial
    have hR : 0 < R := Nat.factorial_pos _
    have hreturn : ∀ v : ZMod M × ZMod M, step^[R] v = v :=
      (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.result.2 M hM (0, 0)).2.1
    have hG : ∀ n, (g a b (n + 2 * R) : ZMod M) = (g a b n : ZMod M) := by
      intro n
      rw [show n + 2 * R = (n + R) + R by omega,
        g_mod_return a b M R hreturn, g_mod_return a b M R hreturn]
    have hcaps (k : ℕ) (hk : Odd k) : sumGcd a b k ∣ M ∧ squareGcd a b k ∣ M := by
      constructor
      · have h := Int.natAbs_dvd_natAbs.mpr (sum_cap a b k hk)
        simpa [M, Int.natAbs_mul] using h
      · have h := Int.natAbs_dvd_natAbs.mpr (square_cap a b k hk)
        simpa [M, Int.natAbs_mul] using h
    refine ⟨R, hR, ?_⟩
    intro j
    have hk : Odd (2 * j + 1) := ⟨j, by omega⟩
    have hl : Odd (2 * (j + R) + 1) := ⟨j + R, by omega⟩
    have hidx : 2 * j + 1 + 2 * R = 2 * (j + R) + 1 := by omega
    have hd := window_congruences a b M (2 * R) hG
    constructor
    · apply gcd_eq_of_congruences (sumWindow a b) (sumGcd a b) (sum_spec a b)
        M (2 * j + 1) (2 * (j + R) + 1) (hcaps _ hk).1 (hcaps _ hl).1
      intro t
      simpa only [hidx] using (hd t (2 * j + 1)).1
    · apply gcd_eq_of_congruences (squareWindow a b) (squareGcd a b) (square_spec a b)
        M (2 * j + 1) (2 * (j + R) + 1) (hcaps _ hk).2 (hcaps _ hl).2
      intro t
      simpa only [hidx] using (hd t (2 * j + 1)).2

/-- Every integer seed pair has both genuine all-shift gcds and a common positive
period from the first odd length. The zero pair uses normalized gcd zero. -/
theorem result (a b : ℤ) :
    (g a b 0 = a ∧ g a b 1 = b ∧
      ∀ n : ℕ, g a b (n + 2) = g a b n + g a b (n + 1)) ∧
    (∀ u : ℕ → ℤ, u 0 = a → u 1 = b →
      (∀ n, u (n + 2) = u n + u (n + 1)) → ∀ n, u n = g a b n) ∧
    (∀ (k : ℕ) (d : ℤ),
      (d ∣ (sumGcd a b k : ℤ) ↔ ∀ t : ℕ, d ∣ sumWindow a b t k) ∧
      (d ∣ (squareGcd a b k : ℤ) ↔ ∀ t : ℕ, d ∣ squareWindow a b t k)) ∧
    (∀ (c : ℤ) (k : ℕ),
      sumGcd (c * a) (c * b) k = c.natAbs * sumGcd a b k ∧
      squareGcd (c * a) (c * b) k = c.natAbs ^ 2 * squareGcd a b k) ∧
    (∃ P : ℕ, 0 < P ∧ ∀ j : ℕ,
      sumGcd a b (2 * (j + P) + 1) = sumGcd a b (2 * j + 1) ∧
      squareGcd a b (2 * (j + P) + 1) = squareGcd a b (2 * j + 1)) ∧
    ((a = 0 ∧ b = 0) → ∀ k : ℕ, sumGcd a b k = 0 ∧ squareGcd a b k = 0) := by
  refine ⟨⟨g_zero a b, g_one a b, g_rec a b⟩, g_unique a b, ?_,
    gcd_scale a b, joint_period a b, ?_⟩
  · exact fun k d => ⟨sum_spec a b d k, square_spec a b d k⟩
  · rintro ⟨rfl, rfl⟩
    exact zero_gcds

end D5.S3.Arith.FibonacciAtomic.Windows.OddBlockGcdPeriodicity
