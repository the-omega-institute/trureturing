/- GID: D5/S3/Constants/Moments/A331474HankelBridge
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/A331474HankelBridge
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: Literal A331474 moments admit a signed continuant Hankel bridge. -/

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/- Library search (2026-09-24): neither this repository nor pinned Mathlib contains
   the literal A331474 determinant identity, a signed integral moment-to-Hankel
   theorem, or a Hankel theorem for Jacobi continued fractions.  The proof below
   uses the pinned Catalan power-series equation, polynomial basis-change
   determinant, adjugate/Cramer identities, and determinant-preserving adjacent
   column operation directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Polynomial

namespace D5.S3.Constants.Moments.A331474HankelBridge

/-- The unsigned Catalan-derivative moments in the literal OEIS source. -/
def b (n : Nat) : Int :=
  Int.ofNat ((2 * n + 2).choose n)

/-- The literal alternating binomial transform in A331474, at offset zero. -/
def s (n : Nat) : Int :=
  ∑ k ∈ Finset.range (n + 1), (-1 : Int) ^ (n - k) * b k

/-- The literal `(n+1)`-square Hankel determinant in A331474. -/
def H (n : Nat) : Int :=
  Matrix.det (fun i j : Fin (n + 1) => s (i.1 + j.1))

/-- The alternating diagonal coefficient of the source-specific monic recurrence. -/
def a (n : Nat) : Int :=
  if n % 2 = 0 then 4 else 0

/-- Monic polynomials for the signed Catalan-derivative functional. -/
def P : Nat → Int[X]
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C 4
  | n + 2 =>
      (Polynomial.X - Polynomial.C (a (n + 1))) * P (n + 1) + P n

/-- Evaluation of a polynomial by the unsigned moment functional. -/
def B (f : Int[X]) : Int :=
  f.sum fun n c => c * b n

/-- Evaluation of a polynomial by the literal alternating moment functional. -/
def S (f : Int[X]) : Int :=
  f.sum fun n c => c * s n

/-- Constant terms of the signed orthogonal polynomials. -/
def p (n : Nat) : Int :=
  (P n).coeff 0

/-- Literal-source evaluations of the signed orthogonal polynomials. -/
def u (n : Nat) : Int :=
  S (P n)

private def catalanInt : PowerSeries Int :=
  PowerSeries.map (Nat.castRingHom Int) PowerSeries.catalanSeries

private def F0 : PowerSeries Int :=
  PowerSeries.derivative Int catalanInt

private def F1 : PowerSeries Int :=
  (1 - 4 * PowerSeries.X) * F0

private def tail : Nat → PowerSeries Int
  | n => if n % 2 = 0 then F0 else F1

private def A : Nat → Int[X]
  | 0 => 1
  | 1 => 1 - Polynomial.C 4 * Polynomial.X
  | n + 2 =>
      (1 - Polynomial.C (a (n + 1)) * Polynomial.X) * A (n + 1) +
        Polynomial.X ^ 2 * A n

private def Q : Nat → Int[X]
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      (1 - Polynomial.C (a (n + 1)) * Polynomial.X) * Q (n + 1) +
        Polynomial.X ^ 2 * Q n

private def E (n : Nat) : PowerSeries Int :=
  F0 * (A n : PowerSeries Int) - (Q n : PowerSeries Int)

private def G : Nat → PowerSeries Int
  | 0 => F0
  | n + 1 => -tail (n + 1) * G n

private theorem source_moments :
    (∀ n, PowerSeries.coeff n F0 = b n) ∧
    (∀ n, b (n + 1) = s (n + 1) + s n) := by
  have hcoeff (n : Nat) : PowerSeries.coeff n F0 = b n := by
    have hcatNat := succ_mul_catalan_eq_centralBinom (n + 1)
    have hchooseNat := Nat.choose_succ_right_eq (2 * n + 2) n
    have hcatNat' : (n + 2) * catalan (n + 1) =
        (2 * n + 2).choose (n + 1) := by
      simpa [Nat.centralBinom, show 2 * (n + 1) = 2 * n + 2 by omega] using hcatNat
    have hchooseNat' : (2 * n + 2).choose (n + 1) * (n + 1) =
        (2 * n + 2).choose n * (n + 2) := by
      simpa [show 2 * n + 2 - n = n + 2 by omega] using hchooseNat
    have hmul : (n + 2) * ((n + 1) * catalan (n + 1)) =
        (n + 2) * (2 * n + 2).choose n := by
      calc
        (n + 2) * ((n + 1) * catalan (n + 1)) =
            ((n + 2) * catalan (n + 1)) * (n + 1) := by ring
        _ = (2 * n + 2).choose (n + 1) * (n + 1) := by rw [hcatNat']
        _ = (2 * n + 2).choose n * (n + 2) := hchooseNat'
        _ = (n + 2) * (2 * n + 2).choose n := by ring
    have hbinomNat : (n + 1) * catalan (n + 1) = (2 * n + 2).choose n := by
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
    have hbinom := congrArg Int.ofNat hbinomNat
    rw [F0, PowerSeries.coeff_derivative]
    simp only [catalanInt, PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff,
      b]
    simpa [mul_comm] using hbinom
  have htransform (n : Nat) : b (n + 1) = s (n + 1) + s n := by
    have hsign (k : Nat) (hk : k ∈ Finset.range (n + 1)) :
        (-1 : Int) ^ (n + 1 - k) = -((-1 : Int) ^ (n - k)) := by
      have hk' : k ≤ n := by simpa [Finset.mem_range] using hk
      rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
      ring
    have hneg :
        (∑ k ∈ Finset.range (n + 1), (-1 : Int) ^ (n + 1 - k) * b k) =
          -(∑ k ∈ Finset.range (n + 1), (-1 : Int) ^ (n - k) * b k) := by
      calc
        (∑ k ∈ Finset.range (n + 1), (-1 : Int) ^ (n + 1 - k) * b k) =
            ∑ k ∈ Finset.range (n + 1), -((-1 : Int) ^ (n - k) * b k) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hsign k hk]
              ring
        _ = -(∑ k ∈ Finset.range (n + 1),
            (-1 : Int) ^ (n - k) * b k) := by
              rw [Finset.sum_neg_distrib]
    symm
    calc
      s (n + 1) + s n =
          ((∑ k ∈ Finset.range (n + 1),
              (-1 : Int) ^ (n + 1 - k) * b k) + b (n + 1)) + s n := by
        rw [s, Finset.sum_range_succ]
        norm_num
      _ = b (n + 1) := by rw [hneg, s]; ring
  exact ⟨hcoeff, htransform⟩

private theorem source_tails :
    F1 * (1 + PowerSeries.X ^ 2 * F0) = 1 ∧
    F0 * (1 - 4 * PowerSeries.X + PowerSeries.X ^ 2 * F1) = 1 ∧
    E 1 = -PowerSeries.X ^ 2 * tail 1 * E 0 := by
  have hcat : catalanInt ^ 2 * PowerSeries.X + 1 = catalanInt := by
    have hmapped := congrArg (PowerSeries.map (Nat.castRingHom Int))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simpa [catalanInt] using hmapped
  have hder :
      catalanInt ^ 2 + 2 * catalanInt * F0 * PowerSeries.X = F0 := by
    have hd := congrArg (PowerSeries.derivative Int) hcat
    simp only [map_add, (PowerSeries.derivative Int).leibniz,
      PowerSeries.derivative_one, PowerSeries.derivative_X,
      PowerSeries.derivative_pow, smul_eq_mul] at hd
    change catalanInt ^ 2 * 1 + PowerSeries.X *
      (2 * catalanInt ^ (2 - 1) * F0) + 0 = F0 at hd
    calc
      catalanInt ^ 2 + 2 * catalanInt * F0 * PowerSeries.X =
          catalanInt ^ 2 * 1 + PowerSeries.X *
            (2 * catalanInt ^ (2 - 1) * F0) + 0 := by
              norm_num
              ring_nf
      _ = F0 := hd
  have hfd :
      F0 * (1 - 2 * PowerSeries.X * catalanInt) = catalanInt ^ 2 := by
    have hc2 : catalanInt ^ 2 =
        F0 - 2 * catalanInt * F0 * PowerSeries.X := eq_sub_of_add_eq hder
    calc
      F0 * (1 - 2 * PowerSeries.X * catalanInt) =
          F0 - 2 * catalanInt * F0 * PowerSeries.X := by ring_nf
      _ = catalanInt ^ 2 := hc2.symm
  have hxC : PowerSeries.X * catalanInt ^ 2 = catalanInt - 1 := by
    have hc2x : catalanInt ^ 2 * PowerSeries.X = catalanInt - 1 :=
      eq_sub_of_add_eq hcat
    calc
      PowerSeries.X * catalanInt ^ 2 = catalanInt ^ 2 * PowerSeries.X := by ring_nf
      _ = catalanInt - 1 := hc2x
  have hCsub : catalanInt - PowerSeries.X * catalanInt ^ 2 = 1 := by
    rw [hxC]
    ring_nf
  have hsq :
      (1 - 2 * PowerSeries.X * catalanInt) ^ 2 =
        1 - 4 * PowerSeries.X := by
    calc
      (1 - 2 * PowerSeries.X * catalanInt) ^ 2 =
          1 - 4 * PowerSeries.X * catalanInt +
            4 * PowerSeries.X * (PowerSeries.X * catalanInt ^ 2) := by ring_nf
      _ = 1 - 4 * PowerSeries.X := by
        rw [hxC]
        ring_nf
  have haux :
      catalanInt ^ 2 * (1 - PowerSeries.X * catalanInt - PowerSeries.X) = 1 := by
    calc
      catalanInt ^ 2 * (1 - PowerSeries.X * catalanInt - PowerSeries.X) =
          catalanInt * (catalanInt - PowerSeries.X * catalanInt ^ 2) -
            PowerSeries.X * catalanInt ^ 2 := by ring_nf
      _ = 1 := by
        rw [hCsub, hxC]
        ring_nf
  have hmaster :
      (1 - 4 * PowerSeries.X) * F0 * (1 + PowerSeries.X ^ 2 * F0) = 1 := by
    calc
      (1 - 4 * PowerSeries.X) * F0 * (1 + PowerSeries.X ^ 2 * F0) =
          (1 - 2 * PowerSeries.X * catalanInt) *
            (F0 * (1 - 2 * PowerSeries.X * catalanInt)) *
              (1 + PowerSeries.X ^ 2 * F0) := by rw [← hsq]; ring_nf
      _ = catalanInt ^ 2 *
          ((1 - 2 * PowerSeries.X * catalanInt) *
            (1 + PowerSeries.X ^ 2 * F0)) := by rw [hfd]; ring_nf
      _ = catalanInt ^ 2 *
          (1 - PowerSeries.X * catalanInt - PowerSeries.X) := by
        congr 1
        calc
          (1 - 2 * PowerSeries.X * catalanInt) *
              (1 + PowerSeries.X ^ 2 * F0) =
            (1 - 2 * PowerSeries.X * catalanInt) +
              PowerSeries.X ^ 2 *
                (F0 * (1 - 2 * PowerSeries.X * catalanInt)) := by ring_nf
          _ = 1 - PowerSeries.X * catalanInt - PowerSeries.X := by
            rw [hfd]
            calc
              1 - 2 * PowerSeries.X * catalanInt +
                    PowerSeries.X ^ 2 * catalanInt ^ 2 =
                  1 - 2 * PowerSeries.X * catalanInt +
                    PowerSeries.X * (PowerSeries.X * catalanInt ^ 2) := by ring_nf
              _ = 1 - PowerSeries.X * catalanInt - PowerSeries.X := by
                rw [hxC]
                ring_nf
      _ = 1 := haux
  have heven : F1 * (1 + PowerSeries.X ^ 2 * F0) = 1 := by
    simpa [F1] using hmaster
  have hodd : F0 * (1 - 4 * PowerSeries.X + PowerSeries.X ^ 2 * F1) = 1 := by
    change F0 * (1 - 4 * PowerSeries.X +
      PowerSeries.X ^ 2 * ((1 - 4 * PowerSeries.X) * F0)) = 1
    calc
      F0 * (1 - 4 * PowerSeries.X +
          PowerSeries.X ^ 2 * ((1 - 4 * PowerSeries.X) * F0)) =
        (1 - 4 * PowerSeries.X) * F0 *
          (1 + PowerSeries.X ^ 2 * F0) := by ring
      _ = 1 := hmaster
  have hbase : E 1 = -PowerSeries.X ^ 2 * tail 1 * E 0 := by
    have hE0 : E 0 = F0 := by
      simp [E, A, Q]
    have hE1 : E 1 = F1 - 1 := by
      have hcast : (((4 : Int[X]) : PowerSeries Int)) = (4 : PowerSeries Int) := by
        calc
          (((4 : Int[X]) : PowerSeries Int)) =
              ((Polynomial.C 4 : Int[X]) : PowerSeries Int) := by norm_num
          _ = PowerSeries.C 4 := Polynomial.coe_C 4
          _ = 4 := map_ofNat (PowerSeries.C : Int →+* PowerSeries Int) 4
      simp [E, A, Q, F1]
      rw [hcast]
      ring
    have ht1 : tail 1 = F1 := by simp [tail]
    rw [hE0, hE1, ht1]
    calc
      F1 - 1 = -PowerSeries.X ^ 2 * F0 * F1 := by
        calc
          F1 - 1 = F1 - F1 * (1 + PowerSeries.X ^ 2 * F0) := by
            exact congrArg (fun z => F1 - z) heven.symm
          _ = -PowerSeries.X ^ 2 * F0 * F1 := by ring
      _ = -PowerSeries.X ^ 2 * F1 * F0 := by ring
  exact ⟨heven, hodd, hbase⟩

private theorem continuant_shape :
    (∀ n, Polynomial.IsMonicOfDegree (P n) n) ∧
    (∀ n, A n = Polynomial.reflect n (P n)) ∧
    (∀ n, tail n * (1 - PowerSeries.C (a n) * PowerSeries.X +
      PowerSeries.X ^ 2 * tail (n + 1)) = 1) ∧
    (∀ n, E (n + 2) =
      (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X) * E (n + 1) +
        PowerSeries.X ^ 2 * E n) := by
  have hmonic : ∀ n, Polynomial.IsMonicOfDegree (P n) n := by
    apply Nat.twoStepInduction
    · simp [P]
    · simpa [P, sub_eq_add_neg] using
        (Polynomial.isMonicOfDegree_X_add_one (-4 : Int))
    · intro n hn hn1
      rw [P]
      have hm := ((Polynomial.isMonicOfDegree_X_add_one (-a (n + 1))).mul hn1).add_right
        (by rw [hn.natDegree_eq]; omega)
      rw [sub_eq_add_neg, ← map_neg]
      simpa only [show 1 + (n + 1) = n + 2 by omega] using hm
  have hreflect : ∀ n, A n = Polynomial.reflect n (P n) := by
    apply Nat.twoStepInduction
    · simp [A, P]
    · rw [A, P, Polynomial.reflect_sub]
      simp only [Polynomial.reflect_one_X, Polynomial.reflect_C]
      ring
    · intro n hn hn1
      have hlinear :
          Polynomial.reflect (n + 2)
              ((Polynomial.X - Polynomial.C (a (n + 1))) * P (n + 1)) =
            (1 - Polynomial.C (a (n + 1)) * Polynomial.X) *
              Polynomial.reflect (n + 1) (P (n + 1)) := by
        have hm := Polynomial.reflect_mul
          (Polynomial.X - Polynomial.C (a (n + 1))) (P (n + 1))
          (F := 1) (G := n + 1) (Polynomial.natDegree_X_sub_C_le _)
          (hmonic (n + 1)).natDegree_eq.le
        have hc : Polynomial.reflect 1 (Polynomial.C (a (n + 1))) =
            Polynomial.C (a (n + 1)) * Polynomial.X :=
          by simpa using Polynomial.reflect_C (a (n + 1)) 1
        rw [Polynomial.reflect_sub, Polynomial.reflect_one_X, hc] at hm
        simpa only [show 1 + (n + 1) = n + 2 by omega] using hm
      have hshift :
          Polynomial.reflect (n + 2) (P n) =
            Polynomial.X ^ 2 * Polynomial.reflect n (P n) := by
        have hm := Polynomial.reflect_mul (1 : Int[X]) (P n)
          (F := 2) (G := n) (by simp) (hmonic n).natDegree_eq.le
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
      rw [P, A, Polynomial.reflect_add, hlinear, hshift, ← hn, ← hn1]
  have htail (n : Nat) :
      tail n * (1 - PowerSeries.C (a n) * PowerSeries.X +
        PowerSeries.X ^ 2 * tail (n + 1)) = 1 := by
    have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
    have hmod' : (n + 1) % 2 < 2 := Nat.mod_lt (n + 1) (by omega)
    by_cases hn : n % 2 = 0
    · have hn' : (n + 1) % 2 ≠ 0 := by omega
      simpa [tail, a, hn, hn', F1] using source_tails.2.1
    · have hn1 : n % 2 = 1 := by omega
      have hn' : (n + 1) % 2 = 0 := by omega
      simpa [tail, a, hn, hn1, hn'] using source_tails.1
  have hrecE (n : Nat) :
      E (n + 2) =
        (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X) * E (n + 1) +
          PowerSeries.X ^ 2 * E n := by
    change
      F0 * (((1 - Polynomial.C (a (n + 1)) * Polynomial.X) * A (n + 1) +
          Polynomial.X ^ 2 * A n : Int[X]) : PowerSeries Int) -
        (((1 - Polynomial.C (a (n + 1)) * Polynomial.X) * Q (n + 1) +
          Polynomial.X ^ 2 * Q n : Int[X]) : PowerSeries Int) =
      (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X) *
          (F0 * (A (n + 1) : PowerSeries Int) - (Q (n + 1) : PowerSeries Int)) +
        PowerSeries.X ^ 2 * (F0 * (A n : PowerSeries Int) - (Q n : PowerSeries Int))
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
    simp only [mul_add, mul_sub]
    ring
  exact ⟨hmonic, hreflect, htail, hrecE⟩

private theorem continuant_step (n : Nat) :
    E (n + 1) = -PowerSeries.X ^ 2 * tail (n + 1) * E n := by
  induction n with
    | zero =>
        simpa using source_tails.2.2
    | succ n ih =>
        have htail (m : Nat) :
            tail m * (1 - PowerSeries.C (a m) * PowerSeries.X +
              PowerSeries.X ^ 2 * tail (m + 1)) = 1 :=
          continuant_shape.2.2.1 m
        have hrecE (m : Nat) :
            E (m + 2) =
              (1 - PowerSeries.C (a (m + 1)) * PowerSeries.X) * E (m + 1) +
                PowerSeries.X ^ 2 * E m :=
          continuant_shape.2.2.2 m
        change E (n + 2) = -PowerSeries.X ^ 2 * tail (n + 2) * E (n + 1)
        rw [hrecE n]
        conv_lhs => rw [ih]
        have ht := htail (n + 1)
        calc
          (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X) *
                (-PowerSeries.X ^ 2 * tail (n + 1) * E n) +
              PowerSeries.X ^ 2 * E n =
            PowerSeries.X ^ 2 *
              (1 - (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X) *
                tail (n + 1)) * E n := by ring
          _ = PowerSeries.X ^ 4 * tail (n + 1) * tail (n + 2) * E n := by
            have hsolve :
                1 - (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X) *
                    tail (n + 1) =
                  PowerSeries.X ^ 2 * tail (n + 1) * tail (n + 2) := by
              calc
                1 - (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X) *
                    tail (n + 1) =
                  tail (n + 1) *
                    (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X +
                      PowerSeries.X ^ 2 * tail (n + 2)) -
                    (1 - PowerSeries.C (a (n + 1)) * PowerSeries.X) *
                      tail (n + 1) := by rw [ht]
                _ = PowerSeries.X ^ 2 * tail (n + 1) * tail (n + 2) := by
                  ring
            rw [hsolve]
            ring
          _ = -PowerSeries.X ^ 2 * tail (n + 2) *
              (-PowerSeries.X ^ 2 * tail (n + 1) * E n) := by ring
          _ = -PowerSeries.X ^ 2 * tail (n + 2) * E (n + 1) := by
            simpa only [] using
              congrArg (fun z => -PowerSeries.X ^ 2 * tail (n + 2) * z) ih.symm

private theorem continuant_error :
    (∀ n, E n = PowerSeries.X ^ (2 * n) * G n) ∧
    (∀ n, PowerSeries.constantCoeff (G n) = (-1 : Int) ^ n) := by
  have hstep := continuant_step
  have herror : ∀ n, E n = PowerSeries.X ^ (2 * n) * G n := by
    intro n
    induction n with
    | zero => simp [E, A, Q, G]
    | succ n ih =>
        rw [hstep n, ih]
        simp only [G]
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        ring
  have hconstant : ∀ n, PowerSeries.constantCoeff (G n) = (-1 : Int) ^ n := by
    have hF0constant : PowerSeries.constantCoeff F0 = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, source_moments.1]
      norm_num [b]
    intro n
    induction n with
    | zero =>
        simpa [G] using hF0constant
    | succ n ih =>
        simp only [G, map_mul, map_neg, ih, pow_succ]
        have ht : PowerSeries.constantCoeff (tail (n + 1)) = 1 := by
          by_cases hn : (n + 1) % 2 = 0
          · simp [tail, hn, hF0constant]
          · simp [tail, hn, F1, hF0constant]
        rw [ht]
        ring
  exact ⟨herror, hconstant⟩

private theorem signed_monomial_orthogonality :
    (∀ n k, k < n → B (Polynomial.X ^ k * P n) = 0) ∧
    (∀ n, B (Polynomial.X ^ n * P n) = (-1 : Int) ^ n) := by
  have hpair (f : Int[X]) (N : Nat) (hf : f.natDegree ≤ N) :
      B f = PowerSeries.coeff N
        (F0 * (Polynomial.reflect N f : PowerSeries Int)) := by
    rw [B, f.sum_over_range' (fun _ => by simp) (N + 1) (by omega)]
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := by simpa [Finset.mem_range] using hk
    rw [Polynomial.coeff_coe, Polynomial.coeff_reflect,
      ← Polynomial.revAt_le hkN, Polynomial.revAt_invol, source_moments.1]
    ring
  have hQdegree : ∀ n, n = 0 ∨ (Q n).natDegree < n := by
    apply Nat.twoStepInduction
    · exact Or.inl rfl
    · right
      simp [Q]
    · intro n hn hn1
      right
      by_cases hn0 : n = 0
      · subst n
        norm_num [Q, a]
      · have hqn : (Q n).natDegree < n := hn.resolve_left hn0
        have hqn1 : (Q (n + 1)).natDegree < n + 1 :=
          hn1.resolve_left (by omega)
        rw [Q]
        refine (Polynomial.natDegree_add_le _ _).trans_lt ?_
        apply max_lt
        · refine Polynomial.natDegree_mul_le.trans_lt ?_
          have hlinear :
              (1 - Polynomial.C (a (n + 1)) * Polynomial.X : Int[X]).natDegree ≤ 1 := by
            exact (Polynomial.natDegree_sub_le _ _).trans
              (max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp)))
          omega
        · refine Polynomial.natDegree_mul_le.trans_lt ?_
          have hx2 : (Polynomial.X ^ 2 : Int[X]).natDegree ≤ 2 := by simp
          omega
  have hreflect_mul (n k : Nat) :
      Polynomial.reflect (n + k) (Polynomial.X ^ k * P n) = A n := by
    have hm := Polynomial.reflect_mul (Polynomial.X ^ k : Int[X]) (P n)
      (F := k) (G := n) (by simp) (continuant_shape.1 n).natDegree_eq.le
    rw [Polynomial.reflect_monomial] at hm
    have hrev : Polynomial.revAt k k = 0 := by rw [Polynomial.revAt_le le_rfl]; simp
    rw [hrev, pow_zero, one_mul] at hm
    calc
      Polynomial.reflect (n + k) (Polynomial.X ^ k * P n) =
          Polynomial.reflect (k + n) (Polynomial.X ^ k * P n) := by
            rw [Nat.add_comm]
      _ = Polynomial.reflect n (P n) := hm
      _ = A n := (continuant_shape.2.1 n).symm
  have hQcoeff (n k : Nat) (hn : 0 < n) (hnk : n ≤ n + k) :
      PowerSeries.coeff (n + k) (Q n : PowerSeries Int) = 0 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt]
    exact (hQdegree n).resolve_left hn.ne' |>.trans_le hnk
  have hEzero (n k : Nat) (hk : k < n) :
      PowerSeries.coeff (n + k) (E n) = 0 := by
    rw [continuant_error.1 n, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hElead (n : Nat) :
      PowerSeries.coeff (2 * n) (E n) = (-1 : Int) ^ n := by
    rw [continuant_error.1 n, PowerSeries.coeff_X_pow_mul', if_pos le_rfl,
      Nat.sub_self]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using continuant_error.2 n
  constructor
  · intro n k hk
    have hn : 0 < n := by omega
    have hdeg : (Polynomial.X ^ k * P n).natDegree ≤ n + k := by
      refine Polynomial.natDegree_mul_le.trans ?_
      rw [(continuant_shape.1 n).natDegree_eq]
      simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
      omega
    rw [hpair _ (n + k) hdeg, hreflect_mul]
    have heq :
        PowerSeries.coeff (n + k) (F0 * (A n : PowerSeries Int)) =
          PowerSeries.coeff (n + k) (E n) +
            PowerSeries.coeff (n + k) (Q n : PowerSeries Int) := by
      have hdef : F0 * (A n : PowerSeries Int) = E n + (Q n : PowerSeries Int) := by
        simp [E]
      rw [hdef, map_add]
    rw [heq, hEzero n k hk, hQcoeff n k hn (by omega), zero_add]
  · intro n
    by_cases hn : n = 0
    · subst n
      simp only [P, pow_zero, one_mul]
      rw [hpair 1 0 (by simp)]
      simp [source_moments.1, b]
    have hdeg : (Polynomial.X ^ n * P n).natDegree ≤ n + n := by
      refine Polynomial.natDegree_mul_le.trans ?_
      rw [(continuant_shape.1 n).natDegree_eq]
      simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
      exact le_rfl
    rw [hpair _ (n + n) hdeg, hreflect_mul]
    have heq :
        PowerSeries.coeff (n + n) (F0 * (A n : PowerSeries Int)) =
          PowerSeries.coeff (2 * n) (E n) +
            PowerSeries.coeff (n + n) (Q n : PowerSeries Int) := by
      have hdef : F0 * (A n : PowerSeries Int) = E n + (Q n : PowerSeries Int) := by
        simp [E]
      rw [hdef, map_add, two_mul]
    rw [heq, hElead, hQcoeff n n (Nat.pos_of_ne_zero hn) (by omega), add_zero]

private theorem signed_polynomial_orthogonality (i j : Nat) :
    B (P i * P j) = if i = j then (-1 : Int) ^ i else 0 := by
  let BL : Int[X] →ₗ[Int] Int :=
    Polynomial.lsum fun n =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight (b n)
  have hBL (f : Int[X]) : BL f = B f := rfl
  have hexpand (f g : Int[X]) (N : Nat) (hf : f.natDegree < N) :
      B (f * g) = ∑ k ∈ Finset.range N, f.coeff k * B (Polynomial.X ^ k * g) := by
    rw [← hBL]
    change BL (f * g) = ∑ k ∈ Finset.range N, f.coeff k * BL (Polynomial.X ^ k * g)
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf]
    rw [Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show Polynomial.C (f.coeff k) * Polynomial.X ^ k * g =
        f.coeff k • (Polynomial.X ^ k * g) by
          rw [← Polynomial.smul_eq_C_mul, smul_mul_assoc]]
    exact map_smul BL (f.coeff k) (Polynomial.X ^ k * g)
  wlog hij : i ≤ j generalizing i j
  · rw [mul_comm, this j i (by omega)]
    simp only [if_neg (by omega : j ≠ i), if_neg (by omega : i ≠ j)]
  by_cases heq : i = j
  · subst j
    rw [if_pos rfl, hexpand (P i) (P i) (i + 1)
      (by rw [(continuant_shape.1 i).natDegree_eq]; omega), Finset.sum_range_succ]
    have hlow :
        ∑ k ∈ Finset.range i, (P i).coeff k * B (Polynomial.X ^ k * P i) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [signed_monomial_orthogonality.1 i k (by simpa [Finset.mem_range] using hk),
        mul_zero]
    rw [hlow, zero_add, signed_monomial_orthogonality.2]
    have hc : (P i).coeff i = 1 := by
      exact (Polynomial.isMonicOfDegree_iff (P i) i).mp (continuant_shape.1 i) |>.2
    rw [hc, one_mul]
  · have hij' : i < j := lt_of_le_of_ne hij heq
    rw [if_neg heq, hexpand (P i) (P j) (i + 1)
      (by rw [(continuant_shape.1 i).natDegree_eq]; omega)]
    apply Finset.sum_eq_zero
    intro k hk
    rw [signed_monomial_orthogonality.1 j k (by
      have hk' : k < i + 1 := by simpa [Finset.mem_range] using hk
      omega), mul_zero]

private def momentMatrix (N : Nat) : Matrix (Fin N) (Fin N) Int :=
  fun i j => b (i.1 + j.1)

private def coefficientMatrix (N : Nat) : Matrix (Fin N) (Fin N) Int :=
  Matrix.of fun i j => (P j.1).coeff i.1

private def signedDiagonal (N : Nat) : Matrix (Fin N) (Fin N) Int :=
  Matrix.diagonal fun i => (-1 : Int) ^ i.1

private theorem signed_gram_adjugate (N : Nat) :
    (coefficientMatrix N).det = 1 ∧
    (coefficientMatrix N).transpose * momentMatrix N * coefficientMatrix N = signedDiagonal N ∧
    (momentMatrix N).det = ∏ i : Fin N, (-1 : Int) ^ i.1 ∧
    (momentMatrix N).adjugate = (momentMatrix N).det •
      (coefficientMatrix N * signedDiagonal N * (coefficientMatrix N).transpose) := by
  let BL : Int[X] →ₗ[Int] Int :=
    Polynomial.lsum fun n =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight (b n)
  have hBL (f : Int[X]) : BL f = B f := rfl
  have hBmonomial (n : Nat) : B (Polynomial.X ^ n) = b n := by
    rw [← hBL]
    simp [BL, Polynomial.X_pow_eq_monomial]
  have hexpand (f g : Int[X]) (hf : f.natDegree < N) :
      B (f * g) = ∑ k ∈ Finset.range N, f.coeff k * B (Polynomial.X ^ k * g) := by
    rw [← hBL]
    change BL (f * g) = ∑ k ∈ Finset.range N, f.coeff k * BL (Polynomial.X ^ k * g)
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf]
    rw [Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show Polynomial.C (f.coeff k) * Polynomial.X ^ k * g =
        f.coeff k • (Polynomial.X ^ k * g) by
          rw [← Polynomial.smul_eq_C_mul, smul_mul_assoc]]
    exact map_smul BL (f.coeff k) (Polynomial.X ^ k * g)
  have hCdet : (coefficientMatrix N).det = 1 := by
    apply Matrix.det_matrixOfPolynomials (fun i : Fin N => P i.1)
    · intro i
      exact (continuant_shape.1 i.1).natDegree_eq
    · intro i
      exact (continuant_shape.1 i.1).monic
  have hMC : momentMatrix N * coefficientMatrix N =
      Matrix.of (fun i j => B (Polynomial.X ^ i.1 * P j.1)) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have hjdeg : (P j.1).natDegree < N := by
      rw [(continuant_shape.1 j.1).natDegree_eq]
      exact j.2
    have he := hexpand (P j.1) (Polynomial.X ^ i.1) hjdeg
    rw [← Fin.sum_univ_eq_sum_range] at he
    calc
      ∑ k : Fin N, momentMatrix N i k * coefficientMatrix N k j =
          ∑ k : Fin N, (P j.1).coeff k.1 *
            B (Polynomial.X ^ k.1 * Polynomial.X ^ i.1) := by
        apply Fintype.sum_congr
        intro k
        simp only [momentMatrix, coefficientMatrix, Matrix.of_apply]
        rw [show Polynomial.X ^ k.1 * Polynomial.X ^ i.1 =
            Polynomial.X ^ (k.1 + i.1) by rw [← pow_add], hBmonomial]
        rw [add_comm i.1 k.1, mul_comm]
      _ = B (P j.1 * Polynomial.X ^ i.1) := he.symm
      _ = B (Polynomial.X ^ i.1 * P j.1) := by rw [mul_comm]
  have hgram :
      (coefficientMatrix N).transpose * momentMatrix N * coefficientMatrix N = signedDiagonal N := by
    rw [Matrix.mul_assoc, hMC]
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.transpose_apply, coefficientMatrix, Matrix.of_apply]
    have hideg : (P i.1).natDegree < N := by
      rw [(continuant_shape.1 i.1).natDegree_eq]
      exact i.2
    have he := hexpand (P i.1) (P j.1) hideg
    rw [← Fin.sum_univ_eq_sum_range] at he
    rw [← he, signed_polynomial_orthogonality]
    simp only [signedDiagonal, Matrix.diagonal_apply]
    simpa only [Fin.ext_iff]
  have hDsq : signedDiagonal N * signedDiagonal N = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [signedDiagonal, Matrix.mul_apply, Matrix.diagonal_apply,
        Matrix.one_apply, ← pow_add, two_mul]
    · simp [signedDiagonal, Matrix.mul_apply, Matrix.diagonal_apply,
        Matrix.one_apply, hij]
  have hdet : (momentMatrix N).det = ∏ i : Fin N, (-1 : Int) ^ i.1 := by
    have hd := congrArg Matrix.det hgram
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCdet,
      one_mul, mul_one] at hd
    rw [signedDiagonal, Matrix.det_diagonal] at hd
    exact hd
  have hCleft : (coefficientMatrix N).adjugate * coefficientMatrix N = 1 := by
    simpa [hCdet] using Matrix.adjugate_mul (coefficientMatrix N)
  have hCright : coefficientMatrix N * (coefficientMatrix N).adjugate = 1 := by
    simpa [hCdet] using Matrix.mul_adjugate (coefficientMatrix N)
  have hCtleft : (coefficientMatrix N).transpose.adjugate *
      (coefficientMatrix N).transpose = 1 := by
    simpa [Matrix.det_transpose, hCdet] using
      Matrix.adjugate_mul (coefficientMatrix N).transpose
  have hCtright : (coefficientMatrix N).transpose *
      (coefficientMatrix N).transpose.adjugate = 1 := by
    simpa [Matrix.det_transpose, hCdet] using
      Matrix.mul_adjugate (coefficientMatrix N).transpose
  have hrepr : momentMatrix N =
      (coefficientMatrix N).transpose.adjugate * signedDiagonal N *
        (coefficientMatrix N).adjugate := by
    calc
      momentMatrix N = 1 * momentMatrix N * 1 := by simp
      _ = ((coefficientMatrix N).transpose.adjugate *
          (coefficientMatrix N).transpose) *
          momentMatrix N *
            (coefficientMatrix N * (coefficientMatrix N).adjugate) := by
        rw [hCtleft, hCright]
      _ = (coefficientMatrix N).transpose.adjugate *
          ((coefficientMatrix N).transpose * momentMatrix N * coefficientMatrix N) *
            (coefficientMatrix N).adjugate := by noncomm_ring
      _ = (coefficientMatrix N).transpose.adjugate * signedDiagonal N *
          (coefficientMatrix N).adjugate := by rw [hgram]
  let T := coefficientMatrix N * signedDiagonal N * (coefficientMatrix N).transpose
  have hleft : T * momentMatrix N = 1 := by
    dsimp [T]
    rw [hrepr]
    calc
      (coefficientMatrix N * signedDiagonal N * (coefficientMatrix N).transpose) *
          ((coefficientMatrix N).transpose.adjugate * signedDiagonal N *
            (coefficientMatrix N).adjugate) =
          coefficientMatrix N * (signedDiagonal N * signedDiagonal N) *
            (coefficientMatrix N).adjugate := by
        calc
          _ = coefficientMatrix N * signedDiagonal N *
              ((coefficientMatrix N).transpose *
                (coefficientMatrix N).transpose.adjugate) * signedDiagonal N *
                (coefficientMatrix N).adjugate := by noncomm_ring
          _ = _ := by rw [hCtright]; noncomm_ring
      _ = 1 := by rw [hDsq]; simpa using hCright
  have hadj : (momentMatrix N).adjugate = (momentMatrix N).det • T := by
    calc
      (momentMatrix N).adjugate = 1 * (momentMatrix N).adjugate := by simp
      _ = (T * momentMatrix N) * (momentMatrix N).adjugate := by rw [hleft]
      _ = T * (momentMatrix N * (momentMatrix N).adjugate) := by noncomm_ring
      _ = T * ((momentMatrix N).det • (1 : Matrix (Fin N) (Fin N) Int)) := by
        rw [Matrix.mul_adjugate]
      _ = (momentMatrix N).det • T := by
        rw [Matrix.mul_smul, Matrix.mul_one]
  exact ⟨hCdet, hgram, hdet, hadj⟩

/-- The literal A331474 Hankel determinant is the signed finite reproducing
kernel evaluated by the alternating source functional. -/
theorem literal_hankel_eq_signed_kernel (n : Nat) :
    H n = (∏ k : Fin (n + 1), (-1 : Int) ^ k.1) *
      ∑ k : Fin (n + 1), (-1 : Int) ^ k.1 * p k.1 * u k.1 ∧
    p 0 = 1 ∧ p 1 = -4 ∧
    (∀ m, p (m + 2) = -a (m + 1) * p (m + 1) + p m) ∧
    u 0 = 1 ∧ u 1 = -1 ∧ u 2 = 1 ∧
    ∀ m, 2 ≤ m → u (m + 1) = -(a m + 1) * u m + u (m - 1) := by
  refine ⟨?_, ?_⟩
  let SM : Matrix (Fin (n + 1)) (Fin (n + 1)) Int :=
    fun i j => s (i.1 + j.1)
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) Int :=
    fun i j => if j = 0 then s i.1 else b (i.1 + j.1)
  let sv : Fin (n + 1) → Int := fun i => s i.1
  have hcolumns : SM.det = L.det := by
    apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (c := fun _ => (-1 : Int))
    · intro i
      simp [SM, L]
    · intro i j
      have ht := source_moments.2 (i.1 + j.1)
      simp only [SM, L, Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ,
        Fin.val_castSucc]
      rw [show i.1 + (j.1 + 1) = i.1 + j.1 + 1 by omega]
      omega
  have hupdate : (momentMatrix (n + 1)).updateCol 0 sv = L := by
    ext i j
    by_cases hj : j = 0
    · subst j
      simp [L, sv]
    · simp [Matrix.updateCol, L, sv, momentMatrix, hj]
  let SL : Int[X] →ₗ[Int] Int :=
    Polynomial.lsum fun m =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight (s m)
  have hSL (f : Int[X]) : SL f = S f := rfl
  have hSmonomial (m : Nat) : S (Polynomial.X ^ m) = s m := by
    rw [← hSL]
    simp [SL, Polynomial.X_pow_eq_monomial]
  have hSexpand (f : Int[X]) (hf : f.natDegree < n + 1) :
      S f = ∑ m ∈ Finset.range (n + 1), f.coeff m * s m := by
    rw [← hSL]
    change SL f = ∑ m ∈ Finset.range (n + 1), f.coeff m * s m
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [show Polynomial.C (f.coeff m) * Polynomial.X ^ m =
        f.coeff m • Polynomial.X ^ m by rw [← Polynomial.smul_eq_C_mul]]
    rw [map_smul]
    change f.coeff m * S (Polynomial.X ^ m) = _
    rw [hSmonomial]
  have hCtS (k : Fin (n + 1)) :
      Matrix.mulVec ((coefficientMatrix (n + 1)).transpose) sv k = u k.1 := by
    rw [Matrix.mulVec, dotProduct]
    have hkdeg : (P k.1).natDegree < n + 1 := by
      rw [(continuant_shape.1 k.1).natDegree_eq]
      exact k.2
    have he := hSexpand (P k.1) hkdeg
    rw [← Fin.sum_univ_eq_sum_range] at he
    change (∑ i : Fin (n + 1), (P k.1).coeff i.1 * s i.1) = S (P k.1)
    exact he.symm
  have hkernel :
      Matrix.mulVec (coefficientMatrix (n + 1) * signedDiagonal (n + 1) *
          (coefficientMatrix (n + 1)).transpose) sv 0 =
        ∑ k : Fin (n + 1), (-1 : Int) ^ k.1 * p k.1 * u k.1 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hCtSfun : Matrix.mulVec ((coefficientMatrix (n + 1)).transpose) sv =
        fun k => u k.1 := funext hCtS
    rw [hCtSfun]
    have hDfun : Matrix.mulVec (signedDiagonal (n + 1)) (fun k => u k.1) =
        fun k => (-1 : Int) ^ k.1 * u k.1 := by
      ext k
      simp [Matrix.mulVec, dotProduct, signedDiagonal, Matrix.diagonal_apply]
    rw [hDfun]
    simp [Matrix.mulVec, dotProduct, coefficientMatrix, p]
    apply Fintype.sum_congr
    intro k
    ring
  have hadj := (signed_gram_adjugate (n + 1)).2.2.2
  have hdet := (signed_gram_adjugate (n + 1)).2.2.1
  calc
    H n = SM.det := rfl
    _ = L.det := hcolumns
    _ = ((momentMatrix (n + 1)).updateCol 0 sv).det := by rw [hupdate]
    _ = Matrix.cramer (momentMatrix (n + 1)) sv 0 := rfl
    _ = Matrix.mulVec ((momentMatrix (n + 1)).adjugate) sv 0 := by
      rw [Matrix.cramer_eq_adjugate_mulVec]
    _ = (momentMatrix (n + 1)).det *
        Matrix.mulVec (coefficientMatrix (n + 1) * signedDiagonal (n + 1) *
          (coefficientMatrix (n + 1)).transpose) sv 0 := by
      rw [hadj, Matrix.smul_mulVec]
      rfl
    _ = _ := by rw [hdet, hkernel]
  let BL : Int[X] →ₗ[Int] Int :=
    Polynomial.lsum fun m =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight (b m)
  let SL : Int[X] →ₗ[Int] Int :=
    Polynomial.lsum fun m =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight (s m)
  have hBL (f : Int[X]) : BL f = B f := rfl
  have hSL (f : Int[X]) : SL f = S f := rfl
  have hBmonomial (m : Nat) : B (Polynomial.X ^ m) = b m := by
    rw [← hBL]
    simp [BL, Polynomial.X_pow_eq_monomial]
  have hSmonomial (m : Nat) : S (Polynomial.X ^ m) = s m := by
    rw [← hSL]
    simp [SL, Polynomial.X_pow_eq_monomial]
  have hmomentRelation (f : Int[X]) :
      B (Polynomial.X * f) = S ((Polynomial.X + 1) * f) := by
    let LB := BL.comp (LinearMap.mulLeft Int Polynomial.X)
    let LS := SL.comp (LinearMap.mulLeft Int (Polynomial.X + 1))
    have hmono (m : Nat) : LB (Polynomial.X ^ m) = LS (Polynomial.X ^ m) := by
      change B (Polynomial.X * Polynomial.X ^ m) =
        S ((Polynomial.X + 1) * Polynomial.X ^ m)
      rw [show Polynomial.X * Polynomial.X ^ m = Polynomial.X ^ (m + 1) by
        rw [pow_succ'], hBmonomial]
      rw [add_mul]
      rw [← hSL, map_add, hSL, hSL]
      simp only [one_mul]
      rw [show Polynomial.X * Polynomial.X ^ m = Polynomial.X ^ (m + 1) by
        rw [pow_succ'], hSmonomial, hSmonomial]
      exact source_moments.2 m
    rw [← hBL, ← hSL]
    change LB f = LS f
    have hmaps : LB = LS := by
      apply Polynomial.lhom_ext'
      intro m
      apply LinearMap.ext
      intro c
      change LB (Polynomial.monomial m c) = LS (Polynomial.monomial m c)
      rw [← Polynomial.C_mul_X_pow_eq_monomial,
        ← Polynomial.smul_eq_C_mul, map_smul, map_smul, hmono]
    exact LinearMap.congr_fun hmaps f
  have hBXP (m : Nat) (hm : 2 ≤ m) : B (Polynomial.X * P m) = 0 := by
    have h1 := signed_polynomial_orthogonality 1 m
    have h0 := signed_polynomial_orthogonality 0 m
    rw [if_neg (by omega : 1 ≠ m)] at h1
    rw [if_neg (by omega : 0 ≠ m)] at h0
    rw [← hBL] at h1 h0
    simp only [P, one_mul] at h0
    change BL ((Polynomial.X - Polynomial.C 4) * P m) = 0 at h1
    have hc : Polynomial.C 4 * P m = (4 : Int) • P m :=
      (Polynomial.smul_eq_C_mul (p := P m) 4).symm
    rw [sub_mul, map_sub, hc, map_smul, h0, smul_zero, sub_zero] at h1
    exact h1
  have hSXP (m : Nat) (hm : 2 ≤ m) : S (Polynomial.X * P m) = -u m := by
    have hr := hmomentRelation (P m)
    rw [hBXP m hm] at hr
    rw [add_mul] at hr
    simp only [one_mul] at hr
    rw [← hSL, map_add, hSL, hSL] at hr
    change 0 = S (Polynomial.X * P m) + u m at hr
    omega
  have hp0 : p 0 = 1 := by norm_num [p, P]
  have hp1 : p 1 = -4 := by norm_num [p, P]
  have hprec (m : Nat) : p (m + 2) = -a (m + 1) * p (m + 1) + p m := by
    simp [p, P, Polynomial.coeff_add, Polynomial.coeff_mul]
  have hSX : S Polynomial.X = s 1 := by
    simpa using hSmonomial 1
  have hSC (c : Int) : S (Polynomial.C c) = c * s 0 := by
    rw [← hSL, show Polynomial.C c = c • (1 : Int[X]) by simp, map_smul, hSL]
    change c * S 1 = c * s 0
    rw [show (1 : Int[X]) = Polynomial.X ^ 0 by simp, hSmonomial]
  have hu0 : u 0 = 1 := by
    change S 1 = 1
    rw [show (1 : Int[X]) = Polynomial.X ^ 0 by simp, hSmonomial]
    norm_num [s, b, Finset.sum_range_succ, Nat.choose]
  have hu1 : u 1 = -1 := by
    change S (Polynomial.X - Polynomial.C 4) = -1
    rw [← hSL, map_sub, hSL, hSL, hSX, hSC]
    norm_num [s, b, Finset.sum_range_succ]
  have hu2 : u 2 = 1 := by
    change S (P 2) = 1
    rw [show P 2 = Polynomial.X * (Polynomial.X - Polynomial.C 4) + 1 by
      norm_num [P, a]]
    rw [← hSL, map_add, mul_sub, map_sub]
    have hxC : (Polynomial.X : Int[X]) * Polynomial.C 4 =
        (4 : Int) • (Polynomial.X : Int[X]) := by
      calc
        (Polynomial.X : Int[X]) * Polynomial.C 4 =
            Polynomial.C 4 * Polynomial.X := by rw [mul_comm]
        _ = (4 : Int) • (Polynomial.X : Int[X]) :=
          (Polynomial.smul_eq_C_mul (p := (Polynomial.X : Int[X])) 4).symm
    rw [show (Polynomial.X : Int[X]) * Polynomial.X = Polynomial.X ^ 2 by rw [pow_two],
      hxC, map_smul, hSL, hSL, hSL]
    rw [hSmonomial, hSX, show S 1 = s 0 by
      rw [show (1 : Int[X]) = Polynomial.X ^ 0 by simp, hSmonomial]]
    norm_num [s, b, Finset.sum_range_succ, Nat.choose]
  refine ⟨hp0, hp1, hprec, hu0, hu1, hu2, ?_⟩
  intro m hm
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 2 := ⟨m - 2, by omega⟩
  rw [show q + 2 - 1 = q + 1 by omega]
  change S (P ((q + 1) + 2)) =
    -(a (q + 2) + 1) * S (P (q + 2)) + S (P (q + 1))
  rw [P.eq_def]
  change S ((Polynomial.X - Polynomial.C (a (q + 2))) * P (q + 2) + P (q + 1)) = _
  rw [← hSL, map_add, sub_mul, map_sub, hSL, hSL, hSL]
  rw [show S (Polynomial.C (a (q + 2)) * P (q + 2)) =
      a (q + 2) * u (q + 2) by
    rw [← hSL, ← Polynomial.smul_eq_C_mul, map_smul, hSL]; rfl]
  rw [hSXP (q + 2) (by omega)]
  simp only [u]
  ring_nf

end D5.S3.Constants.Moments.A331474HankelBridge
