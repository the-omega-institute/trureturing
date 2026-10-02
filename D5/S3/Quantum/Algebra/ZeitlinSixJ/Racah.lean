/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/Racah
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/

/-
binomial_harmonic:
  proof_shape: content
  escape_witness: Local alternating_shifted_choose_zero: for every n, sum k in range(n+2), (-1:Rat)^k * choose(n+1,k) * choose(n+k,k) = 0; its polynomial-coefficient construction is used in the live harmonic induction.
polynomial_harmonic:
  proof_shape: content
  escape_witness: binomial_harmonic: sum k in range n, (-1:Rat)^(k+2)*choose(n,k+1)*choose(n+k+1,k+1)/(k+1) = 2*harmonic n. The harmonic induction supplies the finite double-sum evaluation.
recurrence_unique:
  proof_shape: content
  escape_witness: Conclusion-witness under the allowed direct-construction shape: forall i<N, f i=g i, constructed by strong induction from equality at 0 and the two recurrences; no pinned direct uniqueness theorem was found.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Coeff

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open Finset Polynomial Matrix

def triangle (a b c : ℕ) : Prop :=
  a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ (a + b + c) % 2 = 0

instance triangleDecidable (a b c : ℕ) : Decidable (triangle a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def admissible (a b c d e f : ℕ) : Prop :=
  triangle a b c ∧ triangle a e f ∧ triangle d b f ∧ triangle d e c

instance admissibleDecidable (a b c d e f : ℕ) : Decidable (admissible a b c d e f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def deltaSq (a b c : ℕ) : ℚ :=
  ((Nat.factorial ((a + b - c) / 2) : ℚ) *
    Nat.factorial ((a + c - b) / 2) * Nat.factorial ((b + c - a) / 2)) /
    Nat.factorial ((a + b + c) / 2 + 1)

def lower (a b c d e f : ℕ) : ℕ :=
  max (max ((a+b+c)/2) ((a+e+f)/2)) (max ((d+b+f)/2) ((d+e+c)/2))

def upper (a b c d e f : ℕ) : ℕ :=
  min ((a+b+d+e)/2) (min ((b+c+e+f)/2) ((c+a+f+d)/2))

def racahTerm (a b c d e f z : ℕ) : ℚ :=
  (-1 : ℚ)^z * Nat.factorial (z+1) /
   (Nat.factorial (z-(a+b+c)/2) * Nat.factorial (z-(a+e+f)/2) *
    Nat.factorial (z-(d+b+f)/2) * Nat.factorial (z-(d+e+c)/2) *
    Nat.factorial ((a+b+d+e)/2-z) * Nat.factorial ((b+c+e+f)/2-z) *
    Nat.factorial ((c+a+f+d)/2-z) : ℚ)

def racahSum (a b c d e f : ℕ) : ℚ :=
  ∑ z ∈ range (upper a b c d e f + 1),
    if lower a b c d e f ≤ z then racahTerm a b c d e f z else 0

noncomputable def sixJ (a b c d e f : ℕ) : ℝ :=
  if admissible a b c d e f then
    Real.sqrt ((deltaSq a b c * deltaSq a e f * deltaSq d b f * deltaSq d e c : ℚ) : ℝ) *
      (racahSum a b c d e f : ℝ)
  else 0

private lemma binomial_harmonic (n : ℕ) :
    (∑ k ∈ range n, (-1 : ℚ)^(k+2) * Nat.choose n (k+1) *
      Nat.choose (n+k+1) (k+1) / (k+1)) = 2 * harmonic n := by
  have alternating_shifted_choose_zero (n : ℕ) :
      (∑ k ∈ range (n+2), (-1 : ℚ)^k * (Nat.choose (n+1) k) * (Nat.choose (n+k) k)) = 0 := by
    have hp : (∑ k ∈ range (n+2),
        C ((-1 : ℚ)^k * Nat.choose (n+1) k) * (X+1)^k) =
        (-(X : ℚ[X]))^(n+1) := by
      calc
        _ = ∑ k ∈ range (n+1+1),
            (-(X+1) : ℚ[X])^k * 1^(n+1-k) * (Nat.choose (n+1) k : ℚ[X]) := by
          apply sum_congr rfl
          intro k hk
          rw [neg_pow (X+1 : ℚ[X]) k]
          simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one,
            C_eq_natCast]
          ring
        _ = (-(X+1) + 1 : ℚ[X])^(n+1) := (add_pow _ _ _).symm
        _ = (-(X : ℚ[X]))^(n+1) := by congr 1; ring
    have hc := congrArg (fun p : ℚ[X] => p.coeff n) (congrArg (fun p => (X+1)^n * p) hp)
    rw [mul_sum, finsetSum_coeff] at hc
    have he : (∑ k ∈ range (n+2),
        (((X+1)^n : ℚ[X]) * (C ((-1 : ℚ)^k * Nat.choose (n+1) k) * (X+1)^k)).coeff n) =
        ∑ k ∈ range (n+2), (-1 : ℚ)^k * Nat.choose (n+1) k * Nat.choose (n+k) k := by
      apply sum_congr rfl
      intro k hk
      rw [show (X+1)^n * (C ((-1 : ℚ)^k * Nat.choose (n+1) k) * (X+1)^k) =
          C ((-1 : ℚ)^k * Nat.choose (n+1) k) * (X+1)^(n+k) by rw [pow_add]; ring]
      rw [coeff_C_mul, coeff_X_add_one_pow]
      congr 2
      exact_mod_cast Nat.choose_symm_of_eq_add rfl
    rw [he] at hc
    rw [hc, neg_pow (X : ℚ[X]) (n+1)]
    rw [show (X+1)^n * ((-1 : ℚ[X])^(n+1) * X^(n+1)) =
        C ((-1 : ℚ)^(n+1)) * ((X+1)^n * X^(n+1)) by simp; ring]
    rw [coeff_C_mul, coeff_mul_X_pow']
    simp
  induction n with
  | zero => simp
  | succ n ih =>
    have hN : (n+1 : ℚ) ≠ 0 := by positivity
    have hz := alternating_shifted_choose_zero n
    rw [show n+2 = (n+1)+1 by omega, sum_range_succ'] at hz
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero] at hz
    have hsum : (∑ k ∈ range (n+1), (-1 : ℚ)^(k+2) * Nat.choose (n+1) (k+1) *
        Nat.choose (n+k+1) (k+1)) = 1 := by
      have hsign : (∑ k ∈ range (n+1), (-1 : ℚ)^(k+2) * Nat.choose (n+1) (k+1) *
          Nat.choose (n+k+1) (k+1)) =
          -(∑ k ∈ range (n+1), (-1 : ℚ)^(k+1) * Nat.choose (n+1) (k+1) *
          Nat.choose (n+(k+1)) (k+1)) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro k hk
        rw [show k+2 = (k+1)+1 by omega, pow_succ]
        ring
      rw [hsign]
      linarith
    have hstep : ∀ k ∈ range (n+1),
        (-1 : ℚ)^(k+2) * Nat.choose (n+1) (k+1) * Nat.choose (n+1+k+1) (k+1) / (k+1) -
        (-1 : ℚ)^(k+2) * Nat.choose n (k+1) * Nat.choose (n+k+1) (k+1) / (k+1) =
        (2/(n+1)) * ((-1 : ℚ)^(k+2) * Nat.choose (n+1) (k+1) *
          Nat.choose (n+k+1) (k+1)) := by
      intro k hk
      have hk' : k+1 ≤ n+1 := by simpa using mem_range.mp hk
      have hk0 : (k+1 : ℚ) ≠ 0 := by positivity
      have ha := Nat.choose_mul_succ_eq n (k+1)
      have hb := Nat.choose_mul_succ_eq (n+k+1) (k+1)
      have ha' : (Nat.choose n (k+1) : ℚ) * (n+1) =
          Nat.choose (n+1) (k+1) * ((n+1 : ℚ)-(k+1)) := by
        simpa only [Nat.cast_mul, Nat.cast_sub hk', Nat.cast_add, Nat.cast_one] using
          (congrArg (fun t : ℕ => (t : ℚ)) ha)
      have hb' : (Nat.choose (n+k+1) (k+1) : ℚ) * ((n : ℚ)+k+2) =
          Nat.choose (n+1+k+1) (k+1) * (n+1) := by
        have hidx : n+k+1+1-(k+1) = n+1 := by omega
        have he : n+k+1+1 = n+1+k+1 := by omega
        rw [hidx, he] at hb
        convert congrArg (fun t : ℕ => (t : ℚ)) hb using 1 <;> push_cast <;> ring
      field_simp [hN, hk0]
      linear_combination -(Nat.choose (n+k+1) (k+1) : ℚ) * ha' -
        (Nat.choose (n+1) (k+1) : ℚ) * hb'
    have hext : (∑ k ∈ range (n+1), (-1 : ℚ)^(k+2) * Nat.choose n (k+1) *
        Nat.choose (n+k+1) (k+1) / (k+1)) = 2 * harmonic n := by
      rw [sum_range_succ]
      simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, mul_zero, zero_mul,
        zero_div, add_zero]
      exact ih
    have hdiff := sum_congr rfl hstep
    rw [sum_sub_distrib, ← mul_sum, hsum, mul_one, hext] at hdiff
    rw [harmonic_succ]
    rw [show (↑(n+1) : ℚ)⁻¹ = 1/(n+1) by simp]
    linear_combination hdiff

private def antidifference (k i : ℕ) : ℚ :=
  if k ≤ i then (Nat.factorial (i+k+1) : ℚ) /
    ((k : ℚ)*(i+1)*Nat.factorial (i-k)) else 0

def racahMonomial (k i : ℕ) : ℚ :=
  if k ≤ i then (Nat.factorial (i+k) : ℚ) / Nat.factorial (i-k) else 0

def racahCoefficient (N j k : ℕ) : ℚ :=
  (-1 : ℚ)^k * Nat.choose j k * Nat.choose (j+k) k *
    ((N : ℚ)*Nat.factorial (N-k-1)/Nat.factorial (N+k))

def racahPolynomial (N j i : ℕ) : ℚ :=
  1 + ∑ k ∈ range j, racahCoefficient N j (k+1) * racahMonomial (k+1) i

lemma polynomial_harmonic (N j : ℕ) (hN : 2 ≤ N) (hj : j < N) :
    (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℚ)+1) /
      (((i+1 : ℕ) : ℚ)*((i+1 : ℕ)+1)) * (1-racahPolynomial N j (i+1))) =
      2 * harmonic j := by
  have weighted_telescope (k N : ℕ) (hk : 1 ≤ k) (hN : k < N) :
      (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℚ)+1) /
        (((i+1 : ℕ) : ℚ)*((i+1 : ℕ)+1)) * racahMonomial k (i+1)) =
        (Nat.factorial (N+k) : ℚ) / ((k : ℚ)*N*Nat.factorial (N-k-1)) := by
    have antidifference_step (k i : ℕ) (hk : 1 ≤ k) (hi : k ≤ i) :
        antidifference k i - antidifference k (i-1) = (2*(i : ℚ)+1)/((i : ℚ)*(i+1)) * racahMonomial k i := by
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
      have hi1 : (i : ℚ)+1 ≠ 0 := by positivity
      by_cases heq : i = k
      · subst i
        have hprev : ¬ k ≤ k-1 := by omega
        simp only [antidifference, racahMonomial, if_pos (le_refl k), if_neg hprev, sub_zero, Nat.sub_self,
          Nat.factorial_zero, Nat.cast_one, mul_one, div_one, Nat.factorial_succ, Nat.cast_mul,
          Nat.cast_add, Nat.cast_one]
        field_simp [hk0]
        ring
      · have hprev : k ≤ i-1 := by omega
        have hfac : Nat.factorial (i-k) = (i-k) * Nat.factorial (i-1-k) := by
          rw [show i-k = (i-1-k)+1 by omega, Nat.factorial_succ]
        have hfac0 : (Nat.factorial (i-1-k) : ℚ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (i-1-k)
        have hsub0 : (i : ℚ)-(k : ℚ) ≠ 0 := by
          have hlt : (k : ℚ) < i := by exact_mod_cast (by omega : k < i)
          exact sub_ne_zero.mpr (ne_of_gt hlt)
        simp only [antidifference, racahMonomial, if_pos hi, if_pos hprev]
        rw [show i-1+k+1 = i+k by omega, Nat.factorial_succ, hfac]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hi,
          Nat.cast_sub (by omega : 1 ≤ i)]
        field_simp [hk0, hi0, hi1, hfac0, hsub0]
        ring
    have hs : (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℚ)+1) /
        (((i+1 : ℕ) : ℚ)*((i+1 : ℕ)+1)) * racahMonomial k (i+1)) =
        ∑ i ∈ range (N-1), (antidifference k (i+1) - antidifference k i) := by
      apply sum_congr rfl
      intro i hi
      by_cases hki : k ≤ i+1
      · simpa using (antidifference_step k (i+1) hk hki).symm
      · have hki' : ¬ k ≤ i := by omega
        simp [antidifference, racahMonomial, hki, hki']
    rw [hs, sum_range_sub (antidifference k) (N-1)]
    simp only [antidifference, if_pos (by omega : k ≤ N-1), if_neg (by omega : ¬ k ≤ 0), sub_zero]
    rw [show N-1+k+1 = N+k by omega, show N-1-k = N-k-1 by omega]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    push_cast
    ring
  have hn0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  calc
    _ = ∑ i ∈ range (N-1), ∑ k ∈ range j,
        -racahCoefficient N j (k+1) *
        ((2*((i+1 : ℕ) : ℚ)+1)/(((i+1 : ℕ) : ℚ)*((i+1 : ℕ)+1)) *
          racahMonomial (k+1) (i+1)) := by
      apply sum_congr rfl
      intro i hi
      simp only [racahPolynomial, sub_add_eq_sub_sub, sub_self, zero_sub, mul_neg,
        mul_sum, ← sum_neg_distrib]
      apply sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ range j, -racahCoefficient N j (k+1) *
        (∑ i ∈ range (N-1),
          (2*((i+1 : ℕ) : ℚ)+1)/(((i+1 : ℕ) : ℚ)*((i+1 : ℕ)+1)) *
          racahMonomial (k+1) (i+1)) := by rw [sum_comm]; simp_rw [mul_sum]
    _ = ∑ k ∈ range j, (-1 : ℚ)^(k+2) * Nat.choose j (k+1) *
        Nat.choose (j+k+1) (k+1) / (k+1) := by
      apply sum_congr rfl
      intro k hk
      have hki : k+1 < N := by have := mem_range.mp hk; omega
      have hk0 : (k+1 : ℚ) ≠ 0 := by positivity
      have hf0 : (Nat.factorial (N-(k+1)-1) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      have hf1 : (Nat.factorial (N+(k+1)) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      rw [weighted_telescope (k+1) N (by omega) hki]
      simp only [racahCoefficient]
      rw [show k+2 = (k+1)+1 by omega, pow_succ]
      rw [show j+(k+1) = j+k+1 by omega]
      field_simp [hn0, hk0, hf0, hf1]
      push_cast
      ring
    _ = 2 * harmonic j := binomial_harmonic j

noncomputable def W (N i j l : ℕ) : ℝ :=
  sixJ (2*i) (2*j) (2*l) (N-1) (N-1) (N-1)

noncomputable def Wij (N i j : ℕ) : ℝ :=
  sixJ (2*i) (N-1) (N-1) (2*j) (N-1) (N-1)

def casimir (i : ℕ) : ℝ := (i : ℝ)*(i+1)

def newtonBasis (k : ℕ) (x : ℚ) : ℚ :=
  ∏ r ∈ range k, (x-r)*(x+r+1)

lemma recurrence_unique (N j : ℕ) (f g : ℕ → ℚ) (hN : 2 ≤ N)
    (h0 : f 0 = g 0)
    (hf : ∀ i, i+1 < N →
      ((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2)*(f i-f (i+1)) +
        (i : ℚ)*((N : ℚ)^2-i^2)*(f i-f (i-1)) =
      2*(2*(i : ℚ)+1)*(j : ℚ)*(j+1)*f i)
    (hg : ∀ i, i+1 < N →
      ((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2)*(g i-g (i+1)) +
        (i : ℚ)*((N : ℚ)^2-i^2)*(g i-g (i-1)) =
      2*(2*(i : ℚ)+1)*(j : ℚ)*(j+1)*g i) :
    ∀ i, i < N → f i = g i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    cases i with
    | zero => exact h0
    | succ i =>
      have hei := ih i (by omega) (by omega)
      have heprev := ih (i-1) (by omega) (by omega)
      have ha := hf i hi
      have hb := hg i hi
      rw [hei, heprev] at ha
      have hlt : (i : ℚ)+1 < N := by exact_mod_cast hi
      have hpos : 0 < ((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2) := by
        have hfactor : (N : ℚ)^2-(i+1)^2 = (N-i-1)*(N+i+1) := by ring
        rw [hfactor]
        have hl : (0 : ℚ) < N-i-1 := by linarith
        positivity
      have hz : (((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2))*(f (i+1)-g (i+1)) = 0 := by
        linear_combination hb-ha
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos))

def certificatePolynomial (N i j k : ℚ) : ℚ :=
  (N^2-i*(2*j+1))*(i+1-k)^2 +
    2*i*(N^2-j*(i+j+1))*(i+1-k) + i*(i+1)*(N^2-j^2)

def normalizedRacah (N i j : ℕ) : ℚ :=
  (-1 : ℚ)^(N-1+i+j)*N*deltaSq (2*i) (N-1) (N-1)*
    deltaSq (2*j) (N-1) (N-1)*racahSum (2*i) (N-1) (N-1) (2*j) (N-1) (N-1)

def invFactorial (z : ℤ) : ℚ :=
  if 0 ≤ z then (Nat.factorial z.toNat : ℚ)⁻¹ else 0

def factorialKernel (N i j k : ℕ) : ℚ :=
  (-1 : ℚ)^k * Nat.factorial (N+i+j-k) *
    invFactorial ((i : ℤ)-k)^2 * invFactorial ((j : ℤ)-k)^2 *
    invFactorial (k : ℤ)^2 * invFactorial ((N : ℤ)-1+k-i-j)

def certificateBase (N i j k : ℕ) : ℚ :=
  (-1 : ℚ)^k * Nat.factorial (N+i+j-k-1) *
    invFactorial ((i : ℤ)+1-k)^2 * invFactorial ((j : ℤ)-k)^2 *
    invFactorial (k : ℤ)^2 * invFactorial ((N : ℤ)+k-i-j)

def kernelFlux (N i j k : ℕ) : ℚ :=
  (-1 : ℚ)^k * certificatePolynomial N i j k * Nat.factorial (N+i+j-k) *
    invFactorial ((i : ℤ)+1-k)^2 * invFactorial ((j : ℤ)-k)^2 *
    invFactorial ((k : ℤ)-1)^2 * invFactorial ((N : ℤ)-1+k-i-j)

def racahPrefactor (N i j : ℕ) : ℚ :=
  N*deltaSq (2*i) (N-1) (N-1)*deltaSq (2*j) (N-1) (N-1)

def kernelSequence (N j i : ℕ) : ℚ :=
  racahPrefactor N i j * ∑ k ∈ range (j+1), factorialKernel N i j k

end D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
