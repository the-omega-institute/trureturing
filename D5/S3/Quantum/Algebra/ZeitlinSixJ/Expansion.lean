/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/Expansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/
/-
kernel_recurrence_interior:
  proof_shape: content
  escape_witness: Local kernel_wz_step: the i-scaled three-term factorial-kernel residual equals racahPrefactor N i j * (kernelFlux N i j (k+1)-kernelFlux N i j k), uniformly in the finite k range; both boundary fluxes vanish.
racah_expansion_open:
  proof_shape: content
  escape_witness: kernel_recurrence_interior: the actual zero-extended kernelSequence satisfies the displayed second-order recurrence for 1<=i and i+1<N. This constructed identity remains live in recurrence_unique.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
import Mathlib.Data.Nat.Factorial.BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah

private lemma kernel_recurrence_interior (N j i : ℕ) (hN : 2 ≤ N)
    (hi : 1 ≤ i) (hit : i+1 < N) (hj : j < N) : ((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2)*(kernelSequence N j i-kernelSequence N j (i+1)) + (i : ℚ)*((N : ℚ)^2-i^2)*(kernelSequence N j i-kernelSequence N j (i-1)) =
    2*(2*(i : ℚ)+1)*(j : ℚ)*(j+1)*kernelSequence N j i := by
  have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
    simp only [invFactorial, if_neg (not_le.mpr hz)]
  have flux_zero (N i j : ℕ) : kernelFlux N i j 0 = 0 := by
    unfold kernelFlux
    simp only [Nat.cast_zero, Int.cast_zero, zero_sub]
    rw [invFactorial_neg (-1) (by omega)]
    simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul]
  have flux_end (N i j : ℕ) : kernelFlux N i j (j+1) = 0 := by
    unfold kernelFlux
    simp only [Int.natCast_add, Int.natCast_one]
    rw [show (j : ℤ)-(j+1) = -1 by ring, invFactorial_neg (-1) (by omega)]
    simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul]
  have kernel_wz_step (N i j k : ℕ) (hN : 2 ≤ N) (hi : 1 ≤ i)
      (hit : i+1 < N) (hj : j < N) (hk : k ≤ j+1) : (i : ℚ)*(
        ((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2)* (racahPrefactor N i j*factorialKernel N i j k- racahPrefactor N (i+1) j*factorialKernel N (i+1) j k) + (i : ℚ)*((N : ℚ)^2-i^2)* (racahPrefactor N i j*factorialKernel N i j k-
            racahPrefactor N (i-1) j*factorialKernel N (i-1) j k) - 2*(2*(i : ℚ)+1)*(j : ℚ)*(j+1)*racahPrefactor N i j*factorialKernel N i j k) = racahPrefactor N i j*(kernelFlux N i j (k+1)-kernelFlux N i j k) := by
    have certificate_identity (N i j k : ℚ) : i*(i+1)*(N^2-(i+1)^2)*(i+1-k)^2*(N^2-(i+j-k)^2) - i*(i+1)^3*(N^2-(i+j-k)^2)*(N^2-(i+j-k+1)^2) + i^2*(N^2-i^2)*(i+1-k)^2*(N^2-(i+j-k)^2) - (N^2-i^2)^2*(i-k)^2*(i+1-k)^2 -
          2*i*(2*i+1)*j*(j+1)*(i+1-k)^2*(N^2-(i+j-k)^2) = -(j-k)^2*(i+1-k)^2*certificatePolynomial N i j (k+1) - k^2*(N^2-(i+j-k)^2)*certificatePolynomial N i j k := by
      unfold certificatePolynomial
      ring
    have invFactorial_step (z : ℤ) : invFactorial (z-1) = (z : ℚ)*invFactorial z := by
      by_cases hz : 0 < z
      · have hz0 : 0 ≤ z := by omega
        have hz1 : 0 ≤ z-1 := by omega
        have he : z.toNat = (z-1).toNat+1 := by omega
        have hc : ((z-1).toNat+1 : ℚ) = (z : ℚ) := by
          have h : (((z-1).toNat+1 : ℕ) : ℤ) = z := by omega
          exact_mod_cast h
        have hn0 : (z : ℚ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
        have hf0 : (Nat.factorial (z-1).toNat : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        simp only [invFactorial, if_pos hz0, if_pos hz1]
        rw [he, Nat.factorial_succ, Nat.cast_mul]
        simp only [Nat.cast_add, Nat.cast_one]
        rw [hc]
        field_simp
      · have hz1 : z-1 < 0 := by omega
        rw [invFactorial_neg _ hz1]
        by_cases he : z = 0
        · subst z; simp only [Int.cast_zero, zero_mul]
        · rw [invFactorial_neg _ (by omega)]; simp only [mul_zero]
    have kernel_at_base (N i j k : ℕ) (hN : 2 ≤ N) (hk : k ≤ j+1) : factorialKernel N i j k = ((i : ℚ)+1-k)^2*((N : ℚ)^2-(i+j-k)^2)*certificateBase N i j k := by
      have ht : N+i+j-k = (N+i+j-k-1)+1 := by omega
      have hc : ((N+i+j-k-1 : ℕ) : ℚ)+1 = (N : ℚ)+i+j-k := by
        simp only [Nat.cast_sub (by omega : 1 ≤ N+i+j-k), Nat.cast_sub (by omega : k ≤ N+i+j), Nat.cast_add, Nat.cast_one]
        ring
      have ha := invFactorial_step ((i : ℤ)+1-k)
      have hb := invFactorial_step ((N : ℤ)+k-i-j)
      have hae : (i : ℤ)+1-k-1 = (i : ℤ)-k := by ring
      have hbe : (N : ℤ)+k-i-j-1 = (N : ℤ)-1+k-i-j := by ring
      rw [hae] at ha
      rw [hbe] at hb
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] at ha hb
      unfold factorialKernel certificateBase
      rw [ht, Nat.factorial_succ, Nat.cast_mul]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [hc, ha, hb]
      ring
    have kernel_up_at_base (N i j k : ℕ) (hN : 2 ≤ N) (hk : k ≤ j+1) : factorialKernel N (i+1) j k = ((N : ℚ)+i+j-k)*((N : ℚ)+i+j-k+1)* ((N : ℚ)+k-i-j)*((N : ℚ)+k-i-j-1)*certificateBase N i j k := by
      have ht : N+(i+1)+j-k = ((N+i+j-k-1)+1)+1 := by omega
      have hc : ((N+i+j-k-1 : ℕ) : ℚ)+1 = (N : ℚ)+i+j-k := by
        simp only [Nat.cast_sub (by omega : 1 ≤ N+i+j-k), Nat.cast_sub (by omega : k ≤ N+i+j), Nat.cast_add, Nat.cast_one]
        ring
      have ha := invFactorial_step ((N : ℤ)+k-i-j)
      have hb := invFactorial_step ((N : ℤ)+k-i-j-1)
      have hae : (N : ℤ)+k-i-j-1 = (N : ℤ)-1+k-i-j := by ring
      have hbe : (N : ℤ)+k-i-j-1-1 = (N : ℤ)-1+k-(i+1)-j := by ring
      rw [hbe] at hb
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] at ha hb
      unfold factorialKernel certificateBase
      rw [ht, Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
      simp only [Nat.cast_add, Nat.cast_one, Int.natCast_add, Int.natCast_one]
      rw [hc, hb, ha]
      ring
    have kernel_down_at_base (N i j k : ℕ) (hi : 1 ≤ i) : factorialKernel N (i-1) j k = ((i : ℚ)-k)^2*((i : ℚ)+1-k)^2*certificateBase N i j k := by
      have ht : N+(i-1)+j-k = N+i+j-k-1 := by omega
      have ha := invFactorial_step ((i : ℤ)+1-k)
      have hb := invFactorial_step ((i : ℤ)-k)
      have hae : (i : ℤ)+1-k-1 = (i : ℤ)-k := by ring
      have hbe : (i : ℤ)-k-1 = (i : ℤ)-1-k := by ring
      rw [hae] at ha
      rw [hbe] at hb
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] at ha hb
      unfold factorialKernel certificateBase
      rw [ht, Int.natCast_sub hi]
      simp only [Int.natCast_one]
      rw [hb, ha]
      have he : (N : ℤ)-1+k-(i-1)-j = (N : ℤ)+k-i-j := by ring
      rw [he]
      ring
    have flux_at_base (N i j k : ℕ) (hN : 2 ≤ N) (hk : k ≤ j+1) : kernelFlux N i j k = (k : ℚ)^2*((N : ℚ)^2-(i+j-k)^2)* certificatePolynomial N i j k*certificateBase N i j k := by
      have ht : N+i+j-k = (N+i+j-k-1)+1 := by omega
      have hc : ((N+i+j-k-1 : ℕ) : ℚ)+1 = (N : ℚ)+i+j-k := by
        simp only [Nat.cast_sub (by omega : 1 ≤ N+i+j-k), Nat.cast_sub (by omega : k ≤ N+i+j), Nat.cast_add, Nat.cast_one]
        ring
      have ha := invFactorial_step (k : ℤ)
      have hb := invFactorial_step ((N : ℤ)+k-i-j)
      rw [show (N : ℤ)+k-i-j-1 = (N : ℤ)-1+k-i-j by ring] at hb
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] at ha hb
      unfold kernelFlux certificateBase
      rw [ht, Nat.factorial_succ, Nat.cast_mul]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [hc, ha, hb]
      ring
    have flux_up_at_base (N i j k : ℕ) : kernelFlux N i j (k+1) = -((j : ℚ)-k)^2*((i : ℚ)+1-k)^2* certificatePolynomial N i j (k+1)*certificateBase N i j k := by
      have ht : N+i+j-(k+1) = N+i+j-k-1 := by omega
      have ha := invFactorial_step ((i : ℤ)+1-k)
      have hb := invFactorial_step ((j : ℤ)-k)
      rw [show (i : ℤ)+1-k-1 = (i : ℤ)-k by ring] at ha
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] at ha hb
      unfold kernelFlux certificateBase
      rw [ht, pow_succ]
      simp only [Int.natCast_add, Int.natCast_one]
      rw [show (i : ℤ)+1-(k+1) = (i : ℤ)-k by ring, show (j : ℤ)-(k+1) = (j : ℤ)-k-1 by ring, show (k : ℤ)+1-1 = (k : ℤ) by ring, show (N : ℤ)-1+(k+1)-i-j = (N : ℤ)+k-i-j by ring, ha, hb]
      push_cast
      ring
    have prefactor_step (N i j : ℕ) (hi : i+1 < N) (hj : j < N) : racahPrefactor N (i+1) j*((N : ℚ)^2-(i+1)^2) = racahPrefactor N i j*((i : ℚ)+1)^2 := by
      have deltaSq_equal (N i : ℕ) (hi : i < N) : deltaSq (2*i) (N-1) (N-1) = ((Nat.factorial i : ℚ)^2*Nat.factorial (N-1-i))/Nat.factorial (N+i) := by
        unfold deltaSq
        rw [show (2*i+(N-1)-(N-1))/2 = i by omega, show ((N-1)+(N-1)-2*i)/2 = N-1-i by omega, show (2*i+(N-1)+(N-1))/2+1 = N+i by omega]
        ring
      unfold racahPrefactor
      rw [deltaSq_equal N (i+1) hi, deltaSq_equal N i (by omega), deltaSq_equal N j hj]
      have ht : Nat.factorial (N-1-i) = (N-1-i)*Nat.factorial (N-1-(i+1)) := by
        have he : N-1-i = (N-1-(i+1))+1 := by omega
        conv_lhs => rw [he, Nat.factorial_succ]
        congr 1
        omega
      rw [Nat.factorial_succ, show N+(i+1) = (N+i)+1 by omega, Nat.factorial_succ, ht]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : i ≤ N-1), Nat.cast_sub (by omega : 1 ≤ N)]
      field_simp
      ring
    have hp := prefactor_step N i j hit hj
    have hm := prefactor_step N (i-1) j (by omega) hj
    rw [show i-1+1 = i by omega] at hm
    have hc := certificate_identity (N : ℚ) i j k
    rw [kernel_at_base N i j k hN hk, kernel_up_at_base N i j k hN hk, kernel_down_at_base N i j k hi, flux_at_base N i j k hN hk, flux_up_at_base]
    simp only [Nat.cast_sub hi, Nat.cast_one, Nat.cast_add] at hm ⊢
    linear_combination racahPrefactor N i j*certificateBase N i j k*hc - (i : ℚ)*((i : ℚ)+1)*((N : ℚ)+i+j-k)*((N : ℚ)+i+j-k+1)* ((N : ℚ)+k-i-j)*((N : ℚ)+k-i-j-1)*certificateBase N i j k*hp +
      ((N : ℚ)^2-i^2)*((i : ℚ)-k)^2*((i : ℚ)+1-k)^2*certificateBase N i j k*hm
  have hs := sum_congr rfl (fun k (hk : k ∈ range (j+1)) =>
    kernel_wz_step N i j k hN hi hit hj (by have := mem_range.mp hk; omega))
  simp only [← mul_sum, ← sum_sub_distrib] at hs
  rw [sum_range_sub, flux_zero, flux_end] at hs
  simp only [sub_self, mul_zero] at hs
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  have he : (i : ℚ)*(
      ((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2)*(kernelSequence N j i-kernelSequence N j (i+1)) + (i : ℚ)*((N : ℚ)^2-i^2)*(kernelSequence N j i-kernelSequence N j (i-1)) - 2*(2*(i : ℚ)+1)*(j : ℚ)*(j+1)*kernelSequence N j i) = 0 := by
    dsimp only [kernelSequence]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hs
    linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hi0)
theorem racah_expansion_open (N i j : ℕ) (hN : 2 ≤ N)
    (hi : i < N) (hj : j < N) : (-1 : ℝ)^(N-1+i+j) * N * Wij N i j = (racahPolynomial N j i : ℝ) := by
  let newtonPolynomial (N j : ℕ) (x : ℚ) : ℚ := ∑ k ∈ range (j+1), racahCoefficient N j k * newtonBasis k x
  have newtonBasis_shift_down (k : ℕ) (x : ℚ) : newtonBasis (k+1) (x-1) = (x-k-1)*(x-k)*newtonBasis k x := by
    unfold newtonBasis
    simp only [prod_mul_distrib]
    have ha : (∏ r ∈ range (k+1), ((x-1)+r+1)) = (∏ r ∈ range k, (x+r+1))*x := by
      rw [prod_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      convert rfl using 1 <;> congr 1
      · apply prod_congr rfl
        intro r _
        ring
      · ring
    have hd : x*(∏ r ∈ range (k+1), ((x-1)-(r : ℚ))) = (x-k-1)*(x-k)*(∏ r ∈ range k, (x-r)) := by
      have h := prod_range_succ' (fun r : ℕ => x-r) (k+1)
      rw [prod_range_succ, prod_range_succ] at h
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero] at h
      have he : (∏ r ∈ range (k+1), (x-((r : ℚ)+1))) = ∏ r ∈ range (k+1), ((x-1)-r) := by
        apply prod_congr rfl
        intro r _
        ring
      rw [he] at h
      linear_combination -h
    rw [ha]
    calc
      _ = (x*(∏ r ∈ range (k+1), ((x-1)-r)))*(∏ r ∈ range k, (x+r+1)) := by ring
      _ = _ := by rw [hd]; ring
  have newtonBasis_shift_up (k : ℕ) (x : ℚ) : newtonBasis (k+1) (x+1) = (x+k+1)*(x+k+2)*newtonBasis k x := by
    unfold newtonBasis
    simp only [prod_mul_distrib]
    have hd : (∏ r ∈ range (k+1), ((x+1)-(r : ℚ))) = (∏ r ∈ range k, (x-r))*(x+1) := by
      rw [prod_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
      congr 1
      apply prod_congr rfl
      intro r _
      ring
    have ha : (x+1)*(∏ r ∈ range (k+1), ((x+1)+r+1)) = (x+k+1)*(x+k+2)*(∏ r ∈ range k, (x+r+1)) := by
      have h := prod_range_succ' (fun r : ℕ => x+r+1) (k+1)
      rw [prod_range_succ, prod_range_succ] at h
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at h
      have he : (∏ r ∈ range (k+1), (x+((r : ℚ)+1)+1)) = ∏ r ∈ range (k+1), ((x+1)+r+1) := by
        apply prod_congr rfl
        intro r _
        ring
      rw [he] at h
      linear_combination -h
    rw [hd]
    calc
      _ = (∏ r ∈ range k, (x-r))*((x+1)*(∏ r ∈ range (k+1), ((x+1)+r+1))) := by ring
      _ = _ := by rw [ha]; ring
  have newtonPolynomial_operator (N j : ℕ) (hj : j < N) (x : ℚ) : (x+1)*((N : ℚ)^2-(x+1)^2)*(newtonPolynomial N j x-newtonPolynomial N j (x+1)) + x*((N : ℚ)^2-x^2)*(newtonPolynomial N j x-newtonPolynomial N j (x-1)) =
      2*(2*x+1)*(j : ℚ)*(j+1)*newtonPolynomial N j x := by
    have newtonBasis_zero (x : ℚ) : newtonBasis 0 x = 1 := by
      simp only [newtonBasis, prod_range_zero]
    have newtonBasis_succ (k : ℕ) (x : ℚ) : newtonBasis (k+1) x = (x-k)*(x+k+1)*newtonBasis k x := by
      simp only [newtonBasis, prod_range_succ]
      ring
    have newtonBasis_operator (N x : ℚ) (k : ℕ) : (x+1)*(N^2-(x+1)^2)*(newtonBasis (k+1) x-newtonBasis (k+1) (x+1)) + x*(N^2-x^2)*(newtonBasis (k+1) x-newtonBasis (k+1) (x-1)) = 2*(2*x+1)*(((k : ℚ)+1)*(k+2)*newtonBasis (k+1) x -
          ((k : ℚ)+1)^2*(N^2-(k+1)^2)*newtonBasis k x) := by
      rw [newtonBasis_shift_up, newtonBasis_shift_down, newtonBasis_succ]
      ring
    have racahCoefficient_step (N j k : ℕ) (hk : k < j) (hj : j < N) : racahCoefficient N j (k+1) * ((k : ℚ)+1)^2 * ((N : ℚ)^2-(k+1)^2) = racahCoefficient N j k * ((k : ℚ)*(k+1)-(j : ℚ)*(j+1)) := by
      have hkn : k+1 < N := by omega
      have ha := congrArg (fun n : ℕ => (n : ℚ)) (Nat.choose_succ_right_eq j k)
      have hb := congrArg (fun n : ℕ => (n : ℚ)) (Nat.add_one_mul_choose_eq (j+k) k)
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : k ≤ j)] at ha
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hb
      have hfac : Nat.factorial (N-k-1) = (N-k-1)*Nat.factorial (N-(k+1)-1) := by
        rw [show N-k-1 = (N-(k+1)-1)+1 by omega, Nat.factorial_succ]
      have hf0 : (Nat.factorial (N+k) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hf1 : (N : ℚ)+k+1 ≠ 0 := by positivity
      have hk1 : (k : ℚ)+1 ≠ 0 := by positivity
      have hb' : (Nat.choose (j+k+1) (k+1) : ℚ) * (k+1) = ((j : ℚ)+k+1)*Nat.choose (j+k) k := by
        exact hb.symm
      unfold racahCoefficient
      rw [pow_succ, show N+(k+1) = (N+k)+1 by omega, Nat.factorial_succ, hfac]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ N-k), Nat.cast_sub (by omega : k ≤ N)]
      have hc : (Nat.choose j (k+1) : ℚ) * Nat.choose (j+k+1) (k+1) * (k+1)^2 = (Nat.choose j k : ℚ)*Nat.choose (j+k) k*((j : ℚ)-k)*((j : ℚ)+k+1) := by
        linear_combination (Nat.choose (j+k+1) (k+1) : ℚ)*(k+1)*ha + (Nat.choose j k : ℚ)*((j : ℚ)-k)*hb'
      field_simp [hf0, hf1]
      linear_combination -(N : ℚ)*((N : ℚ)^2-(k+1)^2)*hc
    let f : ℕ → ℚ := fun k => racahCoefficient N j k * (k : ℚ)*(k+1)*newtonBasis k x
    have hinner : ∀ k ∈ range j, racahCoefficient N j (k+1) * (((k : ℚ)+1)*(k+2)*newtonBasis (k+1) x - ((k : ℚ)+1)^2*((N : ℚ)^2-(k+1)^2)*newtonBasis k x) = (f (k+1)-f k)+(j : ℚ)*(j+1)*(racahCoefficient N j k*newtonBasis k x) := by
      intro k hk
      have hc := racahCoefficient_step N j k (mem_range.mp hk) hj
      simp only [f, Nat.cast_add, Nat.cast_one]
      linear_combination -newtonBasis k x*hc
    calc
      _ = ∑ k ∈ range (j+1), racahCoefficient N j k * ((x+1)*((N : ℚ)^2-(x+1)^2)*(newtonBasis k x-newtonBasis k (x+1)) + x*((N : ℚ)^2-x^2)*(newtonBasis k x-newtonBasis k (x-1))) := by
        simp only [newtonPolynomial, ← sum_sub_distrib, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro k hk
        ring
      _ = 2*(2*x+1)*(∑ k ∈ range j, racahCoefficient N j (k+1) * (((k : ℚ)+1)*(k+2)*newtonBasis (k+1) x - ((k : ℚ)+1)^2*((N : ℚ)^2-(k+1)^2)*newtonBasis k x)) := by
        rw [sum_range_succ']
        simp only [newtonBasis_zero, sub_self, mul_zero, add_zero]
        simp_rw [newtonBasis_operator]
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        ring
      _ = 2*(2*x+1)*(f j-f 0 + (j : ℚ)*(j+1)* (∑ k ∈ range j, racahCoefficient N j k*newtonBasis k x)) := by
        rw [sum_congr rfl hinner, sum_add_distrib, sum_range_sub, ← mul_sum]
      _ = 2*(2*x+1)*(j : ℚ)*(j+1)*newtonPolynomial N j x := by
        simp only [newtonPolynomial, sum_range_succ, f, Nat.cast_zero, zero_mul, mul_zero, sub_zero]
        ring
  have newtonBasis_eq_monomial (k i : ℕ) : newtonBasis k (i : ℚ) = racahMonomial k i := by
    by_cases hk : k ≤ i
    · rw [racahMonomial, if_pos hk]
      have hd : (∏ r ∈ range k, ((i : ℚ)-r)) = (i.descFactorial k : ℚ) := by
        rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
        apply prod_congr rfl
        intro r hr
        rw [Nat.cast_sub (by have := mem_range.mp hr; omega)]
      have ha : (∏ r ∈ range k, ((i : ℚ)+r+1)) = ((i+1).ascFactorial k : ℚ) := by
        rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
        apply prod_congr rfl
        intro r _
        push_cast
        ring
      rw [newtonBasis, prod_mul_distrib, hd, ha]
      have hd' := congrArg (fun n : ℕ => (n : ℚ)) (Nat.factorial_mul_descFactorial hk)
      have ha' := congrArg (fun n : ℕ => (n : ℚ)) (Nat.factorial_mul_ascFactorial i k)
      simp only [Nat.cast_mul] at hd' ha'
      have hfi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      have hfd : ((i-k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i-k)
      apply (eq_div_iff hfd).mpr
      calc
        _ = ((i-k).factorial : ℚ)*(i.descFactorial k : ℚ)*((i+1).ascFactorial k : ℚ) := by ring
        _ = (i.factorial : ℚ)*((i+1).ascFactorial k : ℚ) := by rw [hd']
        _ = _ := ha'
    · rw [racahMonomial, if_neg hk, newtonBasis]
      apply prod_eq_zero (mem_range.mpr (by omega : i < k))
      simp
  have polynomial_recurrence (N j i : ℕ) (hN : 2 ≤ N) (hj : j < N) : ((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2)*(racahPolynomial N j i-racahPolynomial N j (i+1)) + (i : ℚ)*((N : ℚ)^2-i^2)*(racahPolynomial N j i-racahPolynomial N j (i-1)) =
      2*(2*(i : ℚ)+1)*(j : ℚ)*(j+1)*racahPolynomial N j i := by
    have newtonBasis_zero (x : ℚ) : newtonBasis 0 x = 1 := by
      simp only [newtonBasis, prod_range_zero]
    have racahCoefficient_zero (N j : ℕ) (hN : 1 ≤ N) : racahCoefficient N j 0 = 1 := by
      have hn0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have hf0 : (Nat.factorial (N-1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      simp only [racahCoefficient, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.add_zero]
      rw [show Nat.factorial N = N*Nat.factorial (N-1) by
        have he : N-1+1 = N := by omega
        simpa only [he] using Nat.factorial_succ (N-1)]
      push_cast
      field_simp
    have newtonPolynomial_nat (N j i : ℕ) (hN : 1 ≤ N) : newtonPolynomial N j (i : ℚ) = racahPolynomial N j i := by
      dsimp only [newtonPolynomial]
      rw [sum_range_succ']
      simp only [racahCoefficient_zero N j hN, newtonBasis_zero, mul_one]
      rw [add_comm]
      simp only [racahPolynomial, newtonBasis_eq_monomial]
    have hp := newtonPolynomial_operator N j hj (i : ℚ)
    have hn : 1 ≤ N := by omega
    by_cases hi : i = 0
    · subst i
      have hp0 : newtonPolynomial N j 0 = racahPolynomial N j 0 := newtonPolynomial_nat N j 0 hn
      have hp1 : newtonPolynomial N j 1 = racahPolynomial N j 1 := newtonPolynomial_nat N j 1 hn
      simpa only [Nat.cast_zero, zero_mul, zero_add, add_zero, hp0, hp1] using hp
    · have hcsub : (i : ℚ)-1 = ((i-1 : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ i)]; rfl
      have hcadd : (i : ℚ)+1 = ((i+1 : ℕ) : ℚ) := by push_cast; rfl
      rw [hcsub, hcadd] at hp
      rw [newtonPolynomial_nat N j i hn, newtonPolynomial_nat N j (i-1) hn, newtonPolynomial_nat N j (i+1) hn] at hp
      simpa only [Nat.cast_add, Nat.cast_one] using hp
  have normalizedRacah_initial (N j : ℕ) (hN : 2 ≤ N) (hj : j < N) : normalizedRacah N 0 j = 1 := by
    have deltaSq_equal (N i : ℕ) (hi : i < N) : deltaSq (2*i) (N-1) (N-1) = ((Nat.factorial i : ℚ)^2*Nat.factorial (N-1-i))/Nat.factorial (N+i) := by
      unfold deltaSq
      rw [show (2*i+(N-1)-(N-1))/2 = i by omega, show ((N-1)+(N-1)-2*i)/2 = N-1-i by omega, show (2*i+(N-1)+(N-1))/2+1 = N+i by omega]
      ring
    have hlow : lower 0 (N-1) (N-1) (2*j) (N-1) (N-1) = N-1+j := by
      unfold lower
      omega
    have hupp : upper 0 (N-1) (N-1) (2*j) (N-1) (N-1) = N-1+j := by
      unfold upper
      omega
    have hs : racahSum 0 (N-1) (N-1) (2*j) (N-1) (N-1) = racahTerm 0 (N-1) (N-1) (2*j) (N-1) (N-1) (N-1+j) := by
      unfold racahSum
      rw [hlow, hupp]
      rw [sum_eq_single (N-1+j)]
      · simp only [le_refl, if_true]
      · intro z hz hne
        have hz' := mem_range.mp hz
        have hnz : ¬ N-1+j ≤ z := by omega
        simp only [if_neg hnz]
      · intro h
        exact False.elim (h (mem_range.mpr (by omega)))
    have ht : racahTerm 0 (N-1) (N-1) (2*j) (N-1) (N-1) (N-1+j) = (-1 : ℚ)^(N-1+j)*Nat.factorial (N+j) / ((Nat.factorial j : ℚ)^2*Nat.factorial (N-1-j)) := by
      unfold racahTerm
      rw [show (0+(N-1)+(N-1))/2 = N-1 by omega, show (2*j+(N-1)+(N-1))/2 = N-1+j by omega, show (0+(N-1)+2*j+(N-1))/2 = N-1+j by omega, show ((N-1)+(N-1)+(N-1)+(N-1))/2 = 2*(N-1) by omega, show ((N-1)+0+(N-1)+2*j)/2 = N-1+j by omega]
      rw [show N-1+j+1 = N+j by omega, show N-1+j-(N-1) = j by omega, show 2*(N-1)-(N-1+j) = N-1-j by omega]
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      ring
    have hn : 0 < N := by omega
    have hn0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hf0 : (Nat.factorial (N-1) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hfj : (Nat.factorial j : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hf1 : (Nat.factorial (N-1-j) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hf2 : (Nat.factorial (N+j) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    unfold normalizedRacah
    simp only [Nat.add_zero, Nat.mul_zero]
    rw [hs, ht, deltaSq_equal N 0 (by omega), deltaSq_equal N j hj]
    simp only [Nat.factorial_zero, Nat.cast_one, one_pow, one_mul, Nat.sub_zero, Nat.add_zero]
    rw [show Nat.factorial N = N*Nat.factorial (N-1) by
      have he : N-1+1 = N := by omega
      simpa only [he] using Nat.factorial_succ (N-1)]
    have hsign : ((-1 : ℚ)^(N-1+j))^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      simp only [neg_one_sq, one_pow]
    field_simp [hn0, hf0, hfj, hf1, hf2]
    push_cast
    linear_combination (N : ℚ)*(Nat.factorial (N-1) : ℚ)*hsign
  have racah_kernel_identification (N i j : ℕ) (hN : 2 ≤ N)
      (hi : i < N) (hj : j < N) : normalizedRacah N i j = kernelSequence N j i := by
    have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
      simp only [invFactorial, if_neg (not_le.mpr hz)]
    have invFactorial_nat (n : ℕ) : invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
      simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    have factorialKernel_vanish (N i j k : ℕ) (hk : j < k ∨ i < k) : factorialKernel N i j k = 0 := by
      rcases hk with hk | hk
      · have hz : (j : ℤ)-k < 0 := by omega
        simp only [factorialKernel, invFactorial_neg _ hz, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul]
      · have hz : (i : ℤ)-k < 0 := by omega
        simp only [factorialKernel, invFactorial_neg _ hz, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul]
    have phase_reflection (n z : ℕ) (hz : z ≤ n) : (-1 : ℚ)^n*(-1 : ℚ)^z = (-1 : ℚ)^(n-z) := by
      have he : n = z+(n-z) := by omega
      conv_lhs => lhs; rw [he, pow_add]
      have hs : (-1 : ℚ)^z*(-1 : ℚ)^z = 1 := by
        rw [← mul_pow]
        simp only [neg_mul_neg, one_mul, one_pow]
      calc
        _ = ((-1 : ℚ)^z*(-1 : ℚ)^z)*(-1 : ℚ)^(n-z) := by ring
        _ = _ := by rw [hs, one_mul]
    have hlow : lower (2*i) (N-1) (N-1) (2*j) (N-1) (N-1) = max (N-1+i) (N-1+j) := by unfold lower; omega
    have hupp : upper (2*i) (N-1) (N-1) (2*j) (N-1) (N-1) = min (N-1+i+j) (2*(N-1)) := by unfold upper; omega
    let S := (range (min (N-1+i+j) (2*(N-1))+1)).filter
      (fun z => max (N-1+i) (N-1+j) ≤ z)
    let K := (range (j+1)).filter (fun k => k ≤ i ∧ i+j ≤ N-1+k)
    have hs : (∑ z ∈ S, (-1 : ℚ)^(N-1+i+j)* racahTerm (2*i) (N-1) (N-1) (2*j) (N-1) (N-1) z) = ∑ k ∈ K, factorialKernel N i j k := by
      apply sum_bij (fun z _ => N-1+i+j-z)
      · intro z hz
        simp only [S, mem_filter, mem_range] at hz
        simp only [K, mem_filter, mem_range]
        omega
      · intro z hz z' hz' he
        simp only [S, mem_filter, mem_range] at hz hz'
        omega
      · intro k hk
        simp only [K, mem_filter, mem_range] at hk
        have hz : N-1+i+j-k ∈ S := by
          simp only [S, mem_filter, mem_range]
          omega
        exact ⟨N-1+i+j-k, hz, by omega⟩
      · intro z hz
        simp only [S, mem_filter, mem_range] at hz
        have hz0 : z ≤ N-1+i+j := by omega
        have he0 : ((i : ℤ)-((N-1+i+j-z : ℕ) : ℤ)) = ((z-(N-1+j) : ℕ) : ℤ) := by omega
        have he1 : ((j : ℤ)-((N-1+i+j-z : ℕ) : ℤ)) = ((z-(N-1+i) : ℕ) : ℤ) := by omega
        have he2 : (N : ℤ)-1+((N-1+i+j-z : ℕ) : ℤ)-i-j = ((2*(N-1)-z : ℕ) : ℤ) := by omega
        unfold racahTerm factorialKernel
        rw [he0, he1, he2, invFactorial_nat, invFactorial_nat, invFactorial_nat, invFactorial_nat]
        rw [show (2*i+(N-1)+(N-1))/2 = N-1+i by omega, show (2*j+(N-1)+(N-1))/2 = N-1+j by omega, show (2*i+(N-1)+2*j+(N-1))/2 = N-1+i+j by omega, show ((N-1)+(N-1)+(N-1)+(N-1))/2 = 2*(N-1) by omega,
          show ((N-1)+2*i+(N-1)+2*j)/2 = N-1+i+j by omega, show N+i+j-(N-1+i+j-z) = z+1 by omega]
        rw [show (-1 : ℚ)^(N-1+i+j)* ((-1 : ℚ)^z*Nat.factorial (z+1) / (Nat.factorial (z-(N-1+i))*Nat.factorial (z-(N-1+i))* Nat.factorial (z-(N-1+j))*Nat.factorial (z-(N-1+j))* Nat.factorial (N-1+i+j-z)*Nat.factorial (2*(N-1)-z)*
                Nat.factorial (N-1+i+j-z) : ℚ)) = ((-1 : ℚ)^(N-1+i+j)*(-1 : ℚ)^z)*Nat.factorial (z+1) / (Nat.factorial (z-(N-1+i))*Nat.factorial (z-(N-1+i))* Nat.factorial (z-(N-1+j))*Nat.factorial (z-(N-1+j))*
                Nat.factorial (N-1+i+j-z)*Nat.factorial (2*(N-1)-z)* Nat.factorial (N-1+i+j-z) : ℚ) by ring]
        rw [phase_reflection _ _ hz0]
        simp only [div_eq_mul_inv, _root_.mul_inv_rev]
        ring
    have hfull : (∑ k ∈ K, factorialKernel N i j k) = ∑ k ∈ range (j+1), factorialKernel N i j k := by
      simp only [K, sum_filter]
      apply sum_congr rfl
      intro k hk
      by_cases h : k ≤ i ∧ i+j ≤ N-1+k
      · rw [if_pos h]
      · rw [if_neg h]
        by_cases hik : k ≤ i
        · have hz : (N : ℤ)-1+k-i-j < 0 := by omega
          simp only [factorialKernel, invFactorial_neg _ hz, mul_zero]
        · exact (factorialKernel_vanish N i j k (Or.inr (by omega))).symm
    have hsum : (-1 : ℚ)^(N-1+i+j)* racahSum (2*i) (N-1) (N-1) (2*j) (N-1) (N-1) = ∑ k ∈ range (j+1), factorialKernel N i j k := by
      rw [← hfull, ← hs]
      simp only [racahSum, hlow, hupp, S, sum_filter, mul_sum, mul_ite, mul_zero]
    calc
      _ = racahPrefactor N i j*((-1 : ℚ)^(N-1+i+j)* racahSum (2*i) (N-1) (N-1) (2*j) (N-1) (N-1)) := by
        unfold normalizedRacah racahPrefactor
        ring
      _ = _ := by rw [hsum]; rfl
  have polynomial_initial (N j : ℕ) : racahPolynomial N j 0 = 1 := by
    simp only [racahPolynomial, racahMonomial, Nat.add_one_le_iff, not_lt_zero, if_false, mul_zero, sum_const_zero, add_zero]
  have normalizedRacah_real (N i j : ℕ) (hi : i < N) (hj : j < N) : (normalizedRacah N i j : ℝ) = (-1 : ℝ)^(N-1+i+j)*N*Wij N i j := by
    have equal_triangle (N i : ℕ) (hi : i < N) : triangle (2*i) (N-1) (N-1) := by
      unfold triangle
      omega
    have had : admissible (2*i) (N-1) (N-1) (2*j) (N-1) (N-1) := ⟨equal_triangle N i hi, equal_triangle N i hi, equal_triangle N j hj, equal_triangle N j hj⟩
    have hd : 0 ≤ ((deltaSq (2*i) (N-1) (N-1)*deltaSq (2*j) (N-1) (N-1) : ℚ) : ℝ) := by
      unfold deltaSq
      push_cast
      positivity
    have he : ((deltaSq (2*i) (N-1) (N-1)*deltaSq (2*i) (N-1) (N-1)* deltaSq (2*j) (N-1) (N-1)*deltaSq (2*j) (N-1) (N-1) : ℚ) : ℝ) = (((deltaSq (2*i) (N-1) (N-1)*deltaSq (2*j) (N-1) (N-1) : ℚ) : ℝ))^2 := by
      push_cast
      ring
    rw [Wij, sixJ, if_pos had, he, Real.sqrt_sq hd]
    simp only [normalizedRacah, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg, Rat.cast_one]
    ring
  have kernel_recurrence (N j i : ℕ) (hN : 2 ≤ N) (hj : j < N)
      (hit : i+1 < N) : ((i : ℚ)+1)*((N : ℚ)^2-(i+1)^2)*(kernelSequence N j i-kernelSequence N j (i+1)) + (i : ℚ)*((N : ℚ)^2-i^2)*(kernelSequence N j i-kernelSequence N j (i-1)) = 2*(2*(i : ℚ)+1)*(j : ℚ)*(j+1)*kernelSequence N j i := by
    have kernel_boundary (N j : ℕ) (hN : 2 ≤ N) (hj : j < N) : ((N : ℚ)^2-1)*(kernelSequence N j 0-kernelSequence N j 1) = 2*(j : ℚ)*(j+1)*kernelSequence N j 0 := by
      have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
        simp only [invFactorial, if_neg (not_le.mpr hz)]
      have invFactorial_step (z : ℤ) : invFactorial (z-1) = (z : ℚ)*invFactorial z := by
        by_cases hz : 0 < z
        · have hz0 : 0 ≤ z := by omega
          have hz1 : 0 ≤ z-1 := by omega
          have he : z.toNat = (z-1).toNat+1 := by omega
          have hc : ((z-1).toNat+1 : ℚ) = (z : ℚ) := by
            have h : (((z-1).toNat+1 : ℕ) : ℤ) = z := by omega
            exact_mod_cast h
          have hn0 : (z : ℚ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
          have hf0 : (Nat.factorial (z-1).toNat : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
          simp only [invFactorial, if_pos hz0, if_pos hz1]
          rw [he, Nat.factorial_succ, Nat.cast_mul]
          simp only [Nat.cast_add, Nat.cast_one]
          rw [hc]
          field_simp
        · have hz1 : z-1 < 0 := by omega
          rw [invFactorial_neg _ hz1]
          by_cases he : z = 0
          · subst z; simp only [Int.cast_zero, zero_mul]
          · rw [invFactorial_neg _ (by omega)]; simp only [mul_zero]
      have factorialKernel_vanish (N i j k : ℕ) (hk : j < k ∨ i < k) : factorialKernel N i j k = 0 := by
        rcases hk with hk | hk
        · have hz : (j : ℤ)-k < 0 := by omega
          simp only [factorialKernel, invFactorial_neg _ hz, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul]
        · have hz : (i : ℤ)-k < 0 := by omega
          simp only [factorialKernel, invFactorial_neg _ hz, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul]
      have kernel_at_base (N i j k : ℕ) (hN : 2 ≤ N) (hk : k ≤ j+1) : factorialKernel N i j k = ((i : ℚ)+1-k)^2*((N : ℚ)^2-(i+j-k)^2)*certificateBase N i j k := by
        have ht : N+i+j-k = (N+i+j-k-1)+1 := by omega
        have hc : ((N+i+j-k-1 : ℕ) : ℚ)+1 = (N : ℚ)+i+j-k := by
          simp only [Nat.cast_sub (by omega : 1 ≤ N+i+j-k), Nat.cast_sub (by omega : k ≤ N+i+j), Nat.cast_add, Nat.cast_one]
          ring
        have ha := invFactorial_step ((i : ℤ)+1-k)
        have hb := invFactorial_step ((N : ℤ)+k-i-j)
        have hae : (i : ℤ)+1-k-1 = (i : ℤ)-k := by ring
        have hbe : (N : ℤ)+k-i-j-1 = (N : ℤ)-1+k-i-j := by ring
        rw [hae] at ha
        rw [hbe] at hb
        simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] at ha hb
        unfold factorialKernel certificateBase
        rw [ht, Nat.factorial_succ, Nat.cast_mul]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        rw [hc, ha, hb]
        ring
      have kernel_up_at_base (N i j k : ℕ) (hN : 2 ≤ N) (hk : k ≤ j+1) : factorialKernel N (i+1) j k = ((N : ℚ)+i+j-k)*((N : ℚ)+i+j-k+1)* ((N : ℚ)+k-i-j)*((N : ℚ)+k-i-j-1)*certificateBase N i j k := by
        have ht : N+(i+1)+j-k = ((N+i+j-k-1)+1)+1 := by omega
        have hc : ((N+i+j-k-1 : ℕ) : ℚ)+1 = (N : ℚ)+i+j-k := by
          simp only [Nat.cast_sub (by omega : 1 ≤ N+i+j-k), Nat.cast_sub (by omega : k ≤ N+i+j), Nat.cast_add, Nat.cast_one]
          ring
        have ha := invFactorial_step ((N : ℤ)+k-i-j)
        have hb := invFactorial_step ((N : ℤ)+k-i-j-1)
        have hae : (N : ℤ)+k-i-j-1 = (N : ℤ)-1+k-i-j := by ring
        have hbe : (N : ℤ)+k-i-j-1-1 = (N : ℤ)-1+k-(i+1)-j := by ring
        rw [hbe] at hb
        simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] at ha hb
        unfold factorialKernel certificateBase
        rw [ht, Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
        simp only [Nat.cast_add, Nat.cast_one, Int.natCast_add, Int.natCast_one]
        rw [hc, hb, ha]
        ring
      have prefactor_step (N i j : ℕ) (hi : i+1 < N) (hj : j < N) : racahPrefactor N (i+1) j*((N : ℚ)^2-(i+1)^2) = racahPrefactor N i j*((i : ℚ)+1)^2 := by
        have deltaSq_equal (N i : ℕ) (hi : i < N) : deltaSq (2*i) (N-1) (N-1) = ((Nat.factorial i : ℚ)^2*Nat.factorial (N-1-i))/Nat.factorial (N+i) := by
          unfold deltaSq
          rw [show (2*i+(N-1)-(N-1))/2 = i by omega, show ((N-1)+(N-1)-2*i)/2 = N-1-i by omega, show (2*i+(N-1)+(N-1))/2+1 = N+i by omega]
          ring
        unfold racahPrefactor
        rw [deltaSq_equal N (i+1) hi, deltaSq_equal N i (by omega), deltaSq_equal N j hj]
        have ht : Nat.factorial (N-1-i) = (N-1-i)*Nat.factorial (N-1-(i+1)) := by
          have he : N-1-i = (N-1-(i+1))+1 := by omega
          conv_lhs => rw [he, Nat.factorial_succ]
          congr 1
          omega
        rw [Nat.factorial_succ, show N+(i+1) = (N+i)+1 by omega, Nat.factorial_succ, ht]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : i ≤ N-1), Nat.cast_sub (by omega : 1 ≤ N)]
        field_simp
        ring
      have kernel_sum_zero (N j : ℕ) : (∑ k ∈ range (j+1), factorialKernel N 0 j k) = factorialKernel N 0 j 0 := by
        apply sum_eq_single
        · intro k hk hne
          exact factorialKernel_vanish N 0 j k (Or.inr (by omega))
        · intro h
          exact False.elim (h (mem_range.mpr (by omega)))
      have kernel_sum_one (N j : ℕ) : (∑ k ∈ range (j+1), factorialKernel N 1 j k) = factorialKernel N 1 j 0+factorialKernel N 1 j 1 := by
        have hext : (∑ k ∈ range (j+2), factorialKernel N 1 j k) = ∑ k ∈ range (j+1), factorialKernel N 1 j k := by
          rw [show j+2 = (j+1)+1 by omega, sum_range_succ, factorialKernel_vanish N 1 j (j+1) (Or.inl (by omega)), add_zero]
        rw [← hext, show j+2 = (j+1)+1 by omega, sum_range_succ', sum_range_succ']
        have hrest : (∑ k ∈ range j, factorialKernel N 1 j (k+1+1)) = 0 := by
          apply sum_eq_zero
          intro k hk
          exact factorialKernel_vanish N 1 j (k+1+1) (Or.inr (by omega))
        rw [hrest]
        ring
      have kernel_one_last_at_base (N j : ℕ) (hN : 2 ≤ N) : factorialKernel N 1 j 1 = -((N : ℚ)^2-j^2)*(j : ℚ)^2*certificateBase N 0 j 0 := by
        have ht : N+1+j-1 = (N+j-1)+1 := by omega
        have hc : ((N+j-1 : ℕ) : ℚ)+1 = (N : ℚ)+j := by
          simp only [Nat.cast_sub (by omega : 1 ≤ N+j), Nat.cast_add, Nat.cast_one]
          ring
        have ha := invFactorial_step (j : ℤ)
        have hb := invFactorial_step ((N : ℤ)-j)
        simp only [Int.cast_sub, Int.cast_natCast] at ha hb
        unfold factorialKernel certificateBase
        simp only [Int.natCast_one, Int.natCast_zero, pow_one, pow_zero, Nat.add_zero, Nat.sub_zero, Int.sub_self, Int.zero_add, sub_zero, zero_add, mul_one, one_mul]
        rw [show (N : ℤ)-1+1-1-j = (N : ℤ)-j-1 by ring, show (N : ℤ)+0-j = (N : ℤ)-j by ring]
        rw [ht, Nat.factorial_succ, Nat.cast_mul]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        rw [hc, ha, hb]
        have hzero : invFactorial 0 = 1 := by
          simp only [invFactorial, le_refl, if_true, Int.toNat_zero, Nat.factorial_zero, Nat.cast_one, inv_one]
        have hone : invFactorial 1 = 1 := by
          simp only [invFactorial, show (0 : ℤ) ≤ 1 by omega, if_true, Int.toNat_one, Nat.factorial_one, Nat.cast_one, inv_one]
        simp only [hzero, hone, one_pow, mul_one]
        ring
      have hp := prefactor_step N 0 j (by omega) hj
      simp only [Nat.cast_zero, zero_add, one_pow] at hp
      have hz := kernel_at_base N 0 j 0 hN (by omega)
      have hu := kernel_up_at_base N 0 j 0 hN (by omega)
      have hl := kernel_one_last_at_base N j hN
      simp only [Nat.cast_zero, zero_add, add_zero, sub_zero] at hz hu
      have he : factorialKernel N 1 j 0+factorialKernel N 1 j 1 = ((N : ℚ)^2-1-2*(j : ℚ)*(j+1))*factorialKernel N 0 j 0 := by
        rw [hz, hu, hl]
        ring
      unfold kernelSequence
      rw [kernel_sum_zero, kernel_sum_one, he]
      linear_combination -(((N : ℚ)^2-1-2*(j : ℚ)*(j+1))*factorialKernel N 0 j 0)*hp
    by_cases hi : i = 0
    · subst i
      simpa only [Nat.cast_zero, zero_add, zero_mul, mul_zero, add_zero, one_pow, one_mul, mul_one] using kernel_boundary N j hN hj
    · exact kernel_recurrence_interior N j i hN (by omega) hit hj
  have h0 : kernelSequence N j 0 = racahPolynomial N j 0 := by
    rw [← racah_kernel_identification N 0 j hN (by omega) hj, normalizedRacah_initial N j hN hj, polynomial_initial]
  have he := recurrence_unique N j (kernelSequence N j) (racahPolynomial N j) hN h0
    (fun i hit => kernel_recurrence N j i hN hj hit)
    (fun i _ => polynomial_recurrence N j i hN hj)
  rw [← normalizedRacah_real N i j hi hj, racah_kernel_identification N i j hN hi hj]
  exact congrArg (fun x : ℚ => (x : ℝ)) (he i hi)
def rawAlpha (a b c d y : ℚ) : ℚ := (((y+1)^2-(a-d)^2)*((y+1)^2-(b-c)^2))/(2*(y+1)*(2*y+1))

def rawGamma (a b c d y : ℚ) : ℚ := (((a+d+1)^2-y^2)*((b+c+1)^2-y^2))/(2*y*(2*y+1))

def rawDiagonal (a b c d y : ℚ) : ℚ := a*(a+1)+b*(b+1)- ((y*(y+1)+a*(a+1)-d*(d+1))*(y*(y+1)+b*(b+1)-c*(c+1)))/(2*y*(y+1))

def fourSpinDenominator (y : ℚ) : ℚ := 2*y*(y+1)*(2*y+1)

def fourSpinCertificateNumerator (a b c d u y z : ℚ) : ℚ := -(y+1)*(b+c+1-y)*(a+d+y+1)*(a-b+u+1)*(d-c+u+1) + 2*(y+1)*((u+1)*((a+d+1)*(b+c+1)-y^2)+y*((a-b)*(c-d)-(u+1)^2))* (z-(b+c+y)) +
    (2*u*y*(y+1)+y^2-(a+d+1)*(b+c+1)-y*(2*a*c+2*b*d+a+b+c+d))* (z-(b+c+y))*(z-(a+d+y))
def fourSpinCertificate (a b c d u y z : ℚ) : ℚ := fourSpinCertificateNumerator a b c d u y z / fourSpinDenominator y

def compressedAlpha (h v p q y : ℚ) : ℚ := y*((p-q)^2-2*(y+1)*(v-2*y-2)*(p-q)+4*(y+1)^2*q)

def compressedBeta (m h v p q y : ℚ) : ℚ := -(2*y+1)*((p-q)*(m+y*h-y)+2*y*(y+1)*p+(y+1)*(m+2*y*h)*(1-v))

def compressedGamma (m h y : ℚ) : ℚ := (y+1)*m*(m+2*y*h)

def compressedV (v p x : ℚ) : ℚ := x^2-v*x+p

def compressedZ (m h y x : ℚ) : ℚ := m+(2*y+1)*(h-1)+(h-2*y-2)*x-x^2

def compressedQ (v q y x : ℚ) : ℚ := x^2-(v-2*y-2)*x+q

def compressedCertificate (m h v p q y x : ℚ) : ℚ := -(y+1)*m*p+(y+1)*((v-h)*(m+2*y*h)-2*y*p)*x + (y*(p-q)-(y+1)*m-2*y*(y+1)*h)*x*(x-h)

structure RacahOffsets where
  ta : ℤ
  tb : ℤ
  tc : ℤ
  td : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
def RacahOffsets.raise (q : RacahOffsets) : RacahOffsets := ⟨q.ta+1, q.tb+1, q.tc, q.td, q.e, q.f+1, q.g+1⟩

def RacahOffsets.lower (q : RacahOffsets) : RacahOffsets := ⟨q.ta-1, q.tb-1, q.tc, q.td, q.e, q.f-1, q.g-1⟩

def offsetTerm (q : RacahOffsets) (z : ℕ) : ℚ := (-1 : ℚ)^z * Nat.factorial (z+1) * invFactorial ((z : ℤ)-q.ta) * invFactorial ((z : ℤ)-q.tb) * invFactorial ((z : ℤ)-q.tc) * invFactorial ((z : ℤ)-q.td) *
    invFactorial (q.e-z) * invFactorial (q.f-z) * invFactorial (q.g-z)
def offsetBase (q : RacahOffsets) (z : ℕ) : ℚ := (-1 : ℚ)^z * Nat.factorial (z+1) * invFactorial ((z : ℤ)-q.ta+1) * invFactorial ((z : ℤ)-q.tb+1) * invFactorial ((z : ℤ)-q.tc) * invFactorial ((z : ℤ)-q.td) *
    invFactorial (q.e-z) * invFactorial (q.f-z+1) * invFactorial (q.g-z+1)
def offsetFlux (q : RacahOffsets) (P : ℚ → ℚ) (z : ℕ) : ℚ := (-1 : ℚ)^z * Nat.factorial (z+1) * P z * invFactorial ((z : ℤ)-q.ta) * invFactorial ((z : ℤ)-q.tb) * invFactorial ((z : ℤ)-q.tc-1) * invFactorial ((z : ℤ)-q.td-1) *
    invFactorial (q.e-z) * invFactorial (q.f-z+1) * invFactorial (q.g-z+1)
def RacahOffsets.compatible (q : RacahOffsets) (a b c d u y : ℚ) : Prop := (q.ta : ℚ) = a+d+y ∧ (q.tb : ℚ) = b+c+y ∧ (q.tc : ℚ) = a+b+u ∧ (q.td : ℚ) = c+d+u ∧ (q.e : ℚ) = a+b+c+d ∧ (q.f : ℚ) = a+c+u+y ∧ (q.g : ℚ) = b+d+u+y

end D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
