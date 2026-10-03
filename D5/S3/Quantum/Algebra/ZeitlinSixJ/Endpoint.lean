/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/
/-
endpoint_normalization:
  proof_shape: content
  escape_witness: Local endpoint_sum_step: for d<=n, sum i in range(p+1), endpointWeight (n+1) p d i = sum i in range(p+1), endpointWeight n p d i, obtained from the exact WZ difference and used in Nat.le_induction.
signed_endpoint_normalization:
  proof_shape: content
  escape_witness: Local signed_endpoint_sum_step: for d<=n, the signedEndpointWeight sums at n+1 and n are equal; the signed WZ flux and vanishing endpoints feed the live unbounded induction.
stretched_row_alternating:
  proof_shape: content
  escape_witness: signed_endpoint_normalization: for d<=n,p, sum i in range(p+1), signedEndpointWeight n p d i = (-1)^d. Its WZ/induction construction is used after converting the squared stretched Racah symbol to endpoint weights.
signed_stretched_endpoint_match:
  proof_shape: content
  escape_witness: signed_endpoint_normalization at p=2*j+d: the full signed endpoint sum equals (-1)^d. This nontrivial sum evaluation remains live after the stretched-row and star-endpoint factorial substitutions.
dual_intertwining_orthogonality:
  proof_shape: content
  escape_witness: Local hconst: forall i:Fin(m+1), (U*transpose U) i i = (U*transpose U) 0 0. It is constructed by Fin.induction from the nonzero adjacent T entries, after hQ proves that the Gram matrix is diagonal, and is used with the anchor.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
import Mathlib.Data.Matrix.Basic

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence

lemma endpoint_normalization (n p d : ℕ) (hd : d ≤ n) (hp : d ≤ p) : (∑ i ∈ range (p+1), endpointWeight n p d i) = 1 := by
  have endpoint_base_sum (p d : ℕ) (hp : d ≤ p) : (∑ i ∈ range (p+1), endpointWeight d p d i) = 1 := by
    have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
      simp only [invFactorial, if_neg (not_le.mpr hz)]
    have invFactorial_nat (n : ℕ) : invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
      simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    have invFactorial_zero : invFactorial (0 : ℤ) = 1 := by
      simp [invFactorial]
    have invFactorial_nat_sub (n m : ℕ) (h : m ≤ n) : invFactorial ((n : ℤ)-(m : ℤ)) = (Nat.factorial (n-m) : ℚ)⁻¹ := by
      rw [← Int.natCast_sub h, invFactorial_nat]
    have endpointKernel_vanish (n p d i : ℕ) (h : i < d ∨ n < i ∨ p < i) : endpointKernel n p d i = 0 := by
      unfold endpointKernel
      rcases h with h | h | h
      · rw [invFactorial_neg ((i : ℤ)-d) (by omega)]; ring
      · rw [invFactorial_neg ((n : ℤ)-i) (by omega)]; ring
      · rw [invFactorial_neg ((p : ℤ)-i) (by omega)]; ring
    have endpointConstant_base (p d : ℕ) : endpointConstant d p d = signedEndpointConstant d p d := by
      unfold endpointConstant signedEndpointConstant
      rw [show (d : ℤ)+p-d = (p : ℤ) by ring, invFactorial_nat, invFactorial_nat]
      have hd : (Nat.factorial d : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
      have hp : (Nat.factorial p : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
      field_simp
    have endpoint_base_term (p d : ℕ) (hp : d ≤ p) : signedEndpointConstant d p d * (2*(d : ℚ)+1)*endpointKernel d p d d = 1 := by
      unfold signedEndpointConstant endpointKernel
      simp only [Nat.sub_self, Nat.factorial_zero, Int.sub_self, invFactorial_zero, one_mul, mul_one]
      rw [invFactorial_nat_sub p d hp, show (d : ℤ)+d+1 = ((d+d+1 : ℕ) : ℤ) by omega, show (p : ℤ)+d+1 = ((p+d+1 : ℕ) : ℤ) by omega, invFactorial_nat, invFactorial_nat, show p+d+1 = d+p+1 by omega, Nat.factorial_succ (d+d)]
      have hf : ∀ t : ℕ, (Nat.factorial t : ℚ) ≠ 0 := fun t => by exact_mod_cast Nat.factorial_ne_zero t
      have hd : ((d+d+1 : ℕ) : ℚ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [sum_eq_single d]
    · rw [endpointWeight, endpointConstant_base, endpoint_base_term p d hp]
    · intro i hi hdi
      unfold endpointWeight
      rw [endpointKernel_vanish _ _ _ _ (by omega)]
      ring
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))
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
  have endpointKernel_new_base (n p d i : ℕ) : endpointKernel (n+1) p d i = ((i : ℚ)+1-d)*endpointBase n p d i := by
    have h := invFactorial_step ((i : ℤ)+1-d)
    rw [show (i : ℤ)+1-d-1 = (i : ℤ)-d by ring] at h
    unfold endpointKernel endpointBase
    rw [h]
    push_cast
    rw [show (n : ℤ)+1+i+1 = (n : ℤ)+i+2 by ring]
    ring
  have endpointKernel_old_base (n p d i : ℕ) : endpointKernel n p d i = ((n : ℚ)+1-i)*((n : ℚ)+i+2)*((i : ℚ)+1-d)*endpointBase n p d i := by
    have h1 := invFactorial_step ((n : ℤ)+1-i)
    have h2 := invFactorial_step ((n : ℤ)+i+2)
    have h3 := invFactorial_step ((i : ℤ)+1-d)
    rw [show (n : ℤ)+1-i-1 = (n : ℤ)-i by ring] at h1
    rw [show (n : ℤ)+i+2-1 = (n : ℤ)+i+1 by ring] at h2
    rw [show (i : ℤ)+1-d-1 = (i : ℤ)-d by ring] at h3
    unfold endpointKernel endpointBase
    rw [h1,h2,h3]
    push_cast
    ring
  have endpointKernel_next_base (n p d i : ℕ) : ((p : ℚ)+i+2)*((n : ℚ)+i+3)*endpointKernel (n+1) p d (i+1) = ((i : ℚ)+d+1)*((n : ℚ)+1-i)*((p : ℚ)-i)*endpointBase n p d i := by
    have h1 := invFactorial_step ((n : ℤ)+1-i)
    have h2 := invFactorial_step ((p : ℤ)-i)
    have h3 := invFactorial_step ((n : ℤ)+i+3)
    have h4 := invFactorial_step ((p : ℤ)+i+2)
    rw [show (n : ℤ)+1-i-1 = (n : ℤ)-i by ring] at h1
    rw [show (n : ℤ)+i+3-1 = (n : ℤ)+i+2 by ring] at h3
    rw [show (p : ℤ)+i+2-1 = (p : ℤ)+i+1 by ring] at h4
    unfold endpointKernel endpointBase
    rw [show i+1+d = i+d+1 by omega, Nat.factorial_succ]
    push_cast
    rw [show (n : ℤ)+1-(i+1) = (n : ℤ)-i by ring, show (p : ℤ)-(i+1) = (p : ℤ)-i-1 by ring, show (i : ℤ)+1-d = (i : ℤ)+1-d by rfl, show (n : ℤ)+1+(i+1)+1 = (n : ℤ)+i+3 by ring, show (p : ℤ)+(i+1)+1 = (p : ℤ)+i+2 by ring, h1, h2]
    have h3' : ((n : ℚ)+i+3)*invFactorial ((n : ℤ)+i+3) = invFactorial ((n : ℤ)+i+2) := by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using h3.symm
    have h4' : ((p : ℚ)+i+2)*invFactorial ((p : ℤ)+i+2) = invFactorial ((p : ℤ)+i+1) := by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using h4.symm
    calc
      _ = (↑i+↑d+1)*((↑n+1-↑i : ℤ) : ℚ)*((↑p-↑i : ℤ) : ℚ)* (Nat.factorial (i+d) : ℚ)*invFactorial ((n : ℤ)+1-i)* invFactorial ((p : ℤ)-i)*invFactorial ((i : ℤ)+1-d)* (((n : ℚ)+i+3)*invFactorial ((n : ℤ)+i+3))*
        (((p : ℚ)+i+2)*invFactorial ((p : ℤ)+i+2)) := by ring
      _ = _ := by rw [h3',h4']; push_cast; ring
  have endpointKernel_vanish (n p d i : ℕ) (h : i < d ∨ n < i ∨ p < i) : endpointKernel n p d i = 0 := by
    unfold endpointKernel
    rcases h with h | h | h
    · rw [invFactorial_neg ((i : ℤ)-d) (by omega)]; ring
    · rw [invFactorial_neg ((n : ℤ)-i) (by omega)]; ring
    · rw [invFactorial_neg ((p : ℤ)-i) (by omega)]; ring
  have endpointConstant_step (n p d : ℕ) (hd : d ≤ n) : ((n : ℚ)+p-d+1)*endpointConstant (n+1) p d = ((n : ℚ)+1-d)*((n : ℚ)+1)*((n : ℚ)+p+2)*endpointConstant n p d := by
    have h := invFactorial_step ((n : ℤ)+p-d+1)
    rw [show (n : ℤ)+p-d+1-1 = (n : ℤ)+p-d by ring] at h
    have h' : ((n : ℚ)+p-d+1)*invFactorial ((n : ℤ)+p-d+1) = invFactorial ((n : ℤ)+p-d) := by
      simpa only [Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one] using h.symm
    unfold endpointConstant
    rw [show n+1-d = n-d+1 by omega, show n+1+p+1 = (n+p+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rw [show (n : ℤ)+1+p-d = (n : ℤ)+p-d+1 by ring]
    rw [Nat.cast_sub hd]
    calc
      _ = ((n : ℚ)+1-d)*((n : ℚ)+1)*((n : ℚ)+p+2)* (Nat.factorial (n-d) : ℚ)*Nat.factorial p*Nat.factorial (p-d)* Nat.factorial n*Nat.factorial (n+p+1)*invFactorial (d : ℤ)* (((n : ℚ)+p-d+1)*invFactorial ((n : ℤ)+p-d+1)) := by ring
      _ = _ := by rw [h']; ring
  have endpoint_polynomial_certificate (n p d i : ℚ) : (n+1-d)*(n+1)*(n+p+2)*(2*i+1)*(i+1-d) - (n+p-d+1)*(2*i+1)*(n+1-i)*(n+i+2)*(i+1-d) = -(i+1)*(i+1-d)*(i+d+1)*(n+1-i)*(p-i) + i*(i-d)*(p+i+1)*(n+i+2)*(i+1-d) := by ring
  have endpoint_kernel_wz (n p d i : ℕ) : ((n : ℚ)+1-d)*((n : ℚ)+1)*((n : ℚ)+p+2)*(2*(i : ℚ)+1)* endpointKernel (n+1) p d i - ((n : ℚ)+p-d+1)*(2*(i : ℚ)+1)*endpointKernel n p d i = -((i : ℚ)+1)*((i : ℚ)+1-d)*
        (((p : ℚ)+i+2)*((n : ℚ)+i+3)*endpointKernel (n+1) p d (i+1)) + (i : ℚ)*((i : ℚ)-d)*((p : ℚ)+i+1)*((n : ℚ)+i+2)* endpointKernel (n+1) p d i := by
    rw [endpointKernel_next_base, endpointKernel_new_base, endpointKernel_old_base]
    linear_combination endpoint_polynomial_certificate (n : ℚ) p d i * endpointBase n p d i
  have endpoint_wz_step (n p d i : ℕ) (hd : d ≤ n) : endpointWeight (n+1) p d i - endpointWeight n p d i = endpointFlux n p d (i+1) - endpointFlux n p d i := by
    have hnd : (0 : ℚ) < (n : ℚ)+1-d := by
      have hdq : (d : ℚ) ≤ n := by exact_mod_cast hd
      linarith
    have hD : ((n : ℚ)+1-d)*((n : ℚ)+1)*((n : ℚ)+p+2) ≠ 0 := by positivity
    have hc := endpointConstant_step n p d hd
    apply mul_left_cancel₀ hD
    calc
      _ = endpointConstant (n+1) p d * (((n : ℚ)+1-d)*((n : ℚ)+1)*((n : ℚ)+p+2)*(2*(i : ℚ)+1)* endpointKernel (n+1) p d i - ((n : ℚ)+p-d+1)*(2*(i : ℚ)+1)*endpointKernel n p d i) := by
        unfold endpointWeight
        linear_combination (2*(i : ℚ)+1)*endpointKernel n p d i * hc
      _ = _ := by
        rw [endpoint_kernel_wz]
        unfold endpointFlux
        push_cast
        field_simp [hD]
        ring
  have endpoint_flux_zero (n p d : ℕ) : endpointFlux n p d 0 = 0 := by
    simp [endpointFlux]
  have endpoint_flux_end (n p d : ℕ) : endpointFlux n p d (p+1) = 0 := by
    unfold endpointFlux
    rw [endpointKernel_vanish _ _ _ _ (Or.inr (Or.inr (by omega)))]
    ring
  have endpoint_sum_step (n p d : ℕ) (hd : d ≤ n) : (∑ i ∈ range (p+1), endpointWeight (n+1) p d i) = ∑ i ∈ range (p+1), endpointWeight n p d i := by
    apply sub_eq_zero.mp
    rw [← sum_sub_distrib]
    simp_rw [endpoint_wz_step n p d _ hd]
    rw [sum_range_sub, endpoint_flux_zero, endpoint_flux_end]
    ring
  induction n, hd using Nat.le_induction with
  | base => exact endpoint_base_sum p d hp
  | succ n hn ih => rw [endpoint_sum_step n p d hn, ih]
private lemma signed_endpoint_normalization (n p d : ℕ) (hd : d ≤ n) (hp : d ≤ p) : (∑ i ∈ range (p+1), signedEndpointWeight n p d i) = (-1)^d := by
  have signed_endpoint_base_sum (p d : ℕ) (hp : d ≤ p) : (∑ i ∈ range (p+1), signedEndpointWeight d p d i) = (-1)^d := by
    have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
      simp only [invFactorial, if_neg (not_le.mpr hz)]
    have invFactorial_nat (n : ℕ) : invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
      simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    have invFactorial_zero : invFactorial (0 : ℤ) = 1 := by
      simp [invFactorial]
    have invFactorial_nat_sub (n m : ℕ) (h : m ≤ n) : invFactorial ((n : ℤ)-(m : ℤ)) = (Nat.factorial (n-m) : ℚ)⁻¹ := by
      rw [← Int.natCast_sub h, invFactorial_nat]
    have endpointKernel_vanish (n p d i : ℕ) (h : i < d ∨ n < i ∨ p < i) : endpointKernel n p d i = 0 := by
      unfold endpointKernel
      rcases h with h | h | h
      · rw [invFactorial_neg ((i : ℤ)-d) (by omega)]; ring
      · rw [invFactorial_neg ((n : ℤ)-i) (by omega)]; ring
      · rw [invFactorial_neg ((p : ℤ)-i) (by omega)]; ring
    have endpoint_base_term (p d : ℕ) (hp : d ≤ p) : signedEndpointConstant d p d * (2*(d : ℚ)+1)*endpointKernel d p d d = 1 := by
      unfold signedEndpointConstant endpointKernel
      simp only [Nat.sub_self, Nat.factorial_zero, Int.sub_self, invFactorial_zero, one_mul, mul_one]
      rw [invFactorial_nat_sub p d hp, show (d : ℤ)+d+1 = ((d+d+1 : ℕ) : ℤ) by omega, show (p : ℤ)+d+1 = ((p+d+1 : ℕ) : ℤ) by omega, invFactorial_nat, invFactorial_nat, show p+d+1 = d+p+1 by omega, Nat.factorial_succ (d+d)]
      have hf : ∀ t : ℕ, (Nat.factorial t : ℚ) ≠ 0 := fun t => by exact_mod_cast Nat.factorial_ne_zero t
      have hd : ((d+d+1 : ℕ) : ℚ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [sum_eq_single d]
    · unfold signedEndpointWeight
      calc
        _ = (-1 : ℚ)^d*(signedEndpointConstant d p d*(2*(d : ℚ)+1)*endpointKernel d p d d) := by ring
        _ = _ := by rw [endpoint_base_term p d hp]; ring
    · intro i hi hdi
      unfold signedEndpointWeight
      rw [endpointKernel_vanish _ _ _ _ (by omega)]
      ring
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))
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
  have endpointKernel_new_base (n p d i : ℕ) : endpointKernel (n+1) p d i = ((i : ℚ)+1-d)*endpointBase n p d i := by
    have h := invFactorial_step ((i : ℤ)+1-d)
    rw [show (i : ℤ)+1-d-1 = (i : ℤ)-d by ring] at h
    unfold endpointKernel endpointBase
    rw [h]
    push_cast
    rw [show (n : ℤ)+1+i+1 = (n : ℤ)+i+2 by ring]
    ring
  have endpointKernel_old_base (n p d i : ℕ) : endpointKernel n p d i = ((n : ℚ)+1-i)*((n : ℚ)+i+2)*((i : ℚ)+1-d)*endpointBase n p d i := by
    have h1 := invFactorial_step ((n : ℤ)+1-i)
    have h2 := invFactorial_step ((n : ℤ)+i+2)
    have h3 := invFactorial_step ((i : ℤ)+1-d)
    rw [show (n : ℤ)+1-i-1 = (n : ℤ)-i by ring] at h1
    rw [show (n : ℤ)+i+2-1 = (n : ℤ)+i+1 by ring] at h2
    rw [show (i : ℤ)+1-d-1 = (i : ℤ)-d by ring] at h3
    unfold endpointKernel endpointBase
    rw [h1,h2,h3]
    push_cast
    ring
  have endpointKernel_next_base (n p d i : ℕ) : ((p : ℚ)+i+2)*((n : ℚ)+i+3)*endpointKernel (n+1) p d (i+1) = ((i : ℚ)+d+1)*((n : ℚ)+1-i)*((p : ℚ)-i)*endpointBase n p d i := by
    have h1 := invFactorial_step ((n : ℤ)+1-i)
    have h2 := invFactorial_step ((p : ℤ)-i)
    have h3 := invFactorial_step ((n : ℤ)+i+3)
    have h4 := invFactorial_step ((p : ℤ)+i+2)
    rw [show (n : ℤ)+1-i-1 = (n : ℤ)-i by ring] at h1
    rw [show (n : ℤ)+i+3-1 = (n : ℤ)+i+2 by ring] at h3
    rw [show (p : ℤ)+i+2-1 = (p : ℤ)+i+1 by ring] at h4
    unfold endpointKernel endpointBase
    rw [show i+1+d = i+d+1 by omega, Nat.factorial_succ]
    push_cast
    rw [show (n : ℤ)+1-(i+1) = (n : ℤ)-i by ring, show (p : ℤ)-(i+1) = (p : ℤ)-i-1 by ring, show (i : ℤ)+1-d = (i : ℤ)+1-d by rfl, show (n : ℤ)+1+(i+1)+1 = (n : ℤ)+i+3 by ring, show (p : ℤ)+(i+1)+1 = (p : ℤ)+i+2 by ring, h1, h2]
    have h3' : ((n : ℚ)+i+3)*invFactorial ((n : ℤ)+i+3) = invFactorial ((n : ℤ)+i+2) := by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using h3.symm
    have h4' : ((p : ℚ)+i+2)*invFactorial ((p : ℤ)+i+2) = invFactorial ((p : ℤ)+i+1) := by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using h4.symm
    calc
      _ = (↑i+↑d+1)*((↑n+1-↑i : ℤ) : ℚ)*((↑p-↑i : ℤ) : ℚ)* (Nat.factorial (i+d) : ℚ)*invFactorial ((n : ℤ)+1-i)* invFactorial ((p : ℤ)-i)*invFactorial ((i : ℤ)+1-d)* (((n : ℚ)+i+3)*invFactorial ((n : ℤ)+i+3))*
        (((p : ℚ)+i+2)*invFactorial ((p : ℤ)+i+2)) := by ring
      _ = _ := by rw [h3',h4']; push_cast; ring
  have endpointKernel_vanish (n p d i : ℕ) (h : i < d ∨ n < i ∨ p < i) : endpointKernel n p d i = 0 := by
    unfold endpointKernel
    rcases h with h | h | h
    · rw [invFactorial_neg ((i : ℤ)-d) (by omega)]; ring
    · rw [invFactorial_neg ((n : ℤ)-i) (by omega)]; ring
    · rw [invFactorial_neg ((p : ℤ)-i) (by omega)]; ring
  have signedEndpointConstant_step (n p d : ℕ) (hd : d ≤ n) : signedEndpointConstant (n+1) p d = ((n : ℚ)+1-d)*((n : ℚ)+p+2)*signedEndpointConstant n p d := by
    unfold signedEndpointConstant
    rw [show n+1-d = n-d+1 by omega, show n+1+p+1 = (n+p+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rw [Nat.cast_sub hd]
    ring
  have signed_endpoint_polynomial_certificate (n p d i : ℚ) : (n+1-d)*(n+p+2)*(2*i+1)*(i+1-d) - (2*i+1)*(n+1-i)*(n+i+2)*(i+1-d) = (i+1-d)*(i+d+1)*(n+1-i)*(p-i) + (i-d)*(p+i+1)*(n+i+2)*(i+1-d) := by ring
  have signed_endpoint_kernel_wz (n p d i : ℕ) : ((n : ℚ)+1-d)*((n : ℚ)+p+2)*(2*(i : ℚ)+1)*endpointKernel (n+1) p d i - (2*(i : ℚ)+1)*endpointKernel n p d i = ((i : ℚ)+1-d)* (((p : ℚ)+i+2)*((n : ℚ)+i+3)*endpointKernel (n+1) p d (i+1)) +
        ((i : ℚ)-d)*((p : ℚ)+i+1)*((n : ℚ)+i+2)*endpointKernel (n+1) p d i := by
    rw [endpointKernel_next_base, endpointKernel_new_base, endpointKernel_old_base]
    linear_combination signed_endpoint_polynomial_certificate (n : ℚ) p d i * endpointBase n p d i
  have signed_endpoint_wz_step (n p d i : ℕ) (hd : d ≤ n) : signedEndpointWeight (n+1) p d i - signedEndpointWeight n p d i = signedEndpointFlux n p d (i+1) - signedEndpointFlux n p d i := by
    have hnd : (0 : ℚ) < (n : ℚ)+1-d := by
      have hdq : (d : ℚ) ≤ n := by exact_mod_cast hd
      linarith
    have hD : ((n : ℚ)+1-d)*((n : ℚ)+p+2) ≠ 0 := by positivity
    have hc := signedEndpointConstant_step n p d hd
    apply mul_left_cancel₀ hD
    calc
      _ = (-1 : ℚ)^i*signedEndpointConstant (n+1) p d * (((n : ℚ)+1-d)*((n : ℚ)+p+2)*(2*(i : ℚ)+1)*endpointKernel (n+1) p d i - (2*(i : ℚ)+1)*endpointKernel n p d i) := by
        unfold signedEndpointWeight
        linear_combination (-1 : ℚ)^i*(2*(i : ℚ)+1)*endpointKernel n p d i * hc
      _ = _ := by
        rw [signed_endpoint_kernel_wz]
        unfold signedEndpointFlux
        rw [pow_succ]
        push_cast
        field_simp [hD]
        ring
  have signed_endpoint_flux_zero (n p d : ℕ) : signedEndpointFlux n p d 0 = 0 := by
    by_cases hd : d = 0
    · subst d; simp [signedEndpointFlux]
    · unfold signedEndpointFlux
      rw [endpointKernel_vanish _ _ _ _ (Or.inl (by omega))]
      ring
  have signed_endpoint_flux_end (n p d : ℕ) : signedEndpointFlux n p d (p+1) = 0 := by
    unfold signedEndpointFlux
    rw [endpointKernel_vanish _ _ _ _ (Or.inr (Or.inr (by omega)))]
    ring
  have signed_endpoint_sum_step (n p d : ℕ) (hd : d ≤ n) : (∑ i ∈ range (p+1), signedEndpointWeight (n+1) p d i) = ∑ i ∈ range (p+1), signedEndpointWeight n p d i := by
    apply sub_eq_zero.mp
    rw [← sum_sub_distrib]
    simp_rw [signed_endpoint_wz_step n p d _ hd]
    rw [sum_range_sub, signed_endpoint_flux_zero, signed_endpoint_flux_end]
    ring
  induction n, hd using Nat.le_induction with
  | base => exact signed_endpoint_base_sum p d hp
  | succ n hn ih => rw [signed_endpoint_sum_step n p d hn, ih]
private lemma stretched_row_alternating (n j d : ℕ) (hdn : d ≤ n) : (∑ i ∈ range (2*j+d+1), (-1 : ℝ)^i* (((n+2*j+1 : ℕ) : ℝ)*(2*(i : ℝ)+1)*sixJ n n (2*i) (2*j) (2*(j+d)) (n+2*j)^2)) = (-1 : ℝ)^d*Nat.factorial n*Nat.factorial (2*j+d) /
          (Nat.factorial d*Nat.factorial (n+2*j)) := by
  have stretched_racah_sum (n j d i : ℕ) (hdn : d ≤ n) (hdi : d ≤ i)
      (hin : i ≤ n) (hip : i ≤ 2*j+d) : racahSum n n (2*i) (2*j) (2*(j+d)) (n+2*j) = (-1 : ℚ)^(n+2*j+d)*Nat.factorial (n+2*j+d+1) / (Nat.factorial (2*j+d-i)*Nat.factorial d*Nat.factorial (n-i)* Nat.factorial i*Nat.factorial (i-d)) := by
    have hl : lower n n (2*i) (2*j) (2*(j+d)) (n+2*j) = n+2*j+d := by
      unfold lower
      omega
    have hu : upper n n (2*i) (2*j) (2*(j+d)) (n+2*j) = n+2*j+d := by
      unfold upper
      omega
    unfold racahSum
    rw [hl,hu,sum_eq_single (n+2*j+d)]
    · rw [if_pos (by omega)]
      unfold racahTerm
      rw [show (n+n+2*i)/2=n+i by omega, show (n+2*(j+d)+(n+2*j))/2=n+2*j+d by omega, show (2*j+n+(n+2*j))/2=n+2*j by omega, show (2*j+2*(j+d)+2*i)/2=2*j+d+i by omega, show (n+n+2*j+2*(j+d))/2=n+2*j+d by omega,
        show (n+2*i+2*(j+d)+(n+2*j))/2=n+2*j+d+i by omega, show (2*i+n+(n+2*j)+2*j)/2=n+2*j+i by omega, show n+2*j+d-(n+i)=2*j+d-i by omega, show n+2*j+d-(n+2*j)=d by omega, show n+2*j+d-(2*j+d+i)=n-i by omega,
        show n+2*j+d+i-(n+2*j+d)=i by omega, show n+2*j+i-(n+2*j+d)=i-d by omega]
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
    · intro z hz hne
      rw [if_neg (by simp only [mem_range] at hz; omega)]
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))
  have endpoint_alternating_sum (n p d : ℕ) (hd : d ≤ n) (hp : d ≤ p) : (∑ i ∈ range (p+1), (-1 : ℚ)^i*endpointWeight n p d i) = (-1 : ℚ)^d*Nat.factorial n*Nat.factorial p / (Nat.factorial d*Nat.factorial (n+p-d)) := by
    have invFactorial_nat (n : ℕ) : invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
      simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    have invFactorial_nat_sub (n m : ℕ) (h : m ≤ n) : invFactorial ((n : ℤ)-(m : ℤ)) = (Nat.factorial (n-m) : ℚ)⁻¹ := by
      rw [← Int.natCast_sub h, invFactorial_nat]
    have hterm (i : ℕ) : (-1 : ℚ)^i*endpointWeight n p d i = (Nat.factorial n*Nat.factorial p*invFactorial d*invFactorial ((n : ℤ)+p-d)) * signedEndpointWeight n p d i := by
      unfold endpointWeight signedEndpointWeight endpointConstant signedEndpointConstant
      ring
    simp_rw [hterm]
    rw [← mul_sum, signed_endpoint_normalization n p d hd hp, show (n : ℤ)+p-d = ((n+p : ℕ) : ℤ)-(d : ℤ) by omega, invFactorial_nat_sub (n+p) d (by omega), invFactorial_nat]
    rw [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
    simp only [invFactorial, if_neg (not_le.mpr hz)]
  have invFactorial_nat (n : ℕ) : invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
    simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
  have invFactorial_nat_sub (n m : ℕ) (h : m ≤ n) : invFactorial ((n : ℤ)-(m : ℤ)) = (Nat.factorial (n-m) : ℚ)⁻¹ := by
    rw [← Int.natCast_sub h, invFactorial_nat]
  have endpointKernel_vanish (n p d i : ℕ) (h : i < d ∨ n < i ∨ p < i) : endpointKernel n p d i = 0 := by
    unfold endpointKernel
    rcases h with h | h | h
    · rw [invFactorial_neg ((i : ℤ)-d) (by omega)]; ring
    · rw [invFactorial_neg ((n : ℤ)-i) (by omega)]; ring
    · rw [invFactorial_neg ((p : ℤ)-i) (by omega)]; ring
  have endpointWeight_factorials (n p d i : ℕ)
      (hd : d ≤ n) (hp : d ≤ p) (hdi : d ≤ i) (hin : i ≤ n) (hip : i ≤ p) : endpointWeight n p d i = ((Nat.factorial (n-d)*Nat.factorial p*Nat.factorial (p-d)*Nat.factorial n*
          Nat.factorial (n+p+1) : ℚ)/(Nat.factorial d*Nat.factorial (n+p-d))) * ((2*(i : ℚ)+1)*Nat.factorial (i+d)/ (Nat.factorial (n-i)*Nat.factorial (p-i)*Nat.factorial (i-d)* Nat.factorial (n+i+1)*Nat.factorial (p+i+1))) := by
    unfold endpointWeight endpointConstant endpointKernel
    rw [invFactorial_nat_sub n i hin, invFactorial_nat_sub p i hip, invFactorial_nat_sub i d hdi, show (n : ℤ)+i+1 = ((n+i+1 : ℕ) : ℤ) by omega, show (p : ℤ)+i+1 = ((p+i+1 : ℕ) : ℤ) by omega,
      show (n : ℤ)+p-d = ((n+p : ℕ) : ℤ)-(d : ℤ) by omega, invFactorial_nat_sub (n+p) d (by omega), invFactorial_nat, invFactorial_nat, invFactorial_nat]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have deltaSq_pos (a b c : ℕ) : 0 < deltaSq a b c := by
    unfold deltaSq
    positivity
  have sixJ_square (a b c d e f : ℕ) (ha : admissible a b c d e f) : sixJ a b c d e f ^ 2 = ((deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c* racahSum a b c d e f ^ 2 : ℚ) : ℝ) := by
    have hq : (0 : ℚ) ≤ deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c := by
      have h1 := deltaSq_pos a b c
      have h2 := deltaSq_pos a e f
      have h3 := deltaSq_pos d b f
      have h4 := deltaSq_pos d e c
      positivity
    have hr : (0 : ℝ) ≤ ((deltaSq a b c*deltaSq a e f*deltaSq d b f*deltaSq d e c : ℚ) : ℝ) := by
      exact_mod_cast hq
    rw [sixJ, if_pos ha, mul_pow, Real.sq_sqrt hr]
    push_cast
    rfl
  have stretched_delta_first (n i : ℕ) (hi : i ≤ n) : deltaSq n n (2*i) = Nat.factorial (n-i)*Nat.factorial i*Nat.factorial i / (Nat.factorial (n+i+1) : ℚ) := by
    unfold deltaSq
    rw [show (n+n-2*i)/2=n-i by omega, show (n+2*i-n)/2=i by omega, show (n+n+2*i)/2+1=n+i+1 by omega]
  have stretched_delta_second (n j d : ℕ) (hd : d ≤ n) : deltaSq n (2*(j+d)) (n+2*j) = Nat.factorial d*Nat.factorial (n-d)*Nat.factorial (2*j+d) / (Nat.factorial (n+2*j+d+1) : ℚ) := by
    unfold deltaSq
    rw [show (n+2*(j+d)-(n+2*j))/2=d by omega, show (n+(n+2*j)-2*(j+d))/2=n-d by omega, show (2*(j+d)+(n+2*j)-n)/2=2*j+d by omega, show (n+2*(j+d)+(n+2*j))/2+1=n+2*j+d+1 by omega]
  have stretched_delta_third (n j : ℕ) : deltaSq (2*j) n (n+2*j) = Nat.factorial (2*j)*Nat.factorial n / (Nat.factorial (n+2*j+1) : ℚ) := by
    unfold deltaSq
    rw [show (2*j+n-(n+2*j))/2=0 by omega, show (2*j+(n+2*j)-n)/2=2*j by omega, show (n+(n+2*j)-2*j)/2=n by omega, show (2*j+n+(n+2*j))/2+1=n+2*j+1 by omega]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
  have stretched_delta_fourth (j d i : ℕ) (hd : d ≤ i) (hi : i ≤ 2*j+d) : deltaSq (2*j) (2*(j+d)) (2*i) = Nat.factorial (2*j+d-i)*Nat.factorial (i-d)*Nat.factorial (i+d) / (Nat.factorial (2*j+d+i+1) : ℚ) := by
    unfold deltaSq
    rw [show (2*j+2*(j+d)-2*i)/2=2*j+d-i by omega, show (2*j+2*i-2*(j+d))/2=i-d by omega, show (2*(j+d)+2*i-2*j)/2=i+d by omega, show (2*j+2*(j+d)+2*i)/2+1=2*j+d+i+1 by omega]
  have stretched_row_square (n j d i : ℕ) (hdn : d ≤ n) : ((n+2*j+1 : ℕ) : ℝ)*(2*(i : ℝ)+1)* sixJ n n (2*i) (2*j) (2*(j+d)) (n+2*j)^2 = (endpointWeight n (2*j+d) d i : ℝ) := by
    by_cases hdi : d ≤ i
    · by_cases hin : i ≤ n
      · by_cases hip : i ≤ 2*j+d
        · have ha : admissible n n (2*i) (2*j) (2*(j+d)) (n+2*j) := by
            unfold admissible triangle
            omega
          rw [sixJ_square _ _ _ _ _ _ ha]
          rw [stretched_delta_first n i hin, stretched_delta_second n j d hdn, stretched_delta_third n j, stretched_delta_fourth j d i hdi hip, stretched_racah_sum n j d i hdn hdi hin hip,
            endpointWeight_factorials n (2*j+d) d i hdn (by omega) hdi hin hip]
          have hsign : ((-1 : ℚ)^(n+2*j+d))^2 = 1 := by
            rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]
          have he : ((n+2*j+1 : ℕ) : ℚ)*(2*(i : ℚ)+1)* ((Nat.factorial (n-i)*Nat.factorial i*Nat.factorial i/(Nat.factorial (n+i+1) : ℚ))* (Nat.factorial d*Nat.factorial (n-d)*Nat.factorial (2*j+d)/(Nat.factorial (n+2*j+d+1) : ℚ))*
              (Nat.factorial (2*j)*Nat.factorial n/(Nat.factorial (n+2*j+1) : ℚ))* (Nat.factorial (2*j+d-i)*Nat.factorial (i-d)*Nat.factorial (i+d)/(Nat.factorial (2*j+d+i+1) : ℚ))* ((-1 : ℚ)^(n+2*j+d)*Nat.factorial (n+2*j+d+1)/
                (Nat.factorial (2*j+d-i)*Nat.factorial d*Nat.factorial (n-i)*Nat.factorial i*Nat.factorial (i-d)))^2) = (Nat.factorial (n-d)*Nat.factorial (2*j+d)*Nat.factorial (2*j+d-d)*Nat.factorial n*
                Nat.factorial (n+(2*j+d)+1)/(Nat.factorial d*Nat.factorial (n+(2*j+d)-d) : ℚ))* ((2*(i : ℚ)+1)*Nat.factorial (i+d)/(Nat.factorial (n-i)*Nat.factorial (2*j+d-i)*
                Nat.factorial (i-d)*Nat.factorial (n+i+1)*Nat.factorial (2*j+d+i+1) : ℚ)) := by
            rw [div_pow, mul_pow, hsign, one_mul, show 2*j+d-d=2*j by omega, show n+(2*j+d)-d=n+2*j by omega, show n+(2*j+d)+1=n+2*j+d+1 by omega, Nat.factorial_succ (n+2*j)]
            have hf : ∀ t : ℕ, (Nat.factorial t : ℚ) ≠ 0 := fun t => by exact_mod_cast Nat.factorial_ne_zero t
            have hn : ((n+2*j+1 : ℕ) : ℚ) ≠ 0 := by positivity
            field_simp
            push_cast
            ring
          exact_mod_cast he
        · have ha : ¬ admissible n n (2*i) (2*j) (2*(j+d)) (n+2*j) := by
            unfold admissible triangle
            omega
          rw [sixJ, if_neg ha, endpointWeight, endpointKernel_vanish _ _ _ _ (Or.inr (Or.inr (by omega)))]
          simp
      · have ha : ¬ admissible n n (2*i) (2*j) (2*(j+d)) (n+2*j) := by
          unfold admissible triangle
          omega
        rw [sixJ, if_neg ha, endpointWeight, endpointKernel_vanish _ _ _ _ (Or.inr (Or.inl (by omega)))]
        simp
    · have ha : ¬ admissible n n (2*i) (2*j) (2*(j+d)) (n+2*j) := by
        unfold admissible triangle
        omega
      rw [sixJ, if_neg ha, endpointWeight, endpointKernel_vanish _ _ _ _ (Or.inl (by omega))]
      simp
  simp_rw [stretched_row_square n j d _ hdn]
  have h := endpoint_alternating_sum n (2*j+d) d hdn (by omega)
  rw [show n+(2*j+d)-d=n+2*j by omega] at h
  exact_mod_cast h
lemma signed_stretched_endpoint_match (n j d : ℕ) (hdn : d ≤ n) : (∑ i ∈ range (2*j+d+1), (-1 : ℝ)^i* (((n+2*j+1 : ℕ) : ℝ)*(2*(i : ℝ)+1)*sixJ n n (2*i) (2*j) (2*(j+d)) (n+2*j)^2)) = (-1 : ℝ)^(n+2*j)*((n+2*j+1 : ℕ) : ℝ)*
        sixJ n (2*(j+d)) (n+2*j) n (2*j) (n+2*j) := by
  have star_stretched_raw_sum (n j d : ℕ) (hdn : d ≤ n) : racahSum n (2*(j+d)) (n+2*j) n (2*j) (n+2*j) = (-1 : ℚ)^(n+2*j+d)*Nat.factorial (n+2*j+d+1) / (Nat.factorial d*Nat.factorial d*Nat.factorial (2*j)*Nat.factorial (n-d)) := by
    have hl : lower n (2*(j+d)) (n+2*j) n (2*j) (n+2*j) = n+2*j+d := by
      unfold lower
      omega
    have hu : upper n (2*(j+d)) (n+2*j) n (2*j) (n+2*j) = n+2*j+d := by
      unfold upper
      omega
    unfold racahSum
    rw [hl,hu,sum_eq_single (n+2*j+d)]
    · rw [if_pos (by omega)]
      unfold racahTerm
      rw [show (n+2*(j+d)+(n+2*j))/2=n+2*j+d by omega, show (n+2*j+(n+2*j))/2=n+2*j by omega, show (n+2*(j+d)+n+2*j)/2=n+2*j+d by omega, show (2*(j+d)+(n+2*j)+2*j+(n+2*j))/2=n+4*j+d by omega, show ((n+2*j)+n+(n+2*j)+n)/2=2*n+2*j by omega,
        show n+2*j+d-(n+2*j)=d by omega, show n+4*j+d-(n+2*j+d)=2*j by omega, show 2*n+2*j-(n+2*j+d)=n-d by omega]
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
    · intro z hz hne
      rw [if_neg (by simp only [mem_range] at hz; omega)]
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))
  have deltaSq_pos (a b c : ℕ) : 0 < deltaSq a b c := by
    unfold deltaSq
    positivity
  have stretched_delta_second (n j d : ℕ) (hd : d ≤ n) : deltaSq n (2*(j+d)) (n+2*j) = Nat.factorial d*Nat.factorial (n-d)*Nat.factorial (2*j+d) / (Nat.factorial (n+2*j+d+1) : ℚ) := by
    unfold deltaSq
    rw [show (n+2*(j+d)-(n+2*j))/2=d by omega, show (n+(n+2*j)-2*(j+d))/2=n-d by omega, show (2*(j+d)+(n+2*j)-n)/2=2*j+d by omega, show (n+2*(j+d)+(n+2*j))/2+1=n+2*j+d+1 by omega]
  have stretched_delta_third (n j : ℕ) : deltaSq (2*j) n (n+2*j) = Nat.factorial (2*j)*Nat.factorial n / (Nat.factorial (n+2*j+1) : ℚ) := by
    unfold deltaSq
    rw [show (2*j+n-(n+2*j))/2=0 by omega, show (2*j+(n+2*j)-n)/2=2*j by omega, show (n+(n+2*j)-2*j)/2=n by omega, show (2*j+n+(n+2*j))/2+1=n+2*j+1 by omega]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
  have deltaSq_swap (a b c : ℕ) : deltaSq a b c = deltaSq b a c := by
    unfold deltaSq
    rw [show b+a-c=a+b-c by omega, show b+a+c=a+b+c by omega]
    ring
  have star_stretched_value (n j d : ℕ) (hdn : d ≤ n) : sixJ n (2*(j+d)) (n+2*j) n (2*j) (n+2*j) = (-1 : ℝ)^(n+2*j+d)*Nat.factorial n*Nat.factorial (2*j+d) / (Nat.factorial d*Nat.factorial (n+2*j+1)) := by
    have ha : admissible n (2*(j+d)) (n+2*j) n (2*j) (n+2*j) := by
      unfold admissible triangle
      omega
    have hprod : deltaSq n (2*(j+d)) (n+2*j)*deltaSq n (2*j) (n+2*j)* deltaSq n (2*(j+d)) (n+2*j)*deltaSq n (2*j) (n+2*j) = (deltaSq n (2*(j+d)) (n+2*j)*deltaSq n (2*j) (n+2*j))^2 := by ring
    have hp : (0 : ℝ) ≤ ((deltaSq n (2*(j+d)) (n+2*j)*deltaSq n (2*j) (n+2*j) : ℚ) : ℝ) := by
      have h1 := deltaSq_pos n (2*(j+d)) (n+2*j)
      have h2 := deltaSq_pos n (2*j) (n+2*j)
      have hq : (0 : ℚ) ≤ deltaSq n (2*(j+d)) (n+2*j)*deltaSq n (2*j) (n+2*j) := by positivity
      exact_mod_cast hq
    rw [sixJ, if_pos ha, hprod, Rat.cast_pow, Real.sqrt_sq hp]
    rw [stretched_delta_second n j d hdn, deltaSq_swap n (2*j) (n+2*j), stretched_delta_third n j, star_stretched_raw_sum n j d hdn]
    have he : (Nat.factorial d*Nat.factorial (n-d)*Nat.factorial (2*j+d)/(Nat.factorial (n+2*j+d+1) : ℚ))* (Nat.factorial (2*j)*Nat.factorial n/(Nat.factorial (n+2*j+1) : ℚ))* ((-1 : ℚ)^(n+2*j+d)*Nat.factorial (n+2*j+d+1)/
          (Nat.factorial d*Nat.factorial d*Nat.factorial (2*j)*Nat.factorial (n-d))) = (-1 : ℚ)^(n+2*j+d)*Nat.factorial n*Nat.factorial (2*j+d)/ (Nat.factorial d*Nat.factorial (n+2*j+1)) := by
      have hf : ∀ t : ℕ, (Nat.factorial t : ℚ) ≠ 0 := fun t => by exact_mod_cast Nat.factorial_ne_zero t
      field_simp <;> ring
    exact_mod_cast he
  rw [stretched_row_alternating n j d hdn, star_stretched_value n j d hdn, show n+2*j+d=(n+2*j)+d by rfl, pow_add]
  have hsign : (-1 : ℝ)^(n+2*j)*(-1 : ℝ)^(n+2*j)=1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]
  have hf : ∀ t : ℕ, (Nat.factorial t : ℝ) ≠ 0 := fun t => by exact_mod_cast Nat.factorial_ne_zero t
  rw [Nat.factorial_succ (n+2*j), Nat.cast_mul]
  push_cast
  have hn : (n : ℝ)+2*j+1 ≠ 0 := by positivity
  field_simp
  linear_combination -(-1 : ℝ)^d*hsign
lemma dual_intertwining_orthogonality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix (Fin (m+1)) ι ℝ) (T : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (H : Matrix ι ι ℝ) (dk : Fin (m+1) → ℝ) (li : ι → ℝ)
    (hdk : Function.Injective dk) (hT : Tᵀ = T) (hH : Hᵀ = H)
    (hTU : T*U = U*diagonal li) (hDU : diagonal dk*U = U*H)
    (hedge : ∀ t : Fin m, T t.castSucc t.succ ≠ 0)
    (hanchor : (U*Uᵀ) (Fin.last m) (Fin.last m) = 1) : U*Uᵀ = 1 := by
  let Q := U*Uᵀ
  have hUD : Uᵀ*diagonal dk = H*Uᵀ := by
    have ht := congrArg Matrix.transpose hDU
    simpa only [transpose_mul, diagonal_transpose, hH] using ht
  have hUT : Uᵀ*T = diagonal li*Uᵀ := by
    have ht := congrArg Matrix.transpose hTU
    simpa only [transpose_mul, diagonal_transpose, hT] using ht
  have hDQ : diagonal dk*Q = Q*diagonal dk := by
    dsimp [Q]
    rw [← Matrix.mul_assoc, hDU, Matrix.mul_assoc, ← hUD, ← Matrix.mul_assoc]
  have hTQ : T*Q = Q*T := by
    dsimp [Q]
    rw [← Matrix.mul_assoc, hTU, Matrix.mul_assoc, ← hUT, ← Matrix.mul_assoc]
  have hoff (i j : Fin (m+1)) (hij : i ≠ j) : Q i j = 0 := by
    have h := congrArg (fun A => A i j) hDQ
    simp only [diagonal_mul, mul_diagonal] at h
    have hne : dk i-dk j ≠ 0 := sub_ne_zero.mpr (fun he => hij (hdk he))
    have hz : (dk i-dk j)*Q i j = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hne
  let q := fun i => Q i i
  have hQ : Q = diagonal q := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [q]
    · simp [hoff i j hij, hij]
  have hstep (t : Fin m) : q t.succ = q t.castSucc := by
    have h := congrArg (fun A => A t.castSucc t.succ) hTQ
    rw [hQ] at h
    simp only [mul_diagonal, diagonal_mul] at h
    have hz : T t.castSucc t.succ*(q t.succ-q t.castSucc) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hedge t))
  have hconst : ∀ i : Fin (m+1), q i = q 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hstep i).trans ih
  have hzero : q 0 = 1 := (hconst (Fin.last m)).symm.trans hanchor
  have hone : q = fun _ => (1 : ℝ) := funext (fun i => (hconst i).trans hzero)
  change Q = 1
  rw [hQ, hone, diagonal_one]
def jacobiEdgeSq (s j l k : ℚ) : ℚ := (k^2-(s-j)^2)*((s+j+1)^2-k^2)*(k^2-(s-l)^2)*((s+l+1)^2-k^2) / (4*k^2*(2*k-1)*(2*k+1))

def triangleSqProduct (a b u c d y : ℕ) : ℚ := deltaSq a b u*deltaSq a d y*deltaSq c b y*deltaSq c d u

def raisingNumerator (a b c d y : ℕ) : ℚ := (((y : ℚ)/2+1)^2-(((a : ℚ)-d)/2)^2)* (((y : ℚ)/2+1)^2-(((b : ℚ)-c)/2)^2)

def raisingDenominator (a b c d y : ℕ) : ℚ := ((((a : ℚ)+d)/2+1)^2-((y : ℚ)/2+1)^2)* ((((b : ℚ)+c)/2+1)^2-((y : ℚ)/2+1)^2)

noncomputable def recurrenceUpperCoefficient (a b c d y : ℕ) : ℝ := Real.sqrt ((raisingNumerator a b c d y*raisingDenominator a b c d y : ℚ) : ℝ) / ((2*((y : ℚ)/2+1)*(2*((y : ℚ)/2)+1) : ℚ) : ℝ)

noncomputable def recurrenceLowerCoefficient (a b c d y : ℕ) : ℝ := Real.sqrt ((raisingNumerator a b c d (y-2)*raisingDenominator a b c d (y-2) : ℚ) : ℝ) / ((2*((y : ℚ)/2)*(2*((y : ℚ)/2)+1) : ℚ) : ℝ)

def channelWidth (n j l : ℕ) : ℕ := min n (j+l) - (l-j)

def channelBase (n j l : ℕ) : ℕ := max n (j+l) - min n (j+l) + (l-j)

end D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
